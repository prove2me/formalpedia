-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedSourceBridge.chunkSound5_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T04:35:16.536196+00:00
-- url     : https://prove2.me/submissions/8fe1faae-43dc-45c9-bd09-e8ec5c79d8e8

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E077
import Definitions.Def_OAIQ106E086
import Definitions.Def_OAIQ106E094
import Definitions.Def_OAIQ106E190
import Definitions.Def_OAIQ106E191
import Definitions.Def_OAIQ106E102
import Definitions.Def_OAIQ106E109
import Definitions.Def_OAIQ106E110
import Definitions.Def_OAIQ106E111
import Definitions.Def_OAIQ106E112
import Definitions.Def_OAIQ106E113
import Definitions.Def_OAIQ106E114
import Definitions.Def_OAIQ106E119
import Definitions.Def_OAIQ106E123
import Definitions.Def_OAIQ106E128
import Definitions.Def_OAIQ106E140
import Definitions.Def_OAIQ106E141
import Definitions.Def_OAIQ106E142
import Definitions.Def_OAIQ106E144
import Definitions.Def_OAIQ106E145
import Definitions.Def_OAIQ106E146
import Definitions.Def_OAIQ106E147
import Definitions.Def_OAIQ106E148
import Definitions.Def_OAIQ106E170
import Definitions.Def_OAIQ106E171
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound91_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound92_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound94_e

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical14
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical1821 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1821 raw1821Labels = mixedMoment B node4890 node4890Labels := by
  calc
    mixedMoment B raw1821 raw1821Labels = mixedMoment B raw1821step0 raw1821step0Labels := by
      have ha : raw1821step0 = (fun i j => raw1821 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1821step0 raw1821; decide +kernel
      have hl : raw1821step0Labels = raw1821Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1821 raw1821Labels permutation8 permutation4
    mixedMoment B raw1821step0 raw1821step0Labels = mixedMoment B raw1821step1 raw1821step1Labels := by
      have ha : raw1821step1 = raw1821step0 := by apply Matrix.ext; unfold raw1821step1 raw1821step0; decide +kernel
      have hl : raw1821step0Labels = labelEmbedding7 ∘ raw1821step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1821step0 raw1821step0Labels raw1821step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4890 node4890Labels := by rfl

theorem canonical1822 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1822 raw1822Labels = mixedMoment B node2247 node2247Labels := by
  calc
    mixedMoment B raw1822 raw1822Labels = mixedMoment B raw1822step0 raw1822step0Labels := by
      have ha : raw1822step0 = (fun i j => raw1822 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1822step0 raw1822; decide +kernel
      have hl : raw1822step0Labels = raw1822Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1822 raw1822Labels permutation8 permutation4
    _ = mixedMoment B node2247 node2247Labels := by rfl

theorem canonical1823 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1823 raw1823Labels = mixedMoment B node2290 node2290Labels := by
  calc
    mixedMoment B raw1823 raw1823Labels = mixedMoment B raw1823step0 raw1823step0Labels := by
      have ha : raw1823step0 = (fun i j => raw1823 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1823step0 raw1823; decide +kernel
      have hl : raw1823step0Labels = raw1823Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1823 raw1823Labels permutation8 permutation6
    mixedMoment B raw1823step0 raw1823step0Labels = mixedMoment B raw1823step1 raw1823step1Labels := by
      have ha : raw1823step1 = -raw1823step0 := by apply Matrix.ext; change ∀ i j, raw1823step1 i j = -(raw1823step0 i j); unfold raw1823step1 raw1823step0; decide +kernel
      have hl : raw1823step1Labels = raw1823step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1823step1 raw1823step1Labels = mixedMoment B raw1823step2 raw1823step2Labels := by
      have ha : raw1823step2 = raw1823step1 := by apply Matrix.ext; unfold raw1823step2 raw1823step1; decide +kernel
      have hl : raw1823step1Labels = labelEmbedding1 ∘ raw1823step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1823step1 raw1823step1Labels raw1823step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2290 node2290Labels := by rfl

theorem canonical1830 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1830 raw1830Labels = mixedMoment B node4899 node4899Labels := by
  calc
    mixedMoment B raw1830 raw1830Labels = mixedMoment B raw1830step0 raw1830step0Labels := by
      have ha : raw1830step0 = (fun i j => raw1830 (permutation2 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1830step0 raw1830; decide +kernel
      have hl : raw1830step0Labels = raw1830Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1830 raw1830Labels permutation2 permutation4
    mixedMoment B raw1830step0 raw1830step0Labels = mixedMoment B raw1830step1 raw1830step1Labels := by
      have ha : raw1830step1 = raw1830step0 := by apply Matrix.ext; unfold raw1830step1 raw1830step0; decide +kernel
      have hl : raw1830step0Labels = labelEmbedding7 ∘ raw1830step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1830step0 raw1830step0Labels raw1830step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4899 node4899Labels := by rfl

theorem canonical1831 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1831 raw1831Labels = mixedMoment B node2281 node2281Labels := by
  calc
    mixedMoment B raw1831 raw1831Labels = mixedMoment B raw1831step0 raw1831step0Labels := by
      have ha : raw1831step0 = (fun i j => raw1831 (permutation2 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1831step0 raw1831; decide +kernel
      have hl : raw1831step0Labels = raw1831Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1831 raw1831Labels permutation2 permutation4
    _ = mixedMoment B node2281 node2281Labels := by rfl

theorem canonical1832 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1832 raw1832Labels = mixedMoment B node2294 node2294Labels := by
  calc
    mixedMoment B raw1832 raw1832Labels = mixedMoment B raw1832step0 raw1832step0Labels := by
      have ha : raw1832step0 = (fun i j => raw1832 (permutation3 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1832step0 raw1832; decide +kernel
      have hl : raw1832step0Labels = raw1832Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1832 raw1832Labels permutation3 permutation6
    mixedMoment B raw1832step0 raw1832step0Labels = mixedMoment B raw1832step1 raw1832step1Labels := by
      have ha : raw1832step1 = -raw1832step0 := by apply Matrix.ext; change ∀ i j, raw1832step1 i j = -(raw1832step0 i j); unfold raw1832step1 raw1832step0; decide +kernel
      have hl : raw1832step1Labels = raw1832step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1832step1 raw1832step1Labels = mixedMoment B raw1832step2 raw1832step2Labels := by
      have ha : raw1832step2 = raw1832step1 := by apply Matrix.ext; unfold raw1832step2 raw1832step1; decide +kernel
      have hl : raw1832step1Labels = labelEmbedding1 ∘ raw1832step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1832step1 raw1832step1Labels raw1832step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2294 node2294Labels := by rfl

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

theorem canonical2277 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2277 raw2277Labels = mixedMoment B node5261 node5261Labels := by
  calc
    mixedMoment B raw2277 raw2277Labels = mixedMoment B raw2277step0 raw2277step0Labels := by
      have ha : raw2277step0 = (fun i j => raw2277 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2277step0 raw2277; decide +kernel
      have hl : raw2277step0Labels = raw2277Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2277 raw2277Labels permutation8 permutation4
    mixedMoment B raw2277step0 raw2277step0Labels = mixedMoment B raw2277step1 raw2277step1Labels := by
      have ha : raw2277step1 = raw2277step0 := by apply Matrix.ext; unfold raw2277step1 raw2277step0; decide +kernel
      have hl : raw2277step0Labels = labelEmbedding7 ∘ raw2277step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2277step0 raw2277step0Labels raw2277step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5261 node5261Labels := by rfl

theorem canonical2278 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2278 raw2278Labels = mixedMoment B node2726 node2726Labels := by
  calc
    mixedMoment B raw2278 raw2278Labels = mixedMoment B raw2278step0 raw2278step0Labels := by
      have ha : raw2278step0 = (fun i j => raw2278 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2278step0 raw2278; decide +kernel
      have hl : raw2278step0Labels = raw2278Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2278 raw2278Labels permutation8 permutation4
    _ = mixedMoment B node2726 node2726Labels := by rfl

theorem canonical2279 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2279 raw2279Labels = mixedMoment B node3545 node3545Labels := by
  calc
    mixedMoment B raw2279 raw2279Labels = mixedMoment B raw2279step0 raw2279step0Labels := by
      have ha : raw2279step0 = (fun i j => raw2279 (permutation31 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2279step0 raw2279; decide +kernel
      have hl : raw2279step0Labels = raw2279Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2279 raw2279Labels permutation31 permutation6
    mixedMoment B raw2279step0 raw2279step0Labels = mixedMoment B raw2279step1 raw2279step1Labels := by
      have ha : raw2279step1 = raw2279step0 := by apply Matrix.ext; unfold raw2279step1 raw2279step0; decide +kernel
      have hl : raw2279step0Labels = labelEmbedding1 ∘ raw2279step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2279step0 raw2279step0Labels raw2279step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3545 node3545Labels := by rfl

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

theorem canonical2307 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2307 raw2307Labels = mixedMoment B node5296 node5296Labels := by
  calc
    mixedMoment B raw2307 raw2307Labels = mixedMoment B raw2307step0 raw2307step0Labels := by
      have ha : raw2307step0 = (fun i j => raw2307 (permutation2 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2307step0 raw2307; decide +kernel
      have hl : raw2307step0Labels = raw2307Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2307 raw2307Labels permutation2 permutation4
    mixedMoment B raw2307step0 raw2307step0Labels = mixedMoment B raw2307step1 raw2307step1Labels := by
      have ha : raw2307step1 = raw2307step0 := by apply Matrix.ext; unfold raw2307step1 raw2307step0; decide +kernel
      have hl : raw2307step0Labels = labelEmbedding7 ∘ raw2307step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2307step0 raw2307step0Labels raw2307step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5296 node5296Labels := by rfl

theorem canonical2308 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2308 raw2308Labels = mixedMoment B node2770 node2770Labels := by
  calc
    mixedMoment B raw2308 raw2308Labels = mixedMoment B raw2308step0 raw2308step0Labels := by
      have ha : raw2308step0 = (fun i j => raw2308 (permutation2 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2308step0 raw2308; decide +kernel
      have hl : raw2308step0Labels = raw2308Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2308 raw2308Labels permutation2 permutation4
    _ = mixedMoment B node2770 node2770Labels := by rfl

theorem canonical2309 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2309 raw2309Labels = mixedMoment B node3634 node3634Labels := by
  calc
    mixedMoment B raw2309 raw2309Labels = mixedMoment B raw2309step0 raw2309step0Labels := by
      have ha : raw2309step0 = (fun i j => raw2309 (permutation7 i) (permutation3 j)) := by apply Matrix.ext; unfold raw2309step0 raw2309; decide +kernel
      have hl : raw2309step0Labels = raw2309Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2309 raw2309Labels permutation7 permutation3
    mixedMoment B raw2309step0 raw2309step0Labels = mixedMoment B raw2309step1 raw2309step1Labels := by
      have ha : raw2309step1 = raw2309step0 := by apply Matrix.ext; unfold raw2309step1 raw2309step0; decide +kernel
      have hl : raw2309step0Labels = labelEmbedding1 ∘ raw2309step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2309step0 raw2309step0Labels raw2309step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3634 node3634Labels := by rfl

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

theorem canonical274 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw274 raw274Labels = mixedMoment B node2770 node2770Labels := by
  calc
    mixedMoment B raw274 raw274Labels = mixedMoment B raw274step0 raw274step0Labels := by
      have ha : raw274step0 = (fun i j => raw274 (permutation2 i) (permutation5 j)) := by apply Matrix.ext; unfold raw274step0 raw274; decide +kernel
      have hl : raw274step0Labels = raw274Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw274 raw274Labels permutation2 permutation5
    mixedMoment B raw274step0 raw274step0Labels = mixedMoment B raw274step1 raw274step1Labels := by
      have ha : raw274step1 = raw274step0 := by apply Matrix.ext; unfold raw274step1 raw274step0; decide +kernel
      have hl : raw274step0Labels = labelEmbedding1 ∘ raw274step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw274step0 raw274step0Labels raw274step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2770 node2770Labels := by rfl

theorem canonical275 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw275 raw275Labels = mixedMoment B node407 node407Labels := by
  calc
    mixedMoment B raw275 raw275Labels = mixedMoment B raw275step0 raw275step0Labels := by
      have ha : raw275step0 = (fun i j => raw275 (permutation7 i) (permutation4 j)) := by apply Matrix.ext; unfold raw275step0 raw275; decide +kernel
      have hl : raw275step0Labels = raw275Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw275 raw275Labels permutation7 permutation4
    mixedMoment B raw275step0 raw275step0Labels = mixedMoment B raw275step1 raw275step1Labels := by
      have ha : raw275step1 = -raw275step0 := by apply Matrix.ext; change ∀ i j, raw275step1 i j = -(raw275step0 i j); unfold raw275step1 raw275step0; decide +kernel
      have hl : raw275step1Labels = raw275step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node407 node407Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical28
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical3657 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3657 raw3657Labels = mixedMoment B node4899 node4899Labels := by
  calc
    mixedMoment B raw3657 raw3657Labels = mixedMoment B raw3657step0 raw3657step0Labels := by
      have hz : ∀ j, raw3657 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3657step0 = (fun i j => raw3657 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3657step0 raw3657; decide +kernel
      have hl : raw3657step0Labels = raw3657Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3657 raw3657Labels permutation434 hz
    mixedMoment B raw3657step0 raw3657step0Labels = mixedMoment B raw3657step1 raw3657step1Labels := by
      have hz : ∀ j, raw3657step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw3657step1 = (fun i j => raw3657step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw3657step1 raw3657step0; decide +kernel
      have hl : raw3657step1Labels = raw3657step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3657step0 raw3657step0Labels permutation80 hz
    mixedMoment B raw3657step1 raw3657step1Labels = mixedMoment B raw3657step2 raw3657step2Labels := by
      have hz : ∀ j, raw3657step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw3657step2 = (fun i j => raw3657step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw3657step2 raw3657step1; decide +kernel
      have hl : raw3657step2Labels = raw3657step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3657step1 raw3657step1Labels permutation14 hz
    mixedMoment B raw3657step2 raw3657step2Labels = mixedMoment B raw3657step3 raw3657step3Labels := by
      have ha : raw3657step3 = (fun i j => raw3657step2 (permutation7 i) (permutation7 j)) := by apply Matrix.ext; unfold raw3657step3 raw3657step2; decide +kernel
      have hl : raw3657step3Labels = raw3657step2Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3657step2 raw3657step2Labels permutation7 permutation7
    mixedMoment B raw3657step3 raw3657step3Labels = mixedMoment B raw3657step4 raw3657step4Labels := by
      have ha : raw3657step4 = -raw3657step3 := by apply Matrix.ext; change ∀ i j, raw3657step4 i j = -(raw3657step3 i j); unfold raw3657step4 raw3657step3; decide +kernel
      have hl : raw3657step4Labels = raw3657step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw3657step4 raw3657step4Labels = mixedMoment B raw3657step5 raw3657step5Labels := by
      have ha : raw3657step5 = raw3657step4 := by apply Matrix.ext; unfold raw3657step5 raw3657step4; decide +kernel
      have hl : raw3657step4Labels = labelEmbedding10 ∘ raw3657step5Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3657step4 raw3657step4Labels raw3657step5Labels labelEmbedding10 hl
    _ = mixedMoment B node4899 node4899Labels := by rfl

theorem canonical3658 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3658 raw3658Labels = mixedMoment B node4890 node4890Labels := by
  calc
    mixedMoment B raw3658 raw3658Labels = mixedMoment B raw3658step0 raw3658step0Labels := by
      have hz : ∀ j, raw3658 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3658step0 = (fun i j => raw3658 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3658step0 raw3658; decide +kernel
      have hl : raw3658step0Labels = raw3658Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3658 raw3658Labels permutation346 hz
    mixedMoment B raw3658step0 raw3658step0Labels = mixedMoment B raw3658step1 raw3658step1Labels := by
      have hz : ∀ j, raw3658step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw3658step1 = (fun i j => raw3658step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw3658step1 raw3658step0; decide +kernel
      have hl : raw3658step1Labels = raw3658step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3658step0 raw3658step0Labels permutation56 hz
    mixedMoment B raw3658step1 raw3658step1Labels = mixedMoment B raw3658step2 raw3658step2Labels := by
      have ha : raw3658step2 = (fun i j => raw3658step1 (permutation29 i) (permutation7 j)) := by apply Matrix.ext; unfold raw3658step2 raw3658step1; decide +kernel
      have hl : raw3658step2Labels = raw3658step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3658step1 raw3658step1Labels permutation29 permutation7
    mixedMoment B raw3658step2 raw3658step2Labels = mixedMoment B raw3658step3 raw3658step3Labels := by
      have ha : raw3658step3 = -raw3658step2 := by apply Matrix.ext; change ∀ i j, raw3658step3 i j = -(raw3658step2 i j); unfold raw3658step3 raw3658step2; decide +kernel
      have hl : raw3658step3Labels = raw3658step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw3658step3 raw3658step3Labels = mixedMoment B raw3658step4 raw3658step4Labels := by
      have ha : raw3658step4 = raw3658step3 := by apply Matrix.ext; unfold raw3658step4 raw3658step3; decide +kernel
      have hl : raw3658step3Labels = labelEmbedding10 ∘ raw3658step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3658step3 raw3658step3Labels raw3658step4Labels labelEmbedding10 hl
    _ = mixedMoment B node4890 node4890Labels := by rfl

theorem canonical3683 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3683 raw3683Labels = mixedMoment B node4899 node4899Labels := by
  calc
    mixedMoment B raw3683 raw3683Labels = mixedMoment B raw3683step0 raw3683step0Labels := by
      have hz : ∀ j, raw3683 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3683step0 = (fun i j => raw3683 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3683step0 raw3683; decide +kernel
      have hl : raw3683step0Labels = raw3683Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3683 raw3683Labels permutation434 hz
    mixedMoment B raw3683step0 raw3683step0Labels = mixedMoment B raw3683step1 raw3683step1Labels := by
      have hz : ∀ j, raw3683step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw3683step1 = (fun i j => raw3683step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw3683step1 raw3683step0; decide +kernel
      have hl : raw3683step1Labels = raw3683step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3683step0 raw3683step0Labels permutation80 hz
    mixedMoment B raw3683step1 raw3683step1Labels = mixedMoment B raw3683step2 raw3683step2Labels := by
      have hz : ∀ j, raw3683step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw3683step2 = (fun i j => raw3683step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw3683step2 raw3683step1; decide +kernel
      have hl : raw3683step2Labels = raw3683step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3683step1 raw3683step1Labels permutation14 hz
    mixedMoment B raw3683step2 raw3683step2Labels = mixedMoment B raw3683step3 raw3683step3Labels := by
      have ha : raw3683step3 = (fun i j => raw3683step2 (permutation2 i) (permutation6 j)) := by apply Matrix.ext; unfold raw3683step3 raw3683step2; decide +kernel
      have hl : raw3683step3Labels = raw3683step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3683step2 raw3683step2Labels permutation2 permutation6
    mixedMoment B raw3683step3 raw3683step3Labels = mixedMoment B raw3683step4 raw3683step4Labels := by
      have ha : raw3683step4 = raw3683step3 := by apply Matrix.ext; unfold raw3683step4 raw3683step3; decide +kernel
      have hl : raw3683step3Labels = labelEmbedding9 ∘ raw3683step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3683step3 raw3683step3Labels raw3683step4Labels labelEmbedding9 hl
    _ = mixedMoment B node4899 node4899Labels := by rfl

theorem canonical3684 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3684 raw3684Labels = mixedMoment B node4890 node4890Labels := by
  calc
    mixedMoment B raw3684 raw3684Labels = mixedMoment B raw3684step0 raw3684step0Labels := by
      have hz : ∀ j, raw3684 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3684step0 = (fun i j => raw3684 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3684step0 raw3684; decide +kernel
      have hl : raw3684step0Labels = raw3684Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3684 raw3684Labels permutation346 hz
    mixedMoment B raw3684step0 raw3684step0Labels = mixedMoment B raw3684step1 raw3684step1Labels := by
      have hz : ∀ j, raw3684step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw3684step1 = (fun i j => raw3684step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw3684step1 raw3684step0; decide +kernel
      have hl : raw3684step1Labels = raw3684step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3684step0 raw3684step0Labels permutation56 hz
    mixedMoment B raw3684step1 raw3684step1Labels = mixedMoment B raw3684step2 raw3684step2Labels := by
      have ha : raw3684step2 = (fun i j => raw3684step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw3684step2 raw3684step1; decide +kernel
      have hl : raw3684step2Labels = raw3684step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3684step1 raw3684step1Labels permutation8 permutation6
    mixedMoment B raw3684step2 raw3684step2Labels = mixedMoment B raw3684step3 raw3684step3Labels := by
      have ha : raw3684step3 = raw3684step2 := by apply Matrix.ext; unfold raw3684step3 raw3684step2; decide +kernel
      have hl : raw3684step2Labels = labelEmbedding9 ∘ raw3684step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3684step2 raw3684step2Labels raw3684step3Labels labelEmbedding9 hl
    _ = mixedMoment B node4890 node4890Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical29
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical3719 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3719 raw3719Labels = mixedMoment B node2290 node2290Labels := by
  calc
    mixedMoment B raw3719 raw3719Labels = mixedMoment B raw3719step0 raw3719step0Labels := by
      have hz : ∀ j, raw3719 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3719step0 = (fun i j => raw3719 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3719step0 raw3719; decide +kernel
      have hl : raw3719step0Labels = raw3719Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3719 raw3719Labels permutation346 hz
    mixedMoment B raw3719step0 raw3719step0Labels = mixedMoment B raw3719step1 raw3719step1Labels := by
      have hz : ∀ j, raw3719step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw3719step1 = (fun i j => raw3719step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw3719step1 raw3719step0; decide +kernel
      have hl : raw3719step1Labels = raw3719step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3719step0 raw3719step0Labels permutation56 hz
    mixedMoment B raw3719step1 raw3719step1Labels = mixedMoment B raw3719step2 raw3719step2Labels := by
      have ha : raw3719step2 = (fun i j => raw3719step1 (permutation29 i) (permutation2 j)) := by apply Matrix.ext; unfold raw3719step2 raw3719step1; decide +kernel
      have hl : raw3719step2Labels = raw3719step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3719step1 raw3719step1Labels permutation29 permutation2
    _ = mixedMoment B node2290 node2290Labels := by rfl

theorem canonical3721 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3721 raw3721Labels = mixedMoment B node4085 node4085Labels := by
  calc
    mixedMoment B raw3721 raw3721Labels = mixedMoment B raw3721step0 raw3721step0Labels := by
      have hz : ∀ j, raw3721 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw3721step0 = (fun i j => raw3721 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw3721step0 raw3721; decide +kernel
      have hl : raw3721step0Labels = raw3721Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3721 raw3721Labels permutation520 hz
    mixedMoment B raw3721step0 raw3721step0Labels = mixedMoment B raw3721step1 raw3721step1Labels := by
      have hz : ∀ j, raw3721step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw3721step1 = (fun i j => raw3721step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw3721step1 raw3721step0; decide +kernel
      have hl : raw3721step1Labels = raw3721step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3721step0 raw3721step0Labels permutation104 hz
    mixedMoment B raw3721step1 raw3721step1Labels = mixedMoment B raw3721step2 raw3721step2Labels := by
      have hz : ∀ j, raw3721step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw3721step2 = (fun i j => raw3721step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw3721step2 raw3721step1; decide +kernel
      have hl : raw3721step2Labels = raw3721step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3721step1 raw3721step1Labels permutation20 hz
    mixedMoment B raw3721step2 raw3721step2Labels = mixedMoment B raw3721step3 raw3721step3Labels := by
      have hz : ∀ j, raw3721step2 (permutation4 0) j = 0 := by decide +kernel
      have ha : raw3721step3 = (fun i j => raw3721step2 (permutation4 i.succ) j) := by apply Matrix.ext; unfold raw3721step3 raw3721step2; decide +kernel
      have hl : raw3721step3Labels = raw3721step2Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3721step2 raw3721step2Labels permutation4 hz
    mixedMoment B raw3721step3 raw3721step3Labels = mixedMoment B raw3721step4 raw3721step4Labels := by
      have ha : raw3721step4 = (fun i j => raw3721step3 (permutation1 i) (permutation0 j)) := by apply Matrix.ext; unfold raw3721step4 raw3721step3; decide +kernel
      have hl : raw3721step4Labels = raw3721step3Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3721step3 raw3721step3Labels permutation1 permutation0
    _ = mixedMoment B node4085 node4085Labels := by rfl

theorem canonical3734 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3734 raw3734Labels = mixedMoment B node2055 node2055Labels := by
  calc
    mixedMoment B raw3734 raw3734Labels = mixedMoment B raw3734step0 raw3734step0Labels := by
      have hz : ∀ j, raw3734 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3734step0 = (fun i j => raw3734 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3734step0 raw3734; decide +kernel
      have hl : raw3734step0Labels = raw3734Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3734 raw3734Labels permutation346 hz
    mixedMoment B raw3734step0 raw3734step0Labels = mixedMoment B raw3734step1 raw3734step1Labels := by
      have ha : raw3734step1 = (fun i j => raw3734step0 (permutation33 i) (permutation4 j)) := by apply Matrix.ext; unfold raw3734step1 raw3734step0; decide +kernel
      have hl : raw3734step1Labels = raw3734step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3734step0 raw3734step0Labels permutation33 permutation4
    mixedMoment B raw3734step1 raw3734step1Labels = mixedMoment B raw3734step2 raw3734step2Labels := by
      have ha : raw3734step2 = -raw3734step1 := by apply Matrix.ext; change ∀ i j, raw3734step2 i j = -(raw3734step1 i j); unfold raw3734step2 raw3734step1; decide +kernel
      have hl : raw3734step2Labels = raw3734step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2055 node2055Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical30
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical3857 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3857 raw3857Labels = mixedMoment B node4890 node4890Labels := by
  calc
    mixedMoment B raw3857 raw3857Labels = mixedMoment B raw3857step0 raw3857step0Labels := by
      have hz : ∀ j, raw3857 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3857step0 = (fun i j => raw3857 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3857step0 raw3857; decide +kernel
      have hl : raw3857step0Labels = raw3857Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3857 raw3857Labels permutation434 hz
    mixedMoment B raw3857step0 raw3857step0Labels = mixedMoment B raw3857step1 raw3857step1Labels := by
      have hz : ∀ j, raw3857step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw3857step1 = (fun i j => raw3857step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw3857step1 raw3857step0; decide +kernel
      have hl : raw3857step1Labels = raw3857step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3857step0 raw3857step0Labels permutation56 hz
    mixedMoment B raw3857step1 raw3857step1Labels = mixedMoment B raw3857step2 raw3857step2Labels := by
      have ha : raw3857step2 = (fun i j => raw3857step1 (permutation29 i) (permutation7 j)) := by apply Matrix.ext; unfold raw3857step2 raw3857step1; decide +kernel
      have hl : raw3857step2Labels = raw3857step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3857step1 raw3857step1Labels permutation29 permutation7
    mixedMoment B raw3857step2 raw3857step2Labels = mixedMoment B raw3857step3 raw3857step3Labels := by
      have ha : raw3857step3 = -raw3857step2 := by apply Matrix.ext; change ∀ i j, raw3857step3 i j = -(raw3857step2 i j); unfold raw3857step3 raw3857step2; decide +kernel
      have hl : raw3857step3Labels = raw3857step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw3857step3 raw3857step3Labels = mixedMoment B raw3857step4 raw3857step4Labels := by
      have ha : raw3857step4 = raw3857step3 := by apply Matrix.ext; unfold raw3857step4 raw3857step3; decide +kernel
      have hl : raw3857step3Labels = labelEmbedding10 ∘ raw3857step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3857step3 raw3857step3Labels raw3857step4Labels labelEmbedding10 hl
    _ = mixedMoment B node4890 node4890Labels := by rfl

theorem canonical3876 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3876 raw3876Labels = mixedMoment B node4890 node4890Labels := by
  calc
    mixedMoment B raw3876 raw3876Labels = mixedMoment B raw3876step0 raw3876step0Labels := by
      have hz : ∀ j, raw3876 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3876step0 = (fun i j => raw3876 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3876step0 raw3876; decide +kernel
      have hl : raw3876step0Labels = raw3876Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3876 raw3876Labels permutation434 hz
    mixedMoment B raw3876step0 raw3876step0Labels = mixedMoment B raw3876step1 raw3876step1Labels := by
      have hz : ∀ j, raw3876step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw3876step1 = (fun i j => raw3876step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw3876step1 raw3876step0; decide +kernel
      have hl : raw3876step1Labels = raw3876step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3876step0 raw3876step0Labels permutation56 hz
    mixedMoment B raw3876step1 raw3876step1Labels = mixedMoment B raw3876step2 raw3876step2Labels := by
      have ha : raw3876step2 = (fun i j => raw3876step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw3876step2 raw3876step1; decide +kernel
      have hl : raw3876step2Labels = raw3876step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3876step1 raw3876step1Labels permutation8 permutation6
    mixedMoment B raw3876step2 raw3876step2Labels = mixedMoment B raw3876step3 raw3876step3Labels := by
      have ha : raw3876step3 = raw3876step2 := by apply Matrix.ext; unfold raw3876step3 raw3876step2; decide +kernel
      have hl : raw3876step2Labels = labelEmbedding9 ∘ raw3876step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3876step2 raw3876step2Labels raw3876step3Labels labelEmbedding9 hl
    _ = mixedMoment B node4890 node4890Labels := by rfl

theorem canonical3901 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3901 raw3901Labels = mixedMoment B node2050 node2050Labels := by
  calc
    mixedMoment B raw3901 raw3901Labels = mixedMoment B raw3901step0 raw3901step0Labels := by
      have ha : raw3901step0 = (fun i j => raw3901 (permutation609 i) (permutation2 j)) := by apply Matrix.ext; unfold raw3901step0 raw3901; decide +kernel
      have hl : raw3901step0Labels = raw3901Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3901 raw3901Labels permutation609 permutation2
    _ = mixedMoment B node2050 node2050Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical31
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical4036 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4036 raw4036Labels = mixedMoment B node5261 node5261Labels := by
  calc
    mixedMoment B raw4036 raw4036Labels = mixedMoment B raw4036step0 raw4036step0Labels := by
      have hz : ∀ j, raw4036 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4036step0 = (fun i j => raw4036 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4036step0 raw4036; decide +kernel
      have hl : raw4036step0Labels = raw4036Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4036 raw4036Labels permutation434 hz
    mixedMoment B raw4036step0 raw4036step0Labels = mixedMoment B raw4036step1 raw4036step1Labels := by
      have hz : ∀ j, raw4036step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4036step1 = (fun i j => raw4036step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4036step1 raw4036step0; decide +kernel
      have hl : raw4036step1Labels = raw4036step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4036step0 raw4036step0Labels permutation80 hz
    mixedMoment B raw4036step1 raw4036step1Labels = mixedMoment B raw4036step2 raw4036step2Labels := by
      have ha : raw4036step2 = (fun i j => raw4036step1 (permutation10 i) (permutation7 j)) := by apply Matrix.ext; unfold raw4036step2 raw4036step1; decide +kernel
      have hl : raw4036step2Labels = raw4036step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4036step1 raw4036step1Labels permutation10 permutation7
    mixedMoment B raw4036step2 raw4036step2Labels = mixedMoment B raw4036step3 raw4036step3Labels := by
      have ha : raw4036step3 = raw4036step2 := by apply Matrix.ext; unfold raw4036step3 raw4036step2; decide +kernel
      have hl : raw4036step2Labels = labelEmbedding10 ∘ raw4036step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4036step2 raw4036step2Labels raw4036step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5261 node5261Labels := by rfl

theorem canonical4038 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4038 raw4038Labels = mixedMoment B node5268 node5268Labels := by
  calc
    mixedMoment B raw4038 raw4038Labels = mixedMoment B raw4038step0 raw4038step0Labels := by
      have hz : ∀ j, raw4038 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4038step0 = (fun i j => raw4038 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4038step0 raw4038; decide +kernel
      have hl : raw4038step0Labels = raw4038Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4038 raw4038Labels permutation434 hz
    mixedMoment B raw4038step0 raw4038step0Labels = mixedMoment B raw4038step1 raw4038step1Labels := by
      have hz : ∀ j, raw4038step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw4038step1 = (fun i j => raw4038step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw4038step1 raw4038step0; decide +kernel
      have hl : raw4038step1Labels = raw4038step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4038step0 raw4038step0Labels permutation56 hz
    mixedMoment B raw4038step1 raw4038step1Labels = mixedMoment B raw4038step2 raw4038step2Labels := by
      have ha : raw4038step2 = (fun i j => raw4038step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw4038step2 raw4038step1; decide +kernel
      have hl : raw4038step2Labels = raw4038step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4038step1 raw4038step1Labels permutation8 permutation6
    mixedMoment B raw4038step2 raw4038step2Labels = mixedMoment B raw4038step3 raw4038step3Labels := by
      have ha : raw4038step3 = raw4038step2 := by apply Matrix.ext; unfold raw4038step3 raw4038step2; decide +kernel
      have hl : raw4038step2Labels = labelEmbedding9 ∘ raw4038step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4038step2 raw4038step2Labels raw4038step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5268 node5268Labels := by rfl

theorem canonical4039 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4039 raw4039Labels = mixedMoment B node5268 node5268Labels := by
  calc
    mixedMoment B raw4039 raw4039Labels = mixedMoment B raw4039step0 raw4039step0Labels := by
      have hz : ∀ j, raw4039 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4039step0 = (fun i j => raw4039 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4039step0 raw4039; decide +kernel
      have hl : raw4039step0Labels = raw4039Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4039 raw4039Labels permutation346 hz
    mixedMoment B raw4039step0 raw4039step0Labels = mixedMoment B raw4039step1 raw4039step1Labels := by
      have hz : ∀ j, raw4039step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw4039step1 = (fun i j => raw4039step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw4039step1 raw4039step0; decide +kernel
      have hl : raw4039step1Labels = raw4039step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4039step0 raw4039step0Labels permutation56 hz
    mixedMoment B raw4039step1 raw4039step1Labels = mixedMoment B raw4039step2 raw4039step2Labels := by
      have ha : raw4039step2 = (fun i j => raw4039step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw4039step2 raw4039step1; decide +kernel
      have hl : raw4039step2Labels = raw4039step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4039step1 raw4039step1Labels permutation8 permutation6
    mixedMoment B raw4039step2 raw4039step2Labels = mixedMoment B raw4039step3 raw4039step3Labels := by
      have ha : raw4039step3 = raw4039step2 := by apply Matrix.ext; unfold raw4039step3 raw4039step2; decide +kernel
      have hl : raw4039step2Labels = labelEmbedding9 ∘ raw4039step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4039step2 raw4039step2Labels raw4039step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5268 node5268Labels := by rfl

theorem canonical4044 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4044 raw4044Labels = mixedMoment B node5252 node5252Labels := by
  calc
    mixedMoment B raw4044 raw4044Labels = mixedMoment B raw4044step0 raw4044step0Labels := by
      have hz : ∀ j, raw4044 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4044step0 = (fun i j => raw4044 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4044step0 raw4044; decide +kernel
      have hl : raw4044step0Labels = raw4044Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4044 raw4044Labels permutation434 hz
    mixedMoment B raw4044step0 raw4044step0Labels = mixedMoment B raw4044step1 raw4044step1Labels := by
      have ha : raw4044step1 = (fun i j => raw4044step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw4044step1 raw4044step0; decide +kernel
      have hl : raw4044step1Labels = raw4044step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4044step0 raw4044step0Labels permutation32 permutation6
    mixedMoment B raw4044step1 raw4044step1Labels = mixedMoment B raw4044step2 raw4044step2Labels := by
      have ha : raw4044step2 = raw4044step1 := by apply Matrix.ext; unfold raw4044step2 raw4044step1; decide +kernel
      have hl : raw4044step1Labels = labelEmbedding9 ∘ raw4044step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4044step1 raw4044step1Labels raw4044step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5252 node5252Labels := by rfl

theorem canonical4048 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4048 raw4048Labels = mixedMoment B node5252 node5252Labels := by
  calc
    mixedMoment B raw4048 raw4048Labels = mixedMoment B raw4048step0 raw4048step0Labels := by
      have hz : ∀ j, raw4048 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4048step0 = (fun i j => raw4048 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4048step0 raw4048; decide +kernel
      have hl : raw4048step0Labels = raw4048Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4048 raw4048Labels permutation346 hz
    mixedMoment B raw4048step0 raw4048step0Labels = mixedMoment B raw4048step1 raw4048step1Labels := by
      have ha : raw4048step1 = (fun i j => raw4048step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw4048step1 raw4048step0; decide +kernel
      have hl : raw4048step1Labels = raw4048step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4048step0 raw4048step0Labels permutation32 permutation6
    mixedMoment B raw4048step1 raw4048step1Labels = mixedMoment B raw4048step2 raw4048step2Labels := by
      have ha : raw4048step2 = raw4048step1 := by apply Matrix.ext; unfold raw4048step2 raw4048step1; decide +kernel
      have hl : raw4048step1Labels = labelEmbedding9 ∘ raw4048step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4048step1 raw4048step1Labels raw4048step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5252 node5252Labels := by rfl

theorem canonical4058 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4058 raw4058Labels = mixedMoment B node5261 node5261Labels := by
  calc
    mixedMoment B raw4058 raw4058Labels = mixedMoment B raw4058step0 raw4058step0Labels := by
      have hz : ∀ j, raw4058 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4058step0 = (fun i j => raw4058 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4058step0 raw4058; decide +kernel
      have hl : raw4058step0Labels = raw4058Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4058 raw4058Labels permutation434 hz
    mixedMoment B raw4058step0 raw4058step0Labels = mixedMoment B raw4058step1 raw4058step1Labels := by
      have hz : ∀ j, raw4058step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4058step1 = (fun i j => raw4058step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4058step1 raw4058step0; decide +kernel
      have hl : raw4058step1Labels = raw4058step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4058step0 raw4058step0Labels permutation80 hz
    mixedMoment B raw4058step1 raw4058step1Labels = mixedMoment B raw4058step2 raw4058step2Labels := by
      have ha : raw4058step2 = (fun i j => raw4058step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw4058step2 raw4058step1; decide +kernel
      have hl : raw4058step2Labels = raw4058step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4058step1 raw4058step1Labels permutation8 permutation6
    mixedMoment B raw4058step2 raw4058step2Labels = mixedMoment B raw4058step3 raw4058step3Labels := by
      have ha : raw4058step3 = raw4058step2 := by apply Matrix.ext; unfold raw4058step3 raw4058step2; decide +kernel
      have hl : raw4058step2Labels = labelEmbedding9 ∘ raw4058step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4058step2 raw4058step2Labels raw4058step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5261 node5261Labels := by rfl

theorem canonical4089 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4089 raw4089Labels = mixedMoment B node3545 node3545Labels := by
  calc
    mixedMoment B raw4089 raw4089Labels = mixedMoment B raw4089step0 raw4089step0Labels := by
      have hz : ∀ j, raw4089 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4089step0 = (fun i j => raw4089 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4089step0 raw4089; decide +kernel
      have hl : raw4089step0Labels = raw4089Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4089 raw4089Labels permutation434 hz
    mixedMoment B raw4089step0 raw4089step0Labels = mixedMoment B raw4089step1 raw4089step1Labels := by
      have hz : ∀ j, raw4089step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4089step1 = (fun i j => raw4089step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4089step1 raw4089step0; decide +kernel
      have hl : raw4089step1Labels = raw4089step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4089step0 raw4089step0Labels permutation80 hz
    mixedMoment B raw4089step1 raw4089step1Labels = mixedMoment B raw4089step2 raw4089step2Labels := by
      have ha : raw4089step2 = (fun i j => raw4089step1 (permutation29 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4089step2 raw4089step1; decide +kernel
      have hl : raw4089step2Labels = raw4089step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4089step1 raw4089step1Labels permutation29 permutation2
    _ = mixedMoment B node3545 node3545Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical32
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical4097 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4097 raw4097Labels = mixedMoment B node3634 node3634Labels := by
  calc
    mixedMoment B raw4097 raw4097Labels = mixedMoment B raw4097step0 raw4097step0Labels := by
      have hz : ∀ j, raw4097 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4097step0 = (fun i j => raw4097 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4097step0 raw4097; decide +kernel
      have hl : raw4097step0Labels = raw4097Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4097 raw4097Labels permutation434 hz
    mixedMoment B raw4097step0 raw4097step0Labels = mixedMoment B raw4097step1 raw4097step1Labels := by
      have hz : ∀ j, raw4097step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4097step1 = (fun i j => raw4097step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4097step1 raw4097step0; decide +kernel
      have hl : raw4097step1Labels = raw4097step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4097step0 raw4097step0Labels permutation80 hz
    mixedMoment B raw4097step1 raw4097step1Labels = mixedMoment B raw4097step2 raw4097step2Labels := by
      have hz : ∀ j, raw4097step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw4097step2 = (fun i j => raw4097step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw4097step2 raw4097step1; decide +kernel
      have hl : raw4097step2Labels = raw4097step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4097step1 raw4097step1Labels permutation14 hz
    mixedMoment B raw4097step2 raw4097step2Labels = mixedMoment B raw4097step3 raw4097step3Labels := by
      have ha : raw4097step3 = (fun i j => raw4097step2 (permutation7 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4097step3 raw4097step2; decide +kernel
      have hl : raw4097step3Labels = raw4097step2Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4097step2 raw4097step2Labels permutation7 permutation2
    _ = mixedMoment B node3634 node3634Labels := by rfl

theorem canonical4099 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4099 raw4099Labels = mixedMoment B node3393 node3393Labels := by
  calc
    mixedMoment B raw4099 raw4099Labels = mixedMoment B raw4099step0 raw4099step0Labels := by
      have hz : ∀ j, raw4099 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4099step0 = (fun i j => raw4099 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4099step0 raw4099; decide +kernel
      have hl : raw4099step0Labels = raw4099Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4099 raw4099Labels permutation346 hz
    mixedMoment B raw4099step0 raw4099step0Labels = mixedMoment B raw4099step1 raw4099step1Labels := by
      have ha : raw4099step1 = (fun i j => raw4099step0 (permutation136 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4099step1 raw4099step0; decide +kernel
      have hl : raw4099step1Labels = raw4099step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4099step0 raw4099step0Labels permutation136 permutation2
    _ = mixedMoment B node3393 node3393Labels := by rfl

theorem canonical4103 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4103 raw4103Labels = mixedMoment B node3543 node3543Labels := by
  calc
    mixedMoment B raw4103 raw4103Labels = mixedMoment B raw4103step0 raw4103step0Labels := by
      have hz : ∀ j, raw4103 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4103step0 = (fun i j => raw4103 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4103step0 raw4103; decide +kernel
      have hl : raw4103step0Labels = raw4103Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4103 raw4103Labels permutation434 hz
    mixedMoment B raw4103step0 raw4103step0Labels = mixedMoment B raw4103step1 raw4103step1Labels := by
      have ha : raw4103step1 = (fun i j => raw4103step0 (permutation137 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4103step1 raw4103step0; decide +kernel
      have hl : raw4103step1Labels = raw4103step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4103step0 raw4103step0Labels permutation137 permutation2
    _ = mixedMoment B node3543 node3543Labels := by rfl

theorem canonical4200 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4200 raw4200Labels = mixedMoment B node2712 node2712Labels := by
  calc
    mixedMoment B raw4200 raw4200Labels = mixedMoment B raw4200step0 raw4200step0Labels := by
      have hz : ∀ j, raw4200 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4200step0 = (fun i j => raw4200 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4200step0 raw4200; decide +kernel
      have hl : raw4200step0Labels = raw4200Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4200 raw4200Labels permutation346 hz
    _ = mixedMoment B node2712 node2712Labels := by rfl

theorem canonical4201 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4201 raw4201Labels = mixedMoment B node3077 node3077Labels := by
  calc
    mixedMoment B raw4201 raw4201Labels = mixedMoment B raw4201step0 raw4201step0Labels := by
      have hz : ∀ j, raw4201 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4201step0 = (fun i j => raw4201 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4201step0 raw4201; decide +kernel
      have hl : raw4201step0Labels = raw4201Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4201 raw4201Labels permutation346 hz
    mixedMoment B raw4201step0 raw4201step0Labels = mixedMoment B raw4201step1 raw4201step1Labels := by
      have ha : raw4201step1 = (fun i j => raw4201step0 (permutation145 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4201step1 raw4201step0; decide +kernel
      have hl : raw4201step1Labels = raw4201step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4201step0 raw4201step0Labels permutation145 permutation2
    mixedMoment B raw4201step1 raw4201step1Labels = mixedMoment B raw4201step2 raw4201step2Labels := by
      have ha : raw4201step2 = -raw4201step1 := by apply Matrix.ext; change ∀ i j, raw4201step2 i j = -(raw4201step1 i j); unfold raw4201step2 raw4201step1; decide +kernel
      have hl : raw4201step2Labels = raw4201step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3077 node3077Labels := by rfl

theorem canonical4202 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4202 raw4202Labels = mixedMoment B node3064 node3064Labels := by
  calc
    mixedMoment B raw4202 raw4202Labels = mixedMoment B raw4202step0 raw4202step0Labels := by
      have ha : raw4202step0 = (fun i j => raw4202 (permutation662 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4202step0 raw4202; decide +kernel
      have hl : raw4202step0Labels = raw4202Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4202 raw4202Labels permutation662 permutation2
    mixedMoment B raw4202step0 raw4202step0Labels = mixedMoment B raw4202step1 raw4202step1Labels := by
      have ha : raw4202step1 = -raw4202step0 := by apply Matrix.ext; change ∀ i j, raw4202step1 i j = -(raw4202step0 i j); unfold raw4202step1 raw4202step0; decide +kernel
      have hl : raw4202step1Labels = raw4202step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3064 node3064Labels := by rfl

theorem canonical4203 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4203 raw4203Labels = mixedMoment B node3086 node3086Labels := by
  calc
    mixedMoment B raw4203 raw4203Labels = mixedMoment B raw4203step0 raw4203step0Labels := by
      have hz : ∀ j, raw4203 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4203step0 = (fun i j => raw4203 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4203step0 raw4203; decide +kernel
      have hl : raw4203step0Labels = raw4203Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4203 raw4203Labels permutation346 hz
    mixedMoment B raw4203step0 raw4203step0Labels = mixedMoment B raw4203step1 raw4203step1Labels := by
      have ha : raw4203step1 = (fun i j => raw4203step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4203step1 raw4203step0; decide +kernel
      have hl : raw4203step1Labels = raw4203step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4203step0 raw4203step0Labels permutation149 permutation2
    mixedMoment B raw4203step1 raw4203step1Labels = mixedMoment B raw4203step2 raw4203step2Labels := by
      have ha : raw4203step2 = -raw4203step1 := by apply Matrix.ext; change ∀ i j, raw4203step2 i j = -(raw4203step1 i j); unfold raw4203step2 raw4203step1; decide +kernel
      have hl : raw4203step2Labels = raw4203step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3086 node3086Labels := by rfl

theorem canonical4206 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4206 raw4206Labels = mixedMoment B node4091 node4091Labels := by
  calc
    mixedMoment B raw4206 raw4206Labels = mixedMoment B raw4206step0 raw4206step0Labels := by
      have hz : ∀ j, raw4206 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4206step0 = (fun i j => raw4206 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4206step0 raw4206; decide +kernel
      have hl : raw4206step0Labels = raw4206Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4206 raw4206Labels permutation346 hz
    _ = mixedMoment B node4091 node4091Labels := by rfl

theorem canonical4208 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4208 raw4208Labels = mixedMoment B node1206 node1206Labels := by
  calc
    mixedMoment B raw4208 raw4208Labels = mixedMoment B raw4208step0 raw4208step0Labels := by
      have ha : raw4208step0 = (fun i j => raw4208 (permutation160 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4208step0 raw4208; decide +kernel
      have hl : raw4208step0Labels = raw4208Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4208 raw4208Labels permutation160 permutation2
    _ = mixedMoment B node1206 node1206Labels := by rfl

theorem canonical4209 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4209 raw4209Labels = mixedMoment B node1217 node1217Labels := by
  calc
    mixedMoment B raw4209 raw4209Labels = mixedMoment B raw4209step0 raw4209step0Labels := by
      have hz : ∀ j, raw4209 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4209step0 = (fun i j => raw4209 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4209step0 raw4209; decide +kernel
      have hl : raw4209step0Labels = raw4209Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4209 raw4209Labels permutation346 hz
    mixedMoment B raw4209step0 raw4209step0Labels = mixedMoment B raw4209step1 raw4209step1Labels := by
      have ha : raw4209step1 = (fun i j => raw4209step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4209step1 raw4209step0; decide +kernel
      have hl : raw4209step1Labels = raw4209step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4209step0 raw4209step0Labels permutation34 permutation2
    _ = mixedMoment B node1217 node1217Labels := by rfl

theorem canonical4211 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4211 raw4211Labels = mixedMoment B node1209 node1209Labels := by
  calc
    mixedMoment B raw4211 raw4211Labels = mixedMoment B raw4211step0 raw4211step0Labels := by
      have hz : ∀ j, raw4211 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4211step0 = (fun i j => raw4211 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4211step0 raw4211; decide +kernel
      have hl : raw4211step0Labels = raw4211Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4211 raw4211Labels permutation346 hz
    _ = mixedMoment B node1209 node1209Labels := by rfl

theorem canonical4212 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4212 raw4212Labels = mixedMoment B node2562 node2562Labels := by
  calc
    mixedMoment B raw4212 raw4212Labels = mixedMoment B raw4212step0 raw4212step0Labels := by
      have ha : raw4212step0 = (fun i j => raw4212 (permutation184 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4212step0 raw4212; decide +kernel
      have hl : raw4212step0Labels = raw4212Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4212 raw4212Labels permutation184 permutation2
    _ = mixedMoment B node2562 node2562Labels := by rfl

theorem canonical4213 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4213 raw4213Labels = mixedMoment B node2624 node2624Labels := by
  calc
    mixedMoment B raw4213 raw4213Labels = mixedMoment B raw4213step0 raw4213step0Labels := by
      have hz : ∀ j, raw4213 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4213step0 = (fun i j => raw4213 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4213step0 raw4213; decide +kernel
      have hl : raw4213step0Labels = raw4213Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4213 raw4213Labels permutation346 hz
    mixedMoment B raw4213step0 raw4213step0Labels = mixedMoment B raw4213step1 raw4213step1Labels := by
      have ha : raw4213step1 = (fun i j => raw4213step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4213step1 raw4213step0; decide +kernel
      have hl : raw4213step1Labels = raw4213step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4213step0 raw4213step0Labels permutation40 permutation2
    _ = mixedMoment B node2624 node2624Labels := by rfl

theorem canonical4216 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4216 raw4216Labels = mixedMoment B node2470 node2470Labels := by
  calc
    mixedMoment B raw4216 raw4216Labels = mixedMoment B raw4216step0 raw4216step0Labels := by
      have ha : raw4216step0 = (fun i j => raw4216 (permutation160 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4216step0 raw4216; decide +kernel
      have hl : raw4216step0Labels = raw4216Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4216 raw4216Labels permutation160 permutation2
    _ = mixedMoment B node2470 node2470Labels := by rfl

theorem canonical4217 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4217 raw4217Labels = mixedMoment B node2485 node2485Labels := by
  calc
    mixedMoment B raw4217 raw4217Labels = mixedMoment B raw4217step0 raw4217step0Labels := by
      have hz : ∀ j, raw4217 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4217step0 = (fun i j => raw4217 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4217step0 raw4217; decide +kernel
      have hl : raw4217step0Labels = raw4217Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4217 raw4217Labels permutation346 hz
    mixedMoment B raw4217step0 raw4217step0Labels = mixedMoment B raw4217step1 raw4217step1Labels := by
      have ha : raw4217step1 = (fun i j => raw4217step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4217step1 raw4217step0; decide +kernel
      have hl : raw4217step1Labels = raw4217step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4217step0 raw4217step0Labels permutation34 permutation2
    _ = mixedMoment B node2485 node2485Labels := by rfl

theorem canonical4218 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4218 raw4218Labels = mixedMoment B node2485 node2485Labels := by
  calc
    mixedMoment B raw4218 raw4218Labels = mixedMoment B raw4218step0 raw4218step0Labels := by
      have hz : ∀ j, raw4218 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4218step0 = (fun i j => raw4218 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4218step0 raw4218; decide +kernel
      have hl : raw4218step0Labels = raw4218Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4218 raw4218Labels permutation346 hz
    _ = mixedMoment B node2485 node2485Labels := by rfl

theorem canonical4219 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4219 raw4219Labels = mixedMoment B node1388 node1388Labels := by
  calc
    mixedMoment B raw4219 raw4219Labels = mixedMoment B raw4219step0 raw4219step0Labels := by
      have hz : ∀ j, raw4219 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4219step0 = (fun i j => raw4219 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4219step0 raw4219; decide +kernel
      have hl : raw4219step0Labels = raw4219Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4219 raw4219Labels permutation346 hz
    mixedMoment B raw4219step0 raw4219step0Labels = mixedMoment B raw4219step1 raw4219step1Labels := by
      have ha : raw4219step1 = (fun i j => raw4219step0 (permutation145 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4219step1 raw4219step0; decide +kernel
      have hl : raw4219step1Labels = raw4219step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4219step0 raw4219step0Labels permutation145 permutation2
    mixedMoment B raw4219step1 raw4219step1Labels = mixedMoment B raw4219step2 raw4219step2Labels := by
      have ha : raw4219step2 = -raw4219step1 := by apply Matrix.ext; change ∀ i j, raw4219step2 i j = -(raw4219step1 i j); unfold raw4219step2 raw4219step1; decide +kernel
      have hl : raw4219step2Labels = raw4219step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1388 node1388Labels := by rfl

theorem canonical4220 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4220 raw4220Labels = mixedMoment B node2610 node2610Labels := by
  calc
    mixedMoment B raw4220 raw4220Labels = mixedMoment B raw4220step0 raw4220step0Labels := by
      have ha : raw4220step0 = (fun i j => raw4220 (permutation202 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4220step0 raw4220; decide +kernel
      have hl : raw4220step0Labels = raw4220Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4220 raw4220Labels permutation202 permutation2
    _ = mixedMoment B node2610 node2610Labels := by rfl

theorem canonical4221 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4221 raw4221Labels = mixedMoment B node2610 node2610Labels := by
  calc
    mixedMoment B raw4221 raw4221Labels = mixedMoment B raw4221step0 raw4221step0Labels := by
      have ha : raw4221step0 = (fun i j => raw4221 (permutation226 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4221step0 raw4221; decide +kernel
      have hl : raw4221step0Labels = raw4221Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4221 raw4221Labels permutation226 permutation2
    _ = mixedMoment B node2610 node2610Labels := by rfl

theorem canonical4222 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4222 raw4222Labels = mixedMoment B node2709 node2709Labels := by
  calc
    mixedMoment B raw4222 raw4222Labels = mixedMoment B raw4222step0 raw4222step0Labels := by
      have ha : raw4222step0 = (fun i j => raw4222 (permutation160 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4222step0 raw4222; decide +kernel
      have hl : raw4222step0Labels = raw4222Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4222 raw4222Labels permutation160 permutation2
    _ = mixedMoment B node2709 node2709Labels := by rfl

theorem canonical4223 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4223 raw4223Labels = mixedMoment B node2543 node2543Labels := by
  calc
    mixedMoment B raw4223 raw4223Labels = mixedMoment B raw4223step0 raw4223step0Labels := by
      have ha : raw4223step0 = (fun i j => raw4223 (permutation178 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4223step0 raw4223; decide +kernel
      have hl : raw4223step0Labels = raw4223Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4223 raw4223Labels permutation178 permutation2
    _ = mixedMoment B node2543 node2543Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical33
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical4224 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4224 raw4224Labels = mixedMoment B node2543 node2543Labels := by
  calc
    mixedMoment B raw4224 raw4224Labels = mixedMoment B raw4224step0 raw4224step0Labels := by
      have ha : raw4224step0 = (fun i j => raw4224 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4224step0 raw4224; decide +kernel
      have hl : raw4224step0Labels = raw4224Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4224 raw4224Labels permutation176 permutation2
    _ = mixedMoment B node2543 node2543Labels := by rfl

theorem canonical4225 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4225 raw4225Labels = mixedMoment B node1378 node1378Labels := by
  calc
    mixedMoment B raw4225 raw4225Labels = mixedMoment B raw4225step0 raw4225step0Labels := by
      have ha : raw4225step0 = (fun i j => raw4225 (permutation662 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4225step0 raw4225; decide +kernel
      have hl : raw4225step0Labels = raw4225Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4225 raw4225Labels permutation662 permutation2
    mixedMoment B raw4225step0 raw4225step0Labels = mixedMoment B raw4225step1 raw4225step1Labels := by
      have ha : raw4225step1 = -raw4225step0 := by apply Matrix.ext; change ∀ i j, raw4225step1 i j = -(raw4225step0 i j); unfold raw4225step1 raw4225step0; decide +kernel
      have hl : raw4225step1Labels = raw4225step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1378 node1378Labels := by rfl

theorem canonical4226 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4226 raw4226Labels = mixedMoment B node2618 node2618Labels := by
  calc
    mixedMoment B raw4226 raw4226Labels = mixedMoment B raw4226step0 raw4226step0Labels := by
      have hz : ∀ j, raw4226 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4226step0 = (fun i j => raw4226 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4226step0 raw4226; decide +kernel
      have hl : raw4226step0Labels = raw4226Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4226 raw4226Labels permutation346 hz
    mixedMoment B raw4226step0 raw4226step0Labels = mixedMoment B raw4226step1 raw4226step1Labels := by
      have ha : raw4226step1 = (fun i j => raw4226step0 (permutation44 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4226step1 raw4226step0; decide +kernel
      have hl : raw4226step1Labels = raw4226step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4226step0 raw4226step0Labels permutation44 permutation2
    _ = mixedMoment B node2618 node2618Labels := by rfl

theorem canonical4227 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4227 raw4227Labels = mixedMoment B node2723 node2723Labels := by
  calc
    mixedMoment B raw4227 raw4227Labels = mixedMoment B raw4227step0 raw4227step0Labels := by
      have hz : ∀ j, raw4227 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4227step0 = (fun i j => raw4227 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4227step0 raw4227; decide +kernel
      have hl : raw4227step0Labels = raw4227Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4227 raw4227Labels permutation346 hz
    mixedMoment B raw4227step0 raw4227step0Labels = mixedMoment B raw4227step1 raw4227step1Labels := by
      have ha : raw4227step1 = (fun i j => raw4227step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4227step1 raw4227step0; decide +kernel
      have hl : raw4227step1Labels = raw4227step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4227step0 raw4227step0Labels permutation34 permutation2
    _ = mixedMoment B node2723 node2723Labels := by rfl

theorem canonical4228 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4228 raw4228Labels = mixedMoment B node2618 node2618Labels := by
  calc
    mixedMoment B raw4228 raw4228Labels = mixedMoment B raw4228step0 raw4228step0Labels := by
      have hz : ∀ j, raw4228 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4228step0 = (fun i j => raw4228 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4228step0 raw4228; decide +kernel
      have hl : raw4228step0Labels = raw4228Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4228 raw4228Labels permutation346 hz
    mixedMoment B raw4228step0 raw4228step0Labels = mixedMoment B raw4228step1 raw4228step1Labels := by
      have ha : raw4228step1 = (fun i j => raw4228step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4228step1 raw4228step0; decide +kernel
      have hl : raw4228step1Labels = raw4228step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4228step0 raw4228step0Labels permutation38 permutation2
    _ = mixedMoment B node2618 node2618Labels := by rfl

theorem canonical4229 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4229 raw4229Labels = mixedMoment B node1394 node1394Labels := by
  calc
    mixedMoment B raw4229 raw4229Labels = mixedMoment B raw4229step0 raw4229step0Labels := by
      have hz : ∀ j, raw4229 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4229step0 = (fun i j => raw4229 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4229step0 raw4229; decide +kernel
      have hl : raw4229step0Labels = raw4229Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4229 raw4229Labels permutation346 hz
    mixedMoment B raw4229step0 raw4229step0Labels = mixedMoment B raw4229step1 raw4229step1Labels := by
      have ha : raw4229step1 = (fun i j => raw4229step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4229step1 raw4229step0; decide +kernel
      have hl : raw4229step1Labels = raw4229step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4229step0 raw4229step0Labels permutation149 permutation2
    mixedMoment B raw4229step1 raw4229step1Labels = mixedMoment B raw4229step2 raw4229step2Labels := by
      have ha : raw4229step2 = -raw4229step1 := by apply Matrix.ext; change ∀ i j, raw4229step2 i j = -(raw4229step1 i j); unfold raw4229step2 raw4229step1; decide +kernel
      have hl : raw4229step2Labels = raw4229step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1394 node1394Labels := by rfl

theorem canonical4230 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4230 raw4230Labels = mixedMoment B node1394 node1394Labels := by
  calc
    mixedMoment B raw4230 raw4230Labels = mixedMoment B raw4230step0 raw4230step0Labels := by
      have hz : ∀ j, raw4230 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4230step0 = (fun i j => raw4230 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4230step0 raw4230; decide +kernel
      have hl : raw4230step0Labels = raw4230Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4230 raw4230Labels permutation346 hz
    mixedMoment B raw4230step0 raw4230step0Labels = mixedMoment B raw4230step1 raw4230step1Labels := by
      have ha : raw4230step1 = (fun i j => raw4230step0 (permutation143 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4230step1 raw4230step0; decide +kernel
      have hl : raw4230step1Labels = raw4230step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4230step0 raw4230step0Labels permutation143 permutation2
    mixedMoment B raw4230step1 raw4230step1Labels = mixedMoment B raw4230step2 raw4230step2Labels := by
      have ha : raw4230step2 = -raw4230step1 := by apply Matrix.ext; change ∀ i j, raw4230step2 i j = -(raw4230step1 i j); unfold raw4230step2 raw4230step1; decide +kernel
      have hl : raw4230step2Labels = raw4230step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1394 node1394Labels := by rfl

theorem canonical4235 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4235 raw4235Labels = mixedMoment B node5252 node5252Labels := by
  calc
    mixedMoment B raw4235 raw4235Labels = mixedMoment B raw4235step0 raw4235step0Labels := by
      have hz : ∀ j, raw4235 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw4235step0 = (fun i j => raw4235 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw4235step0 raw4235; decide +kernel
      have hl : raw4235step0Labels = raw4235Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4235 raw4235Labels permutation265 hz
    mixedMoment B raw4235step0 raw4235step0Labels = mixedMoment B raw4235step1 raw4235step1Labels := by
      have ha : raw4235step1 = (fun i j => raw4235step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw4235step1 raw4235step0; decide +kernel
      have hl : raw4235step1Labels = raw4235step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4235step0 raw4235step0Labels permutation32 permutation6
    mixedMoment B raw4235step1 raw4235step1Labels = mixedMoment B raw4235step2 raw4235step2Labels := by
      have ha : raw4235step2 = raw4235step1 := by apply Matrix.ext; unfold raw4235step2 raw4235step1; decide +kernel
      have hl : raw4235step1Labels = labelEmbedding9 ∘ raw4235step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4235step1 raw4235step1Labels raw4235step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5252 node5252Labels := by rfl

theorem canonical4236 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4236 raw4236Labels = mixedMoment B node5296 node5296Labels := by
  calc
    mixedMoment B raw4236 raw4236Labels = mixedMoment B raw4236step0 raw4236step0Labels := by
      have hz : ∀ j, raw4236 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw4236step0 = (fun i j => raw4236 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw4236step0 raw4236; decide +kernel
      have hl : raw4236step0Labels = raw4236Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4236 raw4236Labels permutation520 hz
    mixedMoment B raw4236step0 raw4236step0Labels = mixedMoment B raw4236step1 raw4236step1Labels := by
      have hz : ∀ j, raw4236step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4236step1 = (fun i j => raw4236step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4236step1 raw4236step0; decide +kernel
      have hl : raw4236step1Labels = raw4236step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4236step0 raw4236step0Labels permutation80 hz
    mixedMoment B raw4236step1 raw4236step1Labels = mixedMoment B raw4236step2 raw4236step2Labels := by
      have hz : ∀ j, raw4236step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw4236step2 = (fun i j => raw4236step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw4236step2 raw4236step1; decide +kernel
      have hl : raw4236step2Labels = raw4236step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4236step1 raw4236step1Labels permutation14 hz
    mixedMoment B raw4236step2 raw4236step2Labels = mixedMoment B raw4236step3 raw4236step3Labels := by
      have ha : raw4236step3 = (fun i j => raw4236step2 (permutation2 i) (permutation6 j)) := by apply Matrix.ext; unfold raw4236step3 raw4236step2; decide +kernel
      have hl : raw4236step3Labels = raw4236step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4236step2 raw4236step2Labels permutation2 permutation6
    mixedMoment B raw4236step3 raw4236step3Labels = mixedMoment B raw4236step4 raw4236step4Labels := by
      have ha : raw4236step4 = raw4236step3 := by apply Matrix.ext; unfold raw4236step4 raw4236step3; decide +kernel
      have hl : raw4236step3Labels = labelEmbedding9 ∘ raw4236step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4236step3 raw4236step3Labels raw4236step4Labels labelEmbedding9 hl
    _ = mixedMoment B node5296 node5296Labels := by rfl

theorem canonical4244 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4244 raw4244Labels = mixedMoment B node5268 node5268Labels := by
  calc
    mixedMoment B raw4244 raw4244Labels = mixedMoment B raw4244step0 raw4244step0Labels := by
      have hz : ∀ j, raw4244 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4244step0 = (fun i j => raw4244 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4244step0 raw4244; decide +kernel
      have hl : raw4244step0Labels = raw4244Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4244 raw4244Labels permutation434 hz
    mixedMoment B raw4244step0 raw4244step0Labels = mixedMoment B raw4244step1 raw4244step1Labels := by
      have hz : ∀ j, raw4244step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4244step1 = (fun i j => raw4244step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4244step1 raw4244step0; decide +kernel
      have hl : raw4244step1Labels = raw4244step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4244step0 raw4244step0Labels permutation80 hz
    mixedMoment B raw4244step1 raw4244step1Labels = mixedMoment B raw4244step2 raw4244step2Labels := by
      have ha : raw4244step2 = (fun i j => raw4244step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw4244step2 raw4244step1; decide +kernel
      have hl : raw4244step2Labels = raw4244step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4244step1 raw4244step1Labels permutation8 permutation6
    mixedMoment B raw4244step2 raw4244step2Labels = mixedMoment B raw4244step3 raw4244step3Labels := by
      have ha : raw4244step3 = raw4244step2 := by apply Matrix.ext; unfold raw4244step3 raw4244step2; decide +kernel
      have hl : raw4244step2Labels = labelEmbedding9 ∘ raw4244step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4244step2 raw4244step2Labels raw4244step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5268 node5268Labels := by rfl

theorem canonical4267 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4267 raw4267Labels = mixedMoment B node3543 node3543Labels := by
  calc
    mixedMoment B raw4267 raw4267Labels = mixedMoment B raw4267step0 raw4267step0Labels := by
      have hz : ∀ j, raw4267 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4267step0 = (fun i j => raw4267 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4267step0 raw4267; decide +kernel
      have hl : raw4267step0Labels = raw4267Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4267 raw4267Labels permutation346 hz
    mixedMoment B raw4267step0 raw4267step0Labels = mixedMoment B raw4267step1 raw4267step1Labels := by
      have ha : raw4267step1 = (fun i j => raw4267step0 (permutation137 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4267step1 raw4267step0; decide +kernel
      have hl : raw4267step1Labels = raw4267step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4267step0 raw4267step0Labels permutation137 permutation2
    _ = mixedMoment B node3543 node3543Labels := by rfl

theorem canonical4268 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4268 raw4268Labels = mixedMoment B node3389 node3389Labels := by
  calc
    mixedMoment B raw4268 raw4268Labels = mixedMoment B raw4268step0 raw4268step0Labels := by
      have hz : ∀ j, raw4268 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4268step0 = (fun i j => raw4268 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4268step0 raw4268; decide +kernel
      have hl : raw4268step0Labels = raw4268Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4268 raw4268Labels permutation346 hz
    mixedMoment B raw4268step0 raw4268step0Labels = mixedMoment B raw4268step1 raw4268step1Labels := by
      have ha : raw4268step1 = (fun i j => raw4268step0 (permutation137 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4268step1 raw4268step0; decide +kernel
      have hl : raw4268step1Labels = raw4268step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4268step0 raw4268step0Labels permutation137 permutation2
    _ = mixedMoment B node3389 node3389Labels := by rfl

theorem canonical4269 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4269 raw4269Labels = mixedMoment B node3492 node3492Labels := by
  calc
    mixedMoment B raw4269 raw4269Labels = mixedMoment B raw4269step0 raw4269step0Labels := by
      have ha : raw4269step0 = (fun i j => raw4269 (permutation609 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4269step0 raw4269; decide +kernel
      have hl : raw4269step0Labels = raw4269Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4269 raw4269Labels permutation609 permutation2
    _ = mixedMoment B node3492 node3492Labels := by rfl

theorem canonical4270 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4270 raw4270Labels = mixedMoment B node3545 node3545Labels := by
  calc
    mixedMoment B raw4270 raw4270Labels = mixedMoment B raw4270step0 raw4270step0Labels := by
      have hz : ∀ j, raw4270 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw4270step0 = (fun i j => raw4270 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw4270step0 raw4270; decide +kernel
      have hl : raw4270step0Labels = raw4270Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4270 raw4270Labels permutation520 hz
    mixedMoment B raw4270step0 raw4270step0Labels = mixedMoment B raw4270step1 raw4270step1Labels := by
      have hz : ∀ j, raw4270step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4270step1 = (fun i j => raw4270step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4270step1 raw4270step0; decide +kernel
      have hl : raw4270step1Labels = raw4270step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4270step0 raw4270step0Labels permutation80 hz
    mixedMoment B raw4270step1 raw4270step1Labels = mixedMoment B raw4270step2 raw4270step2Labels := by
      have ha : raw4270step2 = (fun i j => raw4270step1 (permutation29 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4270step2 raw4270step1; decide +kernel
      have hl : raw4270step2Labels = raw4270step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4270step1 raw4270step1Labels permutation29 permutation2
    _ = mixedMoment B node3545 node3545Labels := by rfl

theorem canonical4271 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4271 raw4271Labels = mixedMoment B node2052 node2052Labels := by
  calc
    mixedMoment B raw4271 raw4271Labels = mixedMoment B raw4271step0 raw4271step0Labels := by
      have hz : ∀ j, raw4271 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4271step0 = (fun i j => raw4271 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4271step0 raw4271; decide +kernel
      have hl : raw4271step0Labels = raw4271Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4271 raw4271Labels permutation346 hz
    mixedMoment B raw4271step0 raw4271step0Labels = mixedMoment B raw4271step1 raw4271step1Labels := by
      have ha : raw4271step1 = (fun i j => raw4271step0 (permutation137 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4271step1 raw4271step0; decide +kernel
      have hl : raw4271step1Labels = raw4271step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4271step0 raw4271step0Labels permutation137 permutation2
    _ = mixedMoment B node2052 node2052Labels := by rfl

theorem canonical4272 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4272 raw4272Labels = mixedMoment B node2290 node2290Labels := by
  calc
    mixedMoment B raw4272 raw4272Labels = mixedMoment B raw4272step0 raw4272step0Labels := by
      have hz : ∀ j, raw4272 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4272step0 = (fun i j => raw4272 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4272step0 raw4272; decide +kernel
      have hl : raw4272step0Labels = raw4272Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4272 raw4272Labels permutation346 hz
    mixedMoment B raw4272step0 raw4272step0Labels = mixedMoment B raw4272step1 raw4272step1Labels := by
      have hz : ∀ j, raw4272step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw4272step1 = (fun i j => raw4272step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw4272step1 raw4272step0; decide +kernel
      have hl : raw4272step1Labels = raw4272step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4272step0 raw4272step0Labels permutation56 hz
    mixedMoment B raw4272step1 raw4272step1Labels = mixedMoment B raw4272step2 raw4272step2Labels := by
      have ha : raw4272step2 = (fun i j => raw4272step1 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw4272step2 raw4272step1; decide +kernel
      have hl : raw4272step2Labels = raw4272step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4272step1 raw4272step1Labels permutation8 permutation4
    mixedMoment B raw4272step2 raw4272step2Labels = mixedMoment B raw4272step3 raw4272step3Labels := by
      have ha : raw4272step3 = -raw4272step2 := by apply Matrix.ext; change ∀ i j, raw4272step3 i j = -(raw4272step2 i j); unfold raw4272step3 raw4272step2; decide +kernel
      have hl : raw4272step3Labels = raw4272step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2290 node2290Labels := by rfl

theorem canonical4273 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4273 raw4273Labels = mixedMoment B node2050 node2050Labels := by
  calc
    mixedMoment B raw4273 raw4273Labels = mixedMoment B raw4273step0 raw4273step0Labels := by
      have ha : raw4273step0 = (fun i j => raw4273 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw4273step0 raw4273; decide +kernel
      have hl : raw4273step0Labels = raw4273Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4273 raw4273Labels permutation152 permutation4
    mixedMoment B raw4273step0 raw4273step0Labels = mixedMoment B raw4273step1 raw4273step1Labels := by
      have ha : raw4273step1 = -raw4273step0 := by apply Matrix.ext; change ∀ i j, raw4273step1 i j = -(raw4273step0 i j); unfold raw4273step1 raw4273step0; decide +kernel
      have hl : raw4273step1Labels = raw4273step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2050 node2050Labels := by rfl

theorem canonical4274 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4274 raw4274Labels = mixedMoment B node2055 node2055Labels := by
  calc
    mixedMoment B raw4274 raw4274Labels = mixedMoment B raw4274step0 raw4274step0Labels := by
      have hz : ∀ j, raw4274 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4274step0 = (fun i j => raw4274 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4274step0 raw4274; decide +kernel
      have hl : raw4274step0Labels = raw4274Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4274 raw4274Labels permutation346 hz
    mixedMoment B raw4274step0 raw4274step0Labels = mixedMoment B raw4274step1 raw4274step1Labels := by
      have ha : raw4274step1 = (fun i j => raw4274step0 (permutation35 i) (permutation4 j)) := by apply Matrix.ext; unfold raw4274step1 raw4274step0; decide +kernel
      have hl : raw4274step1Labels = raw4274step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4274step0 raw4274step0Labels permutation35 permutation4
    mixedMoment B raw4274step1 raw4274step1Labels = mixedMoment B raw4274step2 raw4274step2Labels := by
      have ha : raw4274step2 = -raw4274step1 := by apply Matrix.ext; change ∀ i j, raw4274step2 i j = -(raw4274step1 i j); unfold raw4274step2 raw4274step1; decide +kernel
      have hl : raw4274step2Labels = raw4274step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2055 node2055Labels := by rfl

theorem canonical4275 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4275 raw4275Labels = mixedMoment B node2052 node2052Labels := by
  calc
    mixedMoment B raw4275 raw4275Labels = mixedMoment B raw4275step0 raw4275step0Labels := by
      have hz : ∀ j, raw4275 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4275step0 = (fun i j => raw4275 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4275step0 raw4275; decide +kernel
      have hl : raw4275step0Labels = raw4275Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4275 raw4275Labels permutation346 hz
    mixedMoment B raw4275step0 raw4275step0Labels = mixedMoment B raw4275step1 raw4275step1Labels := by
      have ha : raw4275step1 = (fun i j => raw4275step0 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw4275step1 raw4275step0; decide +kernel
      have hl : raw4275step1Labels = raw4275step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4275step0 raw4275step0Labels permutation32 permutation4
    mixedMoment B raw4275step1 raw4275step1Labels = mixedMoment B raw4275step2 raw4275step2Labels := by
      have ha : raw4275step2 = -raw4275step1 := by apply Matrix.ext; change ∀ i j, raw4275step2 i j = -(raw4275step1 i j); unfold raw4275step2 raw4275step1; decide +kernel
      have hl : raw4275step2Labels = raw4275step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2052 node2052Labels := by rfl

theorem canonical4276 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4276 raw4276Labels = mixedMoment B node3543 node3543Labels := by
  calc
    mixedMoment B raw4276 raw4276Labels = mixedMoment B raw4276step0 raw4276step0Labels := by
      have hz : ∀ j, raw4276 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw4276step0 = (fun i j => raw4276 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw4276step0 raw4276; decide +kernel
      have hl : raw4276step0Labels = raw4276Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4276 raw4276Labels permutation265 hz
    mixedMoment B raw4276step0 raw4276step0Labels = mixedMoment B raw4276step1 raw4276step1Labels := by
      have ha : raw4276step1 = (fun i j => raw4276step0 (permutation137 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4276step1 raw4276step0; decide +kernel
      have hl : raw4276step1Labels = raw4276step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4276step0 raw4276step0Labels permutation137 permutation2
    _ = mixedMoment B node3543 node3543Labels := by rfl

theorem canonical4277 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4277 raw4277Labels = mixedMoment B node3634 node3634Labels := by
  calc
    mixedMoment B raw4277 raw4277Labels = mixedMoment B raw4277step0 raw4277step0Labels := by
      have hz : ∀ j, raw4277 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw4277step0 = (fun i j => raw4277 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw4277step0 raw4277; decide +kernel
      have hl : raw4277step0Labels = raw4277Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4277 raw4277Labels permutation520 hz
    mixedMoment B raw4277step0 raw4277step0Labels = mixedMoment B raw4277step1 raw4277step1Labels := by
      have hz : ∀ j, raw4277step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4277step1 = (fun i j => raw4277step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4277step1 raw4277step0; decide +kernel
      have hl : raw4277step1Labels = raw4277step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4277step0 raw4277step0Labels permutation80 hz
    mixedMoment B raw4277step1 raw4277step1Labels = mixedMoment B raw4277step2 raw4277step2Labels := by
      have hz : ∀ j, raw4277step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw4277step2 = (fun i j => raw4277step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw4277step2 raw4277step1; decide +kernel
      have hl : raw4277step2Labels = raw4277step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4277step1 raw4277step1Labels permutation14 hz
    mixedMoment B raw4277step2 raw4277step2Labels = mixedMoment B raw4277step3 raw4277step3Labels := by
      have ha : raw4277step3 = (fun i j => raw4277step2 (permutation7 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4277step3 raw4277step2; decide +kernel
      have hl : raw4277step3Labels = raw4277step2Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4277step2 raw4277step2Labels permutation7 permutation2
    _ = mixedMoment B node3634 node3634Labels := by rfl

theorem canonical4278 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4278 raw4278Labels = mixedMoment B node3387 node3387Labels := by
  calc
    mixedMoment B raw4278 raw4278Labels = mixedMoment B raw4278step0 raw4278step0Labels := by
      have ha : raw4278step0 = (fun i j => raw4278 (permutation609 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4278step0 raw4278; decide +kernel
      have hl : raw4278step0Labels = raw4278Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4278 raw4278Labels permutation609 permutation2
    _ = mixedMoment B node3387 node3387Labels := by rfl

theorem canonical4279 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4279 raw4279Labels = mixedMoment B node3393 node3393Labels := by
  calc
    mixedMoment B raw4279 raw4279Labels = mixedMoment B raw4279step0 raw4279step0Labels := by
      have hz : ∀ j, raw4279 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4279step0 = (fun i j => raw4279 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4279step0 raw4279; decide +kernel
      have hl : raw4279step0Labels = raw4279Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4279 raw4279Labels permutation346 hz
    mixedMoment B raw4279step0 raw4279step0Labels = mixedMoment B raw4279step1 raw4279step1Labels := by
      have ha : raw4279step1 = (fun i j => raw4279step0 (permutation138 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4279step1 raw4279step0; decide +kernel
      have hl : raw4279step1Labels = raw4279step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4279step0 raw4279step0Labels permutation138 permutation2
    _ = mixedMoment B node3393 node3393Labels := by rfl

theorem canonical4280 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4280 raw4280Labels = mixedMoment B node3389 node3389Labels := by
  calc
    mixedMoment B raw4280 raw4280Labels = mixedMoment B raw4280step0 raw4280step0Labels := by
      have hz : ∀ j, raw4280 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4280step0 = (fun i j => raw4280 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4280step0 raw4280; decide +kernel
      have hl : raw4280step0Labels = raw4280Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4280 raw4280Labels permutation346 hz
    mixedMoment B raw4280step0 raw4280step0Labels = mixedMoment B raw4280step1 raw4280step1Labels := by
      have ha : raw4280step1 = (fun i j => raw4280step0 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw4280step1 raw4280step0; decide +kernel
      have hl : raw4280step1Labels = raw4280step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4280step0 raw4280step0Labels permutation32 permutation4
    mixedMoment B raw4280step1 raw4280step1Labels = mixedMoment B raw4280step2 raw4280step2Labels := by
      have ha : raw4280step2 = -raw4280step1 := by apply Matrix.ext; change ∀ i j, raw4280step2 i j = -(raw4280step1 i j); unfold raw4280step2 raw4280step1; decide +kernel
      have hl : raw4280step2Labels = raw4280step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3389 node3389Labels := by rfl

theorem canonical4281 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4281 raw4281Labels = mixedMoment B node3543 node3543Labels := by
  calc
    mixedMoment B raw4281 raw4281Labels = mixedMoment B raw4281step0 raw4281step0Labels := by
      have hz : ∀ j, raw4281 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw4281step0 = (fun i j => raw4281 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw4281step0 raw4281; decide +kernel
      have hl : raw4281step0Labels = raw4281Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4281 raw4281Labels permutation520 hz
    mixedMoment B raw4281step0 raw4281step0Labels = mixedMoment B raw4281step1 raw4281step1Labels := by
      have ha : raw4281step1 = (fun i j => raw4281step0 (permutation137 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4281step1 raw4281step0; decide +kernel
      have hl : raw4281step1Labels = raw4281step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4281step0 raw4281step0Labels permutation137 permutation2
    _ = mixedMoment B node3543 node3543Labels := by rfl

theorem canonical4342 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4342 raw4342Labels = mixedMoment B node5261 node5261Labels := by
  calc
    mixedMoment B raw4342 raw4342Labels = mixedMoment B raw4342step0 raw4342step0Labels := by
      have hz : ∀ j, raw4342 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4342step0 = (fun i j => raw4342 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4342step0 raw4342; decide +kernel
      have hl : raw4342step0Labels = raw4342Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4342 raw4342Labels permutation434 hz
    mixedMoment B raw4342step0 raw4342step0Labels = mixedMoment B raw4342step1 raw4342step1Labels := by
      have hz : ∀ j, raw4342step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw4342step1 = (fun i j => raw4342step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw4342step1 raw4342step0; decide +kernel
      have hl : raw4342step1Labels = raw4342step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4342step0 raw4342step0Labels permutation56 hz
    mixedMoment B raw4342step1 raw4342step1Labels = mixedMoment B raw4342step2 raw4342step2Labels := by
      have ha : raw4342step2 = (fun i j => raw4342step1 (permutation10 i) (permutation7 j)) := by apply Matrix.ext; unfold raw4342step2 raw4342step1; decide +kernel
      have hl : raw4342step2Labels = raw4342step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4342step1 raw4342step1Labels permutation10 permutation7
    mixedMoment B raw4342step2 raw4342step2Labels = mixedMoment B raw4342step3 raw4342step3Labels := by
      have ha : raw4342step3 = raw4342step2 := by apply Matrix.ext; unfold raw4342step3 raw4342step2; decide +kernel
      have hl : raw4342step2Labels = labelEmbedding10 ∘ raw4342step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4342step2 raw4342step2Labels raw4342step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5261 node5261Labels := by rfl

theorem canonical4343 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4343 raw4343Labels = mixedMoment B node5261 node5261Labels := by
  calc
    mixedMoment B raw4343 raw4343Labels = mixedMoment B raw4343step0 raw4343step0Labels := by
      have hz : ∀ j, raw4343 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4343step0 = (fun i j => raw4343 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4343step0 raw4343; decide +kernel
      have hl : raw4343step0Labels = raw4343Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4343 raw4343Labels permutation346 hz
    mixedMoment B raw4343step0 raw4343step0Labels = mixedMoment B raw4343step1 raw4343step1Labels := by
      have hz : ∀ j, raw4343step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw4343step1 = (fun i j => raw4343step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw4343step1 raw4343step0; decide +kernel
      have hl : raw4343step1Labels = raw4343step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4343step0 raw4343step0Labels permutation56 hz
    mixedMoment B raw4343step1 raw4343step1Labels = mixedMoment B raw4343step2 raw4343step2Labels := by
      have ha : raw4343step2 = (fun i j => raw4343step1 (permutation10 i) (permutation7 j)) := by apply Matrix.ext; unfold raw4343step2 raw4343step1; decide +kernel
      have hl : raw4343step2Labels = raw4343step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4343step1 raw4343step1Labels permutation10 permutation7
    mixedMoment B raw4343step2 raw4343step2Labels = mixedMoment B raw4343step3 raw4343step3Labels := by
      have ha : raw4343step3 = raw4343step2 := by apply Matrix.ext; unfold raw4343step3 raw4343step2; decide +kernel
      have hl : raw4343step2Labels = labelEmbedding10 ∘ raw4343step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4343step2 raw4343step2Labels raw4343step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5261 node5261Labels := by rfl

theorem canonical4344 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4344 raw4344Labels = mixedMoment B node5312 node5312Labels := by
  calc
    mixedMoment B raw4344 raw4344Labels = mixedMoment B raw4344step0 raw4344step0Labels := by
      have hz : ∀ j, raw4344 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw4344step0 = (fun i j => raw4344 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw4344step0 raw4344; decide +kernel
      have hl : raw4344step0Labels = raw4344Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4344 raw4344Labels permutation520 hz
    mixedMoment B raw4344step0 raw4344step0Labels = mixedMoment B raw4344step1 raw4344step1Labels := by
      have hz : ∀ j, raw4344step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw4344step1 = (fun i j => raw4344step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw4344step1 raw4344step0; decide +kernel
      have hl : raw4344step1Labels = raw4344step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4344step0 raw4344step0Labels permutation104 hz
    mixedMoment B raw4344step1 raw4344step1Labels = mixedMoment B raw4344step2 raw4344step2Labels := by
      have hz : ∀ j, raw4344step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw4344step2 = (fun i j => raw4344step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw4344step2 raw4344step1; decide +kernel
      have hl : raw4344step2Labels = raw4344step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4344step1 raw4344step1Labels permutation20 hz
    mixedMoment B raw4344step2 raw4344step2Labels = mixedMoment B raw4344step3 raw4344step3Labels := by
      have hz : ∀ j, raw4344step2 (permutation4 0) j = 0 := by decide +kernel
      have ha : raw4344step3 = (fun i j => raw4344step2 (permutation4 i.succ) j) := by apply Matrix.ext; unfold raw4344step3 raw4344step2; decide +kernel
      have hl : raw4344step3Labels = raw4344step2Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4344step2 raw4344step2Labels permutation4 hz
    mixedMoment B raw4344step3 raw4344step3Labels = mixedMoment B raw4344step4 raw4344step4Labels := by
      have ha : raw4344step4 = (fun i j => raw4344step3 (permutation0 i) (permutation7 j)) := by apply Matrix.ext; unfold raw4344step4 raw4344step3; decide +kernel
      have hl : raw4344step4Labels = raw4344step3Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4344step3 raw4344step3Labels permutation0 permutation7
    mixedMoment B raw4344step4 raw4344step4Labels = mixedMoment B raw4344step5 raw4344step5Labels := by
      have ha : raw4344step5 = raw4344step4 := by apply Matrix.ext; unfold raw4344step5 raw4344step4; decide +kernel
      have hl : raw4344step4Labels = labelEmbedding10 ∘ raw4344step5Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4344step4 raw4344step4Labels raw4344step5Labels labelEmbedding10 hl
    _ = mixedMoment B node5312 node5312Labels := by rfl

theorem canonical4345 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4345 raw4345Labels = mixedMoment B node4897 node4897Labels := by
  calc
    mixedMoment B raw4345 raw4345Labels = mixedMoment B raw4345step0 raw4345step0Labels := by
      have hz : ∀ j, raw4345 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4345step0 = (fun i j => raw4345 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4345step0 raw4345; decide +kernel
      have hl : raw4345step0Labels = raw4345Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4345 raw4345Labels permutation434 hz
    mixedMoment B raw4345step0 raw4345step0Labels = mixedMoment B raw4345step1 raw4345step1Labels := by
      have hz : ∀ j, raw4345step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4345step1 = (fun i j => raw4345step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4345step1 raw4345step0; decide +kernel
      have hl : raw4345step1Labels = raw4345step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4345step0 raw4345step0Labels permutation80 hz
    mixedMoment B raw4345step1 raw4345step1Labels = mixedMoment B raw4345step2 raw4345step2Labels := by
      have hz : ∀ j, raw4345step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw4345step2 = (fun i j => raw4345step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw4345step2 raw4345step1; decide +kernel
      have hl : raw4345step2Labels = raw4345step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4345step1 raw4345step1Labels permutation14 hz
    mixedMoment B raw4345step2 raw4345step2Labels = mixedMoment B raw4345step3 raw4345step3Labels := by
      have ha : raw4345step3 = (fun i j => raw4345step2 (permutation7 i) (permutation7 j)) := by apply Matrix.ext; unfold raw4345step3 raw4345step2; decide +kernel
      have hl : raw4345step3Labels = raw4345step2Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4345step2 raw4345step2Labels permutation7 permutation7
    mixedMoment B raw4345step3 raw4345step3Labels = mixedMoment B raw4345step4 raw4345step4Labels := by
      have ha : raw4345step4 = -raw4345step3 := by apply Matrix.ext; change ∀ i j, raw4345step4 i j = -(raw4345step3 i j); unfold raw4345step4 raw4345step3; decide +kernel
      have hl : raw4345step4Labels = raw4345step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw4345step4 raw4345step4Labels = mixedMoment B raw4345step5 raw4345step5Labels := by
      have ha : raw4345step5 = raw4345step4 := by apply Matrix.ext; unfold raw4345step5 raw4345step4; decide +kernel
      have hl : raw4345step4Labels = labelEmbedding10 ∘ raw4345step5Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4345step4 raw4345step4Labels raw4345step5Labels labelEmbedding10 hl
    _ = mixedMoment B node4897 node4897Labels := by rfl

theorem canonical4346 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4346 raw4346Labels = mixedMoment B node4890 node4890Labels := by
  calc
    mixedMoment B raw4346 raw4346Labels = mixedMoment B raw4346step0 raw4346step0Labels := by
      have hz : ∀ j, raw4346 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4346step0 = (fun i j => raw4346 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4346step0 raw4346; decide +kernel
      have hl : raw4346step0Labels = raw4346Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4346 raw4346Labels permutation434 hz
    mixedMoment B raw4346step0 raw4346step0Labels = mixedMoment B raw4346step1 raw4346step1Labels := by
      have hz : ∀ j, raw4346step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4346step1 = (fun i j => raw4346step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4346step1 raw4346step0; decide +kernel
      have hl : raw4346step1Labels = raw4346step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4346step0 raw4346step0Labels permutation80 hz
    mixedMoment B raw4346step1 raw4346step1Labels = mixedMoment B raw4346step2 raw4346step2Labels := by
      have ha : raw4346step2 = (fun i j => raw4346step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw4346step2 raw4346step1; decide +kernel
      have hl : raw4346step2Labels = raw4346step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4346step1 raw4346step1Labels permutation8 permutation6
    mixedMoment B raw4346step2 raw4346step2Labels = mixedMoment B raw4346step3 raw4346step3Labels := by
      have ha : raw4346step3 = raw4346step2 := by apply Matrix.ext; unfold raw4346step3 raw4346step2; decide +kernel
      have hl : raw4346step2Labels = labelEmbedding9 ∘ raw4346step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4346step2 raw4346step2Labels raw4346step3Labels labelEmbedding9 hl
    _ = mixedMoment B node4890 node4890Labels := by rfl

theorem canonical4347 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4347 raw4347Labels = mixedMoment B node5252 node5252Labels := by
  calc
    mixedMoment B raw4347 raw4347Labels = mixedMoment B raw4347step0 raw4347step0Labels := by
      have hz : ∀ j, raw4347 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4347step0 = (fun i j => raw4347 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4347step0 raw4347; decide +kernel
      have hl : raw4347step0Labels = raw4347Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4347 raw4347Labels permutation434 hz
    mixedMoment B raw4347step0 raw4347step0Labels = mixedMoment B raw4347step1 raw4347step1Labels := by
      have ha : raw4347step1 = (fun i j => raw4347step0 (permutation38 i) (permutation6 j)) := by apply Matrix.ext; unfold raw4347step1 raw4347step0; decide +kernel
      have hl : raw4347step1Labels = raw4347step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4347step0 raw4347step0Labels permutation38 permutation6
    mixedMoment B raw4347step1 raw4347step1Labels = mixedMoment B raw4347step2 raw4347step2Labels := by
      have ha : raw4347step2 = raw4347step1 := by apply Matrix.ext; unfold raw4347step2 raw4347step1; decide +kernel
      have hl : raw4347step1Labels = labelEmbedding9 ∘ raw4347step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4347step1 raw4347step1Labels raw4347step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5252 node5252Labels := by rfl

theorem canonical4348 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4348 raw4348Labels = mixedMoment B node5252 node5252Labels := by
  calc
    mixedMoment B raw4348 raw4348Labels = mixedMoment B raw4348step0 raw4348step0Labels := by
      have hz : ∀ j, raw4348 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4348step0 = (fun i j => raw4348 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4348step0 raw4348; decide +kernel
      have hl : raw4348step0Labels = raw4348Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4348 raw4348Labels permutation346 hz
    mixedMoment B raw4348step0 raw4348step0Labels = mixedMoment B raw4348step1 raw4348step1Labels := by
      have ha : raw4348step1 = (fun i j => raw4348step0 (permutation38 i) (permutation6 j)) := by apply Matrix.ext; unfold raw4348step1 raw4348step0; decide +kernel
      have hl : raw4348step1Labels = raw4348step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4348step0 raw4348step0Labels permutation38 permutation6
    mixedMoment B raw4348step1 raw4348step1Labels = mixedMoment B raw4348step2 raw4348step2Labels := by
      have ha : raw4348step2 = raw4348step1 := by apply Matrix.ext; unfold raw4348step2 raw4348step1; decide +kernel
      have hl : raw4348step1Labels = labelEmbedding9 ∘ raw4348step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4348step1 raw4348step1Labels raw4348step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5252 node5252Labels := by rfl

theorem canonical4349 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4349 raw4349Labels = mixedMoment B node5296 node5296Labels := by
  calc
    mixedMoment B raw4349 raw4349Labels = mixedMoment B raw4349step0 raw4349step0Labels := by
      have hz : ∀ j, raw4349 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw4349step0 = (fun i j => raw4349 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw4349step0 raw4349; decide +kernel
      have hl : raw4349step0Labels = raw4349Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4349 raw4349Labels permutation520 hz
    mixedMoment B raw4349step0 raw4349step0Labels = mixedMoment B raw4349step1 raw4349step1Labels := by
      have hz : ∀ j, raw4349step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw4349step1 = (fun i j => raw4349step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw4349step1 raw4349step0; decide +kernel
      have hl : raw4349step1Labels = raw4349step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4349step0 raw4349step0Labels permutation104 hz
    mixedMoment B raw4349step1 raw4349step1Labels = mixedMoment B raw4349step2 raw4349step2Labels := by
      have hz : ∀ j, raw4349step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw4349step2 = (fun i j => raw4349step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw4349step2 raw4349step1; decide +kernel
      have hl : raw4349step2Labels = raw4349step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4349step1 raw4349step1Labels permutation20 hz
    mixedMoment B raw4349step2 raw4349step2Labels = mixedMoment B raw4349step3 raw4349step3Labels := by
      have ha : raw4349step3 = (fun i j => raw4349step2 (permutation2 i) (permutation6 j)) := by apply Matrix.ext; unfold raw4349step3 raw4349step2; decide +kernel
      have hl : raw4349step3Labels = raw4349step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4349step2 raw4349step2Labels permutation2 permutation6
    mixedMoment B raw4349step3 raw4349step3Labels = mixedMoment B raw4349step4 raw4349step4Labels := by
      have ha : raw4349step4 = raw4349step3 := by apply Matrix.ext; unfold raw4349step4 raw4349step3; decide +kernel
      have hl : raw4349step3Labels = labelEmbedding9 ∘ raw4349step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4349step3 raw4349step3Labels raw4349step4Labels labelEmbedding9 hl
    _ = mixedMoment B node5296 node5296Labels := by rfl

theorem canonical4350 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4350 raw4350Labels = mixedMoment B node4890 node4890Labels := by
  calc
    mixedMoment B raw4350 raw4350Labels = mixedMoment B raw4350step0 raw4350step0Labels := by
      have hz : ∀ j, raw4350 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4350step0 = (fun i j => raw4350 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4350step0 raw4350; decide +kernel
      have hl : raw4350step0Labels = raw4350Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4350 raw4350Labels permutation434 hz
    mixedMoment B raw4350step0 raw4350step0Labels = mixedMoment B raw4350step1 raw4350step1Labels := by
      have hz : ∀ j, raw4350step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4350step1 = (fun i j => raw4350step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4350step1 raw4350step0; decide +kernel
      have hl : raw4350step1Labels = raw4350step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4350step0 raw4350step0Labels permutation80 hz
    mixedMoment B raw4350step1 raw4350step1Labels = mixedMoment B raw4350step2 raw4350step2Labels := by
      have ha : raw4350step2 = (fun i j => raw4350step1 (permutation29 i) (permutation7 j)) := by apply Matrix.ext; unfold raw4350step2 raw4350step1; decide +kernel
      have hl : raw4350step2Labels = raw4350step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4350step1 raw4350step1Labels permutation29 permutation7
    mixedMoment B raw4350step2 raw4350step2Labels = mixedMoment B raw4350step3 raw4350step3Labels := by
      have ha : raw4350step3 = -raw4350step2 := by apply Matrix.ext; change ∀ i j, raw4350step3 i j = -(raw4350step2 i j); unfold raw4350step3 raw4350step2; decide +kernel
      have hl : raw4350step3Labels = raw4350step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw4350step3 raw4350step3Labels = mixedMoment B raw4350step4 raw4350step4Labels := by
      have ha : raw4350step4 = raw4350step3 := by apply Matrix.ext; unfold raw4350step4 raw4350step3; decide +kernel
      have hl : raw4350step3Labels = labelEmbedding10 ∘ raw4350step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4350step3 raw4350step3Labels raw4350step4Labels labelEmbedding10 hl
    _ = mixedMoment B node4890 node4890Labels := by rfl

theorem canonical4351 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4351 raw4351Labels = mixedMoment B node5252 node5252Labels := by
  calc
    mixedMoment B raw4351 raw4351Labels = mixedMoment B raw4351step0 raw4351step0Labels := by
      have hz : ∀ j, raw4351 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw4351step0 = (fun i j => raw4351 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw4351step0 raw4351; decide +kernel
      have hl : raw4351step0Labels = raw4351Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4351 raw4351Labels permutation265 hz
    mixedMoment B raw4351step0 raw4351step0Labels = mixedMoment B raw4351step1 raw4351step1Labels := by
      have ha : raw4351step1 = (fun i j => raw4351step0 (permutation38 i) (permutation6 j)) := by apply Matrix.ext; unfold raw4351step1 raw4351step0; decide +kernel
      have hl : raw4351step1Labels = raw4351step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4351step0 raw4351step0Labels permutation38 permutation6
    mixedMoment B raw4351step1 raw4351step1Labels = mixedMoment B raw4351step2 raw4351step2Labels := by
      have ha : raw4351step2 = raw4351step1 := by apply Matrix.ext; unfold raw4351step2 raw4351step1; decide +kernel
      have hl : raw4351step1Labels = labelEmbedding9 ∘ raw4351step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4351step1 raw4351step1Labels raw4351step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5252 node5252Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical34
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical4352 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4352 raw4352Labels = mixedMoment B node5296 node5296Labels := by
  calc
    mixedMoment B raw4352 raw4352Labels = mixedMoment B raw4352step0 raw4352step0Labels := by
      have hz : ∀ j, raw4352 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw4352step0 = (fun i j => raw4352 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw4352step0 raw4352; decide +kernel
      have hl : raw4352step0Labels = raw4352Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4352 raw4352Labels permutation520 hz
    mixedMoment B raw4352step0 raw4352step0Labels = mixedMoment B raw4352step1 raw4352step1Labels := by
      have hz : ∀ j, raw4352step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw4352step1 = (fun i j => raw4352step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw4352step1 raw4352step0; decide +kernel
      have hl : raw4352step1Labels = raw4352step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4352step0 raw4352step0Labels permutation104 hz
    mixedMoment B raw4352step1 raw4352step1Labels = mixedMoment B raw4352step2 raw4352step2Labels := by
      have hz : ∀ j, raw4352step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw4352step2 = (fun i j => raw4352step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw4352step2 raw4352step1; decide +kernel
      have hl : raw4352step2Labels = raw4352step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4352step1 raw4352step1Labels permutation14 hz
    mixedMoment B raw4352step2 raw4352step2Labels = mixedMoment B raw4352step3 raw4352step3Labels := by
      have ha : raw4352step3 = (fun i j => raw4352step2 (permutation2 i) (permutation6 j)) := by apply Matrix.ext; unfold raw4352step3 raw4352step2; decide +kernel
      have hl : raw4352step3Labels = raw4352step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4352step2 raw4352step2Labels permutation2 permutation6
    mixedMoment B raw4352step3 raw4352step3Labels = mixedMoment B raw4352step4 raw4352step4Labels := by
      have ha : raw4352step4 = raw4352step3 := by apply Matrix.ext; unfold raw4352step4 raw4352step3; decide +kernel
      have hl : raw4352step3Labels = labelEmbedding9 ∘ raw4352step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4352step3 raw4352step3Labels raw4352step4Labels labelEmbedding9 hl
    _ = mixedMoment B node5296 node5296Labels := by rfl

theorem canonical4353 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4353 raw4353Labels = mixedMoment B node4897 node4897Labels := by
  calc
    mixedMoment B raw4353 raw4353Labels = mixedMoment B raw4353step0 raw4353step0Labels := by
      have hz : ∀ j, raw4353 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4353step0 = (fun i j => raw4353 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4353step0 raw4353; decide +kernel
      have hl : raw4353step0Labels = raw4353Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4353 raw4353Labels permutation434 hz
    mixedMoment B raw4353step0 raw4353step0Labels = mixedMoment B raw4353step1 raw4353step1Labels := by
      have hz : ∀ j, raw4353step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4353step1 = (fun i j => raw4353step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4353step1 raw4353step0; decide +kernel
      have hl : raw4353step1Labels = raw4353step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4353step0 raw4353step0Labels permutation80 hz
    mixedMoment B raw4353step1 raw4353step1Labels = mixedMoment B raw4353step2 raw4353step2Labels := by
      have hz : ∀ j, raw4353step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw4353step2 = (fun i j => raw4353step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw4353step2 raw4353step1; decide +kernel
      have hl : raw4353step2Labels = raw4353step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4353step1 raw4353step1Labels permutation14 hz
    mixedMoment B raw4353step2 raw4353step2Labels = mixedMoment B raw4353step3 raw4353step3Labels := by
      have ha : raw4353step3 = (fun i j => raw4353step2 (permutation2 i) (permutation6 j)) := by apply Matrix.ext; unfold raw4353step3 raw4353step2; decide +kernel
      have hl : raw4353step3Labels = raw4353step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4353step2 raw4353step2Labels permutation2 permutation6
    mixedMoment B raw4353step3 raw4353step3Labels = mixedMoment B raw4353step4 raw4353step4Labels := by
      have ha : raw4353step4 = raw4353step3 := by apply Matrix.ext; unfold raw4353step4 raw4353step3; decide +kernel
      have hl : raw4353step3Labels = labelEmbedding9 ∘ raw4353step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4353step3 raw4353step3Labels raw4353step4Labels labelEmbedding9 hl
    _ = mixedMoment B node4897 node4897Labels := by rfl

theorem canonical4354 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4354 raw4354Labels = mixedMoment B node5261 node5261Labels := by
  calc
    mixedMoment B raw4354 raw4354Labels = mixedMoment B raw4354step0 raw4354step0Labels := by
      have hz : ∀ j, raw4354 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4354step0 = (fun i j => raw4354 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4354step0 raw4354; decide +kernel
      have hl : raw4354step0Labels = raw4354Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4354 raw4354Labels permutation434 hz
    mixedMoment B raw4354step0 raw4354step0Labels = mixedMoment B raw4354step1 raw4354step1Labels := by
      have hz : ∀ j, raw4354step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw4354step1 = (fun i j => raw4354step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw4354step1 raw4354step0; decide +kernel
      have hl : raw4354step1Labels = raw4354step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4354step0 raw4354step0Labels permutation56 hz
    mixedMoment B raw4354step1 raw4354step1Labels = mixedMoment B raw4354step2 raw4354step2Labels := by
      have ha : raw4354step2 = (fun i j => raw4354step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw4354step2 raw4354step1; decide +kernel
      have hl : raw4354step2Labels = raw4354step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4354step1 raw4354step1Labels permutation8 permutation6
    mixedMoment B raw4354step2 raw4354step2Labels = mixedMoment B raw4354step3 raw4354step3Labels := by
      have ha : raw4354step3 = raw4354step2 := by apply Matrix.ext; unfold raw4354step3 raw4354step2; decide +kernel
      have hl : raw4354step2Labels = labelEmbedding9 ∘ raw4354step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4354step2 raw4354step2Labels raw4354step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5261 node5261Labels := by rfl

theorem canonical4355 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4355 raw4355Labels = mixedMoment B node5261 node5261Labels := by
  calc
    mixedMoment B raw4355 raw4355Labels = mixedMoment B raw4355step0 raw4355step0Labels := by
      have hz : ∀ j, raw4355 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4355step0 = (fun i j => raw4355 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4355step0 raw4355; decide +kernel
      have hl : raw4355step0Labels = raw4355Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4355 raw4355Labels permutation346 hz
    mixedMoment B raw4355step0 raw4355step0Labels = mixedMoment B raw4355step1 raw4355step1Labels := by
      have hz : ∀ j, raw4355step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw4355step1 = (fun i j => raw4355step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw4355step1 raw4355step0; decide +kernel
      have hl : raw4355step1Labels = raw4355step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4355step0 raw4355step0Labels permutation56 hz
    mixedMoment B raw4355step1 raw4355step1Labels = mixedMoment B raw4355step2 raw4355step2Labels := by
      have ha : raw4355step2 = (fun i j => raw4355step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw4355step2 raw4355step1; decide +kernel
      have hl : raw4355step2Labels = raw4355step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4355step1 raw4355step1Labels permutation8 permutation6
    mixedMoment B raw4355step2 raw4355step2Labels = mixedMoment B raw4355step3 raw4355step3Labels := by
      have ha : raw4355step3 = raw4355step2 := by apply Matrix.ext; unfold raw4355step3 raw4355step2; decide +kernel
      have hl : raw4355step2Labels = labelEmbedding9 ∘ raw4355step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4355step2 raw4355step2Labels raw4355step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5261 node5261Labels := by rfl

theorem canonical4356 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4356 raw4356Labels = mixedMoment B node5312 node5312Labels := by
  calc
    mixedMoment B raw4356 raw4356Labels = mixedMoment B raw4356step0 raw4356step0Labels := by
      have hz : ∀ j, raw4356 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw4356step0 = (fun i j => raw4356 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw4356step0 raw4356; decide +kernel
      have hl : raw4356step0Labels = raw4356Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4356 raw4356Labels permutation520 hz
    mixedMoment B raw4356step0 raw4356step0Labels = mixedMoment B raw4356step1 raw4356step1Labels := by
      have hz : ∀ j, raw4356step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw4356step1 = (fun i j => raw4356step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw4356step1 raw4356step0; decide +kernel
      have hl : raw4356step1Labels = raw4356step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4356step0 raw4356step0Labels permutation104 hz
    mixedMoment B raw4356step1 raw4356step1Labels = mixedMoment B raw4356step2 raw4356step2Labels := by
      have hz : ∀ j, raw4356step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw4356step2 = (fun i j => raw4356step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw4356step2 raw4356step1; decide +kernel
      have hl : raw4356step2Labels = raw4356step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4356step1 raw4356step1Labels permutation20 hz
    mixedMoment B raw4356step2 raw4356step2Labels = mixedMoment B raw4356step3 raw4356step3Labels := by
      have hz : ∀ j, raw4356step2 (permutation4 0) j = 0 := by decide +kernel
      have ha : raw4356step3 = (fun i j => raw4356step2 (permutation4 i.succ) j) := by apply Matrix.ext; unfold raw4356step3 raw4356step2; decide +kernel
      have hl : raw4356step3Labels = raw4356step2Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4356step2 raw4356step2Labels permutation4 hz
    mixedMoment B raw4356step3 raw4356step3Labels = mixedMoment B raw4356step4 raw4356step4Labels := by
      have ha : raw4356step4 = (fun i j => raw4356step3 (permutation0 i) (permutation6 j)) := by apply Matrix.ext; unfold raw4356step4 raw4356step3; decide +kernel
      have hl : raw4356step4Labels = raw4356step3Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4356step3 raw4356step3Labels permutation0 permutation6
    mixedMoment B raw4356step4 raw4356step4Labels = mixedMoment B raw4356step5 raw4356step5Labels := by
      have ha : raw4356step5 = raw4356step4 := by apply Matrix.ext; unfold raw4356step5 raw4356step4; decide +kernel
      have hl : raw4356step4Labels = labelEmbedding9 ∘ raw4356step5Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4356step4 raw4356step4Labels raw4356step5Labels labelEmbedding9 hl
    _ = mixedMoment B node5312 node5312Labels := by rfl

theorem canonical4372 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4372 raw4372Labels = mixedMoment B node3545 node3545Labels := by
  calc
    mixedMoment B raw4372 raw4372Labels = mixedMoment B raw4372step0 raw4372step0Labels := by
      have hz : ∀ j, raw4372 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4372step0 = (fun i j => raw4372 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4372step0 raw4372; decide +kernel
      have hl : raw4372step0Labels = raw4372Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4372 raw4372Labels permutation434 hz
    mixedMoment B raw4372step0 raw4372step0Labels = mixedMoment B raw4372step1 raw4372step1Labels := by
      have hz : ∀ j, raw4372step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw4372step1 = (fun i j => raw4372step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw4372step1 raw4372step0; decide +kernel
      have hl : raw4372step1Labels = raw4372step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4372step0 raw4372step0Labels permutation56 hz
    mixedMoment B raw4372step1 raw4372step1Labels = mixedMoment B raw4372step2 raw4372step2Labels := by
      have ha : raw4372step2 = (fun i j => raw4372step1 (permutation29 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4372step2 raw4372step1; decide +kernel
      have hl : raw4372step2Labels = raw4372step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4372step1 raw4372step1Labels permutation29 permutation2
    _ = mixedMoment B node3545 node3545Labels := by rfl

theorem canonical4373 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4373 raw4373Labels = mixedMoment B node3545 node3545Labels := by
  calc
    mixedMoment B raw4373 raw4373Labels = mixedMoment B raw4373step0 raw4373step0Labels := by
      have hz : ∀ j, raw4373 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4373step0 = (fun i j => raw4373 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4373step0 raw4373; decide +kernel
      have hl : raw4373step0Labels = raw4373Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4373 raw4373Labels permutation346 hz
    mixedMoment B raw4373step0 raw4373step0Labels = mixedMoment B raw4373step1 raw4373step1Labels := by
      have hz : ∀ j, raw4373step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw4373step1 = (fun i j => raw4373step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw4373step1 raw4373step0; decide +kernel
      have hl : raw4373step1Labels = raw4373step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4373step0 raw4373step0Labels permutation56 hz
    mixedMoment B raw4373step1 raw4373step1Labels = mixedMoment B raw4373step2 raw4373step2Labels := by
      have ha : raw4373step2 = (fun i j => raw4373step1 (permutation29 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4373step2 raw4373step1; decide +kernel
      have hl : raw4373step2Labels = raw4373step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4373step1 raw4373step1Labels permutation29 permutation2
    _ = mixedMoment B node3545 node3545Labels := by rfl

theorem canonical4374 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4374 raw4374Labels = mixedMoment B node3636 node3636Labels := by
  calc
    mixedMoment B raw4374 raw4374Labels = mixedMoment B raw4374step0 raw4374step0Labels := by
      have hz : ∀ j, raw4374 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw4374step0 = (fun i j => raw4374 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw4374step0 raw4374; decide +kernel
      have hl : raw4374step0Labels = raw4374Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4374 raw4374Labels permutation520 hz
    mixedMoment B raw4374step0 raw4374step0Labels = mixedMoment B raw4374step1 raw4374step1Labels := by
      have hz : ∀ j, raw4374step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw4374step1 = (fun i j => raw4374step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw4374step1 raw4374step0; decide +kernel
      have hl : raw4374step1Labels = raw4374step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4374step0 raw4374step0Labels permutation104 hz
    mixedMoment B raw4374step1 raw4374step1Labels = mixedMoment B raw4374step2 raw4374step2Labels := by
      have hz : ∀ j, raw4374step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw4374step2 = (fun i j => raw4374step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw4374step2 raw4374step1; decide +kernel
      have hl : raw4374step2Labels = raw4374step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4374step1 raw4374step1Labels permutation20 hz
    mixedMoment B raw4374step2 raw4374step2Labels = mixedMoment B raw4374step3 raw4374step3Labels := by
      have hz : ∀ j, raw4374step2 (permutation4 0) j = 0 := by decide +kernel
      have ha : raw4374step3 = (fun i j => raw4374step2 (permutation4 i.succ) j) := by apply Matrix.ext; unfold raw4374step3 raw4374step2; decide +kernel
      have hl : raw4374step3Labels = raw4374step2Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4374step2 raw4374step2Labels permutation4 hz
    mixedMoment B raw4374step3 raw4374step3Labels = mixedMoment B raw4374step4 raw4374step4Labels := by
      have ha : raw4374step4 = (fun i j => raw4374step3 (permutation1 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4374step4 raw4374step3; decide +kernel
      have hl : raw4374step4Labels = raw4374step3Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4374step3 raw4374step3Labels permutation1 permutation2
    _ = mixedMoment B node3636 node3636Labels := by rfl

theorem canonical4375 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4375 raw4375Labels = mixedMoment B node2292 node2292Labels := by
  calc
    mixedMoment B raw4375 raw4375Labels = mixedMoment B raw4375step0 raw4375step0Labels := by
      have hz : ∀ j, raw4375 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4375step0 = (fun i j => raw4375 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4375step0 raw4375; decide +kernel
      have hl : raw4375step0Labels = raw4375Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4375 raw4375Labels permutation434 hz
    mixedMoment B raw4375step0 raw4375step0Labels = mixedMoment B raw4375step1 raw4375step1Labels := by
      have hz : ∀ j, raw4375step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4375step1 = (fun i j => raw4375step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4375step1 raw4375step0; decide +kernel
      have hl : raw4375step1Labels = raw4375step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4375step0 raw4375step0Labels permutation80 hz
    mixedMoment B raw4375step1 raw4375step1Labels = mixedMoment B raw4375step2 raw4375step2Labels := by
      have hz : ∀ j, raw4375step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw4375step2 = (fun i j => raw4375step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw4375step2 raw4375step1; decide +kernel
      have hl : raw4375step2Labels = raw4375step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4375step1 raw4375step1Labels permutation14 hz
    mixedMoment B raw4375step2 raw4375step2Labels = mixedMoment B raw4375step3 raw4375step3Labels := by
      have ha : raw4375step3 = (fun i j => raw4375step2 (permutation7 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4375step3 raw4375step2; decide +kernel
      have hl : raw4375step3Labels = raw4375step2Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4375step2 raw4375step2Labels permutation7 permutation2
    _ = mixedMoment B node2292 node2292Labels := by rfl

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

theorem sum_fin_six {R : Type*} [AddCommMonoid R] (f : Fin 6 → R) :
    ∑ i, f i = f 0 + f 1 + f 2 + f 3 + f 4 + f 5 := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change f 0 + (f 1 + (f 2 + (f 3 + (f 4 + f 5)))) = _
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical162
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical24
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical784 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw784 = injectiveMoment H node63 := by
  calc
    injectiveMoment H raw784 = injectiveMoment H raw784step0 := by
      have heq : raw784step0 = raw784.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw784).symm
    injectiveMoment H raw784step0 = injectiveMoment H raw784step1 := by
      have heq : raw784step1 = (fun i j => raw784step0 (permutation7 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw784step0 permutation7 permutation6
    _ = injectiveMoment H node63 := by rfl

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

theorem canonical7683 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7683 = injectiveMoment H node11 := by
  calc
    injectiveMoment H raw7683 = injectiveMoment H raw7683step0 := by
      have heq : raw7683step0 = (fun i j => raw7683 (permutation7 i) (permutation2 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7683 permutation7 permutation2
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

theorem canonical7979 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7979 = injectiveMoment H node0 := by
  calc
    injectiveMoment H raw7979 = injectiveMoment H raw7979step0 := by
      have hz : ∀ j, raw7979 (permutation7 0) j = 0 := by decide +kernel
      have heq : raw7979step0 = (fun i j => raw7979 (permutation7 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7979 permutation7 hz
    injectiveMoment H raw7979step0 = injectiveMoment H raw7979step1 := by
      have hz : ∀ j, raw7979step0 (permutation2 0) j = 0 := by decide +kernel
      have heq : raw7979step1 = (fun i j => raw7979step0 (permutation2 i.succ) j) := by ext i j; fin_cases i; fin_cases j; decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7979step0 permutation2 hz
    injectiveMoment H raw7979step1 = injectiveMoment H raw7979step2 := by
      have hz : ∀ j, raw7979step1 (permutation0 0) j = 0 := by decide +kernel
      have heq : raw7979step2 = (fun i j => raw7979step1 (permutation0 i.succ) j) := by ext i j; fin_cases i
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7979step1 permutation0 hz
    injectiveMoment H raw7979step2 = injectiveMoment H raw7979step3 := by
      have hz : ∀ i, raw7979step2 i (permutation0 0) = 0 := by decide +kernel
      have heq : raw7979step3 = (fun i j => raw7979step2 i (permutation0 j.succ)) := by ext i j; fin_cases i
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw7979step2 permutation0 hz
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

theorem canonical900 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw900 = injectiveMoment H node3 := by
  calc
    injectiveMoment H raw900 = injectiveMoment H raw900step0 := by
      have hz : ∀ j, raw900 (permutation5 0) j = 0 := by decide +kernel
      have heq : raw900step0 = (fun i j => raw900 (permutation5 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw900 permutation5 hz
    _ = injectiveMoment H node3 := by rfl

theorem canonical926 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw926 = injectiveMoment H node3 := by
  rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_SingleGroup24
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singlePair407 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node407 node407Labels = Sparse.eval singlePairValue407 (familyPairVector B) := by
  have hp := single_label_three B hB node407
  have hl : node407Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node407 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node407 (EqualityPatterns.family3.label 0) = PairSemantics.raw7979 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node407 PairSemantics.raw7979; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7979 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node407 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value11 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node407 (EqualityPatterns.family3.label 1) = PairSemantics.raw5199 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node407 PairSemantics.raw5199; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5199 hH).trans (PairSemantics.sound11 hH)
  have hm2 : familyPairMoment B (groupedColumns node407 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value11 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node407 (EqualityPatterns.family3.label 2) = PairSemantics.raw7683 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node407 PairSemantics.raw7683; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7683 hH).trans (PairSemantics.sound11 hH)
  have hm3 : familyPairMoment B (groupedColumns node407 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value3 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node407 (EqualityPatterns.family3.label 3) = PairSemantics.raw900 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node407 PairSemantics.raw900; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical900 hH).trans (PairSemantics.sound3 hH)
  have hm4 : familyPairMoment B (groupedColumns node407 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value63 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node407 (EqualityPatterns.family3.label 4) = PairSemantics.raw784 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node407 PairSemantics.raw784; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical784 hH).trans (PairSemantics.sound63 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue407, PairSemantics.value0, PairSemantics.value3, PairSemantics.value11, PairSemantics.value63, Sparse.eval] at hp ⊢
  linarith only [hp]

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

theorem singleton2770 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node2770 node2770Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node407 node407Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw274 singletonSmall2770
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall2770) = raw274Labels := by decide +kernel
  rw [hl, canonical274 B hB] at h
  have hc0 : mixedMoment B raw274 (Fin.cases (0 : Fin 1) singletonSmall2770) =
      mixedMoment B node407 node407Labels := by
    have ha : raw274 = raw275 := by apply Matrix.ext; unfold raw274 raw275; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall2770 = raw275Labels := by decide +kernel
    rw [ha, hj, canonical275 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
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

theorem singleton4890 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4890 node4890Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2247 node2247Labels + mixedMoment B node2290 node2290Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1821 singletonSmall4890
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4890) = raw1821Labels := by decide +kernel
  rw [hl, canonical1821 B hB] at h
  have hc0 : mixedMoment B raw1821 (Fin.cases (0 : Fin 2) singletonSmall4890) =
      mixedMoment B node2247 node2247Labels := by
    have ha : raw1821 = raw1822 := by apply Matrix.ext; unfold raw1821 raw1822; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4890 = raw1822Labels := by decide +kernel
    rw [ha, hj, canonical1822 B hB]
  have hc1 : mixedMoment B raw1821 (Fin.cases (1 : Fin 2) singletonSmall4890) =
      mixedMoment B node2290 node2290Labels := by
    have ha : raw1821 = raw1823 := by apply Matrix.ext; unfold raw1821 raw1823; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4890 = raw1823Labels := by decide +kernel
    rw [ha, hj, canonical1823 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4899 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4899 node4899Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2281 node2281Labels + mixedMoment B node2294 node2294Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1830 singletonSmall4899
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4899) = raw1830Labels := by decide +kernel
  rw [hl, canonical1830 B hB] at h
  have hc0 : mixedMoment B raw1830 (Fin.cases (0 : Fin 2) singletonSmall4899) =
      mixedMoment B node2281 node2281Labels := by
    have ha : raw1830 = raw1831 := by apply Matrix.ext; unfold raw1830 raw1831; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4899 = raw1831Labels := by decide +kernel
    rw [ha, hj, canonical1831 B hB]
  have hc1 : mixedMoment B raw1830 (Fin.cases (1 : Fin 2) singletonSmall4899) =
      mixedMoment B node2294 node2294Labels := by
    have ha : raw1830 = raw1832 := by apply Matrix.ext; unfold raw1830 raw1832; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4899 = raw1832Labels := by decide +kernel
    rw [ha, hj, canonical1832 B hB]
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

theorem singleton5261 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5261 node5261Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2726 node2726Labels + mixedMoment B node3545 node3545Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2277 singletonSmall5261
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5261) = raw2277Labels := by decide +kernel
  rw [hl, canonical2277 B hB] at h
  have hc0 : mixedMoment B raw2277 (Fin.cases (0 : Fin 2) singletonSmall5261) =
      mixedMoment B node2726 node2726Labels := by
    have ha : raw2277 = raw2278 := by apply Matrix.ext; unfold raw2277 raw2278; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5261 = raw2278Labels := by decide +kernel
    rw [ha, hj, canonical2278 B hB]
  have hc1 : mixedMoment B raw2277 (Fin.cases (1 : Fin 2) singletonSmall5261) =
      mixedMoment B node3545 node3545Labels := by
    have ha : raw2277 = raw2279 := by apply Matrix.ext; unfold raw2277 raw2279; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5261 = raw2279Labels := by decide +kernel
    rw [ha, hj, canonical2279 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton5296 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5296 node5296Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2770 node2770Labels + mixedMoment B node3634 node3634Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2307 singletonSmall5296
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5296) = raw2307Labels := by decide +kernel
  rw [hl, canonical2307 B hB] at h
  have hc0 : mixedMoment B raw2307 (Fin.cases (0 : Fin 2) singletonSmall5296) =
      mixedMoment B node2770 node2770Labels := by
    have ha : raw2307 = raw2308 := by apply Matrix.ext; unfold raw2307 raw2308; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5296 = raw2308Labels := by decide +kernel
    rw [ha, hj, canonical2308 B hB]
  have hc1 : mixedMoment B raw2307 (Fin.cases (1 : Fin 2) singletonSmall5296) =
      mixedMoment B node3634 node3634Labels := by
    have ha : raw2307 = raw2309 := by apply Matrix.ext; unfold raw2307 raw2309; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5296 = raw2309Labels := by decide +kernel
    rw [ha, hj, canonical2309 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
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

theorem sound2281 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2281 node2281Labels = Sparse.eval nodeValue2281 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2281) = mixedMoment B node2281 node2281Labels := rfl
  simpa [nodeValue2281, Sparse.eval] using hc.symm

theorem sound2294 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2294 node2294Labels = Sparse.eval nodeValue2294 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2294) = mixedMoment B node2294 node2294Labels := rfl
  simpa [nodeValue2294, Sparse.eval] using hc.symm

theorem sound4899 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4899 node4899Labels = Sparse.eval nodeValue4899 (mixedVector B) := by
  have h := singleton4899 B _hB
  rw [sound2281 B _hB _hF, sound2294 B _hB _hF] at h
  norm_num [nodeValue4899, nodeValue2281, nodeValue2294, Sparse.eval] at h ⊢
  linarith only [h]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound18
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound1206 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1206 node1206Labels = Sparse.eval nodeValue1206 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1206) = mixedMoment B node1206 node1206Labels := rfl
  simpa [nodeValue1206, Sparse.eval] using hc.symm

theorem sound1209 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1209 node1209Labels = Sparse.eval nodeValue1209 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1209) = mixedMoment B node1209 node1209Labels := rfl
  simpa [nodeValue1209, Sparse.eval] using hc.symm

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

theorem sound1217 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1217 node1217Labels = Sparse.eval nodeValue1217 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1217) = mixedMoment B node1217 node1217Labels := rfl
  simpa [nodeValue1217, Sparse.eval] using hc.symm

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

theorem sound1378 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1378 node1378Labels = Sparse.eval nodeValue1378 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1378) = mixedMoment B node1378 node1378Labels := rfl
  simpa [nodeValue1378, Sparse.eval] using hc.symm

theorem sound1388 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1388 node1388Labels = Sparse.eval nodeValue1388 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1388) = mixedMoment B node1388 node1388Labels := rfl
  simpa [nodeValue1388, Sparse.eval] using hc.symm

theorem sound1394 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1394 node1394Labels = Sparse.eval nodeValue1394 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1394) = mixedMoment B node1394 node1394Labels := rfl
  simpa [nodeValue1394, Sparse.eval] using hc.symm

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

theorem sound2050 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2050 node2050Labels = Sparse.eval nodeValue2050 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2050) = mixedMoment B node2050 node2050Labels := rfl
  simpa [nodeValue2050, Sparse.eval] using hc.symm

theorem sound2052 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2052 node2052Labels = Sparse.eval nodeValue2052 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2052) = mixedMoment B node2052 node2052Labels := rfl
  simpa [nodeValue2052, Sparse.eval] using hc.symm

theorem sound2055 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2055 node2055Labels = Sparse.eval nodeValue2055 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2055) = mixedMoment B node2055 node2055Labels := rfl
  simpa [nodeValue2055, Sparse.eval] using hc.symm

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

theorem sound2247 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2247 node2247Labels = Sparse.eval nodeValue2247 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2247) = mixedMoment B node2247 node2247Labels := rfl
  simpa [nodeValue2247, Sparse.eval] using hc.symm

theorem sound2290 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2290 node2290Labels = Sparse.eval nodeValue2290 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2290) = mixedMoment B node2290 node2290Labels := rfl
  simpa [nodeValue2290, Sparse.eval] using hc.symm

theorem sound2292 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2292 node2292Labels = Sparse.eval nodeValue2292 (mixedVector B) := by
  simpa only [nodeValue2292, Sparse.eval_nil] using zero2292 B _hB _hF

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

theorem sound2470 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2470 node2470Labels = Sparse.eval nodeValue2470 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2470) = mixedMoment B node2470 node2470Labels := rfl
  simpa [nodeValue2470, Sparse.eval] using hc.symm

theorem sound2485 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2485 node2485Labels = Sparse.eval nodeValue2485 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2485) = mixedMoment B node2485 node2485Labels := rfl
  simpa [nodeValue2485, Sparse.eval] using hc.symm

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

theorem sound2543 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2543 node2543Labels = Sparse.eval nodeValue2543 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2543) = mixedMoment B node2543 node2543Labels := rfl
  simpa [nodeValue2543, Sparse.eval] using hc.symm

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

theorem sound2562 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2562 node2562Labels = Sparse.eval nodeValue2562 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2562) = mixedMoment B node2562 node2562Labels := rfl
  simpa [nodeValue2562, Sparse.eval] using hc.symm

theorem sound2610 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2610 node2610Labels = Sparse.eval nodeValue2610 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2610) = mixedMoment B node2610 node2610Labels := rfl
  simpa [nodeValue2610, Sparse.eval] using hc.symm

theorem sound2618 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2618 node2618Labels = Sparse.eval nodeValue2618 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2618) = mixedMoment B node2618 node2618Labels := rfl
  simpa [nodeValue2618, Sparse.eval] using hc.symm

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

theorem sound2624 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2624 node2624Labels = Sparse.eval nodeValue2624 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2624) = mixedMoment B node2624 node2624Labels := rfl
  simpa [nodeValue2624, Sparse.eval] using hc.symm

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

theorem zero2709 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node2709 node2709Labels = 0 := by
  exact mixedMoment_alpha B hF node2709 node2709Labels 1 permutation200
    (by decide +kernel)

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

theorem sound2709 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2709 node2709Labels = Sparse.eval nodeValue2709 (mixedVector B) := by
  simpa only [nodeValue2709, Sparse.eval_nil] using zero2709 B _hB _hF

theorem sound2712 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2712 node2712Labels = Sparse.eval nodeValue2712 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2712) = mixedMoment B node2712 node2712Labels := rfl
  simpa [nodeValue2712, Sparse.eval] using hc.symm

theorem sound2723 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2723 node2723Labels = Sparse.eval nodeValue2723 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2723) = mixedMoment B node2723 node2723Labels := rfl
  simpa [nodeValue2723, Sparse.eval] using hc.symm

theorem sound2726 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2726 node2726Labels = Sparse.eval nodeValue2726 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2726) = mixedMoment B node2726 node2726Labels := rfl
  simpa [nodeValue2726, Sparse.eval] using hc.symm

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

theorem sound407 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node407 node407Labels = Sparse.eval nodeValue407 (mixedVector B) := by
  calc
    _ = Sparse.eval singlePairValue407 (familyPairVector B) := singlePair407 B _hB
    _ = _ := by norm_num [singlePairValue407, nodeValue407, Sparse.eval, mixedVector]

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

theorem sound2770 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2770 node2770Labels = Sparse.eval nodeValue2770 (mixedVector B) := by
  have h := singleton2770 B _hB
  rw [sound407 B _hB _hF] at h
  norm_num [nodeValue2770, nodeValue407, Sparse.eval] at h ⊢
  linarith only [h]

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

theorem sound3064 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3064 node3064Labels = Sparse.eval nodeValue3064 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3064) = mixedMoment B node3064 node3064Labels := rfl
  simpa [nodeValue3064, Sparse.eval] using hc.symm

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

theorem sound3077 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3077 node3077Labels = Sparse.eval nodeValue3077 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3077) = mixedMoment B node3077 node3077Labels := rfl
  simpa [nodeValue3077, Sparse.eval] using hc.symm

theorem sound3086 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3086 node3086Labels = Sparse.eval nodeValue3086 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3086) = mixedMoment B node3086 node3086Labels := rfl
  simpa [nodeValue3086, Sparse.eval] using hc.symm

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

theorem sound3387 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3387 node3387Labels = Sparse.eval nodeValue3387 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3387) = mixedMoment B node3387 node3387Labels := rfl
  simpa [nodeValue3387, Sparse.eval] using hc.symm

theorem sound3389 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3389 node3389Labels = Sparse.eval nodeValue3389 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3389) = mixedMoment B node3389 node3389Labels := rfl
  simpa [nodeValue3389, Sparse.eval] using hc.symm

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

theorem sound3393 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3393 node3393Labels = Sparse.eval nodeValue3393 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3393) = mixedMoment B node3393 node3393Labels := rfl
  simpa [nodeValue3393, Sparse.eval] using hc.symm

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

theorem zero3492 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node3492 node3492Labels = 0 := by
  exact mixedMoment_alpha B hF node3492 node3492Labels 1 permutation437
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

theorem sound3492 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3492 node3492Labels = Sparse.eval nodeValue3492 (mixedVector B) := by
  simpa only [nodeValue3492, Sparse.eval_nil] using zero3492 B _hB _hF

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

theorem sound3543 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3543 node3543Labels = Sparse.eval nodeValue3543 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3543) = mixedMoment B node3543 node3543Labels := rfl
  simpa [nodeValue3543, Sparse.eval] using hc.symm

theorem sound3545 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3545 node3545Labels = Sparse.eval nodeValue3545 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3545) = mixedMoment B node3545 node3545Labels := rfl
  simpa [nodeValue3545, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros56
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero3636 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3636 node3636Labels = 0 := by
  exact mixedMoment_order_one B hB node3636 node3636Labels 1
    (by decide +kernel) (by decide +kernel)

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

theorem sound3634 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3634 node3634Labels = Sparse.eval nodeValue3634 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3634) = mixedMoment B node3634 node3634Labels := rfl
  simpa [nodeValue3634, Sparse.eval] using hc.symm

theorem sound3636 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3636 node3636Labels = Sparse.eval nodeValue3636 (mixedVector B) := by
  simpa only [nodeValue3636, Sparse.eval_nil] using zero3636 B _hB _hF

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

theorem sound4085 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4085 node4085Labels = Sparse.eval nodeValue4085 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4085) = mixedMoment B node4085 node4085Labels := rfl
  simpa [nodeValue4085, Sparse.eval] using hc.symm

theorem sound4091 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4091 node4091Labels = Sparse.eval nodeValue4091 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4091) = mixedMoment B node4091 node4091Labels := rfl
  simpa [nodeValue4091, Sparse.eval] using hc.symm

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

theorem sound4890 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4890 node4890Labels = Sparse.eval nodeValue4890 (mixedVector B) := by
  have h := singleton4890 B _hB
  rw [sound2247 B _hB _hF, sound2290 B _hB _hF] at h
  norm_num [nodeValue4890, nodeValue2247, nodeValue2290, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4897 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4897 node4897Labels = Sparse.eval nodeValue4897 (mixedVector B) := by
  simpa only [nodeValue4897, Sparse.eval_nil] using zero4897 B _hB _hF

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

theorem sound5252 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5252 node5252Labels = Sparse.eval nodeValue5252 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5252) = mixedMoment B node5252 node5252Labels := rfl
  simpa [nodeValue5252, Sparse.eval] using hc.symm

theorem sound5261 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5261 node5261Labels = Sparse.eval nodeValue5261 (mixedVector B) := by
  have h := singleton5261 B _hB
  rw [sound2726 B _hB _hF, sound3545 B _hB _hF] at h
  norm_num [nodeValue5261, nodeValue2726, nodeValue3545, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5268 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5268 node5268Labels = Sparse.eval nodeValue5268 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5268) = mixedMoment B node5268 node5268Labels := rfl
  simpa [nodeValue5268, Sparse.eval] using hc.symm

theorem sound5296 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5296 node5296Labels = Sparse.eval nodeValue5296 (mixedVector B) := by
  have h := singleton5296 B _hB
  rw [sound2770 B _hB _hF, sound3634 B _hB _hF] at h
  norm_num [nodeValue5296, nodeValue2770, nodeValue3634, Sparse.eval] at h ⊢
  linarith only [h]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros83
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero5312 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5312 node5312Labels = 0 := by
  exact mixedMoment_order_one B hB node5312 node5312Labels 1
    (by decide +kernel) (by decide +kernel)

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

theorem sound5312 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5312 node5312Labels = Sparse.eval nodeValue5312 (mixedVector B) := by
  simpa only [nodeValue5312, Sparse.eval_nil] using zero5312 B _hB _hF

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources3
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sourceEq98 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm98 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA98 + difference 0 1) (sourceB98 + difference 1 0) sourceC98) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3077) := by
    have ha : (tripleCharges (sourceA98 + difference 0 1) (sourceB98 + difference 1 0) sourceC98) = raw4201 := by
      apply Matrix.ext; unfold tripleCharges sourceA98 sourceB98 sourceC98 difference raw4201; decide +kernel
    rw [ha]
    exact (canonical4201 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA98 + difference 1 1) (sourceB98 + difference 1 1) sourceC98) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2712) := by
    have ha : (tripleCharges (sourceA98 + difference 1 1) (sourceB98 + difference 1 1) sourceC98) = raw4200 := by
      apply Matrix.ext; unfold tripleCharges sourceA98 sourceB98 sourceC98 difference raw4200; decide +kernel
    rw [ha]
    exact (canonical4200 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA98 + difference 2 1) (sourceB98 + difference 1 2) sourceC98) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2470) := by
    have ha : (tripleCharges (sourceA98 + difference 2 1) (sourceB98 + difference 1 2) sourceC98) = raw4216 := by
      apply Matrix.ext; unfold tripleCharges sourceA98 sourceB98 sourceC98 difference raw4216; decide +kernel
    rw [ha]
    exact (canonical4216 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA98 + difference 3 1) (sourceB98 + difference 1 3) sourceC98) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2485) := by
    have ha : (tripleCharges (sourceA98 + difference 3 1) (sourceB98 + difference 1 3) sourceC98) = raw4217 := by
      apply Matrix.ext; unfold tripleCharges sourceA98 sourceB98 sourceC98 difference raw4217; decide +kernel
    rw [ha]
    exact (canonical4217 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA98 + difference 4 1) (sourceB98 + difference 1 4) sourceC98) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2485) := by
    have ha : (tripleCharges (sourceA98 + difference 4 1) (sourceB98 + difference 1 4) sourceC98) = raw4218 := by
      apply Matrix.ext; unfold tripleCharges sourceA98 sourceB98 sourceC98 difference raw4218; decide +kernel
    rw [ha]
    exact (canonical4218 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA98 + difference 5 1) (sourceB98 + difference 1 5) sourceC98) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1388) := by
    have ha : (tripleCharges (sourceA98 + difference 5 1) (sourceB98 + difference 1 5) sourceC98) = raw4219 := by
      apply Matrix.ext; unfold tripleCharges sourceA98 sourceB98 sourceC98 difference raw4219; decide +kernel
    rw [ha]
    exact (canonical4219 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA98 + sourceB98) sourceC98) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA98 + sourceB98) sourceC98) = raw4206 := by
      apply Matrix.ext; unfold doubleCharges sourceA98 sourceB98 sourceC98 raw4206; decide +kernel
    rw [ha]
    exact (canonical4206 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA98 sourceB98 sourceC98
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm98, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq99 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm99 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA99 + difference 2 0) (sourceB99 + difference 0 2) sourceC99) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1206) := by
    have ha : (tripleCharges (sourceA99 + difference 2 0) (sourceB99 + difference 0 2) sourceC99) = raw4208 := by
      apply Matrix.ext; unfold tripleCharges sourceA99 sourceB99 sourceC99 difference raw4208; decide +kernel
    rw [ha]
    exact (canonical4208 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA99 + difference 2 1) (sourceB99 + difference 1 2) sourceC99) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2470) := by
    have ha : (tripleCharges (sourceA99 + difference 2 1) (sourceB99 + difference 1 2) sourceC99) = raw4216 := by
      apply Matrix.ext; unfold tripleCharges sourceA99 sourceB99 sourceC99 difference raw4216; decide +kernel
    rw [ha]
    exact (canonical4216 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA99 + difference 2 2) (sourceB99 + difference 2 2) sourceC99) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2712) := by
    have ha : (tripleCharges (sourceA99 + difference 2 2) (sourceB99 + difference 2 2) sourceC99) = raw4200 := by
      apply Matrix.ext; unfold tripleCharges sourceA99 sourceB99 sourceC99 difference raw4200; decide +kernel
    rw [ha]
    exact (canonical4200 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA99 + difference 2 3) (sourceB99 + difference 3 2) sourceC99) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2610) := by
    have ha : (tripleCharges (sourceA99 + difference 2 3) (sourceB99 + difference 3 2) sourceC99) = raw4220 := by
      apply Matrix.ext; unfold tripleCharges sourceA99 sourceB99 sourceC99 difference raw4220; decide +kernel
    rw [ha]
    exact (canonical4220 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA99 + difference 2 4) (sourceB99 + difference 4 2) sourceC99) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2610) := by
    have ha : (tripleCharges (sourceA99 + difference 2 4) (sourceB99 + difference 4 2) sourceC99) = raw4221 := by
      apply Matrix.ext; unfold tripleCharges sourceA99 sourceB99 sourceC99 difference raw4221; decide +kernel
    rw [ha]
    exact (canonical4221 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA99 + difference 2 5) (sourceB99 + difference 5 2) sourceC99) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2709) := by
    have ha : (tripleCharges (sourceA99 + difference 2 5) (sourceB99 + difference 5 2) sourceC99) = raw4222 := by
      apply Matrix.ext; unfold tripleCharges sourceA99 sourceB99 sourceC99 difference raw4222; decide +kernel
    rw [ha]
    exact (canonical4222 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA99 + sourceB99) sourceC99) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA99 + sourceB99) sourceC99) = raw4206 := by
      apply Matrix.ext; unfold doubleCharges sourceA99 sourceB99 sourceC99 raw4206; decide +kernel
    rw [ha]
    exact (canonical4206 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA99 sourceB99 sourceC99
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm99, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq100 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm100 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA100 + difference 0 2) (sourceB100 + difference 2 0) sourceC100) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3064) := by
    have ha : (tripleCharges (sourceA100 + difference 0 2) (sourceB100 + difference 2 0) sourceC100) = raw4202 := by
      apply Matrix.ext; unfold tripleCharges sourceA100 sourceB100 sourceC100 difference raw4202; decide +kernel
    rw [ha]
    exact (canonical4202 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA100 + difference 1 2) (sourceB100 + difference 2 1) sourceC100) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2562) := by
    have ha : (tripleCharges (sourceA100 + difference 1 2) (sourceB100 + difference 2 1) sourceC100) = raw4212 := by
      apply Matrix.ext; unfold tripleCharges sourceA100 sourceB100 sourceC100 difference raw4212; decide +kernel
    rw [ha]
    exact (canonical4212 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA100 + difference 2 2) (sourceB100 + difference 2 2) sourceC100) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2712) := by
    have ha : (tripleCharges (sourceA100 + difference 2 2) (sourceB100 + difference 2 2) sourceC100) = raw4200 := by
      apply Matrix.ext; unfold tripleCharges sourceA100 sourceB100 sourceC100 difference raw4200; decide +kernel
    rw [ha]
    exact (canonical4200 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA100 + difference 3 2) (sourceB100 + difference 2 3) sourceC100) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2543) := by
    have ha : (tripleCharges (sourceA100 + difference 3 2) (sourceB100 + difference 2 3) sourceC100) = raw4223 := by
      apply Matrix.ext; unfold tripleCharges sourceA100 sourceB100 sourceC100 difference raw4223; decide +kernel
    rw [ha]
    exact (canonical4223 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA100 + difference 4 2) (sourceB100 + difference 2 4) sourceC100) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2543) := by
    have ha : (tripleCharges (sourceA100 + difference 4 2) (sourceB100 + difference 2 4) sourceC100) = raw4224 := by
      apply Matrix.ext; unfold tripleCharges sourceA100 sourceB100 sourceC100 difference raw4224; decide +kernel
    rw [ha]
    exact (canonical4224 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA100 + difference 5 2) (sourceB100 + difference 2 5) sourceC100) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1378) := by
    have ha : (tripleCharges (sourceA100 + difference 5 2) (sourceB100 + difference 2 5) sourceC100) = raw4225 := by
      apply Matrix.ext; unfold tripleCharges sourceA100 sourceB100 sourceC100 difference raw4225; decide +kernel
    rw [ha]
    exact (canonical4225 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA100 + sourceB100) sourceC100) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA100 + sourceB100) sourceC100) = raw4206 := by
      apply Matrix.ext; unfold doubleCharges sourceA100 sourceB100 sourceC100 raw4206; decide +kernel
    rw [ha]
    exact (canonical4206 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA100 sourceB100 sourceC100
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm100, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq101 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm101 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA101 + difference 3 0) (sourceB101 + difference 0 3) sourceC101) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1217) := by
    have ha : (tripleCharges (sourceA101 + difference 3 0) (sourceB101 + difference 0 3) sourceC101) = raw4209 := by
      apply Matrix.ext; unfold tripleCharges sourceA101 sourceB101 sourceC101 difference raw4209; decide +kernel
    rw [ha]
    exact (canonical4209 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA101 + difference 3 1) (sourceB101 + difference 1 3) sourceC101) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2485) := by
    have ha : (tripleCharges (sourceA101 + difference 3 1) (sourceB101 + difference 1 3) sourceC101) = raw4217 := by
      apply Matrix.ext; unfold tripleCharges sourceA101 sourceB101 sourceC101 difference raw4217; decide +kernel
    rw [ha]
    exact (canonical4217 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA101 + difference 3 2) (sourceB101 + difference 2 3) sourceC101) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2543) := by
    have ha : (tripleCharges (sourceA101 + difference 3 2) (sourceB101 + difference 2 3) sourceC101) = raw4223 := by
      apply Matrix.ext; unfold tripleCharges sourceA101 sourceB101 sourceC101 difference raw4223; decide +kernel
    rw [ha]
    exact (canonical4223 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA101 + difference 3 3) (sourceB101 + difference 3 3) sourceC101) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2712) := by
    have ha : (tripleCharges (sourceA101 + difference 3 3) (sourceB101 + difference 3 3) sourceC101) = raw4200 := by
      apply Matrix.ext; unfold tripleCharges sourceA101 sourceB101 sourceC101 difference raw4200; decide +kernel
    rw [ha]
    exact (canonical4200 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA101 + difference 3 4) (sourceB101 + difference 4 3) sourceC101) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2618) := by
    have ha : (tripleCharges (sourceA101 + difference 3 4) (sourceB101 + difference 4 3) sourceC101) = raw4226 := by
      apply Matrix.ext; unfold tripleCharges sourceA101 sourceB101 sourceC101 difference raw4226; decide +kernel
    rw [ha]
    exact (canonical4226 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA101 + difference 3 5) (sourceB101 + difference 5 3) sourceC101) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2723) := by
    have ha : (tripleCharges (sourceA101 + difference 3 5) (sourceB101 + difference 5 3) sourceC101) = raw4227 := by
      apply Matrix.ext; unfold tripleCharges sourceA101 sourceB101 sourceC101 difference raw4227; decide +kernel
    rw [ha]
    exact (canonical4227 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA101 + sourceB101) sourceC101) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA101 + sourceB101) sourceC101) = raw4206 := by
      apply Matrix.ext; unfold doubleCharges sourceA101 sourceB101 sourceC101 raw4206; decide +kernel
    rw [ha]
    exact (canonical4206 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA101 sourceB101 sourceC101
    (0 : Fin 2) 1 (3 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm101, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq102 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm102 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA102 + difference 0 3) (sourceB102 + difference 3 0) sourceC102) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3086) := by
    have ha : (tripleCharges (sourceA102 + difference 0 3) (sourceB102 + difference 3 0) sourceC102) = raw4203 := by
      apply Matrix.ext; unfold tripleCharges sourceA102 sourceB102 sourceC102 difference raw4203; decide +kernel
    rw [ha]
    exact (canonical4203 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA102 + difference 1 3) (sourceB102 + difference 3 1) sourceC102) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2624) := by
    have ha : (tripleCharges (sourceA102 + difference 1 3) (sourceB102 + difference 3 1) sourceC102) = raw4213 := by
      apply Matrix.ext; unfold tripleCharges sourceA102 sourceB102 sourceC102 difference raw4213; decide +kernel
    rw [ha]
    exact (canonical4213 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA102 + difference 2 3) (sourceB102 + difference 3 2) sourceC102) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2610) := by
    have ha : (tripleCharges (sourceA102 + difference 2 3) (sourceB102 + difference 3 2) sourceC102) = raw4220 := by
      apply Matrix.ext; unfold tripleCharges sourceA102 sourceB102 sourceC102 difference raw4220; decide +kernel
    rw [ha]
    exact (canonical4220 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA102 + difference 3 3) (sourceB102 + difference 3 3) sourceC102) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2712) := by
    have ha : (tripleCharges (sourceA102 + difference 3 3) (sourceB102 + difference 3 3) sourceC102) = raw4200 := by
      apply Matrix.ext; unfold tripleCharges sourceA102 sourceB102 sourceC102 difference raw4200; decide +kernel
    rw [ha]
    exact (canonical4200 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA102 + difference 4 3) (sourceB102 + difference 3 4) sourceC102) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2618) := by
    have ha : (tripleCharges (sourceA102 + difference 4 3) (sourceB102 + difference 3 4) sourceC102) = raw4228 := by
      apply Matrix.ext; unfold tripleCharges sourceA102 sourceB102 sourceC102 difference raw4228; decide +kernel
    rw [ha]
    exact (canonical4228 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA102 + difference 5 3) (sourceB102 + difference 3 5) sourceC102) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1394) := by
    have ha : (tripleCharges (sourceA102 + difference 5 3) (sourceB102 + difference 3 5) sourceC102) = raw4229 := by
      apply Matrix.ext; unfold tripleCharges sourceA102 sourceB102 sourceC102 difference raw4229; decide +kernel
    rw [ha]
    exact (canonical4229 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA102 + sourceB102) sourceC102) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA102 + sourceB102) sourceC102) = raw4206 := by
      apply Matrix.ext; unfold doubleCharges sourceA102 sourceB102 sourceC102 raw4206; decide +kernel
    rw [ha]
    exact (canonical4206 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA102 sourceB102 sourceC102
    (0 : Fin 2) 1 (3 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm102, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq103 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm103 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA103 + difference 5 0) (sourceB103 + difference 0 5) sourceC103) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1209) := by
    have ha : (tripleCharges (sourceA103 + difference 5 0) (sourceB103 + difference 0 5) sourceC103) = raw4211 := by
      apply Matrix.ext; unfold tripleCharges sourceA103 sourceB103 sourceC103 difference raw4211; decide +kernel
    rw [ha]
    exact (canonical4211 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA103 + difference 5 1) (sourceB103 + difference 1 5) sourceC103) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1388) := by
    have ha : (tripleCharges (sourceA103 + difference 5 1) (sourceB103 + difference 1 5) sourceC103) = raw4219 := by
      apply Matrix.ext; unfold tripleCharges sourceA103 sourceB103 sourceC103 difference raw4219; decide +kernel
    rw [ha]
    exact (canonical4219 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA103 + difference 5 2) (sourceB103 + difference 2 5) sourceC103) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1378) := by
    have ha : (tripleCharges (sourceA103 + difference 5 2) (sourceB103 + difference 2 5) sourceC103) = raw4225 := by
      apply Matrix.ext; unfold tripleCharges sourceA103 sourceB103 sourceC103 difference raw4225; decide +kernel
    rw [ha]
    exact (canonical4225 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA103 + difference 5 3) (sourceB103 + difference 3 5) sourceC103) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1394) := by
    have ha : (tripleCharges (sourceA103 + difference 5 3) (sourceB103 + difference 3 5) sourceC103) = raw4229 := by
      apply Matrix.ext; unfold tripleCharges sourceA103 sourceB103 sourceC103 difference raw4229; decide +kernel
    rw [ha]
    exact (canonical4229 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA103 + difference 5 4) (sourceB103 + difference 4 5) sourceC103) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1394) := by
    have ha : (tripleCharges (sourceA103 + difference 5 4) (sourceB103 + difference 4 5) sourceC103) = raw4230 := by
      apply Matrix.ext; unfold tripleCharges sourceA103 sourceB103 sourceC103 difference raw4230; decide +kernel
    rw [ha]
    exact (canonical4230 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA103 + difference 5 5) (sourceB103 + difference 5 5) sourceC103) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2712) := by
    have ha : (tripleCharges (sourceA103 + difference 5 5) (sourceB103 + difference 5 5) sourceC103) = raw4200 := by
      apply Matrix.ext; unfold tripleCharges sourceA103 sourceB103 sourceC103 difference raw4200; decide +kernel
    rw [ha]
    exact (canonical4200 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA103 + sourceB103) sourceC103) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA103 + sourceB103) sourceC103) = raw4206 := by
      apply Matrix.ext; unfold doubleCharges sourceA103 sourceB103 sourceC103 raw4206; decide +kernel
    rw [ha]
    exact (canonical4206 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA103 sourceB103 sourceC103
    (0 : Fin 2) 1 (5 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm103, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq106 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm106 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA106 + difference 0 0) (sourceB106 + difference 0 0) sourceC106) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3543) := by
    have ha : (tripleCharges (sourceA106 + difference 0 0) (sourceB106 + difference 0 0) sourceC106) = raw4267 := by
      apply Matrix.ext; unfold tripleCharges sourceA106 sourceB106 sourceC106 difference raw4267; decide +kernel
    rw [ha]
    exact (canonical4267 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA106 + difference 0 1) (sourceB106 + difference 1 0) sourceC106) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3389) := by
    have ha : (tripleCharges (sourceA106 + difference 0 1) (sourceB106 + difference 1 0) sourceC106) = raw4268 := by
      apply Matrix.ext; unfold tripleCharges sourceA106 sourceB106 sourceC106 difference raw4268; decide +kernel
    rw [ha]
    exact (canonical4268 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA106 + difference 0 2) (sourceB106 + difference 2 0) sourceC106) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3492) := by
    have ha : (tripleCharges (sourceA106 + difference 0 2) (sourceB106 + difference 2 0) sourceC106) = raw4269 := by
      apply Matrix.ext; unfold tripleCharges sourceA106 sourceB106 sourceC106 difference raw4269; decide +kernel
    rw [ha]
    exact (canonical4269 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA106 + difference 0 3) (sourceB106 + difference 3 0) sourceC106) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3545) := by
    have ha : (tripleCharges (sourceA106 + difference 0 3) (sourceB106 + difference 3 0) sourceC106) = raw4089 := by
      apply Matrix.ext; unfold tripleCharges sourceA106 sourceB106 sourceC106 difference raw4089; decide +kernel
    rw [ha]
    exact (canonical4089 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA106 + difference 0 4) (sourceB106 + difference 4 0) sourceC106) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3545) := by
    have ha : (tripleCharges (sourceA106 + difference 0 4) (sourceB106 + difference 4 0) sourceC106) = raw4270 := by
      apply Matrix.ext; unfold tripleCharges sourceA106 sourceB106 sourceC106 difference raw4270; decide +kernel
    rw [ha]
    exact (canonical4270 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA106 + difference 0 5) (sourceB106 + difference 5 0) sourceC106) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2052) := by
    have ha : (tripleCharges (sourceA106 + difference 0 5) (sourceB106 + difference 5 0) sourceC106) = raw4271 := by
      apply Matrix.ext; unfold tripleCharges sourceA106 sourceB106 sourceC106 difference raw4271; decide +kernel
    rw [ha]
    exact (canonical4271 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA106 + sourceB106) sourceC106) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4085) := by
    have ha : (doubleCharges (sourceA106 + sourceB106) sourceC106) = raw3721 := by
      apply Matrix.ext; unfold doubleCharges sourceA106 sourceB106 sourceC106 raw3721; decide +kernel
    rw [ha]
    exact (canonical3721 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA106 sourceB106 sourceC106
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm106, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq107 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm107 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA107 + difference 0 0) (sourceB107 + difference 0 0) sourceC107) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3543) := by
    have ha : (tripleCharges (sourceA107 + difference 0 0) (sourceB107 + difference 0 0) sourceC107) = raw4267 := by
      apply Matrix.ext; unfold tripleCharges sourceA107 sourceB107 sourceC107 difference raw4267; decide +kernel
    rw [ha]
    exact (canonical4267 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA107 + difference 1 0) (sourceB107 + difference 0 1) sourceC107) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2290) := by
    have ha : (tripleCharges (sourceA107 + difference 1 0) (sourceB107 + difference 0 1) sourceC107) = raw4272 := by
      apply Matrix.ext; unfold tripleCharges sourceA107 sourceB107 sourceC107 difference raw4272; decide +kernel
    rw [ha]
    exact (canonical4272 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA107 + difference 2 0) (sourceB107 + difference 0 2) sourceC107) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2050) := by
    have ha : (tripleCharges (sourceA107 + difference 2 0) (sourceB107 + difference 0 2) sourceC107) = raw4273 := by
      apply Matrix.ext; unfold tripleCharges sourceA107 sourceB107 sourceC107 difference raw4273; decide +kernel
    rw [ha]
    exact (canonical4273 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA107 + difference 3 0) (sourceB107 + difference 0 3) sourceC107) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2055) := by
    have ha : (tripleCharges (sourceA107 + difference 3 0) (sourceB107 + difference 0 3) sourceC107) = raw4274 := by
      apply Matrix.ext; unfold tripleCharges sourceA107 sourceB107 sourceC107 difference raw4274; decide +kernel
    rw [ha]
    exact (canonical4274 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA107 + difference 4 0) (sourceB107 + difference 0 4) sourceC107) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2055) := by
    have ha : (tripleCharges (sourceA107 + difference 4 0) (sourceB107 + difference 0 4) sourceC107) = raw3734 := by
      apply Matrix.ext; unfold tripleCharges sourceA107 sourceB107 sourceC107 difference raw3734; decide +kernel
    rw [ha]
    exact (canonical3734 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA107 + difference 5 0) (sourceB107 + difference 0 5) sourceC107) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2052) := by
    have ha : (tripleCharges (sourceA107 + difference 5 0) (sourceB107 + difference 0 5) sourceC107) = raw4275 := by
      apply Matrix.ext; unfold tripleCharges sourceA107 sourceB107 sourceC107 difference raw4275; decide +kernel
    rw [ha]
    exact (canonical4275 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA107 + sourceB107) sourceC107) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4085) := by
    have ha : (doubleCharges (sourceA107 + sourceB107) sourceC107) = raw3721 := by
      apply Matrix.ext; unfold doubleCharges sourceA107 sourceB107 sourceC107 raw3721; decide +kernel
    rw [ha]
    exact (canonical3721 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA107 sourceB107 sourceC107
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm107, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq108 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm108 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA108 + difference 1 0) (sourceB108 + difference 0 1) sourceC108) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2290) := by
    have ha : (tripleCharges (sourceA108 + difference 1 0) (sourceB108 + difference 0 1) sourceC108) = raw4272 := by
      apply Matrix.ext; unfold tripleCharges sourceA108 sourceB108 sourceC108 difference raw4272; decide +kernel
    rw [ha]
    exact (canonical4272 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA108 + difference 1 1) (sourceB108 + difference 1 1) sourceC108) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3543) := by
    have ha : (tripleCharges (sourceA108 + difference 1 1) (sourceB108 + difference 1 1) sourceC108) = raw4267 := by
      apply Matrix.ext; unfold tripleCharges sourceA108 sourceB108 sourceC108 difference raw4267; decide +kernel
    rw [ha]
    exact (canonical4267 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA108 + difference 1 2) (sourceB108 + difference 2 1) sourceC108) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3543) := by
    have ha : (tripleCharges (sourceA108 + difference 1 2) (sourceB108 + difference 2 1) sourceC108) = raw4276 := by
      apply Matrix.ext; unfold tripleCharges sourceA108 sourceB108 sourceC108 difference raw4276; decide +kernel
    rw [ha]
    exact (canonical4276 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA108 + difference 1 3) (sourceB108 + difference 3 1) sourceC108) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3634) := by
    have ha : (tripleCharges (sourceA108 + difference 1 3) (sourceB108 + difference 3 1) sourceC108) = raw4097 := by
      apply Matrix.ext; unfold tripleCharges sourceA108 sourceB108 sourceC108 difference raw4097; decide +kernel
    rw [ha]
    exact (canonical4097 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA108 + difference 1 4) (sourceB108 + difference 4 1) sourceC108) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3634) := by
    have ha : (tripleCharges (sourceA108 + difference 1 4) (sourceB108 + difference 4 1) sourceC108) = raw4277 := by
      apply Matrix.ext; unfold tripleCharges sourceA108 sourceB108 sourceC108 difference raw4277; decide +kernel
    rw [ha]
    exact (canonical4277 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA108 + difference 1 5) (sourceB108 + difference 5 1) sourceC108) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2290) := by
    have ha : (tripleCharges (sourceA108 + difference 1 5) (sourceB108 + difference 5 1) sourceC108) = raw3719 := by
      apply Matrix.ext; unfold tripleCharges sourceA108 sourceB108 sourceC108 difference raw3719; decide +kernel
    rw [ha]
    exact (canonical3719 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA108 + sourceB108) sourceC108) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4085) := by
    have ha : (doubleCharges (sourceA108 + sourceB108) sourceC108) = raw3721 := by
      apply Matrix.ext; unfold doubleCharges sourceA108 sourceB108 sourceC108 raw3721; decide +kernel
    rw [ha]
    exact (canonical3721 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA108 sourceB108 sourceC108
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm108, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq109 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm109 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA109 + difference 0 1) (sourceB109 + difference 1 0) sourceC109) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3389) := by
    have ha : (tripleCharges (sourceA109 + difference 0 1) (sourceB109 + difference 1 0) sourceC109) = raw4268 := by
      apply Matrix.ext; unfold tripleCharges sourceA109 sourceB109 sourceC109 difference raw4268; decide +kernel
    rw [ha]
    exact (canonical4268 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA109 + difference 1 1) (sourceB109 + difference 1 1) sourceC109) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3543) := by
    have ha : (tripleCharges (sourceA109 + difference 1 1) (sourceB109 + difference 1 1) sourceC109) = raw4267 := by
      apply Matrix.ext; unfold tripleCharges sourceA109 sourceB109 sourceC109 difference raw4267; decide +kernel
    rw [ha]
    exact (canonical4267 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA109 + difference 2 1) (sourceB109 + difference 1 2) sourceC109) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3387) := by
    have ha : (tripleCharges (sourceA109 + difference 2 1) (sourceB109 + difference 1 2) sourceC109) = raw4278 := by
      apply Matrix.ext; unfold tripleCharges sourceA109 sourceB109 sourceC109 difference raw4278; decide +kernel
    rw [ha]
    exact (canonical4278 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA109 + difference 3 1) (sourceB109 + difference 1 3) sourceC109) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3393) := by
    have ha : (tripleCharges (sourceA109 + difference 3 1) (sourceB109 + difference 1 3) sourceC109) = raw4279 := by
      apply Matrix.ext; unfold tripleCharges sourceA109 sourceB109 sourceC109 difference raw4279; decide +kernel
    rw [ha]
    exact (canonical4279 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA109 + difference 4 1) (sourceB109 + difference 1 4) sourceC109) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3393) := by
    have ha : (tripleCharges (sourceA109 + difference 4 1) (sourceB109 + difference 1 4) sourceC109) = raw4099 := by
      apply Matrix.ext; unfold tripleCharges sourceA109 sourceB109 sourceC109 difference raw4099; decide +kernel
    rw [ha]
    exact (canonical4099 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA109 + difference 5 1) (sourceB109 + difference 1 5) sourceC109) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3389) := by
    have ha : (tripleCharges (sourceA109 + difference 5 1) (sourceB109 + difference 1 5) sourceC109) = raw4280 := by
      apply Matrix.ext; unfold tripleCharges sourceA109 sourceB109 sourceC109 difference raw4280; decide +kernel
    rw [ha]
    exact (canonical4280 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA109 + sourceB109) sourceC109) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4085) := by
    have ha : (doubleCharges (sourceA109 + sourceB109) sourceC109) = raw3721 := by
      apply Matrix.ext; unfold doubleCharges sourceA109 sourceB109 sourceC109 raw3721; decide +kernel
    rw [ha]
    exact (canonical3721 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA109 sourceB109 sourceC109
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm109, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq110 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm110 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA110 + difference 2 0) (sourceB110 + difference 0 2) sourceC110) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2050) := by
    have ha : (tripleCharges (sourceA110 + difference 2 0) (sourceB110 + difference 0 2) sourceC110) = raw4273 := by
      apply Matrix.ext; unfold tripleCharges sourceA110 sourceB110 sourceC110 difference raw4273; decide +kernel
    rw [ha]
    exact (canonical4273 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA110 + difference 2 1) (sourceB110 + difference 1 2) sourceC110) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3387) := by
    have ha : (tripleCharges (sourceA110 + difference 2 1) (sourceB110 + difference 1 2) sourceC110) = raw4278 := by
      apply Matrix.ext; unfold tripleCharges sourceA110 sourceB110 sourceC110 difference raw4278; decide +kernel
    rw [ha]
    exact (canonical4278 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA110 + difference 2 2) (sourceB110 + difference 2 2) sourceC110) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3543) := by
    have ha : (tripleCharges (sourceA110 + difference 2 2) (sourceB110 + difference 2 2) sourceC110) = raw4267 := by
      apply Matrix.ext; unfold tripleCharges sourceA110 sourceB110 sourceC110 difference raw4267; decide +kernel
    rw [ha]
    exact (canonical4267 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA110 + difference 2 3) (sourceB110 + difference 3 2) sourceC110) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3543) := by
    have ha : (tripleCharges (sourceA110 + difference 2 3) (sourceB110 + difference 3 2) sourceC110) = raw4103 := by
      apply Matrix.ext; unfold tripleCharges sourceA110 sourceB110 sourceC110 difference raw4103; decide +kernel
    rw [ha]
    exact (canonical4103 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA110 + difference 2 4) (sourceB110 + difference 4 2) sourceC110) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3543) := by
    have ha : (tripleCharges (sourceA110 + difference 2 4) (sourceB110 + difference 4 2) sourceC110) = raw4281 := by
      apply Matrix.ext; unfold tripleCharges sourceA110 sourceB110 sourceC110 difference raw4281; decide +kernel
    rw [ha]
    exact (canonical4281 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA110 + difference 2 5) (sourceB110 + difference 5 2) sourceC110) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2050) := by
    have ha : (tripleCharges (sourceA110 + difference 2 5) (sourceB110 + difference 5 2) sourceC110) = raw3901 := by
      apply Matrix.ext; unfold tripleCharges sourceA110 sourceB110 sourceC110 difference raw3901; decide +kernel
    rw [ha]
    exact (canonical3901 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA110 + sourceB110) sourceC110) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4085) := by
    have ha : (doubleCharges (sourceA110 + sourceB110) sourceC110) = raw3721 := by
      apply Matrix.ext; unfold doubleCharges sourceA110 sourceB110 sourceC110 raw3721; decide +kernel
    rw [ha]
    exact (canonical3721 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA110 sourceB110 sourceC110
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm110, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq113 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm113 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA113 + difference 0 1) (sourceB113 + difference 1 0) sourceC113) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5261) := by
    have ha : (tripleCharges (sourceA113 + difference 0 1) (sourceB113 + difference 1 0) sourceC113) = raw4036 := by
      apply Matrix.ext; unfold tripleCharges sourceA113 sourceB113 sourceC113 difference raw4036; decide +kernel
    rw [ha]
    exact (canonical4036 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA113 + difference 0 2) (sourceB113 + difference 2 0) sourceC113) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5261) := by
    have ha : (tripleCharges (sourceA113 + difference 0 2) (sourceB113 + difference 2 0) sourceC113) = raw4342 := by
      apply Matrix.ext; unfold tripleCharges sourceA113 sourceB113 sourceC113 difference raw4342; decide +kernel
    rw [ha]
    exact (canonical4342 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA113 + difference 0 3) (sourceB113 + difference 3 0) sourceC113) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5261) := by
    have ha : (tripleCharges (sourceA113 + difference 0 3) (sourceB113 + difference 3 0) sourceC113) = raw4343 := by
      apply Matrix.ext; unfold tripleCharges sourceA113 sourceB113 sourceC113 difference raw4343; decide +kernel
    rw [ha]
    exact (canonical4343 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA113 + difference 0 4) (sourceB113 + difference 4 0) sourceC113) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5312) := by
    have ha : (tripleCharges (sourceA113 + difference 0 4) (sourceB113 + difference 4 0) sourceC113) = raw4344 := by
      apply Matrix.ext; unfold tripleCharges sourceA113 sourceB113 sourceC113 difference raw4344; decide +kernel
    rw [ha]
    exact (canonical4344 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA113 + difference 0 5) (sourceB113 + difference 5 0) sourceC113) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4897) := by
    have ha : (tripleCharges (sourceA113 + difference 0 5) (sourceB113 + difference 5 0) sourceC113) = raw4345 := by
      apply Matrix.ext; unfold tripleCharges sourceA113 sourceB113 sourceC113 difference raw4345; decide +kernel
    rw [ha]
    exact (canonical4345 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA113 + difference 1 0) (sourceB113 + difference 0 1) sourceC113) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4890) := by
    have ha : (tripleCharges (sourceA113 + difference 1 0) (sourceB113 + difference 0 1) sourceC113) = raw4346 := by
      apply Matrix.ext; unfold tripleCharges sourceA113 sourceB113 sourceC113 difference raw4346; decide +kernel
    rw [ha]
    exact (canonical4346 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA113 + difference 1 2) (sourceB113 + difference 2 1) sourceC113) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5252) := by
    have ha : (tripleCharges (sourceA113 + difference 1 2) (sourceB113 + difference 2 1) sourceC113) = raw4347 := by
      apply Matrix.ext; unfold tripleCharges sourceA113 sourceB113 sourceC113 difference raw4347; decide +kernel
    rw [ha]
    exact (canonical4347 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA113 + difference 1 3) (sourceB113 + difference 3 1) sourceC113) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5252) := by
    have ha : (tripleCharges (sourceA113 + difference 1 3) (sourceB113 + difference 3 1) sourceC113) = raw4348 := by
      apply Matrix.ext; unfold tripleCharges sourceA113 sourceB113 sourceC113 difference raw4348; decide +kernel
    rw [ha]
    exact (canonical4348 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA113 + difference 1 4) (sourceB113 + difference 4 1) sourceC113) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5296) := by
    have ha : (tripleCharges (sourceA113 + difference 1 4) (sourceB113 + difference 4 1) sourceC113) = raw4349 := by
      apply Matrix.ext; unfold tripleCharges sourceA113 sourceB113 sourceC113 difference raw4349; decide +kernel
    rw [ha]
    exact (canonical4349 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA113 + difference 1 5) (sourceB113 + difference 5 1) sourceC113) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4890) := by
    have ha : (tripleCharges (sourceA113 + difference 1 5) (sourceB113 + difference 5 1) sourceC113) = raw4350 := by
      apply Matrix.ext; unfold tripleCharges sourceA113 sourceB113 sourceC113 difference raw4350; decide +kernel
    rw [ha]
    exact (canonical4350 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA113 + difference 2 0) (sourceB113 + difference 0 2) sourceC113) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4890) := by
    have ha : (tripleCharges (sourceA113 + difference 2 0) (sourceB113 + difference 0 2) sourceC113) = raw3876 := by
      apply Matrix.ext; unfold tripleCharges sourceA113 sourceB113 sourceC113 difference raw3876; decide +kernel
    rw [ha]
    exact (canonical3876 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA113 + difference 2 1) (sourceB113 + difference 1 2) sourceC113) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5252) := by
    have ha : (tripleCharges (sourceA113 + difference 2 1) (sourceB113 + difference 1 2) sourceC113) = raw4044 := by
      apply Matrix.ext; unfold tripleCharges sourceA113 sourceB113 sourceC113 difference raw4044; decide +kernel
    rw [ha]
    exact (canonical4044 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA113 + difference 2 3) (sourceB113 + difference 3 2) sourceC113) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5252) := by
    have ha : (tripleCharges (sourceA113 + difference 2 3) (sourceB113 + difference 3 2) sourceC113) = raw4351 := by
      apply Matrix.ext; unfold tripleCharges sourceA113 sourceB113 sourceC113 difference raw4351; decide +kernel
    rw [ha]
    exact (canonical4351 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA113 + difference 2 4) (sourceB113 + difference 4 2) sourceC113) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5296) := by
    have ha : (tripleCharges (sourceA113 + difference 2 4) (sourceB113 + difference 4 2) sourceC113) = raw4352 := by
      apply Matrix.ext; unfold tripleCharges sourceA113 sourceB113 sourceC113 difference raw4352; decide +kernel
    rw [ha]
    exact (canonical4352 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA113 + difference 2 5) (sourceB113 + difference 5 2) sourceC113) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4890) := by
    have ha : (tripleCharges (sourceA113 + difference 2 5) (sourceB113 + difference 5 2) sourceC113) = raw3857 := by
      apply Matrix.ext; unfold tripleCharges sourceA113 sourceB113 sourceC113 difference raw3857; decide +kernel
    rw [ha]
    exact (canonical3857 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA113 + difference 3 0) (sourceB113 + difference 0 3) sourceC113) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4890) := by
    have ha : (tripleCharges (sourceA113 + difference 3 0) (sourceB113 + difference 0 3) sourceC113) = raw3684 := by
      apply Matrix.ext; unfold tripleCharges sourceA113 sourceB113 sourceC113 difference raw3684; decide +kernel
    rw [ha]
    exact (canonical3684 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA113 + difference 3 1) (sourceB113 + difference 1 3) sourceC113) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5252) := by
    have ha : (tripleCharges (sourceA113 + difference 3 1) (sourceB113 + difference 1 3) sourceC113) = raw4048 := by
      apply Matrix.ext; unfold tripleCharges sourceA113 sourceB113 sourceC113 difference raw4048; decide +kernel
    rw [ha]
    exact (canonical4048 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA113 + difference 3 2) (sourceB113 + difference 2 3) sourceC113) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5252) := by
    have ha : (tripleCharges (sourceA113 + difference 3 2) (sourceB113 + difference 2 3) sourceC113) = raw4235 := by
      apply Matrix.ext; unfold tripleCharges sourceA113 sourceB113 sourceC113 difference raw4235; decide +kernel
    rw [ha]
    exact (canonical4235 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA113 + difference 3 4) (sourceB113 + difference 4 3) sourceC113) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5296) := by
    have ha : (tripleCharges (sourceA113 + difference 3 4) (sourceB113 + difference 4 3) sourceC113) = raw4236 := by
      apply Matrix.ext; unfold tripleCharges sourceA113 sourceB113 sourceC113 difference raw4236; decide +kernel
    rw [ha]
    exact (canonical4236 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA113 + difference 3 5) (sourceB113 + difference 5 3) sourceC113) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4890) := by
    have ha : (tripleCharges (sourceA113 + difference 3 5) (sourceB113 + difference 5 3) sourceC113) = raw3658 := by
      apply Matrix.ext; unfold tripleCharges sourceA113 sourceB113 sourceC113 difference raw3658; decide +kernel
    rw [ha]
    exact (canonical3658 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA113 + difference 4 0) (sourceB113 + difference 0 4) sourceC113) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4899) := by
    have ha : (tripleCharges (sourceA113 + difference 4 0) (sourceB113 + difference 0 4) sourceC113) = raw3683 := by
      apply Matrix.ext; unfold tripleCharges sourceA113 sourceB113 sourceC113 difference raw3683; decide +kernel
    rw [ha]
    exact (canonical3683 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA113 + difference 4 1) (sourceB113 + difference 1 4) sourceC113) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5268) := by
    have ha : (tripleCharges (sourceA113 + difference 4 1) (sourceB113 + difference 1 4) sourceC113) = raw4244 := by
      apply Matrix.ext; unfold tripleCharges sourceA113 sourceB113 sourceC113 difference raw4244; decide +kernel
    rw [ha]
    exact (canonical4244 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA113 + difference 4 2) (sourceB113 + difference 2 4) sourceC113) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5268) := by
    have ha : (tripleCharges (sourceA113 + difference 4 2) (sourceB113 + difference 2 4) sourceC113) = raw4038 := by
      apply Matrix.ext; unfold tripleCharges sourceA113 sourceB113 sourceC113 difference raw4038; decide +kernel
    rw [ha]
    exact (canonical4038 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA113 + difference 4 3) (sourceB113 + difference 3 4) sourceC113) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5268) := by
    have ha : (tripleCharges (sourceA113 + difference 4 3) (sourceB113 + difference 3 4) sourceC113) = raw4039 := by
      apply Matrix.ext; unfold tripleCharges sourceA113 sourceB113 sourceC113 difference raw4039; decide +kernel
    rw [ha]
    exact (canonical4039 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA113 + difference 4 5) (sourceB113 + difference 5 4) sourceC113) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4899) := by
    have ha : (tripleCharges (sourceA113 + difference 4 5) (sourceB113 + difference 5 4) sourceC113) = raw3657 := by
      apply Matrix.ext; unfold tripleCharges sourceA113 sourceB113 sourceC113 difference raw3657; decide +kernel
    rw [ha]
    exact (canonical3657 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA113 + difference 5 0) (sourceB113 + difference 0 5) sourceC113) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4897) := by
    have ha : (tripleCharges (sourceA113 + difference 5 0) (sourceB113 + difference 0 5) sourceC113) = raw4353 := by
      apply Matrix.ext; unfold tripleCharges sourceA113 sourceB113 sourceC113 difference raw4353; decide +kernel
    rw [ha]
    exact (canonical4353 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA113 + difference 5 1) (sourceB113 + difference 1 5) sourceC113) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5261) := by
    have ha : (tripleCharges (sourceA113 + difference 5 1) (sourceB113 + difference 1 5) sourceC113) = raw4058 := by
      apply Matrix.ext; unfold tripleCharges sourceA113 sourceB113 sourceC113 difference raw4058; decide +kernel
    rw [ha]
    exact (canonical4058 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA113 + difference 5 2) (sourceB113 + difference 2 5) sourceC113) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5261) := by
    have ha : (tripleCharges (sourceA113 + difference 5 2) (sourceB113 + difference 2 5) sourceC113) = raw4354 := by
      apply Matrix.ext; unfold tripleCharges sourceA113 sourceB113 sourceC113 difference raw4354; decide +kernel
    rw [ha]
    exact (canonical4354 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA113 + difference 5 3) (sourceB113 + difference 3 5) sourceC113) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5261) := by
    have ha : (tripleCharges (sourceA113 + difference 5 3) (sourceB113 + difference 3 5) sourceC113) = raw4355 := by
      apply Matrix.ext; unfold tripleCharges sourceA113 sourceB113 sourceC113 difference raw4355; decide +kernel
    rw [ha]
    exact (canonical4355 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA113 + difference 5 4) (sourceB113 + difference 4 5) sourceC113) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5312) := by
    have ha : (tripleCharges (sourceA113 + difference 5 4) (sourceB113 + difference 4 5) sourceC113) = raw4356 := by
      apply Matrix.ext; unfold tripleCharges sourceA113 sourceB113 sourceC113 difference raw4356; decide +kernel
    rw [ha]
    exact (canonical4356 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA113 sourceB113 sourceC113
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm113, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq115 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm115 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA115 + difference 0 0) (sourceB115 + difference 0 0) sourceC115) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3634) := by
    have ha : (tripleCharges (sourceA115 + difference 0 0) (sourceB115 + difference 0 0) sourceC115) = raw4097 := by
      apply Matrix.ext; unfold tripleCharges sourceA115 sourceB115 sourceC115 difference raw4097; decide +kernel
    rw [ha]
    exact (canonical4097 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA115 + difference 0 1) (sourceB115 + difference 1 0) sourceC115) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3545) := by
    have ha : (tripleCharges (sourceA115 + difference 0 1) (sourceB115 + difference 1 0) sourceC115) = raw4089 := by
      apply Matrix.ext; unfold tripleCharges sourceA115 sourceB115 sourceC115 difference raw4089; decide +kernel
    rw [ha]
    exact (canonical4089 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA115 + difference 0 2) (sourceB115 + difference 2 0) sourceC115) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3545) := by
    have ha : (tripleCharges (sourceA115 + difference 0 2) (sourceB115 + difference 2 0) sourceC115) = raw4372 := by
      apply Matrix.ext; unfold tripleCharges sourceA115 sourceB115 sourceC115 difference raw4372; decide +kernel
    rw [ha]
    exact (canonical4372 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA115 + difference 0 3) (sourceB115 + difference 3 0) sourceC115) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3545) := by
    have ha : (tripleCharges (sourceA115 + difference 0 3) (sourceB115 + difference 3 0) sourceC115) = raw4373 := by
      apply Matrix.ext; unfold tripleCharges sourceA115 sourceB115 sourceC115 difference raw4373; decide +kernel
    rw [ha]
    exact (canonical4373 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA115 + difference 0 4) (sourceB115 + difference 4 0) sourceC115) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3636) := by
    have ha : (tripleCharges (sourceA115 + difference 0 4) (sourceB115 + difference 4 0) sourceC115) = raw4374 := by
      apply Matrix.ext; unfold tripleCharges sourceA115 sourceB115 sourceC115 difference raw4374; decide +kernel
    rw [ha]
    exact (canonical4374 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA115 + difference 0 5) (sourceB115 + difference 5 0) sourceC115) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2292) := by
    have ha : (tripleCharges (sourceA115 + difference 0 5) (sourceB115 + difference 5 0) sourceC115) = raw4375 := by
      apply Matrix.ext; unfold tripleCharges sourceA115 sourceB115 sourceC115 difference raw4375; decide +kernel
    rw [ha]
    exact (canonical4375 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA115 + sourceB115) sourceC115) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4085) := by
    have ha : (doubleCharges (sourceA115 + sourceB115) sourceC115) = raw3721 := by
      apply Matrix.ext; unfold doubleCharges sourceA115 sourceB115 sourceC115 raw3721; decide +kernel
    rw [ha]
    exact (canonical3721 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA115 sourceB115 sourceC115
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm115, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic5
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reindexCheck80 : Integer.Sparse.reindex keyMap MixedData.row80 = numericRow80 := by decide +kernel

theorem numericCheck80 (x : Master → ℝ) : Integer.Sparse.eval numericRow80 x =
    (1 : ℝ) * reducedSource80 x := by
  norm_num [numericRow80, reducedSource80, Integer.Sparse.eval, Sparse.eval, nodeValue1388, nodeValue2470, nodeValue2485, nodeValue2712, nodeValue3077, nodeValue4091]

theorem reindexCheck81 : Integer.Sparse.reindex keyMap MixedData.row81 = numericRow81 := by decide +kernel

theorem numericCheck81 (x : Master → ℝ) : Integer.Sparse.eval numericRow81 x =
    (1 : ℝ) * reducedSource81 x := by
  norm_num [numericRow81, reducedSource81, Integer.Sparse.eval, Sparse.eval, nodeValue1206, nodeValue2470, nodeValue2610, nodeValue2709, nodeValue2712, nodeValue4091]

theorem reindexCheck82 : Integer.Sparse.reindex keyMap MixedData.row82 = numericRow82 := by decide +kernel

theorem numericCheck82 (x : Master → ℝ) : Integer.Sparse.eval numericRow82 x =
    (1 : ℝ) * reducedSource82 x := by
  norm_num [numericRow82, reducedSource82, Integer.Sparse.eval, Sparse.eval, nodeValue1378, nodeValue2543, nodeValue2562, nodeValue2712, nodeValue3064, nodeValue4091]

theorem reindexCheck83 : Integer.Sparse.reindex keyMap MixedData.row83 = numericRow83 := by decide +kernel

theorem numericCheck83 (x : Master → ℝ) : Integer.Sparse.eval numericRow83 x =
    (1 : ℝ) * reducedSource83 x := by
  norm_num [numericRow83, reducedSource83, Integer.Sparse.eval, Sparse.eval, nodeValue1217, nodeValue2485, nodeValue2543, nodeValue2618, nodeValue2712, nodeValue2723, nodeValue4091]

theorem reindexCheck84 : Integer.Sparse.reindex keyMap MixedData.row84 = numericRow84 := by decide +kernel

theorem numericCheck84 (x : Master → ℝ) : Integer.Sparse.eval numericRow84 x =
    (1 : ℝ) * reducedSource84 x := by
  norm_num [numericRow84, reducedSource84, Integer.Sparse.eval, Sparse.eval, nodeValue1394, nodeValue2610, nodeValue2618, nodeValue2624, nodeValue2712, nodeValue3086, nodeValue4091]

theorem reindexCheck85 : Integer.Sparse.reindex keyMap MixedData.row85 = numericRow85 := by decide +kernel

theorem numericCheck85 (x : Master → ℝ) : Integer.Sparse.eval numericRow85 x =
    (1 : ℝ) * reducedSource85 x := by
  norm_num [numericRow85, reducedSource85, Integer.Sparse.eval, Sparse.eval, nodeValue1209, nodeValue1378, nodeValue1388, nodeValue1394, nodeValue2712, nodeValue4091]

theorem reindexCheck86 : Integer.Sparse.reindex keyMap MixedData.row86 = numericRow86 := by decide +kernel

theorem numericCheck86 (x : Master → ℝ) : Integer.Sparse.eval numericRow86 x =
    (1 : ℝ) * reducedSource86 x := by
  norm_num [numericRow86, reducedSource86, Integer.Sparse.eval, Sparse.eval, nodeValue2052, nodeValue3389, nodeValue3492, nodeValue3543, nodeValue3545, nodeValue4085]

theorem reindexCheck87 : Integer.Sparse.reindex keyMap MixedData.row87 = numericRow87 := by decide +kernel

theorem numericCheck87 (x : Master → ℝ) : Integer.Sparse.eval numericRow87 x =
    (1 : ℝ) * reducedSource87 x := by
  norm_num [numericRow87, reducedSource87, Integer.Sparse.eval, Sparse.eval, nodeValue2050, nodeValue2052, nodeValue2055, nodeValue2290, nodeValue3543, nodeValue4085]

theorem reindexCheck88 : Integer.Sparse.reindex keyMap MixedData.row88 = numericRow88 := by decide +kernel

theorem numericCheck88 (x : Master → ℝ) : Integer.Sparse.eval numericRow88 x =
    (1 : ℝ) * reducedSource88 x := by
  norm_num [numericRow88, reducedSource88, Integer.Sparse.eval, Sparse.eval, nodeValue2290, nodeValue3543, nodeValue3634, nodeValue4085]

theorem reindexCheck89 : Integer.Sparse.reindex keyMap MixedData.row89 = numericRow89 := by decide +kernel

theorem numericCheck89 (x : Master → ℝ) : Integer.Sparse.eval numericRow89 x =
    (1 : ℝ) * reducedSource89 x := by
  norm_num [numericRow89, reducedSource89, Integer.Sparse.eval, Sparse.eval, nodeValue3387, nodeValue3389, nodeValue3393, nodeValue3543, nodeValue4085]

theorem reindexCheck90 : Integer.Sparse.reindex keyMap MixedData.row90 = numericRow90 := by decide +kernel

theorem numericCheck90 (x : Master → ℝ) : Integer.Sparse.eval numericRow90 x =
    (1 : ℝ) * reducedSource90 x := by
  norm_num [numericRow90, reducedSource90, Integer.Sparse.eval, Sparse.eval, nodeValue2050, nodeValue3387, nodeValue3543, nodeValue4085]

theorem reindexCheck93 : Integer.Sparse.reindex keyMap MixedData.row93 = numericRow93 := by decide +kernel

theorem numericCheck93 (x : Master → ℝ) : Integer.Sparse.eval numericRow93 x =
    (160 : ℝ) * reducedSource93 x := by
  norm_num [numericRow93, reducedSource93, Integer.Sparse.eval, Sparse.eval, nodeValue4890, nodeValue4897, nodeValue4899, nodeValue5252, nodeValue5261, nodeValue5268, nodeValue5296, nodeValue5312]
  ring

theorem reindexCheck95 : Integer.Sparse.reindex keyMap MixedData.row95 = numericRow95 := by decide +kernel

theorem numericCheck95 (x : Master → ℝ) : Integer.Sparse.eval numericRow95 x =
    (1 : ℝ) * reducedSource95 x := by
  norm_num [numericRow95, reducedSource95, Integer.Sparse.eval, Sparse.eval, nodeValue2292, nodeValue3545, nodeValue3634, nodeValue3636, nodeValue4085]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Rows5
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero80 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource80 (mixedVector B) = 0 := by
  have h1388 : mixedVector B (Sum.inr 1388) = Sparse.eval nodeValue1388 (mixedVector B) := by
    change mixedMoment B node1388 node1388Labels = _
    exact sound1388 B hB hF
  have h2470 : mixedVector B (Sum.inr 2470) = Sparse.eval nodeValue2470 (mixedVector B) := by
    change mixedMoment B node2470 node2470Labels = _
    exact sound2470 B hB hF
  have h2485 : mixedVector B (Sum.inr 2485) = Sparse.eval nodeValue2485 (mixedVector B) := by
    change mixedMoment B node2485 node2485Labels = _
    exact sound2485 B hB hF
  have h2712 : mixedVector B (Sum.inr 2712) = Sparse.eval nodeValue2712 (mixedVector B) := by
    change mixedMoment B node2712 node2712Labels = _
    exact sound2712 B hB hF
  have h3077 : mixedVector B (Sum.inr 3077) = Sparse.eval nodeValue3077 (mixedVector B) := by
    change mixedMoment B node3077 node3077Labels = _
    exact sound3077 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm98, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1388, h2470, h2485, h2712, h3077, h4091, reducedSource80] using sourceEq98 B hB

theorem rowSound80 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row80 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck80, numericCheck80, reducedZero80 B hB hF, mul_zero]

theorem reducedZero81 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource81 (mixedVector B) = 0 := by
  have h1206 : mixedVector B (Sum.inr 1206) = Sparse.eval nodeValue1206 (mixedVector B) := by
    change mixedMoment B node1206 node1206Labels = _
    exact sound1206 B hB hF
  have h2470 : mixedVector B (Sum.inr 2470) = Sparse.eval nodeValue2470 (mixedVector B) := by
    change mixedMoment B node2470 node2470Labels = _
    exact sound2470 B hB hF
  have h2610 : mixedVector B (Sum.inr 2610) = Sparse.eval nodeValue2610 (mixedVector B) := by
    change mixedMoment B node2610 node2610Labels = _
    exact sound2610 B hB hF
  have h2709 : mixedVector B (Sum.inr 2709) = Sparse.eval nodeValue2709 (mixedVector B) := by
    change mixedMoment B node2709 node2709Labels = _
    exact sound2709 B hB hF
  have h2712 : mixedVector B (Sum.inr 2712) = Sparse.eval nodeValue2712 (mixedVector B) := by
    change mixedMoment B node2712 node2712Labels = _
    exact sound2712 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm99, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1206, h2470, h2610, h2709, h2712, h4091, reducedSource81] using sourceEq99 B hB

theorem rowSound81 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row81 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck81, numericCheck81, reducedZero81 B hB hF, mul_zero]

theorem reducedZero82 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource82 (mixedVector B) = 0 := by
  have h1378 : mixedVector B (Sum.inr 1378) = Sparse.eval nodeValue1378 (mixedVector B) := by
    change mixedMoment B node1378 node1378Labels = _
    exact sound1378 B hB hF
  have h2543 : mixedVector B (Sum.inr 2543) = Sparse.eval nodeValue2543 (mixedVector B) := by
    change mixedMoment B node2543 node2543Labels = _
    exact sound2543 B hB hF
  have h2562 : mixedVector B (Sum.inr 2562) = Sparse.eval nodeValue2562 (mixedVector B) := by
    change mixedMoment B node2562 node2562Labels = _
    exact sound2562 B hB hF
  have h2712 : mixedVector B (Sum.inr 2712) = Sparse.eval nodeValue2712 (mixedVector B) := by
    change mixedMoment B node2712 node2712Labels = _
    exact sound2712 B hB hF
  have h3064 : mixedVector B (Sum.inr 3064) = Sparse.eval nodeValue3064 (mixedVector B) := by
    change mixedMoment B node3064 node3064Labels = _
    exact sound3064 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm100, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1378, h2543, h2562, h2712, h3064, h4091, reducedSource82] using sourceEq100 B hB

theorem rowSound82 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row82 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck82, numericCheck82, reducedZero82 B hB hF, mul_zero]

theorem reducedZero83 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource83 (mixedVector B) = 0 := by
  have h1217 : mixedVector B (Sum.inr 1217) = Sparse.eval nodeValue1217 (mixedVector B) := by
    change mixedMoment B node1217 node1217Labels = _
    exact sound1217 B hB hF
  have h2485 : mixedVector B (Sum.inr 2485) = Sparse.eval nodeValue2485 (mixedVector B) := by
    change mixedMoment B node2485 node2485Labels = _
    exact sound2485 B hB hF
  have h2543 : mixedVector B (Sum.inr 2543) = Sparse.eval nodeValue2543 (mixedVector B) := by
    change mixedMoment B node2543 node2543Labels = _
    exact sound2543 B hB hF
  have h2618 : mixedVector B (Sum.inr 2618) = Sparse.eval nodeValue2618 (mixedVector B) := by
    change mixedMoment B node2618 node2618Labels = _
    exact sound2618 B hB hF
  have h2712 : mixedVector B (Sum.inr 2712) = Sparse.eval nodeValue2712 (mixedVector B) := by
    change mixedMoment B node2712 node2712Labels = _
    exact sound2712 B hB hF
  have h2723 : mixedVector B (Sum.inr 2723) = Sparse.eval nodeValue2723 (mixedVector B) := by
    change mixedMoment B node2723 node2723Labels = _
    exact sound2723 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm101, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1217, h2485, h2543, h2618, h2712, h2723, h4091, reducedSource83] using sourceEq101 B hB

theorem rowSound83 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row83 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck83, numericCheck83, reducedZero83 B hB hF, mul_zero]

theorem reducedZero84 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource84 (mixedVector B) = 0 := by
  have h1394 : mixedVector B (Sum.inr 1394) = Sparse.eval nodeValue1394 (mixedVector B) := by
    change mixedMoment B node1394 node1394Labels = _
    exact sound1394 B hB hF
  have h2610 : mixedVector B (Sum.inr 2610) = Sparse.eval nodeValue2610 (mixedVector B) := by
    change mixedMoment B node2610 node2610Labels = _
    exact sound2610 B hB hF
  have h2618 : mixedVector B (Sum.inr 2618) = Sparse.eval nodeValue2618 (mixedVector B) := by
    change mixedMoment B node2618 node2618Labels = _
    exact sound2618 B hB hF
  have h2624 : mixedVector B (Sum.inr 2624) = Sparse.eval nodeValue2624 (mixedVector B) := by
    change mixedMoment B node2624 node2624Labels = _
    exact sound2624 B hB hF
  have h2712 : mixedVector B (Sum.inr 2712) = Sparse.eval nodeValue2712 (mixedVector B) := by
    change mixedMoment B node2712 node2712Labels = _
    exact sound2712 B hB hF
  have h3086 : mixedVector B (Sum.inr 3086) = Sparse.eval nodeValue3086 (mixedVector B) := by
    change mixedMoment B node3086 node3086Labels = _
    exact sound3086 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm102, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1394, h2610, h2618, h2624, h2712, h3086, h4091, reducedSource84] using sourceEq102 B hB

theorem rowSound84 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row84 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck84, numericCheck84, reducedZero84 B hB hF, mul_zero]

theorem reducedZero85 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource85 (mixedVector B) = 0 := by
  have h1209 : mixedVector B (Sum.inr 1209) = Sparse.eval nodeValue1209 (mixedVector B) := by
    change mixedMoment B node1209 node1209Labels = _
    exact sound1209 B hB hF
  have h1378 : mixedVector B (Sum.inr 1378) = Sparse.eval nodeValue1378 (mixedVector B) := by
    change mixedMoment B node1378 node1378Labels = _
    exact sound1378 B hB hF
  have h1388 : mixedVector B (Sum.inr 1388) = Sparse.eval nodeValue1388 (mixedVector B) := by
    change mixedMoment B node1388 node1388Labels = _
    exact sound1388 B hB hF
  have h1394 : mixedVector B (Sum.inr 1394) = Sparse.eval nodeValue1394 (mixedVector B) := by
    change mixedMoment B node1394 node1394Labels = _
    exact sound1394 B hB hF
  have h2712 : mixedVector B (Sum.inr 2712) = Sparse.eval nodeValue2712 (mixedVector B) := by
    change mixedMoment B node2712 node2712Labels = _
    exact sound2712 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm103, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1209, h1378, h1388, h1394, h2712, h4091, reducedSource85] using sourceEq103 B hB

theorem rowSound85 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row85 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck85, numericCheck85, reducedZero85 B hB hF, mul_zero]

theorem reducedZero86 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource86 (mixedVector B) = 0 := by
  have h2052 : mixedVector B (Sum.inr 2052) = Sparse.eval nodeValue2052 (mixedVector B) := by
    change mixedMoment B node2052 node2052Labels = _
    exact sound2052 B hB hF
  have h3389 : mixedVector B (Sum.inr 3389) = Sparse.eval nodeValue3389 (mixedVector B) := by
    change mixedMoment B node3389 node3389Labels = _
    exact sound3389 B hB hF
  have h3492 : mixedVector B (Sum.inr 3492) = Sparse.eval nodeValue3492 (mixedVector B) := by
    change mixedMoment B node3492 node3492Labels = _
    exact sound3492 B hB hF
  have h3543 : mixedVector B (Sum.inr 3543) = Sparse.eval nodeValue3543 (mixedVector B) := by
    change mixedMoment B node3543 node3543Labels = _
    exact sound3543 B hB hF
  have h3545 : mixedVector B (Sum.inr 3545) = Sparse.eval nodeValue3545 (mixedVector B) := by
    change mixedMoment B node3545 node3545Labels = _
    exact sound3545 B hB hF
  have h4085 : mixedVector B (Sum.inr 4085) = Sparse.eval nodeValue4085 (mixedVector B) := by
    change mixedMoment B node4085 node4085Labels = _
    exact sound4085 B hB hF
  simpa only [sourceForm106, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2052, h3389, h3492, h3543, h3545, h4085, reducedSource86] using sourceEq106 B hB

theorem rowSound86 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row86 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck86, numericCheck86, reducedZero86 B hB hF, mul_zero]

theorem reducedZero87 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource87 (mixedVector B) = 0 := by
  have h2050 : mixedVector B (Sum.inr 2050) = Sparse.eval nodeValue2050 (mixedVector B) := by
    change mixedMoment B node2050 node2050Labels = _
    exact sound2050 B hB hF
  have h2052 : mixedVector B (Sum.inr 2052) = Sparse.eval nodeValue2052 (mixedVector B) := by
    change mixedMoment B node2052 node2052Labels = _
    exact sound2052 B hB hF
  have h2055 : mixedVector B (Sum.inr 2055) = Sparse.eval nodeValue2055 (mixedVector B) := by
    change mixedMoment B node2055 node2055Labels = _
    exact sound2055 B hB hF
  have h2290 : mixedVector B (Sum.inr 2290) = Sparse.eval nodeValue2290 (mixedVector B) := by
    change mixedMoment B node2290 node2290Labels = _
    exact sound2290 B hB hF
  have h3543 : mixedVector B (Sum.inr 3543) = Sparse.eval nodeValue3543 (mixedVector B) := by
    change mixedMoment B node3543 node3543Labels = _
    exact sound3543 B hB hF
  have h4085 : mixedVector B (Sum.inr 4085) = Sparse.eval nodeValue4085 (mixedVector B) := by
    change mixedMoment B node4085 node4085Labels = _
    exact sound4085 B hB hF
  simpa only [sourceForm107, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2050, h2052, h2055, h2290, h3543, h4085, reducedSource87] using sourceEq107 B hB

theorem rowSound87 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row87 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck87, numericCheck87, reducedZero87 B hB hF, mul_zero]

theorem reducedZero88 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource88 (mixedVector B) = 0 := by
  have h2290 : mixedVector B (Sum.inr 2290) = Sparse.eval nodeValue2290 (mixedVector B) := by
    change mixedMoment B node2290 node2290Labels = _
    exact sound2290 B hB hF
  have h3543 : mixedVector B (Sum.inr 3543) = Sparse.eval nodeValue3543 (mixedVector B) := by
    change mixedMoment B node3543 node3543Labels = _
    exact sound3543 B hB hF
  have h3634 : mixedVector B (Sum.inr 3634) = Sparse.eval nodeValue3634 (mixedVector B) := by
    change mixedMoment B node3634 node3634Labels = _
    exact sound3634 B hB hF
  have h4085 : mixedVector B (Sum.inr 4085) = Sparse.eval nodeValue4085 (mixedVector B) := by
    change mixedMoment B node4085 node4085Labels = _
    exact sound4085 B hB hF
  simpa only [sourceForm108, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2290, h3543, h3634, h4085, reducedSource88] using sourceEq108 B hB

theorem rowSound88 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row88 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck88, numericCheck88, reducedZero88 B hB hF, mul_zero]

theorem reducedZero89 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource89 (mixedVector B) = 0 := by
  have h3387 : mixedVector B (Sum.inr 3387) = Sparse.eval nodeValue3387 (mixedVector B) := by
    change mixedMoment B node3387 node3387Labels = _
    exact sound3387 B hB hF
  have h3389 : mixedVector B (Sum.inr 3389) = Sparse.eval nodeValue3389 (mixedVector B) := by
    change mixedMoment B node3389 node3389Labels = _
    exact sound3389 B hB hF
  have h3393 : mixedVector B (Sum.inr 3393) = Sparse.eval nodeValue3393 (mixedVector B) := by
    change mixedMoment B node3393 node3393Labels = _
    exact sound3393 B hB hF
  have h3543 : mixedVector B (Sum.inr 3543) = Sparse.eval nodeValue3543 (mixedVector B) := by
    change mixedMoment B node3543 node3543Labels = _
    exact sound3543 B hB hF
  have h4085 : mixedVector B (Sum.inr 4085) = Sparse.eval nodeValue4085 (mixedVector B) := by
    change mixedMoment B node4085 node4085Labels = _
    exact sound4085 B hB hF
  simpa only [sourceForm109, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h3387, h3389, h3393, h3543, h4085, reducedSource89] using sourceEq109 B hB

theorem rowSound89 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row89 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck89, numericCheck89, reducedZero89 B hB hF, mul_zero]

theorem reducedZero90 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource90 (mixedVector B) = 0 := by
  have h2050 : mixedVector B (Sum.inr 2050) = Sparse.eval nodeValue2050 (mixedVector B) := by
    change mixedMoment B node2050 node2050Labels = _
    exact sound2050 B hB hF
  have h3387 : mixedVector B (Sum.inr 3387) = Sparse.eval nodeValue3387 (mixedVector B) := by
    change mixedMoment B node3387 node3387Labels = _
    exact sound3387 B hB hF
  have h3543 : mixedVector B (Sum.inr 3543) = Sparse.eval nodeValue3543 (mixedVector B) := by
    change mixedMoment B node3543 node3543Labels = _
    exact sound3543 B hB hF
  have h4085 : mixedVector B (Sum.inr 4085) = Sparse.eval nodeValue4085 (mixedVector B) := by
    change mixedMoment B node4085 node4085Labels = _
    exact sound4085 B hB hF
  simpa only [sourceForm110, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2050, h3387, h3543, h4085, reducedSource90] using sourceEq110 B hB

theorem rowSound90 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row90 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck90, numericCheck90, reducedZero90 B hB hF, mul_zero]

theorem reducedZero93 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource93 (mixedVector B) = 0 := by
  have h4890 : mixedVector B (Sum.inr 4890) = Sparse.eval nodeValue4890 (mixedVector B) := by
    change mixedMoment B node4890 node4890Labels = _
    exact sound4890 B hB hF
  have h4897 : mixedVector B (Sum.inr 4897) = Sparse.eval nodeValue4897 (mixedVector B) := by
    change mixedMoment B node4897 node4897Labels = _
    exact sound4897 B hB hF
  have h4899 : mixedVector B (Sum.inr 4899) = Sparse.eval nodeValue4899 (mixedVector B) := by
    change mixedMoment B node4899 node4899Labels = _
    exact sound4899 B hB hF
  have h5252 : mixedVector B (Sum.inr 5252) = Sparse.eval nodeValue5252 (mixedVector B) := by
    change mixedMoment B node5252 node5252Labels = _
    exact sound5252 B hB hF
  have h5261 : mixedVector B (Sum.inr 5261) = Sparse.eval nodeValue5261 (mixedVector B) := by
    change mixedMoment B node5261 node5261Labels = _
    exact sound5261 B hB hF
  have h5268 : mixedVector B (Sum.inr 5268) = Sparse.eval nodeValue5268 (mixedVector B) := by
    change mixedMoment B node5268 node5268Labels = _
    exact sound5268 B hB hF
  have h5296 : mixedVector B (Sum.inr 5296) = Sparse.eval nodeValue5296 (mixedVector B) := by
    change mixedMoment B node5296 node5296Labels = _
    exact sound5296 B hB hF
  have h5312 : mixedVector B (Sum.inr 5312) = Sparse.eval nodeValue5312 (mixedVector B) := by
    change mixedMoment B node5312 node5312Labels = _
    exact sound5312 B hB hF
  simpa only [sourceForm113, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4890, h4897, h4899, h5252, h5261, h5268, h5296, h5312, reducedSource93] using sourceEq113 B hB

theorem rowSound93 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row93 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck93, numericCheck93, reducedZero93 B hB hF, mul_zero]

theorem reducedZero95 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource95 (mixedVector B) = 0 := by
  have h2292 : mixedVector B (Sum.inr 2292) = Sparse.eval nodeValue2292 (mixedVector B) := by
    change mixedMoment B node2292 node2292Labels = _
    exact sound2292 B hB hF
  have h3545 : mixedVector B (Sum.inr 3545) = Sparse.eval nodeValue3545 (mixedVector B) := by
    change mixedMoment B node3545 node3545Labels = _
    exact sound3545 B hB hF
  have h3634 : mixedVector B (Sum.inr 3634) = Sparse.eval nodeValue3634 (mixedVector B) := by
    change mixedMoment B node3634 node3634Labels = _
    exact sound3634 B hB hF
  have h3636 : mixedVector B (Sum.inr 3636) = Sparse.eval nodeValue3636 (mixedVector B) := by
    change mixedMoment B node3636 node3636Labels = _
    exact sound3636 B hB hF
  have h4085 : mixedVector B (Sum.inr 4085) = Sparse.eval nodeValue4085 (mixedVector B) := by
    change mixedMoment B node4085 node4085Labels = _
    exact sound4085 B hB hF
  simpa only [sourceForm115, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2292, h3545, h3634, h3636, h4085, reducedSource95] using sourceEq115 B hB

theorem rowSound95 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row95 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck95, numericCheck95, reducedZero95 B hB hF, mul_zero]

theorem sourceRowsAt80 : MixedData.sourceRows (80 : Fin 2425) =
    MixedData.row80 := by decide +kernel

theorem sourceRowsAt81 : MixedData.sourceRows (81 : Fin 2425) =
    MixedData.row81 := by decide +kernel

theorem sourceRowsAt82 : MixedData.sourceRows (82 : Fin 2425) =
    MixedData.row82 := by decide +kernel

theorem sourceRowsAt83 : MixedData.sourceRows (83 : Fin 2425) =
    MixedData.row83 := by decide +kernel

theorem sourceRowsAt84 : MixedData.sourceRows (84 : Fin 2425) =
    MixedData.row84 := by decide +kernel

theorem sourceRowsAt85 : MixedData.sourceRows (85 : Fin 2425) =
    MixedData.row85 := by decide +kernel

theorem sourceRowsAt86 : MixedData.sourceRows (86 : Fin 2425) =
    MixedData.row86 := by decide +kernel

theorem sourceRowsAt87 : MixedData.sourceRows (87 : Fin 2425) =
    MixedData.row87 := by decide +kernel

theorem sourceRowsAt88 : MixedData.sourceRows (88 : Fin 2425) =
    MixedData.row88 := by decide +kernel

theorem sourceRowsAt89 : MixedData.sourceRows (89 : Fin 2425) =
    MixedData.row89 := by decide +kernel

theorem sourceRowsAt90 : MixedData.sourceRows (90 : Fin 2425) =
    MixedData.row90 := by decide +kernel

theorem sourceRowsAt91 : MixedData.sourceRows (91 : Fin 2425) =
    MixedData.row91 := by decide +kernel

theorem sourceRowsAt92 : MixedData.sourceRows (92 : Fin 2425) =
    MixedData.row92 := by decide +kernel

theorem sourceRowsAt93 : MixedData.sourceRows (93 : Fin 2425) =
    MixedData.row93 := by decide +kernel

theorem sourceRowsAt94 : MixedData.sourceRows (94 : Fin 2425) =
    MixedData.row94 := by decide +kernel

theorem sourceRowsAt95 : MixedData.sourceRows (95 : Fin 2425) =
    MixedData.row95 := by decide +kernel

theorem chunkSound5_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) (k : Fin 2425)
    (hk : k.val / 16 = 5) :
    Integer.Sparse.eval (MixedData.sourceRows k) (numericVector B) = 0 := by
  have heq : k.val = 80 ∨ k.val = 81 ∨ k.val = 82 ∨ k.val = 83 ∨ k.val = 84 ∨ k.val = 85 ∨ k.val = 86 ∨ k.val = 87 ∨ k.val = 88 ∨ k.val = 89 ∨ k.val = 90 ∨ k.val = 91 ∨ k.val = 92 ∨ k.val = 93 ∨ k.val = 94 ∨ k.val = 95 := by omega
  rcases heq with h80 | h81 | h82 | h83 | h84 | h85 | h86 | h87 | h88 | h89 | h90 | h91 | h92 | h93 | h94 | h95
  · have he : k = (80 : Fin 2425) := Fin.ext h80
    subst k
    rw [sourceRowsAt80]
    exact rowSound80 B hB hF
  · have he : k = (81 : Fin 2425) := Fin.ext h81
    subst k
    rw [sourceRowsAt81]
    exact rowSound81 B hB hF
  · have he : k = (82 : Fin 2425) := Fin.ext h82
    subst k
    rw [sourceRowsAt82]
    exact rowSound82 B hB hF
  · have he : k = (83 : Fin 2425) := Fin.ext h83
    subst k
    rw [sourceRowsAt83]
    exact rowSound83 B hB hF
  · have he : k = (84 : Fin 2425) := Fin.ext h84
    subst k
    rw [sourceRowsAt84]
    exact rowSound84 B hB hF
  · have he : k = (85 : Fin 2425) := Fin.ext h85
    subst k
    rw [sourceRowsAt85]
    exact rowSound85 B hB hF
  · have he : k = (86 : Fin 2425) := Fin.ext h86
    subst k
    rw [sourceRowsAt86]
    exact rowSound86 B hB hF
  · have he : k = (87 : Fin 2425) := Fin.ext h87
    subst k
    rw [sourceRowsAt87]
    exact rowSound87 B hB hF
  · have he : k = (88 : Fin 2425) := Fin.ext h88
    subst k
    rw [sourceRowsAt88]
    exact rowSound88 B hB hF
  · have he : k = (89 : Fin 2425) := Fin.ext h89
    subst k
    rw [sourceRowsAt89]
    exact rowSound89 B hB hF
  · have he : k = (90 : Fin 2425) := Fin.ext h90
    subst k
    rw [sourceRowsAt90]
    exact rowSound90 B hB hF
  · have he : k = (91 : Fin 2425) := Fin.ext h91
    subst k
    rw [sourceRowsAt91]
    exact rowSound91_e B hB hF
  · have he : k = (92 : Fin 2425) := Fin.ext h92
    subst k
    rw [sourceRowsAt92]
    exact rowSound92_e B hB hF
  · have he : k = (93 : Fin 2425) := Fin.ext h93
    subst k
    rw [sourceRowsAt93]
    exact rowSound93 B hB hF
  · have he : k = (94 : Fin 2425) := Fin.ext h94
    subst k
    rw [sourceRowsAt94]
    exact rowSound94_e B hB hF
  · have he : k = (95 : Fin 2425) := Fin.ext h95
    subst k
    rw [sourceRowsAt95]
    exact rowSound95 B hB hF

end MUB6.Certificate.MixedSourceBridge

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedSourceBridge.chunkSound5_e_oai := @OAI.MUB6.Certificate.MixedSourceBridge.chunkSound5_e_oai
