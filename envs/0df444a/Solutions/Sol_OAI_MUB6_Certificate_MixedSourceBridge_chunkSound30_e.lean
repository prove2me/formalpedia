-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedSourceBridge.chunkSound30_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T04:08:11.821822+00:00
-- url     : https://prove2.me/submissions/e69646c9-c22d-41f5-9389-629ee70bd050

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E077
import Definitions.Def_OAIQ106E086
import Definitions.Def_OAIQ106E115
import Definitions.Def_OAIQ106E118
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
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_reducedZero488_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound481_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound482_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound483_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound484_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound485_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound487_e

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical38
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical4905 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4905 raw4905Labels = mixedMoment B node4092 node4092Labels := by
  calc
    mixedMoment B raw4905 raw4905Labels = mixedMoment B raw4905step0 raw4905step0Labels := by
      have hz : ∀ j, raw4905 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4905step0 = (fun i j => raw4905 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4905step0 raw4905; decide +kernel
      have hl : raw4905step0Labels = raw4905Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4905 raw4905Labels permutation434 hz
    mixedMoment B raw4905step0 raw4905step0Labels = mixedMoment B raw4905step1 raw4905step1Labels := by
      have hz : ∀ j, raw4905step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4905step1 = (fun i j => raw4905step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4905step1 raw4905step0; decide +kernel
      have hl : raw4905step1Labels = raw4905step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4905step0 raw4905step0Labels permutation80 hz
    mixedMoment B raw4905step1 raw4905step1Labels = mixedMoment B raw4905step2 raw4905step2Labels := by
      have ha : raw4905step2 = (fun i j => raw4905step1 (permutation10 i) (permutation0 j)) := by apply Matrix.ext; unfold raw4905step2 raw4905step1; decide +kernel
      have hl : raw4905step2Labels = raw4905step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4905step1 raw4905step1Labels permutation10 permutation0
    _ = mixedMoment B node4092 node4092Labels := by rfl

theorem canonical4921 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4921 raw4921Labels = mixedMoment B node2722 node2722Labels := by
  calc
    mixedMoment B raw4921 raw4921Labels = mixedMoment B raw4921step0 raw4921step0Labels := by
      have hz : ∀ j, raw4921 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4921step0 = (fun i j => raw4921 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4921step0 raw4921; decide +kernel
      have hl : raw4921step0Labels = raw4921Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4921 raw4921Labels permutation434 hz
    mixedMoment B raw4921step0 raw4921step0Labels = mixedMoment B raw4921step1 raw4921step1Labels := by
      have ha : raw4921step1 = (fun i j => raw4921step0 (permutation44 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4921step1 raw4921step0; decide +kernel
      have hl : raw4921step1Labels = raw4921step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4921step0 raw4921step0Labels permutation44 permutation2
    _ = mixedMoment B node2722 node2722Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical4
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical534 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw534 raw534Labels = mixedMoment B node3858 node3858Labels := by
  calc
    mixedMoment B raw534 raw534Labels = mixedMoment B raw534step0 raw534step0Labels := by
      have ha : raw534step0 = (fun i j => raw534 (permutation32 i) (permutation5 j)) := by apply Matrix.ext; unfold raw534step0 raw534; decide +kernel
      have hl : raw534step0Labels = raw534Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw534 raw534Labels permutation32 permutation5
    mixedMoment B raw534step0 raw534step0Labels = mixedMoment B raw534step1 raw534step1Labels := by
      have ha : raw534step1 = raw534step0 := by apply Matrix.ext; unfold raw534step1 raw534step0; decide +kernel
      have hl : raw534step0Labels = labelEmbedding1 ∘ raw534step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw534step0 raw534step0Labels raw534step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3858 node3858Labels := by rfl

theorem canonical535 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw535 raw535Labels = mixedMoment B node494 node494Labels := by
  calc
    mixedMoment B raw535 raw535Labels = mixedMoment B raw535step0 raw535step0Labels := by
      have ha : raw535step0 = (fun i j => raw535 (permutation32 i) (permutation5 j)) := by apply Matrix.ext; unfold raw535step0 raw535; decide +kernel
      have hl : raw535step0Labels = raw535Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw535 raw535Labels permutation32 permutation5
    _ = mixedMoment B node494 node494Labels := by rfl

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

theorem canonical5754 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5754 raw5754Labels = mixedMoment B node4084 node4084Labels := by
  calc
    mixedMoment B raw5754 raw5754Labels = mixedMoment B raw5754step0 raw5754step0Labels := by
      have hz : ∀ j, raw5754 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5754step0 = (fun i j => raw5754 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5754step0 raw5754; decide +kernel
      have hl : raw5754step0Labels = raw5754Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5754 raw5754Labels permutation434 hz
    mixedMoment B raw5754step0 raw5754step0Labels = mixedMoment B raw5754step1 raw5754step1Labels := by
      have hz : ∀ j, raw5754step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5754step1 = (fun i j => raw5754step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5754step1 raw5754step0; decide +kernel
      have hl : raw5754step1Labels = raw5754step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5754step0 raw5754step0Labels permutation80 hz
    mixedMoment B raw5754step1 raw5754step1Labels = mixedMoment B raw5754step2 raw5754step2Labels := by
      have hz : ∀ j, raw5754step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw5754step2 = (fun i j => raw5754step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw5754step2 raw5754step1; decide +kernel
      have hl : raw5754step2Labels = raw5754step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5754step1 raw5754step1Labels permutation14 hz
    mixedMoment B raw5754step2 raw5754step2Labels = mixedMoment B raw5754step3 raw5754step3Labels := by
      have ha : raw5754step3 = -raw5754step2 := by apply Matrix.ext; change ∀ i j, raw5754step3 i j = -(raw5754step2 i j); unfold raw5754step3 raw5754step2; decide +kernel
      have hl : raw5754step3Labels = raw5754step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4084 node4084Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical74
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical9575 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9575 raw9575Labels = mixedMoment B node2765 node2765Labels := by
  calc
    mixedMoment B raw9575 raw9575Labels = mixedMoment B raw9575step0 raw9575step0Labels := by
      have hz : ∀ j, raw9575 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw9575step0 = (fun i j => raw9575 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw9575step0 raw9575; decide +kernel
      have hl : raw9575step0Labels = raw9575Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9575 raw9575Labels permutation434 hz
    mixedMoment B raw9575step0 raw9575step0Labels = mixedMoment B raw9575step1 raw9575step1Labels := by
      have hz : ∀ j, raw9575step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw9575step1 = (fun i j => raw9575step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw9575step1 raw9575step0; decide +kernel
      have hl : raw9575step1Labels = raw9575step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9575step0 raw9575step0Labels permutation80 hz
    _ = mixedMoment B node2765 node2765Labels := by rfl

theorem canonical9581 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9581 raw9581Labels = mixedMoment B node1261 node1261Labels := by
  calc
    mixedMoment B raw9581 raw9581Labels = mixedMoment B raw9581step0 raw9581step0Labels := by
      have hz : ∀ j, raw9581 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw9581step0 = (fun i j => raw9581 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw9581step0 raw9581; decide +kernel
      have hl : raw9581step0Labels = raw9581Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9581 raw9581Labels permutation434 hz
    mixedMoment B raw9581step0 raw9581step0Labels = mixedMoment B raw9581step1 raw9581step1Labels := by
      have ha : raw9581step1 = (fun i j => raw9581step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9581step1 raw9581step0; decide +kernel
      have hl : raw9581step1Labels = raw9581step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9581step0 raw9581step0Labels permutation34 permutation2
    _ = mixedMoment B node1261 node1261Labels := by rfl

theorem canonical9587 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9587 raw9587Labels = mixedMoment B node2632 node2632Labels := by
  calc
    mixedMoment B raw9587 raw9587Labels = mixedMoment B raw9587step0 raw9587step0Labels := by
      have hz : ∀ j, raw9587 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw9587step0 = (fun i j => raw9587 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw9587step0 raw9587; decide +kernel
      have hl : raw9587step0Labels = raw9587Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9587 raw9587Labels permutation434 hz
    mixedMoment B raw9587step0 raw9587step0Labels = mixedMoment B raw9587step1 raw9587step1Labels := by
      have ha : raw9587step1 = (fun i j => raw9587step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9587step1 raw9587step0; decide +kernel
      have hl : raw9587step1Labels = raw9587step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9587step0 raw9587step0Labels permutation34 permutation2
    _ = mixedMoment B node2632 node2632Labels := by rfl

theorem canonical9590 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9590 raw9590Labels = mixedMoment B node2566 node2566Labels := by
  calc
    mixedMoment B raw9590 raw9590Labels = mixedMoment B raw9590step0 raw9590step0Labels := by
      have ha : raw9590step0 = (fun i j => raw9590 (permutation202 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9590step0 raw9590; decide +kernel
      have hl : raw9590step0Labels = raw9590Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9590 raw9590Labels permutation202 permutation2
    _ = mixedMoment B node2566 node2566Labels := by rfl

theorem canonical9591 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9591 raw9591Labels = mixedMoment B node2763 node2763Labels := by
  calc
    mixedMoment B raw9591 raw9591Labels = mixedMoment B raw9591step0 raw9591step0Labels := by
      have hz : ∀ j, raw9591 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw9591step0 = (fun i j => raw9591 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw9591step0 raw9591; decide +kernel
      have hl : raw9591step0Labels = raw9591Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9591 raw9591Labels permutation434 hz
    mixedMoment B raw9591step0 raw9591step0Labels = mixedMoment B raw9591step1 raw9591step1Labels := by
      have ha : raw9591step1 = (fun i j => raw9591step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9591step1 raw9591step0; decide +kernel
      have hl : raw9591step1Labels = raw9591step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9591step0 raw9591step0Labels permutation34 permutation2
    _ = mixedMoment B node2763 node2763Labels := by rfl

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

theorem canonical9724 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9724 raw9724Labels = mixedMoment B node3582 node3582Labels := by
  calc
    mixedMoment B raw9724 raw9724Labels = mixedMoment B raw9724step0 raw9724step0Labels := by
      have hz : ∀ j, raw9724 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw9724step0 = (fun i j => raw9724 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw9724step0 raw9724; decide +kernel
      have hl : raw9724step0Labels = raw9724Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9724 raw9724Labels permutation434 hz
    mixedMoment B raw9724step0 raw9724step0Labels = mixedMoment B raw9724step1 raw9724step1Labels := by
      have hz : ∀ j, raw9724step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw9724step1 = (fun i j => raw9724step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw9724step1 raw9724step0; decide +kernel
      have hl : raw9724step1Labels = raw9724step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9724step0 raw9724step0Labels permutation80 hz
    mixedMoment B raw9724step1 raw9724step1Labels = mixedMoment B raw9724step2 raw9724step2Labels := by
      have ha : raw9724step2 = (fun i j => raw9724step1 (permutation10 i) (permutation4 j)) := by apply Matrix.ext; unfold raw9724step2 raw9724step1; decide +kernel
      have hl : raw9724step2Labels = raw9724step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9724step1 raw9724step1Labels permutation10 permutation4
    mixedMoment B raw9724step2 raw9724step2Labels = mixedMoment B raw9724step3 raw9724step3Labels := by
      have ha : raw9724step3 = -raw9724step2 := by apply Matrix.ext; change ∀ i j, raw9724step3 i j = -(raw9724step2 i j); unfold raw9724step3 raw9724step2; decide +kernel
      have hl : raw9724step3Labels = raw9724step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3582 node3582Labels := by rfl

theorem canonical9725 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9725 raw9725Labels = mixedMoment B node2115 node2115Labels := by
  calc
    mixedMoment B raw9725 raw9725Labels = mixedMoment B raw9725step0 raw9725step0Labels := by
      have hz : ∀ j, raw9725 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw9725step0 = (fun i j => raw9725 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw9725step0 raw9725; decide +kernel
      have hl : raw9725step0Labels = raw9725Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9725 raw9725Labels permutation434 hz
    mixedMoment B raw9725step0 raw9725step0Labels = mixedMoment B raw9725step1 raw9725step1Labels := by
      have hz : ∀ j, raw9725step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw9725step1 = (fun i j => raw9725step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw9725step1 raw9725step0; decide +kernel
      have hl : raw9725step1Labels = raw9725step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9725step0 raw9725step0Labels permutation80 hz
    mixedMoment B raw9725step1 raw9725step1Labels = mixedMoment B raw9725step2 raw9725step2Labels := by
      have ha : raw9725step2 = (fun i j => raw9725step1 (permutation10 i) (permutation4 j)) := by apply Matrix.ext; unfold raw9725step2 raw9725step1; decide +kernel
      have hl : raw9725step2Labels = raw9725step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9725step1 raw9725step1Labels permutation10 permutation4
    mixedMoment B raw9725step2 raw9725step2Labels = mixedMoment B raw9725step3 raw9725step3Labels := by
      have ha : raw9725step3 = -raw9725step2 := by apply Matrix.ext; change ∀ i j, raw9725step3 i j = -(raw9725step2 i j); unfold raw9725step3 raw9725step2; decide +kernel
      have hl : raw9725step3Labels = raw9725step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2115 node2115Labels := by rfl

theorem canonical9726 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9726 raw9726Labels = mixedMoment B node2106 node2106Labels := by
  calc
    mixedMoment B raw9726 raw9726Labels = mixedMoment B raw9726step0 raw9726step0Labels := by
      have hz : ∀ j, raw9726 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw9726step0 = (fun i j => raw9726 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw9726step0 raw9726; decide +kernel
      have hl : raw9726step0Labels = raw9726Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9726 raw9726Labels permutation434 hz
    mixedMoment B raw9726step0 raw9726step0Labels = mixedMoment B raw9726step1 raw9726step1Labels := by
      have ha : raw9726step1 = (fun i j => raw9726step0 (permutation44 i) (permutation4 j)) := by apply Matrix.ext; unfold raw9726step1 raw9726step0; decide +kernel
      have hl : raw9726step1Labels = raw9726step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9726step0 raw9726step0Labels permutation44 permutation4
    mixedMoment B raw9726step1 raw9726step1Labels = mixedMoment B raw9726step2 raw9726step2Labels := by
      have ha : raw9726step2 = -raw9726step1 := by apply Matrix.ext; change ∀ i j, raw9726step2 i j = -(raw9726step1 i j); unfold raw9726step2 raw9726step1; decide +kernel
      have hl : raw9726step2Labels = raw9726step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2106 node2106Labels := by rfl

theorem canonical9727 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9727 raw9727Labels = mixedMoment B node2106 node2106Labels := by
  calc
    mixedMoment B raw9727 raw9727Labels = mixedMoment B raw9727step0 raw9727step0Labels := by
      have hz : ∀ j, raw9727 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw9727step0 = (fun i j => raw9727 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw9727step0 raw9727; decide +kernel
      have hl : raw9727step0Labels = raw9727Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9727 raw9727Labels permutation346 hz
    mixedMoment B raw9727step0 raw9727step0Labels = mixedMoment B raw9727step1 raw9727step1Labels := by
      have ha : raw9727step1 = (fun i j => raw9727step0 (permutation44 i) (permutation4 j)) := by apply Matrix.ext; unfold raw9727step1 raw9727step0; decide +kernel
      have hl : raw9727step1Labels = raw9727step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9727step0 raw9727step0Labels permutation44 permutation4
    mixedMoment B raw9727step1 raw9727step1Labels = mixedMoment B raw9727step2 raw9727step2Labels := by
      have ha : raw9727step2 = -raw9727step1 := by apply Matrix.ext; change ∀ i j, raw9727step2 i j = -(raw9727step1 i j); unfold raw9727step2 raw9727step1; decide +kernel
      have hl : raw9727step2Labels = raw9727step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2106 node2106Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical76
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical9728 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9728 raw9728Labels = mixedMoment B node2264 node2264Labels := by
  calc
    mixedMoment B raw9728 raw9728Labels = mixedMoment B raw9728step0 raw9728step0Labels := by
      have hz : ∀ j, raw9728 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw9728step0 = (fun i j => raw9728 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw9728step0 raw9728; decide +kernel
      have hl : raw9728step0Labels = raw9728Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9728 raw9728Labels permutation434 hz
    mixedMoment B raw9728step0 raw9728step0Labels = mixedMoment B raw9728step1 raw9728step1Labels := by
      have hz : ∀ j, raw9728step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw9728step1 = (fun i j => raw9728step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw9728step1 raw9728step0; decide +kernel
      have hl : raw9728step1Labels = raw9728step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9728step0 raw9728step0Labels permutation80 hz
    mixedMoment B raw9728step1 raw9728step1Labels = mixedMoment B raw9728step2 raw9728step2Labels := by
      have ha : raw9728step2 = (fun i j => raw9728step1 (permutation10 i) (permutation4 j)) := by apply Matrix.ext; unfold raw9728step2 raw9728step1; decide +kernel
      have hl : raw9728step2Labels = raw9728step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9728step1 raw9728step1Labels permutation10 permutation4
    mixedMoment B raw9728step2 raw9728step2Labels = mixedMoment B raw9728step3 raw9728step3Labels := by
      have ha : raw9728step3 = -raw9728step2 := by apply Matrix.ext; change ∀ i j, raw9728step3 i j = -(raw9728step2 i j); unfold raw9728step3 raw9728step2; decide +kernel
      have hl : raw9728step3Labels = raw9728step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2264 node2264Labels := by rfl

theorem canonical9729 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9729 raw9729Labels = mixedMoment B node2109 node2109Labels := by
  calc
    mixedMoment B raw9729 raw9729Labels = mixedMoment B raw9729step0 raw9729step0Labels := by
      have hz : ∀ j, raw9729 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw9729step0 = (fun i j => raw9729 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw9729step0 raw9729; decide +kernel
      have hl : raw9729step0Labels = raw9729Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9729 raw9729Labels permutation434 hz
    mixedMoment B raw9729step0 raw9729step0Labels = mixedMoment B raw9729step1 raw9729step1Labels := by
      have hz : ∀ j, raw9729step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw9729step1 = (fun i j => raw9729step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw9729step1 raw9729step0; decide +kernel
      have hl : raw9729step1Labels = raw9729step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9729step0 raw9729step0Labels permutation80 hz
    mixedMoment B raw9729step1 raw9729step1Labels = mixedMoment B raw9729step2 raw9729step2Labels := by
      have ha : raw9729step2 = (fun i j => raw9729step1 (permutation10 i) (permutation4 j)) := by apply Matrix.ext; unfold raw9729step2 raw9729step1; decide +kernel
      have hl : raw9729step2Labels = raw9729step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9729step1 raw9729step1Labels permutation10 permutation4
    mixedMoment B raw9729step2 raw9729step2Labels = mixedMoment B raw9729step3 raw9729step3Labels := by
      have ha : raw9729step3 = -raw9729step2 := by apply Matrix.ext; change ∀ i j, raw9729step3 i j = -(raw9729step2 i j); unfold raw9729step3 raw9729step2; decide +kernel
      have hl : raw9729step3Labels = raw9729step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2109 node2109Labels := by rfl

theorem canonical9790 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9790 raw9790Labels = mixedMoment B node3857 node3857Labels := by
  calc
    mixedMoment B raw9790 raw9790Labels = mixedMoment B raw9790step0 raw9790step0Labels := by
      have hz : ∀ j, raw9790 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw9790step0 = (fun i j => raw9790 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw9790step0 raw9790; decide +kernel
      have hl : raw9790step0Labels = raw9790Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9790 raw9790Labels permutation346 hz
    mixedMoment B raw9790step0 raw9790step0Labels = mixedMoment B raw9790step1 raw9790step1Labels := by
      have ha : raw9790step1 = (fun i j => raw9790step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw9790step1 raw9790step0; decide +kernel
      have hl : raw9790step1Labels = raw9790step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9790step0 raw9790step0Labels permutation38 permutation7
    mixedMoment B raw9790step1 raw9790step1Labels = mixedMoment B raw9790step2 raw9790step2Labels := by
      have ha : raw9790step2 = -raw9790step1 := by apply Matrix.ext; change ∀ i j, raw9790step2 i j = -(raw9790step1 i j); unfold raw9790step2 raw9790step1; decide +kernel
      have hl : raw9790step2Labels = raw9790step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw9790step2 raw9790step2Labels = mixedMoment B raw9790step3 raw9790step3Labels := by
      have ha : raw9790step3 = raw9790step2 := by apply Matrix.ext; unfold raw9790step3 raw9790step2; decide +kernel
      have hl : raw9790step2Labels = labelEmbedding1 ∘ raw9790step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9790step2 raw9790step2Labels raw9790step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3857 node3857Labels := by rfl

theorem canonical9791 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9791 raw9791Labels = mixedMoment B node3843 node3843Labels := by
  calc
    mixedMoment B raw9791 raw9791Labels = mixedMoment B raw9791step0 raw9791step0Labels := by
      have ha : raw9791step0 = (fun i j => raw9791 (permutation206 i) (permutation7 j)) := by apply Matrix.ext; unfold raw9791step0 raw9791; decide +kernel
      have hl : raw9791step0Labels = raw9791Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9791 raw9791Labels permutation206 permutation7
    mixedMoment B raw9791step0 raw9791step0Labels = mixedMoment B raw9791step1 raw9791step1Labels := by
      have ha : raw9791step1 = -raw9791step0 := by apply Matrix.ext; change ∀ i j, raw9791step1 i j = -(raw9791step0 i j); unfold raw9791step1 raw9791step0; decide +kernel
      have hl : raw9791step1Labels = raw9791step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw9791step1 raw9791step1Labels = mixedMoment B raw9791step2 raw9791step2Labels := by
      have ha : raw9791step2 = raw9791step1 := by apply Matrix.ext; unfold raw9791step2 raw9791step1; decide +kernel
      have hl : raw9791step1Labels = labelEmbedding1 ∘ raw9791step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9791step1 raw9791step1Labels raw9791step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3843 node3843Labels := by rfl

theorem canonical9792 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9792 raw9792Labels = mixedMoment B node3816 node3816Labels := by
  calc
    mixedMoment B raw9792 raw9792Labels = mixedMoment B raw9792step0 raw9792step0Labels := by
      have hz : ∀ j, raw9792 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw9792step0 = (fun i j => raw9792 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw9792step0 raw9792; decide +kernel
      have hl : raw9792step0Labels = raw9792Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9792 raw9792Labels permutation346 hz
    mixedMoment B raw9792step0 raw9792step0Labels = mixedMoment B raw9792step1 raw9792step1Labels := by
      have ha : raw9792step1 = (fun i j => raw9792step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw9792step1 raw9792step0; decide +kernel
      have hl : raw9792step1Labels = raw9792step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9792step0 raw9792step0Labels permutation38 permutation7
    mixedMoment B raw9792step1 raw9792step1Labels = mixedMoment B raw9792step2 raw9792step2Labels := by
      have ha : raw9792step2 = -raw9792step1 := by apply Matrix.ext; change ∀ i j, raw9792step2 i j = -(raw9792step1 i j); unfold raw9792step2 raw9792step1; decide +kernel
      have hl : raw9792step2Labels = raw9792step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw9792step2 raw9792step2Labels = mixedMoment B raw9792step3 raw9792step3Labels := by
      have ha : raw9792step3 = raw9792step2 := by apply Matrix.ext; unfold raw9792step3 raw9792step2; decide +kernel
      have hl : raw9792step2Labels = labelEmbedding1 ∘ raw9792step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9792step2 raw9792step2Labels raw9792step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3816 node3816Labels := by rfl

theorem canonical9793 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9793 raw9793Labels = mixedMoment B node3858 node3858Labels := by
  calc
    mixedMoment B raw9793 raw9793Labels = mixedMoment B raw9793step0 raw9793step0Labels := by
      have hz : ∀ j, raw9793 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw9793step0 = (fun i j => raw9793 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw9793step0 raw9793; decide +kernel
      have hl : raw9793step0Labels = raw9793Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9793 raw9793Labels permutation346 hz
    mixedMoment B raw9793step0 raw9793step0Labels = mixedMoment B raw9793step1 raw9793step1Labels := by
      have ha : raw9793step1 = (fun i j => raw9793step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw9793step1 raw9793step0; decide +kernel
      have hl : raw9793step1Labels = raw9793step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9793step0 raw9793step0Labels permutation38 permutation7
    mixedMoment B raw9793step1 raw9793step1Labels = mixedMoment B raw9793step2 raw9793step2Labels := by
      have ha : raw9793step2 = -raw9793step1 := by apply Matrix.ext; change ∀ i j, raw9793step2 i j = -(raw9793step1 i j); unfold raw9793step2 raw9793step1; decide +kernel
      have hl : raw9793step2Labels = raw9793step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw9793step2 raw9793step2Labels = mixedMoment B raw9793step3 raw9793step3Labels := by
      have ha : raw9793step3 = raw9793step2 := by apply Matrix.ext; unfold raw9793step3 raw9793step2; decide +kernel
      have hl : raw9793step2Labels = labelEmbedding1 ∘ raw9793step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9793step2 raw9793step2Labels raw9793step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3858 node3858Labels := by rfl

theorem canonical9794 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9794 raw9794Labels = mixedMoment B node3859 node3859Labels := by
  calc
    mixedMoment B raw9794 raw9794Labels = mixedMoment B raw9794step0 raw9794step0Labels := by
      have hz : ∀ j, raw9794 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw9794step0 = (fun i j => raw9794 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw9794step0 raw9794; decide +kernel
      have hl : raw9794step0Labels = raw9794Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9794 raw9794Labels permutation346 hz
    mixedMoment B raw9794step0 raw9794step0Labels = mixedMoment B raw9794step1 raw9794step1Labels := by
      have ha : raw9794step1 = (fun i j => raw9794step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw9794step1 raw9794step0; decide +kernel
      have hl : raw9794step1Labels = raw9794step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9794step0 raw9794step0Labels permutation38 permutation7
    mixedMoment B raw9794step1 raw9794step1Labels = mixedMoment B raw9794step2 raw9794step2Labels := by
      have ha : raw9794step2 = -raw9794step1 := by apply Matrix.ext; change ∀ i j, raw9794step2 i j = -(raw9794step1 i j); unfold raw9794step2 raw9794step1; decide +kernel
      have hl : raw9794step2Labels = raw9794step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw9794step2 raw9794step2Labels = mixedMoment B raw9794step3 raw9794step3Labels := by
      have ha : raw9794step3 = raw9794step2 := by apply Matrix.ext; unfold raw9794step3 raw9794step2; decide +kernel
      have hl : raw9794step2Labels = labelEmbedding1 ∘ raw9794step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9794step2 raw9794step2Labels raw9794step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3859 node3859Labels := by rfl

theorem canonical9795 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9795 raw9795Labels = mixedMoment B node3299 node3299Labels := by
  calc
    mixedMoment B raw9795 raw9795Labels = mixedMoment B raw9795step0 raw9795step0Labels := by
      have hz : ∀ j, raw9795 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw9795step0 = (fun i j => raw9795 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw9795step0 raw9795; decide +kernel
      have hl : raw9795step0Labels = raw9795Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9795 raw9795Labels permutation346 hz
    mixedMoment B raw9795step0 raw9795step0Labels = mixedMoment B raw9795step1 raw9795step1Labels := by
      have ha : raw9795step1 = (fun i j => raw9795step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw9795step1 raw9795step0; decide +kernel
      have hl : raw9795step1Labels = raw9795step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9795step0 raw9795step0Labels permutation38 permutation7
    mixedMoment B raw9795step1 raw9795step1Labels = mixedMoment B raw9795step2 raw9795step2Labels := by
      have ha : raw9795step2 = -raw9795step1 := by apply Matrix.ext; change ∀ i j, raw9795step2 i j = -(raw9795step1 i j); unfold raw9795step2 raw9795step1; decide +kernel
      have hl : raw9795step2Labels = raw9795step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw9795step2 raw9795step2Labels = mixedMoment B raw9795step3 raw9795step3Labels := by
      have ha : raw9795step3 = raw9795step2 := by apply Matrix.ext; unfold raw9795step3 raw9795step2; decide +kernel
      have hl : raw9795step2Labels = labelEmbedding1 ∘ raw9795step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9795step2 raw9795step2Labels raw9795step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3299 node3299Labels := by rfl

theorem canonical9796 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9796 raw9796Labels = mixedMoment B node3521 node3521Labels := by
  calc
    mixedMoment B raw9796 raw9796Labels = mixedMoment B raw9796step0 raw9796step0Labels := by
      have ha : raw9796step0 = (fun i j => raw9796 (permutation206 i) (permutation7 j)) := by apply Matrix.ext; unfold raw9796step0 raw9796; decide +kernel
      have hl : raw9796step0Labels = raw9796Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9796 raw9796Labels permutation206 permutation7
    mixedMoment B raw9796step0 raw9796step0Labels = mixedMoment B raw9796step1 raw9796step1Labels := by
      have ha : raw9796step1 = -raw9796step0 := by apply Matrix.ext; change ∀ i j, raw9796step1 i j = -(raw9796step0 i j); unfold raw9796step1 raw9796step0; decide +kernel
      have hl : raw9796step1Labels = raw9796step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw9796step1 raw9796step1Labels = mixedMoment B raw9796step2 raw9796step2Labels := by
      have ha : raw9796step2 = raw9796step1 := by apply Matrix.ext; unfold raw9796step2 raw9796step1; decide +kernel
      have hl : raw9796step1Labels = labelEmbedding1 ∘ raw9796step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9796step1 raw9796step1Labels raw9796step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3521 node3521Labels := by rfl

theorem canonical9797 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9797 raw9797Labels = mixedMoment B node3483 node3483Labels := by
  calc
    mixedMoment B raw9797 raw9797Labels = mixedMoment B raw9797step0 raw9797step0Labels := by
      have hz : ∀ j, raw9797 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw9797step0 = (fun i j => raw9797 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw9797step0 raw9797; decide +kernel
      have hl : raw9797step0Labels = raw9797Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9797 raw9797Labels permutation346 hz
    mixedMoment B raw9797step0 raw9797step0Labels = mixedMoment B raw9797step1 raw9797step1Labels := by
      have ha : raw9797step1 = (fun i j => raw9797step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw9797step1 raw9797step0; decide +kernel
      have hl : raw9797step1Labels = raw9797step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9797step0 raw9797step0Labels permutation38 permutation7
    mixedMoment B raw9797step1 raw9797step1Labels = mixedMoment B raw9797step2 raw9797step2Labels := by
      have ha : raw9797step2 = -raw9797step1 := by apply Matrix.ext; change ∀ i j, raw9797step2 i j = -(raw9797step1 i j); unfold raw9797step2 raw9797step1; decide +kernel
      have hl : raw9797step2Labels = raw9797step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw9797step2 raw9797step2Labels = mixedMoment B raw9797step3 raw9797step3Labels := by
      have ha : raw9797step3 = raw9797step2 := by apply Matrix.ext; unfold raw9797step3 raw9797step2; decide +kernel
      have hl : raw9797step2Labels = labelEmbedding1 ∘ raw9797step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9797step2 raw9797step2Labels raw9797step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3483 node3483Labels := by rfl

theorem canonical9798 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9798 raw9798Labels = mixedMoment B node3544 node3544Labels := by
  calc
    mixedMoment B raw9798 raw9798Labels = mixedMoment B raw9798step0 raw9798step0Labels := by
      have hz : ∀ j, raw9798 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw9798step0 = (fun i j => raw9798 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw9798step0 raw9798; decide +kernel
      have hl : raw9798step0Labels = raw9798Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9798 raw9798Labels permutation346 hz
    mixedMoment B raw9798step0 raw9798step0Labels = mixedMoment B raw9798step1 raw9798step1Labels := by
      have ha : raw9798step1 = (fun i j => raw9798step0 (permutation40 i) (permutation7 j)) := by apply Matrix.ext; unfold raw9798step1 raw9798step0; decide +kernel
      have hl : raw9798step1Labels = raw9798step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9798step0 raw9798step0Labels permutation40 permutation7
    mixedMoment B raw9798step1 raw9798step1Labels = mixedMoment B raw9798step2 raw9798step2Labels := by
      have ha : raw9798step2 = -raw9798step1 := by apply Matrix.ext; change ∀ i j, raw9798step2 i j = -(raw9798step1 i j); unfold raw9798step2 raw9798step1; decide +kernel
      have hl : raw9798step2Labels = raw9798step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw9798step2 raw9798step2Labels = mixedMoment B raw9798step3 raw9798step3Labels := by
      have ha : raw9798step3 = raw9798step2 := by apply Matrix.ext; unfold raw9798step3 raw9798step2; decide +kernel
      have hl : raw9798step2Labels = labelEmbedding1 ∘ raw9798step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9798step2 raw9798step2Labels raw9798step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3544 node3544Labels := by rfl

theorem canonical9799 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9799 raw9799Labels = mixedMoment B node3546 node3546Labels := by
  calc
    mixedMoment B raw9799 raw9799Labels = mixedMoment B raw9799step0 raw9799step0Labels := by
      have hz : ∀ j, raw9799 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw9799step0 = (fun i j => raw9799 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw9799step0 raw9799; decide +kernel
      have hl : raw9799step0Labels = raw9799Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9799 raw9799Labels permutation346 hz
    mixedMoment B raw9799step0 raw9799step0Labels = mixedMoment B raw9799step1 raw9799step1Labels := by
      have ha : raw9799step1 = (fun i j => raw9799step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw9799step1 raw9799step0; decide +kernel
      have hl : raw9799step1Labels = raw9799step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9799step0 raw9799step0Labels permutation38 permutation7
    mixedMoment B raw9799step1 raw9799step1Labels = mixedMoment B raw9799step2 raw9799step2Labels := by
      have ha : raw9799step2 = -raw9799step1 := by apply Matrix.ext; change ∀ i j, raw9799step2 i j = -(raw9799step1 i j); unfold raw9799step2 raw9799step1; decide +kernel
      have hl : raw9799step2Labels = raw9799step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw9799step2 raw9799step2Labels = mixedMoment B raw9799step3 raw9799step3Labels := by
      have ha : raw9799step3 = raw9799step2 := by apply Matrix.ext; unfold raw9799step3 raw9799step2; decide +kernel
      have hl : raw9799step2Labels = labelEmbedding1 ∘ raw9799step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9799step2 raw9799step2Labels raw9799step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3546 node3546Labels := by rfl

theorem canonical9800 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9800 raw9800Labels = mixedMoment B node3290 node3290Labels := by
  calc
    mixedMoment B raw9800 raw9800Labels = mixedMoment B raw9800step0 raw9800step0Labels := by
      have ha : raw9800step0 = (fun i j => raw9800 (permutation166 i) (permutation5 j)) := by apply Matrix.ext; unfold raw9800step0 raw9800; decide +kernel
      have hl : raw9800step0Labels = raw9800Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9800 raw9800Labels permutation166 permutation5
    mixedMoment B raw9800step0 raw9800step0Labels = mixedMoment B raw9800step1 raw9800step1Labels := by
      have ha : raw9800step1 = -raw9800step0 := by apply Matrix.ext; change ∀ i j, raw9800step1 i j = -(raw9800step0 i j); unfold raw9800step1 raw9800step0; decide +kernel
      have hl : raw9800step1Labels = raw9800step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw9800step1 raw9800step1Labels = mixedMoment B raw9800step2 raw9800step2Labels := by
      have ha : raw9800step2 = raw9800step1 := by apply Matrix.ext; unfold raw9800step2 raw9800step1; decide +kernel
      have hl : raw9800step1Labels = labelEmbedding1 ∘ raw9800step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9800step1 raw9800step1Labels raw9800step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3290 node3290Labels := by rfl

theorem canonical9801 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9801 raw9801Labels = mixedMoment B node3529 node3529Labels := by
  calc
    mixedMoment B raw9801 raw9801Labels = mixedMoment B raw9801step0 raw9801step0Labels := by
      have ha : raw9801step0 = (fun i j => raw9801 (permutation206 i) (permutation7 j)) := by apply Matrix.ext; unfold raw9801step0 raw9801; decide +kernel
      have hl : raw9801step0Labels = raw9801Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9801 raw9801Labels permutation206 permutation7
    mixedMoment B raw9801step0 raw9801step0Labels = mixedMoment B raw9801step1 raw9801step1Labels := by
      have ha : raw9801step1 = -raw9801step0 := by apply Matrix.ext; change ∀ i j, raw9801step1 i j = -(raw9801step0 i j); unfold raw9801step1 raw9801step0; decide +kernel
      have hl : raw9801step1Labels = raw9801step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw9801step1 raw9801step1Labels = mixedMoment B raw9801step2 raw9801step2Labels := by
      have ha : raw9801step2 = raw9801step1 := by apply Matrix.ext; unfold raw9801step2 raw9801step1; decide +kernel
      have hl : raw9801step1Labels = labelEmbedding1 ∘ raw9801step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9801step1 raw9801step1Labels raw9801step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3529 node3529Labels := by rfl

theorem canonical9802 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9802 raw9802Labels = mixedMoment B node3467 node3467Labels := by
  calc
    mixedMoment B raw9802 raw9802Labels = mixedMoment B raw9802step0 raw9802step0Labels := by
      have ha : raw9802step0 = (fun i j => raw9802 (permutation206 i) (permutation7 j)) := by apply Matrix.ext; unfold raw9802step0 raw9802; decide +kernel
      have hl : raw9802step0Labels = raw9802Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9802 raw9802Labels permutation206 permutation7
    mixedMoment B raw9802step0 raw9802step0Labels = mixedMoment B raw9802step1 raw9802step1Labels := by
      have ha : raw9802step1 = -raw9802step0 := by apply Matrix.ext; change ∀ i j, raw9802step1 i j = -(raw9802step0 i j); unfold raw9802step1 raw9802step0; decide +kernel
      have hl : raw9802step1Labels = raw9802step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw9802step1 raw9802step1Labels = mixedMoment B raw9802step2 raw9802step2Labels := by
      have ha : raw9802step2 = raw9802step1 := by apply Matrix.ext; unfold raw9802step2 raw9802step1; decide +kernel
      have hl : raw9802step1Labels = labelEmbedding1 ∘ raw9802step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9802step1 raw9802step1Labels raw9802step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3467 node3467Labels := by rfl

theorem canonical9803 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9803 raw9803Labels = mixedMoment B node3531 node3531Labels := by
  calc
    mixedMoment B raw9803 raw9803Labels = mixedMoment B raw9803step0 raw9803step0Labels := by
      have ha : raw9803step0 = (fun i j => raw9803 (permutation206 i) (permutation7 j)) := by apply Matrix.ext; unfold raw9803step0 raw9803; decide +kernel
      have hl : raw9803step0Labels = raw9803Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9803 raw9803Labels permutation206 permutation7
    mixedMoment B raw9803step0 raw9803step0Labels = mixedMoment B raw9803step1 raw9803step1Labels := by
      have ha : raw9803step1 = -raw9803step0 := by apply Matrix.ext; change ∀ i j, raw9803step1 i j = -(raw9803step0 i j); unfold raw9803step1 raw9803step0; decide +kernel
      have hl : raw9803step1Labels = raw9803step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw9803step1 raw9803step1Labels = mixedMoment B raw9803step2 raw9803step2Labels := by
      have ha : raw9803step2 = raw9803step1 := by apply Matrix.ext; unfold raw9803step2 raw9803step1; decide +kernel
      have hl : raw9803step1Labels = labelEmbedding1 ∘ raw9803step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9803step1 raw9803step1Labels raw9803step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3531 node3531Labels := by rfl

theorem canonical9804 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9804 raw9804Labels = mixedMoment B node3532 node3532Labels := by
  calc
    mixedMoment B raw9804 raw9804Labels = mixedMoment B raw9804step0 raw9804step0Labels := by
      have ha : raw9804step0 = (fun i j => raw9804 (permutation206 i) (permutation7 j)) := by apply Matrix.ext; unfold raw9804step0 raw9804; decide +kernel
      have hl : raw9804step0Labels = raw9804Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9804 raw9804Labels permutation206 permutation7
    mixedMoment B raw9804step0 raw9804step0Labels = mixedMoment B raw9804step1 raw9804step1Labels := by
      have ha : raw9804step1 = -raw9804step0 := by apply Matrix.ext; change ∀ i j, raw9804step1 i j = -(raw9804step0 i j); unfold raw9804step1 raw9804step0; decide +kernel
      have hl : raw9804step1Labels = raw9804step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw9804step1 raw9804step1Labels = mixedMoment B raw9804step2 raw9804step2Labels := by
      have ha : raw9804step2 = raw9804step1 := by apply Matrix.ext; unfold raw9804step2 raw9804step1; decide +kernel
      have hl : raw9804step1Labels = labelEmbedding1 ∘ raw9804step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9804step1 raw9804step1Labels raw9804step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3532 node3532Labels := by rfl

theorem canonical9805 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9805 raw9805Labels = mixedMoment B node3294 node3294Labels := by
  calc
    mixedMoment B raw9805 raw9805Labels = mixedMoment B raw9805step0 raw9805step0Labels := by
      have hz : ∀ j, raw9805 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw9805step0 = (fun i j => raw9805 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw9805step0 raw9805; decide +kernel
      have hl : raw9805step0Labels = raw9805Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9805 raw9805Labels permutation346 hz
    mixedMoment B raw9805step0 raw9805step0Labels = mixedMoment B raw9805step1 raw9805step1Labels := by
      have ha : raw9805step1 = (fun i j => raw9805step0 (permutation35 i) (permutation5 j)) := by apply Matrix.ext; unfold raw9805step1 raw9805step0; decide +kernel
      have hl : raw9805step1Labels = raw9805step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9805step0 raw9805step0Labels permutation35 permutation5
    mixedMoment B raw9805step1 raw9805step1Labels = mixedMoment B raw9805step2 raw9805step2Labels := by
      have ha : raw9805step2 = -raw9805step1 := by apply Matrix.ext; change ∀ i j, raw9805step2 i j = -(raw9805step1 i j); unfold raw9805step2 raw9805step1; decide +kernel
      have hl : raw9805step2Labels = raw9805step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw9805step2 raw9805step2Labels = mixedMoment B raw9805step3 raw9805step3Labels := by
      have ha : raw9805step3 = raw9805step2 := by apply Matrix.ext; unfold raw9805step3 raw9805step2; decide +kernel
      have hl : raw9805step2Labels = labelEmbedding1 ∘ raw9805step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9805step2 raw9805step2Labels raw9805step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3294 node3294Labels := by rfl

theorem canonical9806 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9806 raw9806Labels = mixedMoment B node3578 node3578Labels := by
  calc
    mixedMoment B raw9806 raw9806Labels = mixedMoment B raw9806step0 raw9806step0Labels := by
      have hz : ∀ j, raw9806 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw9806step0 = (fun i j => raw9806 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw9806step0 raw9806; decide +kernel
      have hl : raw9806step0Labels = raw9806Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9806 raw9806Labels permutation346 hz
    mixedMoment B raw9806step0 raw9806step0Labels = mixedMoment B raw9806step1 raw9806step1Labels := by
      have ha : raw9806step1 = (fun i j => raw9806step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw9806step1 raw9806step0; decide +kernel
      have hl : raw9806step1Labels = raw9806step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9806step0 raw9806step0Labels permutation38 permutation7
    mixedMoment B raw9806step1 raw9806step1Labels = mixedMoment B raw9806step2 raw9806step2Labels := by
      have ha : raw9806step2 = -raw9806step1 := by apply Matrix.ext; change ∀ i j, raw9806step2 i j = -(raw9806step1 i j); unfold raw9806step2 raw9806step1; decide +kernel
      have hl : raw9806step2Labels = raw9806step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw9806step2 raw9806step2Labels = mixedMoment B raw9806step3 raw9806step3Labels := by
      have ha : raw9806step3 = raw9806step2 := by apply Matrix.ext; unfold raw9806step3 raw9806step2; decide +kernel
      have hl : raw9806step2Labels = labelEmbedding1 ∘ raw9806step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9806step2 raw9806step2Labels raw9806step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3578 node3578Labels := by rfl

theorem canonical9807 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9807 raw9807Labels = mixedMoment B node3562 node3562Labels := by
  calc
    mixedMoment B raw9807 raw9807Labels = mixedMoment B raw9807step0 raw9807step0Labels := by
      have ha : raw9807step0 = (fun i j => raw9807 (permutation206 i) (permutation7 j)) := by apply Matrix.ext; unfold raw9807step0 raw9807; decide +kernel
      have hl : raw9807step0Labels = raw9807Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9807 raw9807Labels permutation206 permutation7
    mixedMoment B raw9807step0 raw9807step0Labels = mixedMoment B raw9807step1 raw9807step1Labels := by
      have ha : raw9807step1 = -raw9807step0 := by apply Matrix.ext; change ∀ i j, raw9807step1 i j = -(raw9807step0 i j); unfold raw9807step1 raw9807step0; decide +kernel
      have hl : raw9807step1Labels = raw9807step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw9807step1 raw9807step1Labels = mixedMoment B raw9807step2 raw9807step2Labels := by
      have ha : raw9807step2 = raw9807step1 := by apply Matrix.ext; unfold raw9807step2 raw9807step1; decide +kernel
      have hl : raw9807step1Labels = labelEmbedding1 ∘ raw9807step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9807step1 raw9807step1Labels raw9807step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3562 node3562Labels := by rfl

theorem canonical9808 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9808 raw9808Labels = mixedMoment B node3580 node3580Labels := by
  calc
    mixedMoment B raw9808 raw9808Labels = mixedMoment B raw9808step0 raw9808step0Labels := by
      have hz : ∀ j, raw9808 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw9808step0 = (fun i j => raw9808 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw9808step0 raw9808; decide +kernel
      have hl : raw9808step0Labels = raw9808Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9808 raw9808Labels permutation346 hz
    mixedMoment B raw9808step0 raw9808step0Labels = mixedMoment B raw9808step1 raw9808step1Labels := by
      have ha : raw9808step1 = (fun i j => raw9808step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw9808step1 raw9808step0; decide +kernel
      have hl : raw9808step1Labels = raw9808step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9808step0 raw9808step0Labels permutation38 permutation7
    mixedMoment B raw9808step1 raw9808step1Labels = mixedMoment B raw9808step2 raw9808step2Labels := by
      have ha : raw9808step2 = -raw9808step1 := by apply Matrix.ext; change ∀ i j, raw9808step2 i j = -(raw9808step1 i j); unfold raw9808step2 raw9808step1; decide +kernel
      have hl : raw9808step2Labels = raw9808step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw9808step2 raw9808step2Labels = mixedMoment B raw9808step3 raw9808step3Labels := by
      have ha : raw9808step3 = raw9808step2 := by apply Matrix.ext; unfold raw9808step3 raw9808step2; decide +kernel
      have hl : raw9808step2Labels = labelEmbedding1 ∘ raw9808step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9808step2 raw9808step2Labels raw9808step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3580 node3580Labels := by rfl

theorem canonical9809 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9809 raw9809Labels = mixedMoment B node3581 node3581Labels := by
  calc
    mixedMoment B raw9809 raw9809Labels = mixedMoment B raw9809step0 raw9809step0Labels := by
      have hz : ∀ j, raw9809 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw9809step0 = (fun i j => raw9809 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw9809step0 raw9809; decide +kernel
      have hl : raw9809step0Labels = raw9809Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9809 raw9809Labels permutation346 hz
    mixedMoment B raw9809step0 raw9809step0Labels = mixedMoment B raw9809step1 raw9809step1Labels := by
      have ha : raw9809step1 = (fun i j => raw9809step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw9809step1 raw9809step0; decide +kernel
      have hl : raw9809step1Labels = raw9809step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9809step0 raw9809step0Labels permutation38 permutation7
    mixedMoment B raw9809step1 raw9809step1Labels = mixedMoment B raw9809step2 raw9809step2Labels := by
      have ha : raw9809step2 = -raw9809step1 := by apply Matrix.ext; change ∀ i j, raw9809step2 i j = -(raw9809step1 i j); unfold raw9809step2 raw9809step1; decide +kernel
      have hl : raw9809step2Labels = raw9809step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw9809step2 raw9809step2Labels = mixedMoment B raw9809step3 raw9809step3Labels := by
      have ha : raw9809step3 = raw9809step2 := by apply Matrix.ext; unfold raw9809step3 raw9809step2; decide +kernel
      have hl : raw9809step2Labels = labelEmbedding1 ∘ raw9809step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9809step2 raw9809step2Labels raw9809step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3581 node3581Labels := by rfl

theorem canonical9810 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9810 raw9810Labels = mixedMoment B node3297 node3297Labels := by
  calc
    mixedMoment B raw9810 raw9810Labels = mixedMoment B raw9810step0 raw9810step0Labels := by
      have hz : ∀ j, raw9810 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw9810step0 = (fun i j => raw9810 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw9810step0 raw9810; decide +kernel
      have hl : raw9810step0Labels = raw9810Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9810 raw9810Labels permutation346 hz
    mixedMoment B raw9810step0 raw9810step0Labels = mixedMoment B raw9810step1 raw9810step1Labels := by
      have ha : raw9810step1 = (fun i j => raw9810step0 (permutation32 i) (permutation5 j)) := by apply Matrix.ext; unfold raw9810step1 raw9810step0; decide +kernel
      have hl : raw9810step1Labels = raw9810step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9810step0 raw9810step0Labels permutation32 permutation5
    mixedMoment B raw9810step1 raw9810step1Labels = mixedMoment B raw9810step2 raw9810step2Labels := by
      have ha : raw9810step2 = -raw9810step1 := by apply Matrix.ext; change ∀ i j, raw9810step2 i j = -(raw9810step1 i j); unfold raw9810step2 raw9810step1; decide +kernel
      have hl : raw9810step2Labels = raw9810step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw9810step2 raw9810step2Labels = mixedMoment B raw9810step3 raw9810step3Labels := by
      have ha : raw9810step3 = raw9810step2 := by apply Matrix.ext; unfold raw9810step3 raw9810step2; decide +kernel
      have hl : raw9810step2Labels = labelEmbedding1 ∘ raw9810step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9810step2 raw9810step2Labels raw9810step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3297 node3297Labels := by rfl

theorem canonical9811 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9811 raw9811Labels = mixedMoment B node3542 node3542Labels := by
  calc
    mixedMoment B raw9811 raw9811Labels = mixedMoment B raw9811step0 raw9811step0Labels := by
      have hz : ∀ j, raw9811 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw9811step0 = (fun i j => raw9811 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw9811step0 raw9811; decide +kernel
      have hl : raw9811step0Labels = raw9811Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9811 raw9811Labels permutation346 hz
    mixedMoment B raw9811step0 raw9811step0Labels = mixedMoment B raw9811step1 raw9811step1Labels := by
      have ha : raw9811step1 = (fun i j => raw9811step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw9811step1 raw9811step0; decide +kernel
      have hl : raw9811step1Labels = raw9811step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9811step0 raw9811step0Labels permutation38 permutation7
    mixedMoment B raw9811step1 raw9811step1Labels = mixedMoment B raw9811step2 raw9811step2Labels := by
      have ha : raw9811step2 = -raw9811step1 := by apply Matrix.ext; change ∀ i j, raw9811step2 i j = -(raw9811step1 i j); unfold raw9811step2 raw9811step1; decide +kernel
      have hl : raw9811step2Labels = raw9811step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw9811step2 raw9811step2Labels = mixedMoment B raw9811step3 raw9811step3Labels := by
      have ha : raw9811step3 = raw9811step2 := by apply Matrix.ext; unfold raw9811step3 raw9811step2; decide +kernel
      have hl : raw9811step2Labels = labelEmbedding1 ∘ raw9811step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9811step2 raw9811step2Labels raw9811step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3542 node3542Labels := by rfl

theorem canonical9812 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9812 raw9812Labels = mixedMoment B node3520 node3520Labels := by
  calc
    mixedMoment B raw9812 raw9812Labels = mixedMoment B raw9812step0 raw9812step0Labels := by
      have ha : raw9812step0 = (fun i j => raw9812 (permutation206 i) (permutation7 j)) := by apply Matrix.ext; unfold raw9812step0 raw9812; decide +kernel
      have hl : raw9812step0Labels = raw9812Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9812 raw9812Labels permutation206 permutation7
    mixedMoment B raw9812step0 raw9812step0Labels = mixedMoment B raw9812step1 raw9812step1Labels := by
      have ha : raw9812step1 = -raw9812step0 := by apply Matrix.ext; change ∀ i j, raw9812step1 i j = -(raw9812step0 i j); unfold raw9812step1 raw9812step0; decide +kernel
      have hl : raw9812step1Labels = raw9812step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw9812step1 raw9812step1Labels = mixedMoment B raw9812step2 raw9812step2Labels := by
      have ha : raw9812step2 = raw9812step1 := by apply Matrix.ext; unfold raw9812step2 raw9812step1; decide +kernel
      have hl : raw9812step1Labels = labelEmbedding1 ∘ raw9812step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9812step1 raw9812step1Labels raw9812step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3520 node3520Labels := by rfl

theorem canonical9813 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9813 raw9813Labels = mixedMoment B node3482 node3482Labels := by
  calc
    mixedMoment B raw9813 raw9813Labels = mixedMoment B raw9813step0 raw9813step0Labels := by
      have hz : ∀ j, raw9813 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw9813step0 = (fun i j => raw9813 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw9813step0 raw9813; decide +kernel
      have hl : raw9813step0Labels = raw9813Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9813 raw9813Labels permutation346 hz
    mixedMoment B raw9813step0 raw9813step0Labels = mixedMoment B raw9813step1 raw9813step1Labels := by
      have ha : raw9813step1 = (fun i j => raw9813step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw9813step1 raw9813step0; decide +kernel
      have hl : raw9813step1Labels = raw9813step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9813step0 raw9813step0Labels permutation38 permutation7
    mixedMoment B raw9813step1 raw9813step1Labels = mixedMoment B raw9813step2 raw9813step2Labels := by
      have ha : raw9813step2 = -raw9813step1 := by apply Matrix.ext; change ∀ i j, raw9813step2 i j = -(raw9813step1 i j); unfold raw9813step2 raw9813step1; decide +kernel
      have hl : raw9813step2Labels = raw9813step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw9813step2 raw9813step2Labels = mixedMoment B raw9813step3 raw9813step3Labels := by
      have ha : raw9813step3 = raw9813step2 := by apply Matrix.ext; unfold raw9813step3 raw9813step2; decide +kernel
      have hl : raw9813step2Labels = labelEmbedding1 ∘ raw9813step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9813step2 raw9813step2Labels raw9813step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3482 node3482Labels := by rfl

theorem canonical9814 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9814 raw9814Labels = mixedMoment B node3544 node3544Labels := by
  calc
    mixedMoment B raw9814 raw9814Labels = mixedMoment B raw9814step0 raw9814step0Labels := by
      have hz : ∀ j, raw9814 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw9814step0 = (fun i j => raw9814 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw9814step0 raw9814; decide +kernel
      have hl : raw9814step0Labels = raw9814Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9814 raw9814Labels permutation346 hz
    mixedMoment B raw9814step0 raw9814step0Labels = mixedMoment B raw9814step1 raw9814step1Labels := by
      have ha : raw9814step1 = (fun i j => raw9814step0 (permutation39 i) (permutation7 j)) := by apply Matrix.ext; unfold raw9814step1 raw9814step0; decide +kernel
      have hl : raw9814step1Labels = raw9814step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9814step0 raw9814step0Labels permutation39 permutation7
    mixedMoment B raw9814step1 raw9814step1Labels = mixedMoment B raw9814step2 raw9814step2Labels := by
      have ha : raw9814step2 = -raw9814step1 := by apply Matrix.ext; change ∀ i j, raw9814step2 i j = -(raw9814step1 i j); unfold raw9814step2 raw9814step1; decide +kernel
      have hl : raw9814step2Labels = raw9814step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw9814step2 raw9814step2Labels = mixedMoment B raw9814step3 raw9814step3Labels := by
      have ha : raw9814step3 = raw9814step2 := by apply Matrix.ext; unfold raw9814step3 raw9814step2; decide +kernel
      have hl : raw9814step2Labels = labelEmbedding1 ∘ raw9814step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9814step2 raw9814step2Labels raw9814step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3544 node3544Labels := by rfl

theorem canonical9815 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9815 raw9815Labels = mixedMoment B node3291 node3291Labels := by
  calc
    mixedMoment B raw9815 raw9815Labels = mixedMoment B raw9815step0 raw9815step0Labels := by
      have hz : ∀ j, raw9815 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw9815step0 = (fun i j => raw9815 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw9815step0 raw9815; decide +kernel
      have hl : raw9815step0Labels = raw9815Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9815 raw9815Labels permutation346 hz
    mixedMoment B raw9815step0 raw9815step0Labels = mixedMoment B raw9815step1 raw9815step1Labels := by
      have ha : raw9815step1 = (fun i j => raw9815step0 (permutation34 i) (permutation5 j)) := by apply Matrix.ext; unfold raw9815step1 raw9815step0; decide +kernel
      have hl : raw9815step1Labels = raw9815step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9815step0 raw9815step0Labels permutation34 permutation5
    mixedMoment B raw9815step1 raw9815step1Labels = mixedMoment B raw9815step2 raw9815step2Labels := by
      have ha : raw9815step2 = -raw9815step1 := by apply Matrix.ext; change ∀ i j, raw9815step2 i j = -(raw9815step1 i j); unfold raw9815step2 raw9815step1; decide +kernel
      have hl : raw9815step2Labels = raw9815step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw9815step2 raw9815step2Labels = mixedMoment B raw9815step3 raw9815step3Labels := by
      have ha : raw9815step3 = raw9815step2 := by apply Matrix.ext; unfold raw9815step3 raw9815step2; decide +kernel
      have hl : raw9815step2Labels = labelEmbedding1 ∘ raw9815step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9815step2 raw9815step2Labels raw9815step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3291 node3291Labels := by rfl

theorem canonical9816 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9816 raw9816Labels = mixedMoment B node3523 node3523Labels := by
  calc
    mixedMoment B raw9816 raw9816Labels = mixedMoment B raw9816step0 raw9816step0Labels := by
      have hz : ∀ j, raw9816 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw9816step0 = (fun i j => raw9816 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw9816step0 raw9816; decide +kernel
      have hl : raw9816step0Labels = raw9816Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9816 raw9816Labels permutation346 hz
    mixedMoment B raw9816step0 raw9816step0Labels = mixedMoment B raw9816step1 raw9816step1Labels := by
      have ha : raw9816step1 = (fun i j => raw9816step0 (permutation144 i) (permutation5 j)) := by apply Matrix.ext; unfold raw9816step1 raw9816step0; decide +kernel
      have hl : raw9816step1Labels = raw9816step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9816step0 raw9816step0Labels permutation144 permutation5
    mixedMoment B raw9816step1 raw9816step1Labels = mixedMoment B raw9816step2 raw9816step2Labels := by
      have ha : raw9816step2 = raw9816step1 := by apply Matrix.ext; unfold raw9816step2 raw9816step1; decide +kernel
      have hl : raw9816step1Labels = labelEmbedding1 ∘ raw9816step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9816step1 raw9816step1Labels raw9816step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3523 node3523Labels := by rfl

theorem canonical9817 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9817 raw9817Labels = mixedMoment B node3519 node3519Labels := by
  calc
    mixedMoment B raw9817 raw9817Labels = mixedMoment B raw9817step0 raw9817step0Labels := by
      have ha : raw9817step0 = (fun i j => raw9817 (permutation662 i) (permutation5 j)) := by apply Matrix.ext; unfold raw9817step0 raw9817; decide +kernel
      have hl : raw9817step0Labels = raw9817Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9817 raw9817Labels permutation662 permutation5
    mixedMoment B raw9817step0 raw9817step0Labels = mixedMoment B raw9817step1 raw9817step1Labels := by
      have ha : raw9817step1 = raw9817step0 := by apply Matrix.ext; unfold raw9817step1 raw9817step0; decide +kernel
      have hl : raw9817step0Labels = labelEmbedding1 ∘ raw9817step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9817step0 raw9817step0Labels raw9817step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3519 node3519Labels := by rfl

theorem canonical9818 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9818 raw9818Labels = mixedMoment B node3481 node3481Labels := by
  calc
    mixedMoment B raw9818 raw9818Labels = mixedMoment B raw9818step0 raw9818step0Labels := by
      have hz : ∀ j, raw9818 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw9818step0 = (fun i j => raw9818 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw9818step0 raw9818; decide +kernel
      have hl : raw9818step0Labels = raw9818Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9818 raw9818Labels permutation346 hz
    mixedMoment B raw9818step0 raw9818step0Labels = mixedMoment B raw9818step1 raw9818step1Labels := by
      have ha : raw9818step1 = (fun i j => raw9818step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw9818step1 raw9818step0; decide +kernel
      have hl : raw9818step1Labels = raw9818step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9818step0 raw9818step0Labels permutation38 permutation7
    mixedMoment B raw9818step1 raw9818step1Labels = mixedMoment B raw9818step2 raw9818step2Labels := by
      have ha : raw9818step2 = -raw9818step1 := by apply Matrix.ext; change ∀ i j, raw9818step2 i j = -(raw9818step1 i j); unfold raw9818step2 raw9818step1; decide +kernel
      have hl : raw9818step2Labels = raw9818step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw9818step2 raw9818step2Labels = mixedMoment B raw9818step3 raw9818step3Labels := by
      have ha : raw9818step3 = raw9818step2 := by apply Matrix.ext; unfold raw9818step3 raw9818step2; decide +kernel
      have hl : raw9818step2Labels = labelEmbedding1 ∘ raw9818step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9818step2 raw9818step2Labels raw9818step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3481 node3481Labels := by rfl

theorem canonical9819 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9819 raw9819Labels = mixedMoment B node3543 node3543Labels := by
  calc
    mixedMoment B raw9819 raw9819Labels = mixedMoment B raw9819step0 raw9819step0Labels := by
      have hz : ∀ j, raw9819 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw9819step0 = (fun i j => raw9819 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw9819step0 raw9819; decide +kernel
      have hl : raw9819step0Labels = raw9819Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9819 raw9819Labels permutation346 hz
    mixedMoment B raw9819step0 raw9819step0Labels = mixedMoment B raw9819step1 raw9819step1Labels := by
      have ha : raw9819step1 = (fun i j => raw9819step0 (permutation143 i) (permutation5 j)) := by apply Matrix.ext; unfold raw9819step1 raw9819step0; decide +kernel
      have hl : raw9819step1Labels = raw9819step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9819step0 raw9819step0Labels permutation143 permutation5
    mixedMoment B raw9819step1 raw9819step1Labels = mixedMoment B raw9819step2 raw9819step2Labels := by
      have ha : raw9819step2 = raw9819step1 := by apply Matrix.ext; unfold raw9819step2 raw9819step1; decide +kernel
      have hl : raw9819step1Labels = labelEmbedding1 ∘ raw9819step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9819step1 raw9819step1Labels raw9819step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3543 node3543Labels := by rfl

theorem canonical9820 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9820 raw9820Labels = mixedMoment B node2723 node2723Labels := by
  calc
    mixedMoment B raw9820 raw9820Labels = mixedMoment B raw9820step0 raw9820step0Labels := by
      have hz : ∀ j, raw9820 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw9820step0 = (fun i j => raw9820 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw9820step0 raw9820; decide +kernel
      have hl : raw9820step0Labels = raw9820Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9820 raw9820Labels permutation346 hz
    mixedMoment B raw9820step0 raw9820step0Labels = mixedMoment B raw9820step1 raw9820step1Labels := by
      have ha : raw9820step1 = (fun i j => raw9820step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9820step1 raw9820step0; decide +kernel
      have hl : raw9820step1Labels = raw9820step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9820step0 raw9820step0Labels permutation38 permutation2
    _ = mixedMoment B node2723 node2723Labels := by rfl

theorem canonical9821 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9821 raw9821Labels = mixedMoment B node3876 node3876Labels := by
  calc
    mixedMoment B raw9821 raw9821Labels = mixedMoment B raw9821step0 raw9821step0Labels := by
      have hz : ∀ j, raw9821 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw9821step0 = (fun i j => raw9821 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw9821step0 raw9821; decide +kernel
      have hl : raw9821step0Labels = raw9821Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9821 raw9821Labels permutation346 hz
    _ = mixedMoment B node3876 node3876Labels := by rfl

theorem canonical9822 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9822 raw9822Labels = mixedMoment B node3838 node3838Labels := by
  calc
    mixedMoment B raw9822 raw9822Labels = mixedMoment B raw9822step0 raw9822step0Labels := by
      have ha : raw9822step0 = (fun i j => raw9822 (permutation182 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9822step0 raw9822; decide +kernel
      have hl : raw9822step0Labels = raw9822Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9822 raw9822Labels permutation182 permutation2
    _ = mixedMoment B node3838 node3838Labels := by rfl

theorem canonical9823 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9823 raw9823Labels = mixedMoment B node3808 node3808Labels := by
  calc
    mixedMoment B raw9823 raw9823Labels = mixedMoment B raw9823step0 raw9823step0Labels := by
      have hz : ∀ j, raw9823 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw9823step0 = (fun i j => raw9823 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw9823step0 raw9823; decide +kernel
      have hl : raw9823step0Labels = raw9823Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9823 raw9823Labels permutation346 hz
    mixedMoment B raw9823step0 raw9823step0Labels = mixedMoment B raw9823step1 raw9823step1Labels := by
      have ha : raw9823step1 = (fun i j => raw9823step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9823step1 raw9823step0; decide +kernel
      have hl : raw9823step1Labels = raw9823step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9823step0 raw9823step0Labels permutation38 permutation2
    _ = mixedMoment B node3808 node3808Labels := by rfl

theorem canonical9824 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9824 raw9824Labels = mixedMoment B node3902 node3902Labels := by
  calc
    mixedMoment B raw9824 raw9824Labels = mixedMoment B raw9824step0 raw9824step0Labels := by
      have hz : ∀ j, raw9824 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw9824step0 = (fun i j => raw9824 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw9824step0 raw9824; decide +kernel
      have hl : raw9824step0Labels = raw9824Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9824 raw9824Labels permutation346 hz
    mixedMoment B raw9824step0 raw9824step0Labels = mixedMoment B raw9824step1 raw9824step1Labels := by
      have ha : raw9824step1 = (fun i j => raw9824step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9824step1 raw9824step0; decide +kernel
      have hl : raw9824step1Labels = raw9824step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9824step0 raw9824step0Labels permutation38 permutation2
    _ = mixedMoment B node3902 node3902Labels := by rfl

theorem canonical9825 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9825 raw9825Labels = mixedMoment B node3904 node3904Labels := by
  calc
    mixedMoment B raw9825 raw9825Labels = mixedMoment B raw9825step0 raw9825step0Labels := by
      have hz : ∀ j, raw9825 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw9825step0 = (fun i j => raw9825 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw9825step0 raw9825; decide +kernel
      have hl : raw9825step0Labels = raw9825Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9825 raw9825Labels permutation346 hz
    mixedMoment B raw9825step0 raw9825step0Labels = mixedMoment B raw9825step1 raw9825step1Labels := by
      have ha : raw9825step1 = (fun i j => raw9825step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9825step1 raw9825step0; decide +kernel
      have hl : raw9825step1Labels = raw9825step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9825step0 raw9825step0Labels permutation38 permutation2
    _ = mixedMoment B node3904 node3904Labels := by rfl

theorem canonical9826 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9826 raw9826Labels = mixedMoment B node4091 node4091Labels := by
  calc
    mixedMoment B raw9826 raw9826Labels = mixedMoment B raw9826step0 raw9826step0Labels := by
      have hz : ∀ j, raw9826 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw9826step0 = (fun i j => raw9826 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw9826step0 raw9826; decide +kernel
      have hl : raw9826step0Labels = raw9826Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9826 raw9826Labels permutation346 hz
    mixedMoment B raw9826step0 raw9826step0Labels = mixedMoment B raw9826step1 raw9826step1Labels := by
      have ha : raw9826step1 = (fun i j => raw9826step0 (permutation38 i) (permutation0 j)) := by apply Matrix.ext; unfold raw9826step1 raw9826step0; decide +kernel
      have hl : raw9826step1Labels = raw9826step0Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9826step0 raw9826step0Labels permutation38 permutation0
    _ = mixedMoment B node4091 node4091Labels := by rfl

theorem canonical9827 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9827 raw9827Labels = mixedMoment B node1240 node1240Labels := by
  calc
    mixedMoment B raw9827 raw9827Labels = mixedMoment B raw9827step0 raw9827step0Labels := by
      have hz : ∀ j, raw9827 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw9827step0 = (fun i j => raw9827 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw9827step0 raw9827; decide +kernel
      have hl : raw9827step0Labels = raw9827Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9827 raw9827Labels permutation346 hz
    mixedMoment B raw9827step0 raw9827step0Labels = mixedMoment B raw9827step1 raw9827step1Labels := by
      have ha : raw9827step1 = (fun i j => raw9827step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9827step1 raw9827step0; decide +kernel
      have hl : raw9827step1Labels = raw9827step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9827step0 raw9827step0Labels permutation38 permutation2
    _ = mixedMoment B node1240 node1240Labels := by rfl

theorem canonical9828 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9828 raw9828Labels = mixedMoment B node1213 node1213Labels := by
  calc
    mixedMoment B raw9828 raw9828Labels = mixedMoment B raw9828step0 raw9828step0Labels := by
      have ha : raw9828step0 = (fun i j => raw9828 (permutation200 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9828step0 raw9828; decide +kernel
      have hl : raw9828step0Labels = raw9828Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9828 raw9828Labels permutation200 permutation2
    _ = mixedMoment B node1213 node1213Labels := by rfl

theorem canonical9829 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9829 raw9829Labels = mixedMoment B node1262 node1262Labels := by
  calc
    mixedMoment B raw9829 raw9829Labels = mixedMoment B raw9829step0 raw9829step0Labels := by
      have hz : ∀ j, raw9829 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw9829step0 = (fun i j => raw9829 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw9829step0 raw9829; decide +kernel
      have hl : raw9829step0Labels = raw9829Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9829 raw9829Labels permutation346 hz
    _ = mixedMoment B node1262 node1262Labels := by rfl

theorem canonical9830 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9830 raw9830Labels = mixedMoment B node1220 node1220Labels := by
  calc
    mixedMoment B raw9830 raw9830Labels = mixedMoment B raw9830step0 raw9830step0Labels := by
      have hz : ∀ j, raw9830 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw9830step0 = (fun i j => raw9830 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw9830step0 raw9830; decide +kernel
      have hl : raw9830step0Labels = raw9830Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9830 raw9830Labels permutation346 hz
    mixedMoment B raw9830step0 raw9830step0Labels = mixedMoment B raw9830step1 raw9830step1Labels := by
      have ha : raw9830step1 = (fun i j => raw9830step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9830step1 raw9830step0; decide +kernel
      have hl : raw9830step1Labels = raw9830step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9830step0 raw9830step0Labels permutation38 permutation2
    _ = mixedMoment B node1220 node1220Labels := by rfl

theorem canonical9831 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9831 raw9831Labels = mixedMoment B node1217 node1217Labels := by
  calc
    mixedMoment B raw9831 raw9831Labels = mixedMoment B raw9831step0 raw9831step0Labels := by
      have hz : ∀ j, raw9831 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw9831step0 = (fun i j => raw9831 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw9831step0 raw9831; decide +kernel
      have hl : raw9831step0Labels = raw9831Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9831 raw9831Labels permutation346 hz
    mixedMoment B raw9831step0 raw9831step0Labels = mixedMoment B raw9831step1 raw9831step1Labels := by
      have ha : raw9831step1 = (fun i j => raw9831step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9831step1 raw9831step0; decide +kernel
      have hl : raw9831step1Labels = raw9831step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9831step0 raw9831step0Labels permutation38 permutation2
    _ = mixedMoment B node1217 node1217Labels := by rfl

theorem canonical9832 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9832 raw9832Labels = mixedMoment B node2556 node2556Labels := by
  calc
    mixedMoment B raw9832 raw9832Labels = mixedMoment B raw9832step0 raw9832step0Labels := by
      have ha : raw9832step0 = (fun i j => raw9832 (permutation182 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9832step0 raw9832; decide +kernel
      have hl : raw9832step0Labels = raw9832Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9832 raw9832Labels permutation182 permutation2
    _ = mixedMoment B node2556 node2556Labels := by rfl

theorem canonical9833 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9833 raw9833Labels = mixedMoment B node2514 node2514Labels := by
  calc
    mixedMoment B raw9833 raw9833Labels = mixedMoment B raw9833step0 raw9833step0Labels := by
      have hz : ∀ j, raw9833 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw9833step0 = (fun i j => raw9833 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw9833step0 raw9833; decide +kernel
      have hl : raw9833step0Labels = raw9833Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9833 raw9833Labels permutation346 hz
    mixedMoment B raw9833step0 raw9833step0Labels = mixedMoment B raw9833step1 raw9833step1Labels := by
      have ha : raw9833step1 = (fun i j => raw9833step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9833step1 raw9833step0; decide +kernel
      have hl : raw9833step1Labels = raw9833step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9833step0 raw9833step0Labels permutation38 permutation2
    _ = mixedMoment B node2514 node2514Labels := by rfl

theorem canonical9834 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9834 raw9834Labels = mixedMoment B node2723 node2723Labels := by
  calc
    mixedMoment B raw9834 raw9834Labels = mixedMoment B raw9834step0 raw9834step0Labels := by
      have hz : ∀ j, raw9834 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw9834step0 = (fun i j => raw9834 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw9834step0 raw9834; decide +kernel
      have hl : raw9834step0Labels = raw9834Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9834 raw9834Labels permutation346 hz
    mixedMoment B raw9834step0 raw9834step0Labels = mixedMoment B raw9834step1 raw9834step1Labels := by
      have ha : raw9834step1 = (fun i j => raw9834step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9834step1 raw9834step0; decide +kernel
      have hl : raw9834step1Labels = raw9834step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9834step0 raw9834step0Labels permutation40 permutation2
    _ = mixedMoment B node2723 node2723Labels := by rfl

theorem canonical9835 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9835 raw9835Labels = mixedMoment B node2741 node2741Labels := by
  calc
    mixedMoment B raw9835 raw9835Labels = mixedMoment B raw9835step0 raw9835step0Labels := by
      have hz : ∀ j, raw9835 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw9835step0 = (fun i j => raw9835 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw9835step0 raw9835; decide +kernel
      have hl : raw9835step0Labels = raw9835Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9835 raw9835Labels permutation346 hz
    mixedMoment B raw9835step0 raw9835step0Labels = mixedMoment B raw9835step1 raw9835step1Labels := by
      have ha : raw9835step1 = (fun i j => raw9835step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9835step1 raw9835step0; decide +kernel
      have hl : raw9835step1Labels = raw9835step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9835step0 raw9835step0Labels permutation38 permutation2
    _ = mixedMoment B node2741 node2741Labels := by rfl

theorem canonical9836 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9836 raw9836Labels = mixedMoment B node2615 node2615Labels := by
  calc
    mixedMoment B raw9836 raw9836Labels = mixedMoment B raw9836step0 raw9836step0Labels := by
      have ha : raw9836step0 = (fun i j => raw9836 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9836step0 raw9836; decide +kernel
      have hl : raw9836step0Labels = raw9836Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9836 raw9836Labels permutation158 permutation2
    _ = mixedMoment B node2615 node2615Labels := by rfl

theorem canonical9837 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9837 raw9837Labels = mixedMoment B node2633 node2633Labels := by
  calc
    mixedMoment B raw9837 raw9837Labels = mixedMoment B raw9837step0 raw9837step0Labels := by
      have hz : ∀ j, raw9837 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw9837step0 = (fun i j => raw9837 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw9837step0 raw9837; decide +kernel
      have hl : raw9837step0Labels = raw9837Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9837 raw9837Labels permutation346 hz
    _ = mixedMoment B node2633 node2633Labels := by rfl

theorem canonical9838 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9838 raw9838Labels = mixedMoment B node2621 node2621Labels := by
  calc
    mixedMoment B raw9838 raw9838Labels = mixedMoment B raw9838step0 raw9838step0Labels := by
      have hz : ∀ j, raw9838 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw9838step0 = (fun i j => raw9838 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw9838step0 raw9838; decide +kernel
      have hl : raw9838step0Labels = raw9838Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9838 raw9838Labels permutation346 hz
    _ = mixedMoment B node2621 node2621Labels := by rfl

theorem canonical9839 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9839 raw9839Labels = mixedMoment B node2618 node2618Labels := by
  calc
    mixedMoment B raw9839 raw9839Labels = mixedMoment B raw9839step0 raw9839step0Labels := by
      have hz : ∀ j, raw9839 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw9839step0 = (fun i j => raw9839 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw9839step0 raw9839; decide +kernel
      have hl : raw9839step0Labels = raw9839Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9839 raw9839Labels permutation346 hz
    _ = mixedMoment B node2618 node2618Labels := by rfl

theorem canonical9840 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9840 raw9840Labels = mixedMoment B node2567 node2567Labels := by
  calc
    mixedMoment B raw9840 raw9840Labels = mixedMoment B raw9840step0 raw9840step0Labels := by
      have ha : raw9840step0 = (fun i j => raw9840 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9840step0 raw9840; decide +kernel
      have hl : raw9840step0Labels = raw9840Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9840 raw9840Labels permutation176 permutation2
    _ = mixedMoment B node2567 node2567Labels := by rfl

theorem canonical9841 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9841 raw9841Labels = mixedMoment B node2546 node2546Labels := by
  calc
    mixedMoment B raw9841 raw9841Labels = mixedMoment B raw9841step0 raw9841step0Labels := by
      have ha : raw9841step0 = (fun i j => raw9841 (permutation182 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9841step0 raw9841; decide +kernel
      have hl : raw9841step0Labels = raw9841Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9841 raw9841Labels permutation182 permutation2
    _ = mixedMoment B node2546 node2546Labels := by rfl

theorem canonical9842 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9842 raw9842Labels = mixedMoment B node2543 node2543Labels := by
  calc
    mixedMoment B raw9842 raw9842Labels = mixedMoment B raw9842step0 raw9842step0Labels := by
      have ha : raw9842step0 = (fun i j => raw9842 (permutation182 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9842step0 raw9842; decide +kernel
      have hl : raw9842step0Labels = raw9842Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9842 raw9842Labels permutation182 permutation2
    _ = mixedMoment B node2543 node2543Labels := by rfl

theorem canonical9843 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9843 raw9843Labels = mixedMoment B node2480 node2480Labels := by
  calc
    mixedMoment B raw9843 raw9843Labels = mixedMoment B raw9843step0 raw9843step0Labels := by
      have ha : raw9843step0 = (fun i j => raw9843 (permutation200 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9843step0 raw9843; decide +kernel
      have hl : raw9843step0Labels = raw9843Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9843 raw9843Labels permutation200 permutation2
    _ = mixedMoment B node2480 node2480Labels := by rfl

theorem canonical9844 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9844 raw9844Labels = mixedMoment B node2489 node2489Labels := by
  calc
    mixedMoment B raw9844 raw9844Labels = mixedMoment B raw9844step0 raw9844step0Labels := by
      have hz : ∀ j, raw9844 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw9844step0 = (fun i j => raw9844 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw9844step0 raw9844; decide +kernel
      have hl : raw9844step0Labels = raw9844Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9844 raw9844Labels permutation346 hz
    mixedMoment B raw9844step0 raw9844step0Labels = mixedMoment B raw9844step1 raw9844step1Labels := by
      have ha : raw9844step1 = (fun i j => raw9844step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9844step1 raw9844step0; decide +kernel
      have hl : raw9844step1Labels = raw9844step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9844step0 raw9844step0Labels permutation38 permutation2
    _ = mixedMoment B node2489 node2489Labels := by rfl

theorem canonical9845 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9845 raw9845Labels = mixedMoment B node2485 node2485Labels := by
  calc
    mixedMoment B raw9845 raw9845Labels = mixedMoment B raw9845step0 raw9845step0Labels := by
      have hz : ∀ j, raw9845 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw9845step0 = (fun i j => raw9845 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw9845step0 raw9845; decide +kernel
      have hl : raw9845step0Labels = raw9845Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9845 raw9845Labels permutation346 hz
    mixedMoment B raw9845step0 raw9845step0Labels = mixedMoment B raw9845step1 raw9845step1Labels := by
      have ha : raw9845step1 = (fun i j => raw9845step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9845step1 raw9845step0; decide +kernel
      have hl : raw9845step1Labels = raw9845step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9845step0 raw9845step0Labels permutation38 permutation2
    _ = mixedMoment B node2485 node2485Labels := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical123
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical3960 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3960 = injectiveMoment H node655 := by
  calc
    injectiveMoment H raw3960 = injectiveMoment H raw3960step0 := by
      have heq : raw3960step0 = -raw3960 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3960).symm
    injectiveMoment H raw3960step0 = injectiveMoment H raw3960step1 := by
      have heq : raw3960step1 = (fun i j => raw3960step0 (permutation33 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3960step0 permutation33 permutation8
    _ = injectiveMoment H node655 := by rfl

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

theorem canonical5165 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5165 = injectiveMoment H node4 := by
  clear _hH
  calc
    injectiveMoment H raw5165 = injectiveMoment H raw5165step0 := by
      have hz : ∀ j, raw5165 (permutation104 0) j = 0 := by decide +kernel
      have heq : raw5165step0 = (fun i j => raw5165 (permutation104 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw5165 permutation104 hz
    injectiveMoment H raw5165step0 = injectiveMoment H raw5165step1 := by
      have hz : ∀ j, raw5165step0 (permutation21 0) j = 0 := by decide +kernel
      have heq : raw5165step1 = (fun i j => raw5165step0 (permutation21 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw5165step0 permutation21 hz
    injectiveMoment H raw5165step1 = injectiveMoment H raw5165step2 := by
      have hz : ∀ j, raw5165step1 (permutation5 0) j = 0 := by decide +kernel
      have heq : raw5165step2 = (fun i j => raw5165step1 (permutation5 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw5165step1 permutation5 hz
    _ = injectiveMoment H node4 := by rfl

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

end MUB6.Certificate.PairSemantics

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical249
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical7981 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7981 = injectiveMoment H node0 := by
  calc
    injectiveMoment H raw7981 = injectiveMoment H raw7981step0 := by
      have hz : ∀ j, raw7981 (permutation128 0) j = 0 := by decide +kernel
      have heq : raw7981step0 = (fun i j => raw7981 (permutation128 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7981 permutation128 hz
    injectiveMoment H raw7981step0 = injectiveMoment H raw7981step1 := by
      have hz : ∀ j, raw7981step0 (permutation27 0) j = 0 := by decide +kernel
      have heq : raw7981step1 = (fun i j => raw7981step0 (permutation27 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7981step0 permutation27 hz
    injectiveMoment H raw7981step1 = injectiveMoment H raw7981step2 := by
      have hz : ∀ j, raw7981step1 (permutation7 0) j = 0 := by decide +kernel
      have heq : raw7981step2 = (fun i j => raw7981step1 (permutation7 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7981step1 permutation7 hz
    injectiveMoment H raw7981step2 = injectiveMoment H raw7981step3 := by
      have hz : ∀ j, raw7981step2 (permutation2 0) j = 0 := by decide +kernel
      have heq : raw7981step3 = (fun i j => raw7981step2 (permutation2 i.succ) j) := by ext i j; fin_cases i; fin_cases j; decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7981step2 permutation2 hz
    injectiveMoment H raw7981step3 = injectiveMoment H raw7981step4 := by
      have hz : ∀ j, raw7981step3 (permutation0 0) j = 0 := by decide +kernel
      have heq : raw7981step4 = (fun i j => raw7981step3 (permutation0 i.succ) j) := by ext i j; fin_cases i
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7981step3 permutation0 hz
    injectiveMoment H raw7981step4 = injectiveMoment H raw7981step5 := by
      have hz : ∀ i, raw7981step4 i (permutation0 0) = 0 := by decide +kernel
      have heq : raw7981step5 = (fun i j => raw7981step4 i (permutation0 j.succ)) := by ext i j; fin_cases i
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw7981step4 permutation0 hz
    _ = injectiveMoment H node0 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical282
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical9030 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9030 = injectiveMoment H node65 := by
  calc
    injectiveMoment H raw9030 = injectiveMoment H raw9030step0 := by
      have hz : ∀ j, raw9030 (permutation33 0) j = 0 := by decide +kernel
      have heq : raw9030step0 = (fun i j => raw9030 (permutation33 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw9030 permutation33 hz
    injectiveMoment H raw9030step0 = injectiveMoment H raw9030step1 := by
      have heq : raw9030step1 = (fun i j => raw9030step0 (permutation13 i) (permutation1 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9030step0 permutation13 permutation1
    _ = injectiveMoment H node65 := by rfl

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

theorem sound36 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node36 = Sparse.eval value36 (momentVector H) := by
  have hc : momentVector H 3 = injectiveMoment H node36 := rfl
  simp [value36, Sparse.eval, hc]

theorem sound41 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node41 = Sparse.eval value41 (momentVector H) := by
  have hc : momentVector H 12 = injectiveMoment H node41 := rfl
  simp [value41, Sparse.eval, hc]

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical240
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical154
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound2
attribute [-simp] _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_toRational _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound3
attribute [-simp] _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_toRational _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound10
attribute [-simp] _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_toRational _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_SingleGroup30
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singlePair494 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node494 node494Labels = Sparse.eval singlePairValue494 (familyPairVector B) := by
  have hp := single_label_three B hB node494
  have hl : node494Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node494 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node494 (EqualityPatterns.family3.label 0) = PairSemantics.raw7981 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node494 PairSemantics.raw7981; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7981 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node494 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value4 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node494 (EqualityPatterns.family3.label 1) = PairSemantics.raw5165 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node494 PairSemantics.raw5165; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5165 hH).trans (PairSemantics.sound4 hH)
  have hm2 : familyPairMoment B (groupedColumns node494 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value65 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node494 (EqualityPatterns.family3.label 2) = PairSemantics.raw9030 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node494 PairSemantics.raw9030; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical9030 hH).trans (PairSemantics.sound65 hH)
  have hm3 : familyPairMoment B (groupedColumns node494 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value232 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node494 (EqualityPatterns.family3.label 3) = PairSemantics.raw5139 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node494 PairSemantics.raw5139; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5139 hH).trans (PairSemantics.sound232 hH)
  have hm4 : familyPairMoment B (groupedColumns node494 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value655 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node494 (EqualityPatterns.family3.label 4) = PairSemantics.raw3960 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node494 PairSemantics.raw3960; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical3960 hH).trans (PairSemantics.sound655 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue494, PairSemantics.value0, PairSemantics.value4, PairSemantics.value65, PairSemantics.value232, PairSemantics.value655, Sparse.eval] at hp ⊢
  linarith only [hp]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons60
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singleton3858 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node3858 node3858Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node494 node494Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw534 singletonSmall3858
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall3858) = raw534Labels := by decide +kernel
  rw [hl, canonical534 B hB] at h
  have hc0 : mixedMoment B raw534 (Fin.cases (0 : Fin 1) singletonSmall3858) =
      mixedMoment B node494 node494Labels := by
    have ha : raw534 = raw535 := by apply Matrix.ext; unfold raw534 raw535; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall3858 = raw535Labels := by decide +kernel
    rw [ha, hj, canonical535 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

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

theorem sound1213 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1213 node1213Labels = Sparse.eval nodeValue1213 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1213) = mixedMoment B node1213 node1213Labels := rfl
  simpa [nodeValue1213, Sparse.eval] using hc.symm

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

theorem sound1220 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1220 node1220Labels = Sparse.eval nodeValue1220 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1220) = mixedMoment B node1220 node1220Labels := rfl
  simpa [nodeValue1220, Sparse.eval] using hc.symm

theorem sound1240 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1240 node1240Labels = Sparse.eval nodeValue1240 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1240) = mixedMoment B node1240 node1240Labels := rfl
  simpa [nodeValue1240, Sparse.eval] using hc.symm

theorem sound1261 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1261 node1261Labels = Sparse.eval nodeValue1261 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1261) = mixedMoment B node1261 node1261Labels := rfl
  simpa [nodeValue1261, Sparse.eval] using hc.symm

theorem sound1262 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1262 node1262Labels = Sparse.eval nodeValue1262 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1262) = mixedMoment B node1262 node1262Labels := rfl
  simpa [nodeValue1262, Sparse.eval] using hc.symm

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

theorem sound2106 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2106 node2106Labels = Sparse.eval nodeValue2106 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2106) = mixedMoment B node2106 node2106Labels := rfl
  simpa [nodeValue2106, Sparse.eval] using hc.symm

theorem sound2109 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2109 node2109Labels = Sparse.eval nodeValue2109 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2109) = mixedMoment B node2109 node2109Labels := rfl
  simpa [nodeValue2109, Sparse.eval] using hc.symm

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

theorem sound2115 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2115 node2115Labels = Sparse.eval nodeValue2115 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2115) = mixedMoment B node2115 node2115Labels := rfl
  simpa [nodeValue2115, Sparse.eval] using hc.symm

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

theorem zero2264 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2264 node2264Labels = 0 := by
  exact mixedMoment_order_one B hB node2264 node2264Labels 1
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

theorem sound2264 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2264 node2264Labels = Sparse.eval nodeValue2264 (mixedVector B) := by
  simpa only [nodeValue2264, Sparse.eval_nil] using zero2264 B _hB _hF

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

theorem sound2480 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2480 node2480Labels = Sparse.eval nodeValue2480 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2480) = mixedMoment B node2480 node2480Labels := rfl
  simpa [nodeValue2480, Sparse.eval] using hc.symm

theorem sound2485 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2485 node2485Labels = Sparse.eval nodeValue2485 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2485) = mixedMoment B node2485 node2485Labels := rfl
  simpa [nodeValue2485, Sparse.eval] using hc.symm

theorem sound2489 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2489 node2489Labels = Sparse.eval nodeValue2489 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2489) = mixedMoment B node2489 node2489Labels := rfl
  simpa [nodeValue2489, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros39
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero2514 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2514 node2514Labels = 0 := by
  exact mixedMoment_order_one B hB node2514 node2514Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero2546 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node2546 node2546Labels = 0 := by
  exact mixedMoment_alpha B hF node2546 node2546Labels 1 permutation158
    (by decide +kernel)

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

theorem sound2514 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2514 node2514Labels = Sparse.eval nodeValue2514 (mixedVector B) := by
  simpa only [nodeValue2514, Sparse.eval_nil] using zero2514 B _hB _hF

theorem sound2543 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2543 node2543Labels = Sparse.eval nodeValue2543 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2543) = mixedMoment B node2543 node2543Labels := rfl
  simpa [nodeValue2543, Sparse.eval] using hc.symm

theorem sound2546 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2546 node2546Labels = Sparse.eval nodeValue2546 (mixedVector B) := by
  simpa only [nodeValue2546, Sparse.eval_nil] using zero2546 B _hB _hF

theorem sound2556 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2556 node2556Labels = Sparse.eval nodeValue2556 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2556) = mixedMoment B node2556 node2556Labels := rfl
  simpa [nodeValue2556, Sparse.eval] using hc.symm

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

theorem sound2566 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2566 node2566Labels = Sparse.eval nodeValue2566 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2566) = mixedMoment B node2566 node2566Labels := rfl
  simpa [nodeValue2566, Sparse.eval] using hc.symm

theorem sound2567 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2567 node2567Labels = Sparse.eval nodeValue2567 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2567) = mixedMoment B node2567 node2567Labels := rfl
  simpa [nodeValue2567, Sparse.eval] using hc.symm

theorem sound2615 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2615 node2615Labels = Sparse.eval nodeValue2615 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2615) = mixedMoment B node2615 node2615Labels := rfl
  simpa [nodeValue2615, Sparse.eval] using hc.symm

theorem sound2618 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2618 node2618Labels = Sparse.eval nodeValue2618 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2618) = mixedMoment B node2618 node2618Labels := rfl
  simpa [nodeValue2618, Sparse.eval] using hc.symm

theorem sound2621 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2621 node2621Labels = Sparse.eval nodeValue2621 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2621) = mixedMoment B node2621 node2621Labels := rfl
  simpa [nodeValue2621, Sparse.eval] using hc.symm

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

theorem sound2632 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2632 node2632Labels = Sparse.eval nodeValue2632 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2632) = mixedMoment B node2632 node2632Labels := rfl
  simpa [nodeValue2632, Sparse.eval] using hc.symm

theorem sound2633 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2633 node2633Labels = Sparse.eval nodeValue2633 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2633) = mixedMoment B node2633 node2633Labels := rfl
  simpa [nodeValue2633, Sparse.eval] using hc.symm

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

theorem sound2722 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2722 node2722Labels = Sparse.eval nodeValue2722 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2722) = mixedMoment B node2722 node2722Labels := rfl
  simpa [nodeValue2722, Sparse.eval] using hc.symm

theorem sound2723 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2723 node2723Labels = Sparse.eval nodeValue2723 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2723) = mixedMoment B node2723 node2723Labels := rfl
  simpa [nodeValue2723, Sparse.eval] using hc.symm

theorem sound2741 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2741 node2741Labels = Sparse.eval nodeValue2741 (mixedVector B) := by
  simpa only [nodeValue2741, Sparse.eval_nil] using zero2741 B _hB _hF

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

theorem sound2763 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2763 node2763Labels = Sparse.eval nodeValue2763 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2763) = mixedMoment B node2763 node2763Labels := rfl
  simpa [nodeValue2763, Sparse.eval] using hc.symm

theorem sound2765 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2765 node2765Labels = Sparse.eval nodeValue2765 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2765) = mixedMoment B node2765 node2765Labels := rfl
  simpa [nodeValue2765, Sparse.eval] using hc.symm

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

theorem sound3290 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3290 node3290Labels = Sparse.eval nodeValue3290 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3290) = mixedMoment B node3290 node3290Labels := rfl
  simpa [nodeValue3290, Sparse.eval] using hc.symm

theorem sound3291 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3291 node3291Labels = Sparse.eval nodeValue3291 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3291) = mixedMoment B node3291 node3291Labels := rfl
  simpa [nodeValue3291, Sparse.eval] using hc.symm

theorem sound3294 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3294 node3294Labels = Sparse.eval nodeValue3294 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3294) = mixedMoment B node3294 node3294Labels := rfl
  simpa [nodeValue3294, Sparse.eval] using hc.symm

theorem sound3297 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3297 node3297Labels = Sparse.eval nodeValue3297 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3297) = mixedMoment B node3297 node3297Labels := rfl
  simpa [nodeValue3297, Sparse.eval] using hc.symm

theorem sound3299 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3299 node3299Labels = Sparse.eval nodeValue3299 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3299) = mixedMoment B node3299 node3299Labels := rfl
  simpa [nodeValue3299, Sparse.eval] using hc.symm

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

theorem zero3483 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3483 node3483Labels = 0 := by
  exact mixedMoment_order_one B hB node3483 node3483Labels 1
    (by decide +kernel) (by decide +kernel)

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

theorem sound3467 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3467 node3467Labels = Sparse.eval nodeValue3467 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3467) = mixedMoment B node3467 node3467Labels := rfl
  simpa [nodeValue3467, Sparse.eval] using hc.symm

theorem sound3481 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3481 node3481Labels = Sparse.eval nodeValue3481 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3481) = mixedMoment B node3481 node3481Labels := rfl
  simpa [nodeValue3481, Sparse.eval] using hc.symm

theorem sound3482 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3482 node3482Labels = Sparse.eval nodeValue3482 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3482) = mixedMoment B node3482 node3482Labels := rfl
  simpa [nodeValue3482, Sparse.eval] using hc.symm

theorem sound3483 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3483 node3483Labels = Sparse.eval nodeValue3483 (mixedVector B) := by
  simpa only [nodeValue3483, Sparse.eval_nil] using zero3483 B _hB _hF

theorem sound3519 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3519 node3519Labels = Sparse.eval nodeValue3519 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3519) = mixedMoment B node3519 node3519Labels := rfl
  simpa [nodeValue3519, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros55
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero3520 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node3520 node3520Labels = 0 := by
  exact mixedMoment_alpha B hF node3520 node3520Labels 1 permutation446
    (by decide +kernel)

theorem zero3531 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node3531 node3531Labels = 0 := by
  exact mixedMoment_alpha B hF node3531 node3531Labels 1 permutation437
    (by decide +kernel)

theorem zero3546 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3546 node3546Labels = 0 := by
  exact mixedMoment_order_one B hB node3546 node3546Labels 1
    (by decide +kernel) (by decide +kernel)

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

theorem sound3520 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3520 node3520Labels = Sparse.eval nodeValue3520 (mixedVector B) := by
  simpa only [nodeValue3520, Sparse.eval_nil] using zero3520 B _hB _hF

theorem sound3521 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3521 node3521Labels = Sparse.eval nodeValue3521 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3521) = mixedMoment B node3521 node3521Labels := rfl
  simpa [nodeValue3521, Sparse.eval] using hc.symm

theorem sound3523 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3523 node3523Labels = Sparse.eval nodeValue3523 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3523) = mixedMoment B node3523 node3523Labels := rfl
  simpa [nodeValue3523, Sparse.eval] using hc.symm

theorem sound3529 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3529 node3529Labels = Sparse.eval nodeValue3529 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3529) = mixedMoment B node3529 node3529Labels := rfl
  simpa [nodeValue3529, Sparse.eval] using hc.symm

theorem sound3531 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3531 node3531Labels = Sparse.eval nodeValue3531 (mixedVector B) := by
  simpa only [nodeValue3531, Sparse.eval_nil] using zero3531 B _hB _hF

theorem sound3532 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3532 node3532Labels = Sparse.eval nodeValue3532 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3532) = mixedMoment B node3532 node3532Labels := rfl
  simpa [nodeValue3532, Sparse.eval] using hc.symm

theorem sound3542 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3542 node3542Labels = Sparse.eval nodeValue3542 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3542) = mixedMoment B node3542 node3542Labels := rfl
  simpa [nodeValue3542, Sparse.eval] using hc.symm

theorem sound3543 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3543 node3543Labels = Sparse.eval nodeValue3543 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3543) = mixedMoment B node3543 node3543Labels := rfl
  simpa [nodeValue3543, Sparse.eval] using hc.symm

theorem sound3544 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3544 node3544Labels = Sparse.eval nodeValue3544 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3544) = mixedMoment B node3544 node3544Labels := rfl
  simpa [nodeValue3544, Sparse.eval] using hc.symm

theorem sound3546 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3546 node3546Labels = Sparse.eval nodeValue3546 (mixedVector B) := by
  simpa only [nodeValue3546, Sparse.eval_nil] using zero3546 B _hB _hF

theorem sound3562 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3562 node3562Labels = Sparse.eval nodeValue3562 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3562) = mixedMoment B node3562 node3562Labels := rfl
  simpa [nodeValue3562, Sparse.eval] using hc.symm

theorem sound3578 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3578 node3578Labels = Sparse.eval nodeValue3578 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3578) = mixedMoment B node3578 node3578Labels := rfl
  simpa [nodeValue3578, Sparse.eval] using hc.symm

theorem sound3580 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3580 node3580Labels = Sparse.eval nodeValue3580 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3580) = mixedMoment B node3580 node3580Labels := rfl
  simpa [nodeValue3580, Sparse.eval] using hc.symm

theorem sound3581 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3581 node3581Labels = Sparse.eval nodeValue3581 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3581) = mixedMoment B node3581 node3581Labels := rfl
  simpa [nodeValue3581, Sparse.eval] using hc.symm

theorem sound3582 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3582 node3582Labels = Sparse.eval nodeValue3582 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3582) = mixedMoment B node3582 node3582Labels := rfl
  simpa [nodeValue3582, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound7
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound494 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node494 node494Labels = Sparse.eval nodeValue494 (mixedVector B) := by
  calc
    _ = Sparse.eval singlePairValue494 (familyPairVector B) := singlePair494 B _hB
    _ = _ := by norm_num [singlePairValue494, nodeValue494, Sparse.eval, mixedVector] <;> ring

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros59
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero3808 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3808 node3808Labels = 0 := by
  exact mixedMoment_order_one B hB node3808 node3808Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero3816 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3816 node3816Labels = 0 := by
  exact mixedMoment_order_one B hB node3816 node3816Labels 1
    (by decide +kernel) (by decide +kernel)

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

theorem sound3808 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3808 node3808Labels = Sparse.eval nodeValue3808 (mixedVector B) := by
  simpa only [nodeValue3808, Sparse.eval_nil] using zero3808 B _hB _hF

theorem sound3816 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3816 node3816Labels = Sparse.eval nodeValue3816 (mixedVector B) := by
  simpa only [nodeValue3816, Sparse.eval_nil] using zero3816 B _hB _hF

theorem sound3838 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3838 node3838Labels = Sparse.eval nodeValue3838 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3838) = mixedMoment B node3838 node3838Labels := rfl
  simpa [nodeValue3838, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros60
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero3859 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3859 node3859Labels = 0 := by
  exact mixedMoment_order_one B hB node3859 node3859Labels 1
    (by decide +kernel) (by decide +kernel)

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

theorem sound3843 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3843 node3843Labels = Sparse.eval nodeValue3843 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3843) = mixedMoment B node3843 node3843Labels := rfl
  simpa [nodeValue3843, Sparse.eval] using hc.symm

theorem sound3857 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3857 node3857Labels = Sparse.eval nodeValue3857 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3857) = mixedMoment B node3857 node3857Labels := rfl
  simpa [nodeValue3857, Sparse.eval] using hc.symm

theorem sound3858 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3858 node3858Labels = Sparse.eval nodeValue3858 (mixedVector B) := by
  have h := singleton3858 B _hB
  rw [sound494 B _hB _hF] at h
  norm_num [nodeValue3858, nodeValue494, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound3859 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3859 node3859Labels = Sparse.eval nodeValue3859 (mixedVector B) := by
  simpa only [nodeValue3859, Sparse.eval_nil] using zero3859 B _hB _hF

theorem sound3876 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3876 node3876Labels = Sparse.eval nodeValue3876 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3876) = mixedMoment B node3876 node3876Labels := rfl
  simpa [nodeValue3876, Sparse.eval] using hc.symm

theorem sound3902 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3902 node3902Labels = Sparse.eval nodeValue3902 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3902) = mixedMoment B node3902 node3902Labels := rfl
  simpa [nodeValue3902, Sparse.eval] using hc.symm

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

theorem zero3904 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3904 node3904Labels = 0 := by
  exact mixedMoment_order_one B hB node3904 node3904Labels 1
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

theorem sound3904 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3904 node3904Labels = Sparse.eval nodeValue3904 (mixedVector B) := by
  simpa only [nodeValue3904, Sparse.eval_nil] using zero3904 B _hB _hF

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

theorem sound4084 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4084 node4084Labels = Sparse.eval nodeValue4084 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4084) = mixedMoment B node4084 node4084Labels := rfl
  simpa [nodeValue4084, Sparse.eval] using hc.symm

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources17
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sourceEq571 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm571 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA571 + difference 2 0) (sourceB571 + difference 0 2) sourceC571) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1261) := by
    have ha : (tripleCharges (sourceA571 + difference 2 0) (sourceB571 + difference 0 2) sourceC571) = raw9581 := by
      apply Matrix.ext; unfold tripleCharges sourceA571 sourceB571 sourceC571 difference raw9581; decide +kernel
    rw [ha]
    exact (canonical9581 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA571 + difference 2 1) (sourceB571 + difference 1 2) sourceC571) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2632) := by
    have ha : (tripleCharges (sourceA571 + difference 2 1) (sourceB571 + difference 1 2) sourceC571) = raw9587 := by
      apply Matrix.ext; unfold tripleCharges sourceA571 sourceB571 sourceC571 difference raw9587; decide +kernel
    rw [ha]
    exact (canonical9587 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA571 + difference 2 2) (sourceB571 + difference 2 2) sourceC571) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2765) := by
    have ha : (tripleCharges (sourceA571 + difference 2 2) (sourceB571 + difference 2 2) sourceC571) = raw9575 := by
      apply Matrix.ext; unfold tripleCharges sourceA571 sourceB571 sourceC571 difference raw9575; decide +kernel
    rw [ha]
    exact (canonical9575 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA571 + difference 2 3) (sourceB571 + difference 3 2) sourceC571) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2566) := by
    have ha : (tripleCharges (sourceA571 + difference 2 3) (sourceB571 + difference 3 2) sourceC571) = raw9590 := by
      apply Matrix.ext; unfold tripleCharges sourceA571 sourceB571 sourceC571 difference raw9590; decide +kernel
    rw [ha]
    exact (canonical9590 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA571 + difference 2 4) (sourceB571 + difference 4 2) sourceC571) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2722) := by
    have ha : (tripleCharges (sourceA571 + difference 2 4) (sourceB571 + difference 4 2) sourceC571) = raw4921 := by
      apply Matrix.ext; unfold tripleCharges sourceA571 sourceB571 sourceC571 difference raw4921; decide +kernel
    rw [ha]
    exact (canonical4921 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA571 + difference 2 5) (sourceB571 + difference 5 2) sourceC571) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2763) := by
    have ha : (tripleCharges (sourceA571 + difference 2 5) (sourceB571 + difference 5 2) sourceC571) = raw9591 := by
      apply Matrix.ext; unfold tripleCharges sourceA571 sourceB571 sourceC571 difference raw9591; decide +kernel
    rw [ha]
    exact (canonical9591 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA571 + sourceB571) sourceC571) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA571 + sourceB571) sourceC571) = raw4905 := by
      apply Matrix.ext; unfold doubleCharges sourceA571 sourceB571 sourceC571 raw4905; decide +kernel
    rw [ha]
    exact (canonical4905 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA571 sourceB571 sourceC571
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm571, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources18
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sourceEq577 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm577 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA577 + difference 0 0) (sourceB577 + difference 0 0) sourceC577) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3582) := by
    have ha : (tripleCharges (sourceA577 + difference 0 0) (sourceB577 + difference 0 0) sourceC577) = raw9724 := by
      apply Matrix.ext; unfold tripleCharges sourceA577 sourceB577 sourceC577 difference raw9724; decide +kernel
    rw [ha]
    exact (canonical9724 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA577 + difference 1 0) (sourceB577 + difference 0 1) sourceC577) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2115) := by
    have ha : (tripleCharges (sourceA577 + difference 1 0) (sourceB577 + difference 0 1) sourceC577) = raw9725 := by
      apply Matrix.ext; unfold tripleCharges sourceA577 sourceB577 sourceC577 difference raw9725; decide +kernel
    rw [ha]
    exact (canonical9725 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA577 + difference 2 0) (sourceB577 + difference 0 2) sourceC577) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2106) := by
    have ha : (tripleCharges (sourceA577 + difference 2 0) (sourceB577 + difference 0 2) sourceC577) = raw9726 := by
      apply Matrix.ext; unfold tripleCharges sourceA577 sourceB577 sourceC577 difference raw9726; decide +kernel
    rw [ha]
    exact (canonical9726 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA577 + difference 3 0) (sourceB577 + difference 0 3) sourceC577) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2106) := by
    have ha : (tripleCharges (sourceA577 + difference 3 0) (sourceB577 + difference 0 3) sourceC577) = raw9727 := by
      apply Matrix.ext; unfold tripleCharges sourceA577 sourceB577 sourceC577 difference raw9727; decide +kernel
    rw [ha]
    exact (canonical9727 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA577 + difference 4 0) (sourceB577 + difference 0 4) sourceC577) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2264) := by
    have ha : (tripleCharges (sourceA577 + difference 4 0) (sourceB577 + difference 0 4) sourceC577) = raw9728 := by
      apply Matrix.ext; unfold tripleCharges sourceA577 sourceB577 sourceC577 difference raw9728; decide +kernel
    rw [ha]
    exact (canonical9728 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA577 + difference 5 0) (sourceB577 + difference 0 5) sourceC577) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2109) := by
    have ha : (tripleCharges (sourceA577 + difference 5 0) (sourceB577 + difference 0 5) sourceC577) = raw9729 := by
      apply Matrix.ext; unfold tripleCharges sourceA577 sourceB577 sourceC577 difference raw9729; decide +kernel
    rw [ha]
    exact (canonical9729 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA577 + sourceB577) sourceC577) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA577 + sourceB577) sourceC577) = raw5754 := by
      apply Matrix.ext; unfold doubleCharges sourceA577 sourceB577 sourceC577 raw5754; decide +kernel
    rw [ha]
    exact (canonical5754 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA577 sourceB577 sourceC577
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm577, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq580 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm580 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA580 + difference 0 1) (sourceB580 + difference 1 0) sourceC580) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3857) := by
    have ha : (tripleCharges (sourceA580 + difference 0 1) (sourceB580 + difference 1 0) sourceC580) = raw9790 := by
      apply Matrix.ext; unfold tripleCharges sourceA580 sourceB580 sourceC580 difference raw9790; decide +kernel
    rw [ha]
    exact (canonical9790 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA580 + difference 0 2) (sourceB580 + difference 2 0) sourceC580) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3843) := by
    have ha : (tripleCharges (sourceA580 + difference 0 2) (sourceB580 + difference 2 0) sourceC580) = raw9791 := by
      apply Matrix.ext; unfold tripleCharges sourceA580 sourceB580 sourceC580 difference raw9791; decide +kernel
    rw [ha]
    exact (canonical9791 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA580 + difference 0 3) (sourceB580 + difference 3 0) sourceC580) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3816) := by
    have ha : (tripleCharges (sourceA580 + difference 0 3) (sourceB580 + difference 3 0) sourceC580) = raw9792 := by
      apply Matrix.ext; unfold tripleCharges sourceA580 sourceB580 sourceC580 difference raw9792; decide +kernel
    rw [ha]
    exact (canonical9792 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA580 + difference 0 4) (sourceB580 + difference 4 0) sourceC580) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3858) := by
    have ha : (tripleCharges (sourceA580 + difference 0 4) (sourceB580 + difference 4 0) sourceC580) = raw9793 := by
      apply Matrix.ext; unfold tripleCharges sourceA580 sourceB580 sourceC580 difference raw9793; decide +kernel
    rw [ha]
    exact (canonical9793 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA580 + difference 0 5) (sourceB580 + difference 5 0) sourceC580) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3859) := by
    have ha : (tripleCharges (sourceA580 + difference 0 5) (sourceB580 + difference 5 0) sourceC580) = raw9794 := by
      apply Matrix.ext; unfold tripleCharges sourceA580 sourceB580 sourceC580 difference raw9794; decide +kernel
    rw [ha]
    exact (canonical9794 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA580 + difference 1 0) (sourceB580 + difference 0 1) sourceC580) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3299) := by
    have ha : (tripleCharges (sourceA580 + difference 1 0) (sourceB580 + difference 0 1) sourceC580) = raw9795 := by
      apply Matrix.ext; unfold tripleCharges sourceA580 sourceB580 sourceC580 difference raw9795; decide +kernel
    rw [ha]
    exact (canonical9795 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA580 + difference 1 2) (sourceB580 + difference 2 1) sourceC580) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3521) := by
    have ha : (tripleCharges (sourceA580 + difference 1 2) (sourceB580 + difference 2 1) sourceC580) = raw9796 := by
      apply Matrix.ext; unfold tripleCharges sourceA580 sourceB580 sourceC580 difference raw9796; decide +kernel
    rw [ha]
    exact (canonical9796 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA580 + difference 1 3) (sourceB580 + difference 3 1) sourceC580) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3483) := by
    have ha : (tripleCharges (sourceA580 + difference 1 3) (sourceB580 + difference 3 1) sourceC580) = raw9797 := by
      apply Matrix.ext; unfold tripleCharges sourceA580 sourceB580 sourceC580 difference raw9797; decide +kernel
    rw [ha]
    exact (canonical9797 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA580 + difference 1 4) (sourceB580 + difference 4 1) sourceC580) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3544) := by
    have ha : (tripleCharges (sourceA580 + difference 1 4) (sourceB580 + difference 4 1) sourceC580) = raw9798 := by
      apply Matrix.ext; unfold tripleCharges sourceA580 sourceB580 sourceC580 difference raw9798; decide +kernel
    rw [ha]
    exact (canonical9798 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA580 + difference 1 5) (sourceB580 + difference 5 1) sourceC580) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3546) := by
    have ha : (tripleCharges (sourceA580 + difference 1 5) (sourceB580 + difference 5 1) sourceC580) = raw9799 := by
      apply Matrix.ext; unfold tripleCharges sourceA580 sourceB580 sourceC580 difference raw9799; decide +kernel
    rw [ha]
    exact (canonical9799 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA580 + difference 2 0) (sourceB580 + difference 0 2) sourceC580) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3290) := by
    have ha : (tripleCharges (sourceA580 + difference 2 0) (sourceB580 + difference 0 2) sourceC580) = raw9800 := by
      apply Matrix.ext; unfold tripleCharges sourceA580 sourceB580 sourceC580 difference raw9800; decide +kernel
    rw [ha]
    exact (canonical9800 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA580 + difference 2 1) (sourceB580 + difference 1 2) sourceC580) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3529) := by
    have ha : (tripleCharges (sourceA580 + difference 2 1) (sourceB580 + difference 1 2) sourceC580) = raw9801 := by
      apply Matrix.ext; unfold tripleCharges sourceA580 sourceB580 sourceC580 difference raw9801; decide +kernel
    rw [ha]
    exact (canonical9801 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA580 + difference 2 3) (sourceB580 + difference 3 2) sourceC580) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3467) := by
    have ha : (tripleCharges (sourceA580 + difference 2 3) (sourceB580 + difference 3 2) sourceC580) = raw9802 := by
      apply Matrix.ext; unfold tripleCharges sourceA580 sourceB580 sourceC580 difference raw9802; decide +kernel
    rw [ha]
    exact (canonical9802 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA580 + difference 2 4) (sourceB580 + difference 4 2) sourceC580) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3531) := by
    have ha : (tripleCharges (sourceA580 + difference 2 4) (sourceB580 + difference 4 2) sourceC580) = raw9803 := by
      apply Matrix.ext; unfold tripleCharges sourceA580 sourceB580 sourceC580 difference raw9803; decide +kernel
    rw [ha]
    exact (canonical9803 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA580 + difference 2 5) (sourceB580 + difference 5 2) sourceC580) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3532) := by
    have ha : (tripleCharges (sourceA580 + difference 2 5) (sourceB580 + difference 5 2) sourceC580) = raw9804 := by
      apply Matrix.ext; unfold tripleCharges sourceA580 sourceB580 sourceC580 difference raw9804; decide +kernel
    rw [ha]
    exact (canonical9804 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA580 + difference 3 0) (sourceB580 + difference 0 3) sourceC580) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3294) := by
    have ha : (tripleCharges (sourceA580 + difference 3 0) (sourceB580 + difference 0 3) sourceC580) = raw9805 := by
      apply Matrix.ext; unfold tripleCharges sourceA580 sourceB580 sourceC580 difference raw9805; decide +kernel
    rw [ha]
    exact (canonical9805 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA580 + difference 3 1) (sourceB580 + difference 1 3) sourceC580) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3578) := by
    have ha : (tripleCharges (sourceA580 + difference 3 1) (sourceB580 + difference 1 3) sourceC580) = raw9806 := by
      apply Matrix.ext; unfold tripleCharges sourceA580 sourceB580 sourceC580 difference raw9806; decide +kernel
    rw [ha]
    exact (canonical9806 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA580 + difference 3 2) (sourceB580 + difference 2 3) sourceC580) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3562) := by
    have ha : (tripleCharges (sourceA580 + difference 3 2) (sourceB580 + difference 2 3) sourceC580) = raw9807 := by
      apply Matrix.ext; unfold tripleCharges sourceA580 sourceB580 sourceC580 difference raw9807; decide +kernel
    rw [ha]
    exact (canonical9807 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA580 + difference 3 4) (sourceB580 + difference 4 3) sourceC580) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3580) := by
    have ha : (tripleCharges (sourceA580 + difference 3 4) (sourceB580 + difference 4 3) sourceC580) = raw9808 := by
      apply Matrix.ext; unfold tripleCharges sourceA580 sourceB580 sourceC580 difference raw9808; decide +kernel
    rw [ha]
    exact (canonical9808 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA580 + difference 3 5) (sourceB580 + difference 5 3) sourceC580) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3581) := by
    have ha : (tripleCharges (sourceA580 + difference 3 5) (sourceB580 + difference 5 3) sourceC580) = raw9809 := by
      apply Matrix.ext; unfold tripleCharges sourceA580 sourceB580 sourceC580 difference raw9809; decide +kernel
    rw [ha]
    exact (canonical9809 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA580 + difference 4 0) (sourceB580 + difference 0 4) sourceC580) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3297) := by
    have ha : (tripleCharges (sourceA580 + difference 4 0) (sourceB580 + difference 0 4) sourceC580) = raw9810 := by
      apply Matrix.ext; unfold tripleCharges sourceA580 sourceB580 sourceC580 difference raw9810; decide +kernel
    rw [ha]
    exact (canonical9810 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA580 + difference 4 1) (sourceB580 + difference 1 4) sourceC580) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3542) := by
    have ha : (tripleCharges (sourceA580 + difference 4 1) (sourceB580 + difference 1 4) sourceC580) = raw9811 := by
      apply Matrix.ext; unfold tripleCharges sourceA580 sourceB580 sourceC580 difference raw9811; decide +kernel
    rw [ha]
    exact (canonical9811 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA580 + difference 4 2) (sourceB580 + difference 2 4) sourceC580) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3520) := by
    have ha : (tripleCharges (sourceA580 + difference 4 2) (sourceB580 + difference 2 4) sourceC580) = raw9812 := by
      apply Matrix.ext; unfold tripleCharges sourceA580 sourceB580 sourceC580 difference raw9812; decide +kernel
    rw [ha]
    exact (canonical9812 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA580 + difference 4 3) (sourceB580 + difference 3 4) sourceC580) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3482) := by
    have ha : (tripleCharges (sourceA580 + difference 4 3) (sourceB580 + difference 3 4) sourceC580) = raw9813 := by
      apply Matrix.ext; unfold tripleCharges sourceA580 sourceB580 sourceC580 difference raw9813; decide +kernel
    rw [ha]
    exact (canonical9813 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA580 + difference 4 5) (sourceB580 + difference 5 4) sourceC580) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3544) := by
    have ha : (tripleCharges (sourceA580 + difference 4 5) (sourceB580 + difference 5 4) sourceC580) = raw9814 := by
      apply Matrix.ext; unfold tripleCharges sourceA580 sourceB580 sourceC580 difference raw9814; decide +kernel
    rw [ha]
    exact (canonical9814 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA580 + difference 5 0) (sourceB580 + difference 0 5) sourceC580) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3291) := by
    have ha : (tripleCharges (sourceA580 + difference 5 0) (sourceB580 + difference 0 5) sourceC580) = raw9815 := by
      apply Matrix.ext; unfold tripleCharges sourceA580 sourceB580 sourceC580 difference raw9815; decide +kernel
    rw [ha]
    exact (canonical9815 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA580 + difference 5 1) (sourceB580 + difference 1 5) sourceC580) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3523) := by
    have ha : (tripleCharges (sourceA580 + difference 5 1) (sourceB580 + difference 1 5) sourceC580) = raw9816 := by
      apply Matrix.ext; unfold tripleCharges sourceA580 sourceB580 sourceC580 difference raw9816; decide +kernel
    rw [ha]
    exact (canonical9816 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA580 + difference 5 2) (sourceB580 + difference 2 5) sourceC580) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3519) := by
    have ha : (tripleCharges (sourceA580 + difference 5 2) (sourceB580 + difference 2 5) sourceC580) = raw9817 := by
      apply Matrix.ext; unfold tripleCharges sourceA580 sourceB580 sourceC580 difference raw9817; decide +kernel
    rw [ha]
    exact (canonical9817 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA580 + difference 5 3) (sourceB580 + difference 3 5) sourceC580) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3481) := by
    have ha : (tripleCharges (sourceA580 + difference 5 3) (sourceB580 + difference 3 5) sourceC580) = raw9818 := by
      apply Matrix.ext; unfold tripleCharges sourceA580 sourceB580 sourceC580 difference raw9818; decide +kernel
    rw [ha]
    exact (canonical9818 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA580 + difference 5 4) (sourceB580 + difference 4 5) sourceC580) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3543) := by
    have ha : (tripleCharges (sourceA580 + difference 5 4) (sourceB580 + difference 4 5) sourceC580) = raw9819 := by
      apply Matrix.ext; unfold tripleCharges sourceA580 sourceB580 sourceC580 difference raw9819; decide +kernel
    rw [ha]
    exact (canonical9819 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA580 sourceB580 sourceC580
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm580, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq581 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm581 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA581 + difference 0 0) (sourceB581 + difference 0 0) sourceC581) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2723) := by
    have ha : (tripleCharges (sourceA581 + difference 0 0) (sourceB581 + difference 0 0) sourceC581) = raw9820 := by
      apply Matrix.ext; unfold tripleCharges sourceA581 sourceB581 sourceC581 difference raw9820; decide +kernel
    rw [ha]
    exact (canonical9820 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA581 + difference 0 1) (sourceB581 + difference 1 0) sourceC581) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3876) := by
    have ha : (tripleCharges (sourceA581 + difference 0 1) (sourceB581 + difference 1 0) sourceC581) = raw9821 := by
      apply Matrix.ext; unfold tripleCharges sourceA581 sourceB581 sourceC581 difference raw9821; decide +kernel
    rw [ha]
    exact (canonical9821 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA581 + difference 0 2) (sourceB581 + difference 2 0) sourceC581) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3838) := by
    have ha : (tripleCharges (sourceA581 + difference 0 2) (sourceB581 + difference 2 0) sourceC581) = raw9822 := by
      apply Matrix.ext; unfold tripleCharges sourceA581 sourceB581 sourceC581 difference raw9822; decide +kernel
    rw [ha]
    exact (canonical9822 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA581 + difference 0 3) (sourceB581 + difference 3 0) sourceC581) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3808) := by
    have ha : (tripleCharges (sourceA581 + difference 0 3) (sourceB581 + difference 3 0) sourceC581) = raw9823 := by
      apply Matrix.ext; unfold tripleCharges sourceA581 sourceB581 sourceC581 difference raw9823; decide +kernel
    rw [ha]
    exact (canonical9823 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA581 + difference 0 4) (sourceB581 + difference 4 0) sourceC581) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3902) := by
    have ha : (tripleCharges (sourceA581 + difference 0 4) (sourceB581 + difference 4 0) sourceC581) = raw9824 := by
      apply Matrix.ext; unfold tripleCharges sourceA581 sourceB581 sourceC581 difference raw9824; decide +kernel
    rw [ha]
    exact (canonical9824 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA581 + difference 0 5) (sourceB581 + difference 5 0) sourceC581) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3904) := by
    have ha : (tripleCharges (sourceA581 + difference 0 5) (sourceB581 + difference 5 0) sourceC581) = raw9825 := by
      apply Matrix.ext; unfold tripleCharges sourceA581 sourceB581 sourceC581 difference raw9825; decide +kernel
    rw [ha]
    exact (canonical9825 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA581 + sourceB581) sourceC581) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA581 + sourceB581) sourceC581) = raw9826 := by
      apply Matrix.ext; unfold doubleCharges sourceA581 sourceB581 sourceC581 raw9826; decide +kernel
    rw [ha]
    exact (canonical9826 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA581 sourceB581 sourceC581
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm581, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq582 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm582 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA582 + difference 0 0) (sourceB582 + difference 0 0) sourceC582) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2723) := by
    have ha : (tripleCharges (sourceA582 + difference 0 0) (sourceB582 + difference 0 0) sourceC582) = raw9820 := by
      apply Matrix.ext; unfold tripleCharges sourceA582 sourceB582 sourceC582 difference raw9820; decide +kernel
    rw [ha]
    exact (canonical9820 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA582 + difference 1 0) (sourceB582 + difference 0 1) sourceC582) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1240) := by
    have ha : (tripleCharges (sourceA582 + difference 1 0) (sourceB582 + difference 0 1) sourceC582) = raw9827 := by
      apply Matrix.ext; unfold tripleCharges sourceA582 sourceB582 sourceC582 difference raw9827; decide +kernel
    rw [ha]
    exact (canonical9827 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA582 + difference 2 0) (sourceB582 + difference 0 2) sourceC582) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1213) := by
    have ha : (tripleCharges (sourceA582 + difference 2 0) (sourceB582 + difference 0 2) sourceC582) = raw9828 := by
      apply Matrix.ext; unfold tripleCharges sourceA582 sourceB582 sourceC582 difference raw9828; decide +kernel
    rw [ha]
    exact (canonical9828 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA582 + difference 3 0) (sourceB582 + difference 0 3) sourceC582) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1262) := by
    have ha : (tripleCharges (sourceA582 + difference 3 0) (sourceB582 + difference 0 3) sourceC582) = raw9829 := by
      apply Matrix.ext; unfold tripleCharges sourceA582 sourceB582 sourceC582 difference raw9829; decide +kernel
    rw [ha]
    exact (canonical9829 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA582 + difference 4 0) (sourceB582 + difference 0 4) sourceC582) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1220) := by
    have ha : (tripleCharges (sourceA582 + difference 4 0) (sourceB582 + difference 0 4) sourceC582) = raw9830 := by
      apply Matrix.ext; unfold tripleCharges sourceA582 sourceB582 sourceC582 difference raw9830; decide +kernel
    rw [ha]
    exact (canonical9830 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA582 + difference 5 0) (sourceB582 + difference 0 5) sourceC582) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1217) := by
    have ha : (tripleCharges (sourceA582 + difference 5 0) (sourceB582 + difference 0 5) sourceC582) = raw9831 := by
      apply Matrix.ext; unfold tripleCharges sourceA582 sourceB582 sourceC582 difference raw9831; decide +kernel
    rw [ha]
    exact (canonical9831 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA582 + sourceB582) sourceC582) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA582 + sourceB582) sourceC582) = raw9826 := by
      apply Matrix.ext; unfold doubleCharges sourceA582 sourceB582 sourceC582 raw9826; decide +kernel
    rw [ha]
    exact (canonical9826 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA582 sourceB582 sourceC582
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm582, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq583 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm583 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA583 + difference 1 0) (sourceB583 + difference 0 1) sourceC583) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1240) := by
    have ha : (tripleCharges (sourceA583 + difference 1 0) (sourceB583 + difference 0 1) sourceC583) = raw9827 := by
      apply Matrix.ext; unfold tripleCharges sourceA583 sourceB583 sourceC583 difference raw9827; decide +kernel
    rw [ha]
    exact (canonical9827 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA583 + difference 1 1) (sourceB583 + difference 1 1) sourceC583) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2723) := by
    have ha : (tripleCharges (sourceA583 + difference 1 1) (sourceB583 + difference 1 1) sourceC583) = raw9820 := by
      apply Matrix.ext; unfold tripleCharges sourceA583 sourceB583 sourceC583 difference raw9820; decide +kernel
    rw [ha]
    exact (canonical9820 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA583 + difference 1 2) (sourceB583 + difference 2 1) sourceC583) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2556) := by
    have ha : (tripleCharges (sourceA583 + difference 1 2) (sourceB583 + difference 2 1) sourceC583) = raw9832 := by
      apply Matrix.ext; unfold tripleCharges sourceA583 sourceB583 sourceC583 difference raw9832; decide +kernel
    rw [ha]
    exact (canonical9832 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA583 + difference 1 3) (sourceB583 + difference 3 1) sourceC583) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2514) := by
    have ha : (tripleCharges (sourceA583 + difference 1 3) (sourceB583 + difference 3 1) sourceC583) = raw9833 := by
      apply Matrix.ext; unfold tripleCharges sourceA583 sourceB583 sourceC583 difference raw9833; decide +kernel
    rw [ha]
    exact (canonical9833 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA583 + difference 1 4) (sourceB583 + difference 4 1) sourceC583) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2723) := by
    have ha : (tripleCharges (sourceA583 + difference 1 4) (sourceB583 + difference 4 1) sourceC583) = raw9834 := by
      apply Matrix.ext; unfold tripleCharges sourceA583 sourceB583 sourceC583 difference raw9834; decide +kernel
    rw [ha]
    exact (canonical9834 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA583 + difference 1 5) (sourceB583 + difference 5 1) sourceC583) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2741) := by
    have ha : (tripleCharges (sourceA583 + difference 1 5) (sourceB583 + difference 5 1) sourceC583) = raw9835 := by
      apply Matrix.ext; unfold tripleCharges sourceA583 sourceB583 sourceC583 difference raw9835; decide +kernel
    rw [ha]
    exact (canonical9835 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA583 + sourceB583) sourceC583) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA583 + sourceB583) sourceC583) = raw9826 := by
      apply Matrix.ext; unfold doubleCharges sourceA583 sourceB583 sourceC583 raw9826; decide +kernel
    rw [ha]
    exact (canonical9826 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA583 sourceB583 sourceC583
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm583, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq584 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm584 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA584 + difference 0 1) (sourceB584 + difference 1 0) sourceC584) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3876) := by
    have ha : (tripleCharges (sourceA584 + difference 0 1) (sourceB584 + difference 1 0) sourceC584) = raw9821 := by
      apply Matrix.ext; unfold tripleCharges sourceA584 sourceB584 sourceC584 difference raw9821; decide +kernel
    rw [ha]
    exact (canonical9821 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA584 + difference 1 1) (sourceB584 + difference 1 1) sourceC584) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2723) := by
    have ha : (tripleCharges (sourceA584 + difference 1 1) (sourceB584 + difference 1 1) sourceC584) = raw9820 := by
      apply Matrix.ext; unfold tripleCharges sourceA584 sourceB584 sourceC584 difference raw9820; decide +kernel
    rw [ha]
    exact (canonical9820 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA584 + difference 2 1) (sourceB584 + difference 1 2) sourceC584) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2615) := by
    have ha : (tripleCharges (sourceA584 + difference 2 1) (sourceB584 + difference 1 2) sourceC584) = raw9836 := by
      apply Matrix.ext; unfold tripleCharges sourceA584 sourceB584 sourceC584 difference raw9836; decide +kernel
    rw [ha]
    exact (canonical9836 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA584 + difference 3 1) (sourceB584 + difference 1 3) sourceC584) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2633) := by
    have ha : (tripleCharges (sourceA584 + difference 3 1) (sourceB584 + difference 1 3) sourceC584) = raw9837 := by
      apply Matrix.ext; unfold tripleCharges sourceA584 sourceB584 sourceC584 difference raw9837; decide +kernel
    rw [ha]
    exact (canonical9837 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA584 + difference 4 1) (sourceB584 + difference 1 4) sourceC584) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2621) := by
    have ha : (tripleCharges (sourceA584 + difference 4 1) (sourceB584 + difference 1 4) sourceC584) = raw9838 := by
      apply Matrix.ext; unfold tripleCharges sourceA584 sourceB584 sourceC584 difference raw9838; decide +kernel
    rw [ha]
    exact (canonical9838 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA584 + difference 5 1) (sourceB584 + difference 1 5) sourceC584) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2618) := by
    have ha : (tripleCharges (sourceA584 + difference 5 1) (sourceB584 + difference 1 5) sourceC584) = raw9839 := by
      apply Matrix.ext; unfold tripleCharges sourceA584 sourceB584 sourceC584 difference raw9839; decide +kernel
    rw [ha]
    exact (canonical9839 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA584 + sourceB584) sourceC584) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA584 + sourceB584) sourceC584) = raw9826 := by
      apply Matrix.ext; unfold doubleCharges sourceA584 sourceB584 sourceC584 raw9826; decide +kernel
    rw [ha]
    exact (canonical9826 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA584 sourceB584 sourceC584
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm584, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq585 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm585 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA585 + difference 0 2) (sourceB585 + difference 2 0) sourceC585) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3838) := by
    have ha : (tripleCharges (sourceA585 + difference 0 2) (sourceB585 + difference 2 0) sourceC585) = raw9822 := by
      apply Matrix.ext; unfold tripleCharges sourceA585 sourceB585 sourceC585 difference raw9822; decide +kernel
    rw [ha]
    exact (canonical9822 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA585 + difference 1 2) (sourceB585 + difference 2 1) sourceC585) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2556) := by
    have ha : (tripleCharges (sourceA585 + difference 1 2) (sourceB585 + difference 2 1) sourceC585) = raw9832 := by
      apply Matrix.ext; unfold tripleCharges sourceA585 sourceB585 sourceC585 difference raw9832; decide +kernel
    rw [ha]
    exact (canonical9832 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA585 + difference 2 2) (sourceB585 + difference 2 2) sourceC585) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2723) := by
    have ha : (tripleCharges (sourceA585 + difference 2 2) (sourceB585 + difference 2 2) sourceC585) = raw9820 := by
      apply Matrix.ext; unfold tripleCharges sourceA585 sourceB585 sourceC585 difference raw9820; decide +kernel
    rw [ha]
    exact (canonical9820 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA585 + difference 3 2) (sourceB585 + difference 2 3) sourceC585) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2567) := by
    have ha : (tripleCharges (sourceA585 + difference 3 2) (sourceB585 + difference 2 3) sourceC585) = raw9840 := by
      apply Matrix.ext; unfold tripleCharges sourceA585 sourceB585 sourceC585 difference raw9840; decide +kernel
    rw [ha]
    exact (canonical9840 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA585 + difference 4 2) (sourceB585 + difference 2 4) sourceC585) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2546) := by
    have ha : (tripleCharges (sourceA585 + difference 4 2) (sourceB585 + difference 2 4) sourceC585) = raw9841 := by
      apply Matrix.ext; unfold tripleCharges sourceA585 sourceB585 sourceC585 difference raw9841; decide +kernel
    rw [ha]
    exact (canonical9841 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA585 + difference 5 2) (sourceB585 + difference 2 5) sourceC585) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2543) := by
    have ha : (tripleCharges (sourceA585 + difference 5 2) (sourceB585 + difference 2 5) sourceC585) = raw9842 := by
      apply Matrix.ext; unfold tripleCharges sourceA585 sourceB585 sourceC585 difference raw9842; decide +kernel
    rw [ha]
    exact (canonical9842 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA585 + sourceB585) sourceC585) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA585 + sourceB585) sourceC585) = raw9826 := by
      apply Matrix.ext; unfold doubleCharges sourceA585 sourceB585 sourceC585 raw9826; decide +kernel
    rw [ha]
    exact (canonical9826 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA585 sourceB585 sourceC585
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm585, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq586 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm586 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA586 + difference 0 3) (sourceB586 + difference 3 0) sourceC586) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3808) := by
    have ha : (tripleCharges (sourceA586 + difference 0 3) (sourceB586 + difference 3 0) sourceC586) = raw9823 := by
      apply Matrix.ext; unfold tripleCharges sourceA586 sourceB586 sourceC586 difference raw9823; decide +kernel
    rw [ha]
    exact (canonical9823 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA586 + difference 1 3) (sourceB586 + difference 3 1) sourceC586) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2514) := by
    have ha : (tripleCharges (sourceA586 + difference 1 3) (sourceB586 + difference 3 1) sourceC586) = raw9833 := by
      apply Matrix.ext; unfold tripleCharges sourceA586 sourceB586 sourceC586 difference raw9833; decide +kernel
    rw [ha]
    exact (canonical9833 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA586 + difference 2 3) (sourceB586 + difference 3 2) sourceC586) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2480) := by
    have ha : (tripleCharges (sourceA586 + difference 2 3) (sourceB586 + difference 3 2) sourceC586) = raw9843 := by
      apply Matrix.ext; unfold tripleCharges sourceA586 sourceB586 sourceC586 difference raw9843; decide +kernel
    rw [ha]
    exact (canonical9843 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA586 + difference 3 3) (sourceB586 + difference 3 3) sourceC586) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2723) := by
    have ha : (tripleCharges (sourceA586 + difference 3 3) (sourceB586 + difference 3 3) sourceC586) = raw9820 := by
      apply Matrix.ext; unfold tripleCharges sourceA586 sourceB586 sourceC586 difference raw9820; decide +kernel
    rw [ha]
    exact (canonical9820 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA586 + difference 4 3) (sourceB586 + difference 3 4) sourceC586) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2489) := by
    have ha : (tripleCharges (sourceA586 + difference 4 3) (sourceB586 + difference 3 4) sourceC586) = raw9844 := by
      apply Matrix.ext; unfold tripleCharges sourceA586 sourceB586 sourceC586 difference raw9844; decide +kernel
    rw [ha]
    exact (canonical9844 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA586 + difference 5 3) (sourceB586 + difference 3 5) sourceC586) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2485) := by
    have ha : (tripleCharges (sourceA586 + difference 5 3) (sourceB586 + difference 3 5) sourceC586) = raw9845 := by
      apply Matrix.ext; unfold tripleCharges sourceA586 sourceB586 sourceC586 difference raw9845; decide +kernel
    rw [ha]
    exact (canonical9845 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA586 + sourceB586) sourceC586) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA586 + sourceB586) sourceC586) = raw9826 := by
      apply Matrix.ext; unfold doubleCharges sourceA586 sourceB586 sourceC586 raw9826; decide +kernel
    rw [ha]
    exact (canonical9826 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA586 sourceB586 sourceC586
    (0 : Fin 2) 1 (3 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm586, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic30
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reindexCheck480 : Integer.Sparse.reindex keyMap MixedData.row480 = numericRow480 := by decide +kernel

theorem numericCheck480 (x : Master → ℝ) : Integer.Sparse.eval numericRow480 x =
    (1 : ℝ) * reducedSource480 x := by
  norm_num [numericRow480, reducedSource480, Integer.Sparse.eval, Sparse.eval, nodeValue1261, nodeValue2566, nodeValue2632, nodeValue2722, nodeValue2763, nodeValue2765, nodeValue4092]

theorem reindexCheck486 : Integer.Sparse.reindex keyMap MixedData.row486 = numericRow486 := by decide +kernel

theorem numericCheck486 (x : Master → ℝ) : Integer.Sparse.eval numericRow486 x =
    (1 : ℝ) * reducedSource486 x := by
  norm_num [numericRow486, reducedSource486, Integer.Sparse.eval, Sparse.eval, nodeValue2106, nodeValue2109, nodeValue2115, nodeValue2264, nodeValue3582, nodeValue4084]

theorem reindexCheck488 : Integer.Sparse.reindex keyMap MixedData.row488 = numericRow488 := by decide +kernel

theorem numericCheck488 (x : Master → ℝ) : Integer.Sparse.eval numericRow488 x =
    (1080 : ℝ) * reducedSource488 x := by
  norm_num [numericRow488, reducedSource488, Integer.Sparse.eval, Sparse.eval, nodeValue1213, nodeValue1215, nodeValue1220, nodeValue1237, nodeValue1266, nodeValue2543, nodeValue2558, nodeValue2572, nodeValue2712, nodeValue2862, nodeValue2868, nodeValue2882, nodeValue2917, nodeValue2925, nodeValue2936, nodeValue2987, nodeValue2991, nodeValue3000, nodeValue3065, nodeValue3078, nodeValue3087, nodeValue3088, nodeValue3099, nodeValue3111, nodeValue3990, nodeValue3993, nodeValue3996, nodeValue4012, nodeValue4036]
  ring

theorem reindexCheck489 : Integer.Sparse.reindex keyMap MixedData.row489 = numericRow489 := by decide +kernel

theorem numericCheck489 (x : Master → ℝ) : Integer.Sparse.eval numericRow489 x =
    (4320 : ℝ) * reducedSource489 x := by
  norm_num [numericRow489, reducedSource489, Integer.Sparse.eval, Sparse.eval, nodeValue3290, nodeValue3291, nodeValue3294, nodeValue3297, nodeValue3299, nodeValue3467, nodeValue3481, nodeValue3482, nodeValue3483, nodeValue3519, nodeValue3520, nodeValue3521, nodeValue3523, nodeValue3529, nodeValue3531, nodeValue3532, nodeValue3542, nodeValue3543, nodeValue3544, nodeValue3546, nodeValue3562, nodeValue3578, nodeValue3580, nodeValue3581, nodeValue3816, nodeValue3843, nodeValue3857, nodeValue3858, nodeValue3859]
  ring

theorem reindexCheck490 : Integer.Sparse.reindex keyMap MixedData.row490 = numericRow490 := by decide +kernel

theorem numericCheck490 (x : Master → ℝ) : Integer.Sparse.eval numericRow490 x =
    (1 : ℝ) * reducedSource490 x := by
  norm_num [numericRow490, reducedSource490, Integer.Sparse.eval, Sparse.eval, nodeValue2723, nodeValue3808, nodeValue3838, nodeValue3876, nodeValue3902, nodeValue3904, nodeValue4091]

theorem reindexCheck491 : Integer.Sparse.reindex keyMap MixedData.row491 = numericRow491 := by decide +kernel

theorem numericCheck491 (x : Master → ℝ) : Integer.Sparse.eval numericRow491 x =
    (1 : ℝ) * reducedSource491 x := by
  norm_num [numericRow491, reducedSource491, Integer.Sparse.eval, Sparse.eval, nodeValue1213, nodeValue1217, nodeValue1220, nodeValue1240, nodeValue1262, nodeValue2723, nodeValue4091]

theorem reindexCheck492 : Integer.Sparse.reindex keyMap MixedData.row492 = numericRow492 := by decide +kernel

theorem numericCheck492 (x : Master → ℝ) : Integer.Sparse.eval numericRow492 x =
    (1 : ℝ) * reducedSource492 x := by
  norm_num [numericRow492, reducedSource492, Integer.Sparse.eval, Sparse.eval, nodeValue1240, nodeValue2514, nodeValue2556, nodeValue2723, nodeValue2741, nodeValue4091]

theorem reindexCheck493 : Integer.Sparse.reindex keyMap MixedData.row493 = numericRow493 := by decide +kernel

theorem numericCheck493 (x : Master → ℝ) : Integer.Sparse.eval numericRow493 x =
    (1 : ℝ) * reducedSource493 x := by
  norm_num [numericRow493, reducedSource493, Integer.Sparse.eval, Sparse.eval, nodeValue2615, nodeValue2618, nodeValue2621, nodeValue2633, nodeValue2723, nodeValue3876, nodeValue4091]

theorem reindexCheck494 : Integer.Sparse.reindex keyMap MixedData.row494 = numericRow494 := by decide +kernel

theorem numericCheck494 (x : Master → ℝ) : Integer.Sparse.eval numericRow494 x =
    (1 : ℝ) * reducedSource494 x := by
  norm_num [numericRow494, reducedSource494, Integer.Sparse.eval, Sparse.eval, nodeValue2543, nodeValue2546, nodeValue2556, nodeValue2567, nodeValue2723, nodeValue3838, nodeValue4091]

theorem reindexCheck495 : Integer.Sparse.reindex keyMap MixedData.row495 = numericRow495 := by decide +kernel

theorem numericCheck495 (x : Master → ℝ) : Integer.Sparse.eval numericRow495 x =
    (1 : ℝ) * reducedSource495 x := by
  norm_num [numericRow495, reducedSource495, Integer.Sparse.eval, Sparse.eval, nodeValue2480, nodeValue2485, nodeValue2489, nodeValue2514, nodeValue2723, nodeValue3808, nodeValue4091]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Rows30
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero480 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource480 (mixedVector B) = 0 := by
  have h1261 : mixedVector B (Sum.inr 1261) = Sparse.eval nodeValue1261 (mixedVector B) := by
    change mixedMoment B node1261 node1261Labels = _
    exact sound1261 B hB hF
  have h2566 : mixedVector B (Sum.inr 2566) = Sparse.eval nodeValue2566 (mixedVector B) := by
    change mixedMoment B node2566 node2566Labels = _
    exact sound2566 B hB hF
  have h2632 : mixedVector B (Sum.inr 2632) = Sparse.eval nodeValue2632 (mixedVector B) := by
    change mixedMoment B node2632 node2632Labels = _
    exact sound2632 B hB hF
  have h2722 : mixedVector B (Sum.inr 2722) = Sparse.eval nodeValue2722 (mixedVector B) := by
    change mixedMoment B node2722 node2722Labels = _
    exact sound2722 B hB hF
  have h2763 : mixedVector B (Sum.inr 2763) = Sparse.eval nodeValue2763 (mixedVector B) := by
    change mixedMoment B node2763 node2763Labels = _
    exact sound2763 B hB hF
  have h2765 : mixedVector B (Sum.inr 2765) = Sparse.eval nodeValue2765 (mixedVector B) := by
    change mixedMoment B node2765 node2765Labels = _
    exact sound2765 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm571, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1261, h2566, h2632, h2722, h2763, h2765, h4092, reducedSource480] using sourceEq571 B hB

theorem rowSound480 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row480 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck480, numericCheck480, reducedZero480 B hB hF, mul_zero]

theorem reducedZero486 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource486 (mixedVector B) = 0 := by
  have h2106 : mixedVector B (Sum.inr 2106) = Sparse.eval nodeValue2106 (mixedVector B) := by
    change mixedMoment B node2106 node2106Labels = _
    exact sound2106 B hB hF
  have h2109 : mixedVector B (Sum.inr 2109) = Sparse.eval nodeValue2109 (mixedVector B) := by
    change mixedMoment B node2109 node2109Labels = _
    exact sound2109 B hB hF
  have h2115 : mixedVector B (Sum.inr 2115) = Sparse.eval nodeValue2115 (mixedVector B) := by
    change mixedMoment B node2115 node2115Labels = _
    exact sound2115 B hB hF
  have h2264 : mixedVector B (Sum.inr 2264) = Sparse.eval nodeValue2264 (mixedVector B) := by
    change mixedMoment B node2264 node2264Labels = _
    exact sound2264 B hB hF
  have h3582 : mixedVector B (Sum.inr 3582) = Sparse.eval nodeValue3582 (mixedVector B) := by
    change mixedMoment B node3582 node3582Labels = _
    exact sound3582 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm577, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2106, h2109, h2115, h2264, h3582, h4084, reducedSource486] using sourceEq577 B hB

theorem rowSound486 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row486 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck486, numericCheck486, reducedZero486 B hB hF, mul_zero]

theorem rowSound488 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row488 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck488, numericCheck488, reducedZero488_e B hB hF, mul_zero]

theorem reducedZero489 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource489 (mixedVector B) = 0 := by
  have h3290 : mixedVector B (Sum.inr 3290) = Sparse.eval nodeValue3290 (mixedVector B) := by
    change mixedMoment B node3290 node3290Labels = _
    exact sound3290 B hB hF
  have h3291 : mixedVector B (Sum.inr 3291) = Sparse.eval nodeValue3291 (mixedVector B) := by
    change mixedMoment B node3291 node3291Labels = _
    exact sound3291 B hB hF
  have h3294 : mixedVector B (Sum.inr 3294) = Sparse.eval nodeValue3294 (mixedVector B) := by
    change mixedMoment B node3294 node3294Labels = _
    exact sound3294 B hB hF
  have h3297 : mixedVector B (Sum.inr 3297) = Sparse.eval nodeValue3297 (mixedVector B) := by
    change mixedMoment B node3297 node3297Labels = _
    exact sound3297 B hB hF
  have h3299 : mixedVector B (Sum.inr 3299) = Sparse.eval nodeValue3299 (mixedVector B) := by
    change mixedMoment B node3299 node3299Labels = _
    exact sound3299 B hB hF
  have h3467 : mixedVector B (Sum.inr 3467) = Sparse.eval nodeValue3467 (mixedVector B) := by
    change mixedMoment B node3467 node3467Labels = _
    exact sound3467 B hB hF
  have h3481 : mixedVector B (Sum.inr 3481) = Sparse.eval nodeValue3481 (mixedVector B) := by
    change mixedMoment B node3481 node3481Labels = _
    exact sound3481 B hB hF
  have h3482 : mixedVector B (Sum.inr 3482) = Sparse.eval nodeValue3482 (mixedVector B) := by
    change mixedMoment B node3482 node3482Labels = _
    exact sound3482 B hB hF
  have h3483 : mixedVector B (Sum.inr 3483) = Sparse.eval nodeValue3483 (mixedVector B) := by
    change mixedMoment B node3483 node3483Labels = _
    exact sound3483 B hB hF
  have h3519 : mixedVector B (Sum.inr 3519) = Sparse.eval nodeValue3519 (mixedVector B) := by
    change mixedMoment B node3519 node3519Labels = _
    exact sound3519 B hB hF
  have h3520 : mixedVector B (Sum.inr 3520) = Sparse.eval nodeValue3520 (mixedVector B) := by
    change mixedMoment B node3520 node3520Labels = _
    exact sound3520 B hB hF
  have h3521 : mixedVector B (Sum.inr 3521) = Sparse.eval nodeValue3521 (mixedVector B) := by
    change mixedMoment B node3521 node3521Labels = _
    exact sound3521 B hB hF
  have h3523 : mixedVector B (Sum.inr 3523) = Sparse.eval nodeValue3523 (mixedVector B) := by
    change mixedMoment B node3523 node3523Labels = _
    exact sound3523 B hB hF
  have h3529 : mixedVector B (Sum.inr 3529) = Sparse.eval nodeValue3529 (mixedVector B) := by
    change mixedMoment B node3529 node3529Labels = _
    exact sound3529 B hB hF
  have h3531 : mixedVector B (Sum.inr 3531) = Sparse.eval nodeValue3531 (mixedVector B) := by
    change mixedMoment B node3531 node3531Labels = _
    exact sound3531 B hB hF
  have h3532 : mixedVector B (Sum.inr 3532) = Sparse.eval nodeValue3532 (mixedVector B) := by
    change mixedMoment B node3532 node3532Labels = _
    exact sound3532 B hB hF
  have h3542 : mixedVector B (Sum.inr 3542) = Sparse.eval nodeValue3542 (mixedVector B) := by
    change mixedMoment B node3542 node3542Labels = _
    exact sound3542 B hB hF
  have h3543 : mixedVector B (Sum.inr 3543) = Sparse.eval nodeValue3543 (mixedVector B) := by
    change mixedMoment B node3543 node3543Labels = _
    exact sound3543 B hB hF
  have h3544 : mixedVector B (Sum.inr 3544) = Sparse.eval nodeValue3544 (mixedVector B) := by
    change mixedMoment B node3544 node3544Labels = _
    exact sound3544 B hB hF
  have h3546 : mixedVector B (Sum.inr 3546) = Sparse.eval nodeValue3546 (mixedVector B) := by
    change mixedMoment B node3546 node3546Labels = _
    exact sound3546 B hB hF
  have h3562 : mixedVector B (Sum.inr 3562) = Sparse.eval nodeValue3562 (mixedVector B) := by
    change mixedMoment B node3562 node3562Labels = _
    exact sound3562 B hB hF
  have h3578 : mixedVector B (Sum.inr 3578) = Sparse.eval nodeValue3578 (mixedVector B) := by
    change mixedMoment B node3578 node3578Labels = _
    exact sound3578 B hB hF
  have h3580 : mixedVector B (Sum.inr 3580) = Sparse.eval nodeValue3580 (mixedVector B) := by
    change mixedMoment B node3580 node3580Labels = _
    exact sound3580 B hB hF
  have h3581 : mixedVector B (Sum.inr 3581) = Sparse.eval nodeValue3581 (mixedVector B) := by
    change mixedMoment B node3581 node3581Labels = _
    exact sound3581 B hB hF
  have h3816 : mixedVector B (Sum.inr 3816) = Sparse.eval nodeValue3816 (mixedVector B) := by
    change mixedMoment B node3816 node3816Labels = _
    exact sound3816 B hB hF
  have h3843 : mixedVector B (Sum.inr 3843) = Sparse.eval nodeValue3843 (mixedVector B) := by
    change mixedMoment B node3843 node3843Labels = _
    exact sound3843 B hB hF
  have h3857 : mixedVector B (Sum.inr 3857) = Sparse.eval nodeValue3857 (mixedVector B) := by
    change mixedMoment B node3857 node3857Labels = _
    exact sound3857 B hB hF
  have h3858 : mixedVector B (Sum.inr 3858) = Sparse.eval nodeValue3858 (mixedVector B) := by
    change mixedMoment B node3858 node3858Labels = _
    exact sound3858 B hB hF
  have h3859 : mixedVector B (Sum.inr 3859) = Sparse.eval nodeValue3859 (mixedVector B) := by
    change mixedMoment B node3859 node3859Labels = _
    exact sound3859 B hB hF
  simpa only [sourceForm580, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h3290, h3291, h3294, h3297, h3299, h3467, h3481, h3482, h3483, h3519, h3520, h3521, h3523, h3529, h3531, h3532, h3542, h3543, h3544, h3546, h3562, h3578, h3580, h3581, h3816, h3843, h3857, h3858, h3859, reducedSource489] using sourceEq580 B hB

theorem rowSound489 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row489 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck489, numericCheck489, reducedZero489 B hB hF, mul_zero]

theorem reducedZero490 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource490 (mixedVector B) = 0 := by
  have h2723 : mixedVector B (Sum.inr 2723) = Sparse.eval nodeValue2723 (mixedVector B) := by
    change mixedMoment B node2723 node2723Labels = _
    exact sound2723 B hB hF
  have h3808 : mixedVector B (Sum.inr 3808) = Sparse.eval nodeValue3808 (mixedVector B) := by
    change mixedMoment B node3808 node3808Labels = _
    exact sound3808 B hB hF
  have h3838 : mixedVector B (Sum.inr 3838) = Sparse.eval nodeValue3838 (mixedVector B) := by
    change mixedMoment B node3838 node3838Labels = _
    exact sound3838 B hB hF
  have h3876 : mixedVector B (Sum.inr 3876) = Sparse.eval nodeValue3876 (mixedVector B) := by
    change mixedMoment B node3876 node3876Labels = _
    exact sound3876 B hB hF
  have h3902 : mixedVector B (Sum.inr 3902) = Sparse.eval nodeValue3902 (mixedVector B) := by
    change mixedMoment B node3902 node3902Labels = _
    exact sound3902 B hB hF
  have h3904 : mixedVector B (Sum.inr 3904) = Sparse.eval nodeValue3904 (mixedVector B) := by
    change mixedMoment B node3904 node3904Labels = _
    exact sound3904 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm581, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2723, h3808, h3838, h3876, h3902, h3904, h4091, reducedSource490] using sourceEq581 B hB

theorem rowSound490 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row490 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck490, numericCheck490, reducedZero490 B hB hF, mul_zero]

theorem reducedZero491 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource491 (mixedVector B) = 0 := by
  have h1213 : mixedVector B (Sum.inr 1213) = Sparse.eval nodeValue1213 (mixedVector B) := by
    change mixedMoment B node1213 node1213Labels = _
    exact sound1213 B hB hF
  have h1217 : mixedVector B (Sum.inr 1217) = Sparse.eval nodeValue1217 (mixedVector B) := by
    change mixedMoment B node1217 node1217Labels = _
    exact sound1217 B hB hF
  have h1220 : mixedVector B (Sum.inr 1220) = Sparse.eval nodeValue1220 (mixedVector B) := by
    change mixedMoment B node1220 node1220Labels = _
    exact sound1220 B hB hF
  have h1240 : mixedVector B (Sum.inr 1240) = Sparse.eval nodeValue1240 (mixedVector B) := by
    change mixedMoment B node1240 node1240Labels = _
    exact sound1240 B hB hF
  have h1262 : mixedVector B (Sum.inr 1262) = Sparse.eval nodeValue1262 (mixedVector B) := by
    change mixedMoment B node1262 node1262Labels = _
    exact sound1262 B hB hF
  have h2723 : mixedVector B (Sum.inr 2723) = Sparse.eval nodeValue2723 (mixedVector B) := by
    change mixedMoment B node2723 node2723Labels = _
    exact sound2723 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm582, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1213, h1217, h1220, h1240, h1262, h2723, h4091, reducedSource491] using sourceEq582 B hB

theorem rowSound491 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row491 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck491, numericCheck491, reducedZero491 B hB hF, mul_zero]

theorem reducedZero492 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource492 (mixedVector B) = 0 := by
  have h1240 : mixedVector B (Sum.inr 1240) = Sparse.eval nodeValue1240 (mixedVector B) := by
    change mixedMoment B node1240 node1240Labels = _
    exact sound1240 B hB hF
  have h2514 : mixedVector B (Sum.inr 2514) = Sparse.eval nodeValue2514 (mixedVector B) := by
    change mixedMoment B node2514 node2514Labels = _
    exact sound2514 B hB hF
  have h2556 : mixedVector B (Sum.inr 2556) = Sparse.eval nodeValue2556 (mixedVector B) := by
    change mixedMoment B node2556 node2556Labels = _
    exact sound2556 B hB hF
  have h2723 : mixedVector B (Sum.inr 2723) = Sparse.eval nodeValue2723 (mixedVector B) := by
    change mixedMoment B node2723 node2723Labels = _
    exact sound2723 B hB hF
  have h2741 : mixedVector B (Sum.inr 2741) = Sparse.eval nodeValue2741 (mixedVector B) := by
    change mixedMoment B node2741 node2741Labels = _
    exact sound2741 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm583, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1240, h2514, h2556, h2723, h2741, h4091, reducedSource492] using sourceEq583 B hB

theorem rowSound492 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row492 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck492, numericCheck492, reducedZero492 B hB hF, mul_zero]

theorem reducedZero493 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource493 (mixedVector B) = 0 := by
  have h2615 : mixedVector B (Sum.inr 2615) = Sparse.eval nodeValue2615 (mixedVector B) := by
    change mixedMoment B node2615 node2615Labels = _
    exact sound2615 B hB hF
  have h2618 : mixedVector B (Sum.inr 2618) = Sparse.eval nodeValue2618 (mixedVector B) := by
    change mixedMoment B node2618 node2618Labels = _
    exact sound2618 B hB hF
  have h2621 : mixedVector B (Sum.inr 2621) = Sparse.eval nodeValue2621 (mixedVector B) := by
    change mixedMoment B node2621 node2621Labels = _
    exact sound2621 B hB hF
  have h2633 : mixedVector B (Sum.inr 2633) = Sparse.eval nodeValue2633 (mixedVector B) := by
    change mixedMoment B node2633 node2633Labels = _
    exact sound2633 B hB hF
  have h2723 : mixedVector B (Sum.inr 2723) = Sparse.eval nodeValue2723 (mixedVector B) := by
    change mixedMoment B node2723 node2723Labels = _
    exact sound2723 B hB hF
  have h3876 : mixedVector B (Sum.inr 3876) = Sparse.eval nodeValue3876 (mixedVector B) := by
    change mixedMoment B node3876 node3876Labels = _
    exact sound3876 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm584, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2615, h2618, h2621, h2633, h2723, h3876, h4091, reducedSource493] using sourceEq584 B hB

theorem rowSound493 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row493 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck493, numericCheck493, reducedZero493 B hB hF, mul_zero]

theorem reducedZero494 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource494 (mixedVector B) = 0 := by
  have h2543 : mixedVector B (Sum.inr 2543) = Sparse.eval nodeValue2543 (mixedVector B) := by
    change mixedMoment B node2543 node2543Labels = _
    exact sound2543 B hB hF
  have h2546 : mixedVector B (Sum.inr 2546) = Sparse.eval nodeValue2546 (mixedVector B) := by
    change mixedMoment B node2546 node2546Labels = _
    exact sound2546 B hB hF
  have h2556 : mixedVector B (Sum.inr 2556) = Sparse.eval nodeValue2556 (mixedVector B) := by
    change mixedMoment B node2556 node2556Labels = _
    exact sound2556 B hB hF
  have h2567 : mixedVector B (Sum.inr 2567) = Sparse.eval nodeValue2567 (mixedVector B) := by
    change mixedMoment B node2567 node2567Labels = _
    exact sound2567 B hB hF
  have h2723 : mixedVector B (Sum.inr 2723) = Sparse.eval nodeValue2723 (mixedVector B) := by
    change mixedMoment B node2723 node2723Labels = _
    exact sound2723 B hB hF
  have h3838 : mixedVector B (Sum.inr 3838) = Sparse.eval nodeValue3838 (mixedVector B) := by
    change mixedMoment B node3838 node3838Labels = _
    exact sound3838 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm585, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2543, h2546, h2556, h2567, h2723, h3838, h4091, reducedSource494] using sourceEq585 B hB

theorem rowSound494 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row494 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck494, numericCheck494, reducedZero494 B hB hF, mul_zero]

theorem reducedZero495 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource495 (mixedVector B) = 0 := by
  have h2480 : mixedVector B (Sum.inr 2480) = Sparse.eval nodeValue2480 (mixedVector B) := by
    change mixedMoment B node2480 node2480Labels = _
    exact sound2480 B hB hF
  have h2485 : mixedVector B (Sum.inr 2485) = Sparse.eval nodeValue2485 (mixedVector B) := by
    change mixedMoment B node2485 node2485Labels = _
    exact sound2485 B hB hF
  have h2489 : mixedVector B (Sum.inr 2489) = Sparse.eval nodeValue2489 (mixedVector B) := by
    change mixedMoment B node2489 node2489Labels = _
    exact sound2489 B hB hF
  have h2514 : mixedVector B (Sum.inr 2514) = Sparse.eval nodeValue2514 (mixedVector B) := by
    change mixedMoment B node2514 node2514Labels = _
    exact sound2514 B hB hF
  have h2723 : mixedVector B (Sum.inr 2723) = Sparse.eval nodeValue2723 (mixedVector B) := by
    change mixedMoment B node2723 node2723Labels = _
    exact sound2723 B hB hF
  have h3808 : mixedVector B (Sum.inr 3808) = Sparse.eval nodeValue3808 (mixedVector B) := by
    change mixedMoment B node3808 node3808Labels = _
    exact sound3808 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm586, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2480, h2485, h2489, h2514, h2723, h3808, h4091, reducedSource495] using sourceEq586 B hB

theorem rowSound495 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row495 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck495, numericCheck495, reducedZero495 B hB hF, mul_zero]

theorem sourceRowsAt480 : MixedData.sourceRows (480 : Fin 2425) =
    MixedData.row480 := by decide +kernel

theorem sourceRowsAt481 : MixedData.sourceRows (481 : Fin 2425) =
    MixedData.row481 := by decide +kernel

theorem sourceRowsAt482 : MixedData.sourceRows (482 : Fin 2425) =
    MixedData.row482 := by decide +kernel

theorem sourceRowsAt483 : MixedData.sourceRows (483 : Fin 2425) =
    MixedData.row483 := by decide +kernel

theorem sourceRowsAt484 : MixedData.sourceRows (484 : Fin 2425) =
    MixedData.row484 := by decide +kernel

theorem sourceRowsAt485 : MixedData.sourceRows (485 : Fin 2425) =
    MixedData.row485 := by decide +kernel

theorem sourceRowsAt486 : MixedData.sourceRows (486 : Fin 2425) =
    MixedData.row486 := by decide +kernel

theorem sourceRowsAt487 : MixedData.sourceRows (487 : Fin 2425) =
    MixedData.row487 := by decide +kernel

theorem sourceRowsAt488 : MixedData.sourceRows (488 : Fin 2425) =
    MixedData.row488 := by decide +kernel

theorem sourceRowsAt489 : MixedData.sourceRows (489 : Fin 2425) =
    MixedData.row489 := by decide +kernel

theorem sourceRowsAt490 : MixedData.sourceRows (490 : Fin 2425) =
    MixedData.row490 := by decide +kernel

theorem sourceRowsAt491 : MixedData.sourceRows (491 : Fin 2425) =
    MixedData.row491 := by decide +kernel

theorem sourceRowsAt492 : MixedData.sourceRows (492 : Fin 2425) =
    MixedData.row492 := by decide +kernel

theorem sourceRowsAt493 : MixedData.sourceRows (493 : Fin 2425) =
    MixedData.row493 := by decide +kernel

theorem sourceRowsAt494 : MixedData.sourceRows (494 : Fin 2425) =
    MixedData.row494 := by decide +kernel

theorem sourceRowsAt495 : MixedData.sourceRows (495 : Fin 2425) =
    MixedData.row495 := by decide +kernel

theorem chunkSound30_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) (k : Fin 2425)
    (hk : k.val / 16 = 30) :
    Integer.Sparse.eval (MixedData.sourceRows k) (numericVector B) = 0 := by
  have heq : k.val = 480 ∨ k.val = 481 ∨ k.val = 482 ∨ k.val = 483 ∨ k.val = 484 ∨ k.val = 485 ∨ k.val = 486 ∨ k.val = 487 ∨ k.val = 488 ∨ k.val = 489 ∨ k.val = 490 ∨ k.val = 491 ∨ k.val = 492 ∨ k.val = 493 ∨ k.val = 494 ∨ k.val = 495 := by omega
  rcases heq with h480 | h481 | h482 | h483 | h484 | h485 | h486 | h487 | h488 | h489 | h490 | h491 | h492 | h493 | h494 | h495
  · have he : k = (480 : Fin 2425) := Fin.ext h480
    subst k
    rw [sourceRowsAt480]
    exact rowSound480 B hB hF
  · have he : k = (481 : Fin 2425) := Fin.ext h481
    subst k
    rw [sourceRowsAt481]
    exact rowSound481_e B hB hF
  · have he : k = (482 : Fin 2425) := Fin.ext h482
    subst k
    rw [sourceRowsAt482]
    exact rowSound482_e B hB hF
  · have he : k = (483 : Fin 2425) := Fin.ext h483
    subst k
    rw [sourceRowsAt483]
    exact rowSound483_e B hB hF
  · have he : k = (484 : Fin 2425) := Fin.ext h484
    subst k
    rw [sourceRowsAt484]
    exact rowSound484_e B hB hF
  · have he : k = (485 : Fin 2425) := Fin.ext h485
    subst k
    rw [sourceRowsAt485]
    exact rowSound485_e B hB hF
  · have he : k = (486 : Fin 2425) := Fin.ext h486
    subst k
    rw [sourceRowsAt486]
    exact rowSound486 B hB hF
  · have he : k = (487 : Fin 2425) := Fin.ext h487
    subst k
    rw [sourceRowsAt487]
    exact rowSound487_e B hB hF
  · have he : k = (488 : Fin 2425) := Fin.ext h488
    subst k
    rw [sourceRowsAt488]
    exact rowSound488 B hB hF
  · have he : k = (489 : Fin 2425) := Fin.ext h489
    subst k
    rw [sourceRowsAt489]
    exact rowSound489 B hB hF
  · have he : k = (490 : Fin 2425) := Fin.ext h490
    subst k
    rw [sourceRowsAt490]
    exact rowSound490 B hB hF
  · have he : k = (491 : Fin 2425) := Fin.ext h491
    subst k
    rw [sourceRowsAt491]
    exact rowSound491 B hB hF
  · have he : k = (492 : Fin 2425) := Fin.ext h492
    subst k
    rw [sourceRowsAt492]
    exact rowSound492 B hB hF
  · have he : k = (493 : Fin 2425) := Fin.ext h493
    subst k
    rw [sourceRowsAt493]
    exact rowSound493 B hB hF
  · have he : k = (494 : Fin 2425) := Fin.ext h494
    subst k
    rw [sourceRowsAt494]
    exact rowSound494 B hB hF
  · have he : k = (495 : Fin 2425) := Fin.ext h495
    subst k
    rw [sourceRowsAt495]
    exact rowSound495 B hB hF

end MUB6.Certificate.MixedSourceBridge

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedSourceBridge.chunkSound30_e_oai := @OAI.MUB6.Certificate.MixedSourceBridge.chunkSound30_e_oai
