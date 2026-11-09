-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedSourceBridge.chunkSound8_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T04:41:44.689921+00:00
-- url     : https://prove2.me/submissions/bed9e35c-e9a8-4b81-8948-a29d2d5c7379

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E077
import Definitions.Def_OAIQ106E086
import Definitions.Def_OAIQ106E090
import Definitions.Def_OAIQ106E097
import Definitions.Def_OAIQ106E190
import Definitions.Def_OAIQ106E191
import Definitions.Def_OAIQ106E109
import Definitions.Def_OAIQ106E110
import Definitions.Def_OAIQ106E114
import Definitions.Def_OAIQ106E115
import Definitions.Def_OAIQ106E119
import Definitions.Def_OAIQ106E120
import Definitions.Def_OAIQ106E124
import Definitions.Def_OAIQ106E140
import Definitions.Def_OAIQ106E147
import Definitions.Def_OAIQ106E170
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound130_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound137_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound138_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound139_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound140_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound141_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound143_e

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical11
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical1434 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1434 raw1434Labels = mixedMoment B node4608 node4608Labels := by
  calc
    mixedMoment B raw1434 raw1434Labels = mixedMoment B raw1434step0 raw1434step0Labels := by
      have ha : raw1434step0 = (fun i j => raw1434 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1434step0 raw1434; decide +kernel
      have hl : raw1434step0Labels = raw1434Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1434 raw1434Labels permutation8 permutation4
    mixedMoment B raw1434step0 raw1434step0Labels = mixedMoment B raw1434step1 raw1434step1Labels := by
      have ha : raw1434step1 = raw1434step0 := by apply Matrix.ext; unfold raw1434step1 raw1434step0; decide +kernel
      have hl : raw1434step0Labels = labelEmbedding7 ∘ raw1434step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1434step0 raw1434step0Labels raw1434step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4608 node4608Labels := by rfl

theorem canonical1435 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1435 raw1435Labels = mixedMoment B node1242 node1242Labels := by
  calc
    mixedMoment B raw1435 raw1435Labels = mixedMoment B raw1435step0 raw1435step0Labels := by
      have ha : raw1435step0 = (fun i j => raw1435 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1435step0 raw1435; decide +kernel
      have hl : raw1435step0Labels = raw1435Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1435 raw1435Labels permutation8 permutation4
    _ = mixedMoment B node1242 node1242Labels := by rfl

theorem canonical1436 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1436 raw1436Labels = mixedMoment B node3300 node3300Labels := by
  calc
    mixedMoment B raw1436 raw1436Labels = mixedMoment B raw1436step0 raw1436step0Labels := by
      have ha : raw1436step0 = (fun i j => raw1436 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1436step0 raw1436; decide +kernel
      have hl : raw1436step0Labels = raw1436Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1436 raw1436Labels permutation8 permutation6
    mixedMoment B raw1436step0 raw1436step0Labels = mixedMoment B raw1436step1 raw1436step1Labels := by
      have ha : raw1436step1 = -raw1436step0 := by apply Matrix.ext; change ∀ i j, raw1436step1 i j = -(raw1436step0 i j); unfold raw1436step1 raw1436step0; decide +kernel
      have hl : raw1436step1Labels = raw1436step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1436step1 raw1436step1Labels = mixedMoment B raw1436step2 raw1436step2Labels := by
      have ha : raw1436step2 = raw1436step1 := by apply Matrix.ext; unfold raw1436step2 raw1436step1; decide +kernel
      have hl : raw1436step1Labels = labelEmbedding1 ∘ raw1436step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1436step1 raw1436step1Labels raw1436step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3300 node3300Labels := by rfl

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

theorem canonical2097 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2097 raw2097Labels = mixedMoment B node5075 node5075Labels := by
  calc
    mixedMoment B raw2097 raw2097Labels = mixedMoment B raw2097step0 raw2097step0Labels := by
      have ha : raw2097step0 = (fun i j => raw2097 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2097step0 raw2097; decide +kernel
      have hl : raw2097step0Labels = raw2097Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2097 raw2097Labels permutation32 permutation4
    mixedMoment B raw2097step0 raw2097step0Labels = mixedMoment B raw2097step1 raw2097step1Labels := by
      have ha : raw2097step1 = raw2097step0 := by apply Matrix.ext; unfold raw2097step1 raw2097step0; decide +kernel
      have hl : raw2097step0Labels = labelEmbedding7 ∘ raw2097step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2097step0 raw2097step0Labels raw2097step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5075 node5075Labels := by rfl

theorem canonical2098 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2098 raw2098Labels = mixedMoment B node2482 node2482Labels := by
  calc
    mixedMoment B raw2098 raw2098Labels = mixedMoment B raw2098step0 raw2098step0Labels := by
      have ha : raw2098step0 = (fun i j => raw2098 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2098step0 raw2098; decide +kernel
      have hl : raw2098step0Labels = raw2098Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2098 raw2098Labels permutation32 permutation4
    _ = mixedMoment B node2482 node2482Labels := by rfl

theorem canonical2099 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2099 raw2099Labels = mixedMoment B node3468 node3468Labels := by
  calc
    mixedMoment B raw2099 raw2099Labels = mixedMoment B raw2099step0 raw2099step0Labels := by
      have ha : raw2099step0 = (fun i j => raw2099 (permutation34 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2099step0 raw2099; decide +kernel
      have hl : raw2099step0Labels = raw2099Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2099 raw2099Labels permutation34 permutation6
    mixedMoment B raw2099step0 raw2099step0Labels = mixedMoment B raw2099step1 raw2099step1Labels := by
      have ha : raw2099step1 = -raw2099step0 := by apply Matrix.ext; change ∀ i j, raw2099step1 i j = -(raw2099step0 i j); unfold raw2099step1 raw2099step0; decide +kernel
      have hl : raw2099step1Labels = raw2099step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2099step1 raw2099step1Labels = mixedMoment B raw2099step2 raw2099step2Labels := by
      have ha : raw2099step2 = raw2099step1 := by apply Matrix.ext; unfold raw2099step2 raw2099step1; decide +kernel
      have hl : raw2099step1Labels = labelEmbedding1 ∘ raw2099step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2099step1 raw2099step1Labels raw2099step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3468 node3468Labels := by rfl

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

theorem canonical2271 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2271 raw2271Labels = mixedMoment B node5258 node5258Labels := by
  calc
    mixedMoment B raw2271 raw2271Labels = mixedMoment B raw2271step0 raw2271step0Labels := by
      have ha : raw2271step0 = (fun i j => raw2271 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2271step0 raw2271; decide +kernel
      have hl : raw2271step0Labels = raw2271Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2271 raw2271Labels permutation32 permutation4
    mixedMoment B raw2271step0 raw2271step0Labels = mixedMoment B raw2271step1 raw2271step1Labels := by
      have ha : raw2271step1 = raw2271step0 := by apply Matrix.ext; unfold raw2271step1 raw2271step0; decide +kernel
      have hl : raw2271step0Labels = labelEmbedding7 ∘ raw2271step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2271step0 raw2271step0Labels raw2271step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5258 node5258Labels := by rfl

theorem canonical2272 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2272 raw2272Labels = mixedMoment B node2722 node2722Labels := by
  calc
    mixedMoment B raw2272 raw2272Labels = mixedMoment B raw2272step0 raw2272step0Labels := by
      have ha : raw2272step0 = (fun i j => raw2272 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2272step0 raw2272; decide +kernel
      have hl : raw2272step0Labels = raw2272Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2272 raw2272Labels permutation32 permutation4
    _ = mixedMoment B node2722 node2722Labels := by rfl

theorem canonical2273 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2273 raw2273Labels = mixedMoment B node3533 node3533Labels := by
  calc
    mixedMoment B raw2273 raw2273Labels = mixedMoment B raw2273step0 raw2273step0Labels := by
      have ha : raw2273step0 = (fun i j => raw2273 (permutation34 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2273step0 raw2273; decide +kernel
      have hl : raw2273step0Labels = raw2273Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2273 raw2273Labels permutation34 permutation6
    mixedMoment B raw2273step0 raw2273step0Labels = mixedMoment B raw2273step1 raw2273step1Labels := by
      have ha : raw2273step1 = -raw2273step0 := by apply Matrix.ext; change ∀ i j, raw2273step1 i j = -(raw2273step0 i j); unfold raw2273step1 raw2273step0; decide +kernel
      have hl : raw2273step1Labels = raw2273step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2273step1 raw2273step1Labels = mixedMoment B raw2273step2 raw2273step2Labels := by
      have ha : raw2273step2 = raw2273step1 := by apply Matrix.ext; unfold raw2273step2 raw2273step1; decide +kernel
      have hl : raw2273step1Labels = labelEmbedding1 ∘ raw2273step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2273step1 raw2273step1Labels raw2273step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3533 node3533Labels := by rfl

theorem canonical2295 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2295 raw2295Labels = mixedMoment B node5291 node5291Labels := by
  calc
    mixedMoment B raw2295 raw2295Labels = mixedMoment B raw2295step0 raw2295step0Labels := by
      have ha : raw2295step0 = (fun i j => raw2295 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2295step0 raw2295; decide +kernel
      have hl : raw2295step0Labels = raw2295Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2295 raw2295Labels permutation8 permutation4
    mixedMoment B raw2295step0 raw2295step0Labels = mixedMoment B raw2295step1 raw2295step1Labels := by
      have ha : raw2295step1 = raw2295step0 := by apply Matrix.ext; unfold raw2295step1 raw2295step0; decide +kernel
      have hl : raw2295step0Labels = labelEmbedding7 ∘ raw2295step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2295step0 raw2295step0Labels raw2295step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5291 node5291Labels := by rfl

theorem canonical2296 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2296 raw2296Labels = mixedMoment B node2765 node2765Labels := by
  calc
    mixedMoment B raw2296 raw2296Labels = mixedMoment B raw2296step0 raw2296step0Labels := by
      have ha : raw2296step0 = (fun i j => raw2296 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2296step0 raw2296; decide +kernel
      have hl : raw2296step0Labels = raw2296Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2296 raw2296Labels permutation8 permutation4
    _ = mixedMoment B node2765 node2765Labels := by rfl

theorem canonical2297 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2297 raw2297Labels = mixedMoment B node3582 node3582Labels := by
  calc
    mixedMoment B raw2297 raw2297Labels = mixedMoment B raw2297step0 raw2297step0Labels := by
      have ha : raw2297step0 = (fun i j => raw2297 (permutation10 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2297step0 raw2297; decide +kernel
      have hl : raw2297step0Labels = raw2297Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2297 raw2297Labels permutation10 permutation6
    mixedMoment B raw2297step0 raw2297step0Labels = mixedMoment B raw2297step1 raw2297step1Labels := by
      have ha : raw2297step1 = -raw2297step0 := by apply Matrix.ext; change ∀ i j, raw2297step1 i j = -(raw2297step0 i j); unfold raw2297step1 raw2297step0; decide +kernel
      have hl : raw2297step1Labels = raw2297step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2297step1 raw2297step1Labels = mixedMoment B raw2297step2 raw2297step2Labels := by
      have ha : raw2297step2 = raw2297step1 := by apply Matrix.ext; unfold raw2297step2 raw2297step1; decide +kernel
      have hl : raw2297step1Labels = labelEmbedding1 ∘ raw2297step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2297step1 raw2297step1Labels raw2297step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3582 node3582Labels := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical37
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical4806 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4806 raw4806Labels = mixedMoment B node2052 node2052Labels := by
  calc
    mixedMoment B raw4806 raw4806Labels = mixedMoment B raw4806step0 raw4806step0Labels := by
      have hz : ∀ j, raw4806 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw4806step0 = (fun i j => raw4806 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw4806step0 raw4806; decide +kernel
      have hl : raw4806step0Labels = raw4806Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4806 raw4806Labels permutation265 hz
    mixedMoment B raw4806step0 raw4806step0Labels = mixedMoment B raw4806step1 raw4806step1Labels := by
      have ha : raw4806step1 = (fun i j => raw4806step0 (permutation137 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4806step1 raw4806step0; decide +kernel
      have hl : raw4806step1Labels = raw4806step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4806step0 raw4806step0Labels permutation137 permutation2
    _ = mixedMoment B node2052 node2052Labels := by rfl

theorem canonical4807 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4807 raw4807Labels = mixedMoment B node2292 node2292Labels := by
  calc
    mixedMoment B raw4807 raw4807Labels = mixedMoment B raw4807step0 raw4807step0Labels := by
      have hz : ∀ j, raw4807 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw4807step0 = (fun i j => raw4807 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw4807step0 raw4807; decide +kernel
      have hl : raw4807step0Labels = raw4807Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4807 raw4807Labels permutation520 hz
    mixedMoment B raw4807step0 raw4807step0Labels = mixedMoment B raw4807step1 raw4807step1Labels := by
      have hz : ∀ j, raw4807step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4807step1 = (fun i j => raw4807step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4807step1 raw4807step0; decide +kernel
      have hl : raw4807step1Labels = raw4807step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4807step0 raw4807step0Labels permutation80 hz
    mixedMoment B raw4807step1 raw4807step1Labels = mixedMoment B raw4807step2 raw4807step2Labels := by
      have hz : ∀ j, raw4807step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw4807step2 = (fun i j => raw4807step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw4807step2 raw4807step1; decide +kernel
      have hl : raw4807step2Labels = raw4807step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4807step1 raw4807step1Labels permutation14 hz
    mixedMoment B raw4807step2 raw4807step2Labels = mixedMoment B raw4807step3 raw4807step3Labels := by
      have ha : raw4807step3 = (fun i j => raw4807step2 (permutation7 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4807step3 raw4807step2; decide +kernel
      have hl : raw4807step3Labels = raw4807step2Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4807step2 raw4807step2Labels permutation7 permutation2
    _ = mixedMoment B node2292 node2292Labels := by rfl

theorem canonical4808 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4808 raw4808Labels = mixedMoment B node1080 node1080Labels := by
  calc
    mixedMoment B raw4808 raw4808Labels = mixedMoment B raw4808step0 raw4808step0Labels := by
      have hz : ∀ j, raw4808 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4808step0 = (fun i j => raw4808 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4808step0 raw4808; decide +kernel
      have hl : raw4808step0Labels = raw4808Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4808 raw4808Labels permutation346 hz
    mixedMoment B raw4808step0 raw4808step0Labels = mixedMoment B raw4808step1 raw4808step1Labels := by
      have hz : ∀ j, raw4808step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw4808step1 = (fun i j => raw4808step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw4808step1 raw4808step0; decide +kernel
      have hl : raw4808step1Labels = raw4808step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4808step0 raw4808step0Labels permutation56 hz
    mixedMoment B raw4808step1 raw4808step1Labels = mixedMoment B raw4808step2 raw4808step2Labels := by
      have ha : raw4808step2 = (fun i j => raw4808step1 (permutation29 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4808step2 raw4808step1; decide +kernel
      have hl : raw4808step2Labels = raw4808step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4808step1 raw4808step1Labels permutation29 permutation2
    _ = mixedMoment B node1080 node1080Labels := by rfl

theorem canonical4809 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4809 raw4809Labels = mixedMoment B node5291 node5291Labels := by
  calc
    mixedMoment B raw4809 raw4809Labels = mixedMoment B raw4809step0 raw4809step0Labels := by
      have hz : ∀ j, raw4809 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4809step0 = (fun i j => raw4809 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4809step0 raw4809; decide +kernel
      have hl : raw4809step0Labels = raw4809Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4809 raw4809Labels permutation434 hz
    mixedMoment B raw4809step0 raw4809step0Labels = mixedMoment B raw4809step1 raw4809step1Labels := by
      have hz : ∀ j, raw4809step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4809step1 = (fun i j => raw4809step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4809step1 raw4809step0; decide +kernel
      have hl : raw4809step1Labels = raw4809step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4809step0 raw4809step0Labels permutation80 hz
    mixedMoment B raw4809step1 raw4809step1Labels = mixedMoment B raw4809step2 raw4809step2Labels := by
      have ha : raw4809step2 = (fun i j => raw4809step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4809step2 raw4809step1; decide +kernel
      have hl : raw4809step2Labels = raw4809step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4809step1 raw4809step1Labels permutation31 permutation2
    mixedMoment B raw4809step2 raw4809step2Labels = mixedMoment B raw4809step3 raw4809step3Labels := by
      have ha : raw4809step3 = -raw4809step2 := by apply Matrix.ext; change ∀ i j, raw4809step3 i j = -(raw4809step2 i j); unfold raw4809step3 raw4809step2; decide +kernel
      have hl : raw4809step3Labels = raw4809step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5291 node5291Labels := by rfl

theorem canonical4810 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4810 raw4810Labels = mixedMoment B node5258 node5258Labels := by
  calc
    mixedMoment B raw4810 raw4810Labels = mixedMoment B raw4810step0 raw4810step0Labels := by
      have hz : ∀ j, raw4810 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4810step0 = (fun i j => raw4810 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4810step0 raw4810; decide +kernel
      have hl : raw4810step0Labels = raw4810Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4810 raw4810Labels permutation434 hz
    mixedMoment B raw4810step0 raw4810step0Labels = mixedMoment B raw4810step1 raw4810step1Labels := by
      have ha : raw4810step1 = (fun i j => raw4810step0 (permutation139 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4810step1 raw4810step0; decide +kernel
      have hl : raw4810step1Labels = raw4810step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4810step0 raw4810step0Labels permutation139 permutation2
    mixedMoment B raw4810step1 raw4810step1Labels = mixedMoment B raw4810step2 raw4810step2Labels := by
      have ha : raw4810step2 = -raw4810step1 := by apply Matrix.ext; change ∀ i j, raw4810step2 i j = -(raw4810step1 i j); unfold raw4810step2 raw4810step1; decide +kernel
      have hl : raw4810step2Labels = raw4810step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5258 node5258Labels := by rfl

theorem canonical4811 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4811 raw4811Labels = mixedMoment B node5258 node5258Labels := by
  calc
    mixedMoment B raw4811 raw4811Labels = mixedMoment B raw4811step0 raw4811step0Labels := by
      have hz : ∀ j, raw4811 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4811step0 = (fun i j => raw4811 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4811step0 raw4811; decide +kernel
      have hl : raw4811step0Labels = raw4811Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4811 raw4811Labels permutation346 hz
    mixedMoment B raw4811step0 raw4811step0Labels = mixedMoment B raw4811step1 raw4811step1Labels := by
      have ha : raw4811step1 = (fun i j => raw4811step0 (permutation139 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4811step1 raw4811step0; decide +kernel
      have hl : raw4811step1Labels = raw4811step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4811step0 raw4811step0Labels permutation139 permutation2
    mixedMoment B raw4811step1 raw4811step1Labels = mixedMoment B raw4811step2 raw4811step2Labels := by
      have ha : raw4811step2 = -raw4811step1 := by apply Matrix.ext; change ∀ i j, raw4811step2 i j = -(raw4811step1 i j); unfold raw4811step2 raw4811step1; decide +kernel
      have hl : raw4811step2Labels = raw4811step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5258 node5258Labels := by rfl

theorem canonical4812 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4812 raw4812Labels = mixedMoment B node5274 node5274Labels := by
  calc
    mixedMoment B raw4812 raw4812Labels = mixedMoment B raw4812step0 raw4812step0Labels := by
      have hz : ∀ j, raw4812 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4812step0 = (fun i j => raw4812 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4812step0 raw4812; decide +kernel
      have hl : raw4812step0Labels = raw4812Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4812 raw4812Labels permutation434 hz
    mixedMoment B raw4812step0 raw4812step0Labels = mixedMoment B raw4812step1 raw4812step1Labels := by
      have hz : ∀ j, raw4812step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4812step1 = (fun i j => raw4812step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4812step1 raw4812step0; decide +kernel
      have hl : raw4812step1Labels = raw4812step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4812step0 raw4812step0Labels permutation80 hz
    mixedMoment B raw4812step1 raw4812step1Labels = mixedMoment B raw4812step2 raw4812step2Labels := by
      have ha : raw4812step2 = (fun i j => raw4812step1 (permutation29 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4812step2 raw4812step1; decide +kernel
      have hl : raw4812step2Labels = raw4812step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4812step1 raw4812step1Labels permutation29 permutation2
    mixedMoment B raw4812step2 raw4812step2Labels = mixedMoment B raw4812step3 raw4812step3Labels := by
      have ha : raw4812step3 = -raw4812step2 := by apply Matrix.ext; change ∀ i j, raw4812step3 i j = -(raw4812step2 i j); unfold raw4812step3 raw4812step2; decide +kernel
      have hl : raw4812step3Labels = raw4812step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5274 node5274Labels := by rfl

theorem canonical4813 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4813 raw4813Labels = mixedMoment B node5441 node5441Labels := by
  calc
    mixedMoment B raw4813 raw4813Labels = mixedMoment B raw4813step0 raw4813step0Labels := by
      have hz : ∀ j, raw4813 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4813step0 = (fun i j => raw4813 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4813step0 raw4813; decide +kernel
      have hl : raw4813step0Labels = raw4813Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4813 raw4813Labels permutation434 hz
    mixedMoment B raw4813step0 raw4813step0Labels = mixedMoment B raw4813step1 raw4813step1Labels := by
      have hz : ∀ j, raw4813step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4813step1 = (fun i j => raw4813step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4813step1 raw4813step0; decide +kernel
      have hl : raw4813step1Labels = raw4813step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4813step0 raw4813step0Labels permutation80 hz
    mixedMoment B raw4813step1 raw4813step1Labels = mixedMoment B raw4813step2 raw4813step2Labels := by
      have ha : raw4813step2 = (fun i j => raw4813step1 (permutation29 i) (permutation7 j)) := by apply Matrix.ext; unfold raw4813step2 raw4813step1; decide +kernel
      have hl : raw4813step2Labels = raw4813step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4813step1 raw4813step1Labels permutation29 permutation7
    mixedMoment B raw4813step2 raw4813step2Labels = mixedMoment B raw4813step3 raw4813step3Labels := by
      have ha : raw4813step3 = raw4813step2 := by apply Matrix.ext; unfold raw4813step3 raw4813step2; decide +kernel
      have hl : raw4813step2Labels = labelEmbedding10 ∘ raw4813step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4813step2 raw4813step2Labels raw4813step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5441 node5441Labels := by rfl

theorem canonical4814 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4814 raw4814Labels = mixedMoment B node4608 node4608Labels := by
  calc
    mixedMoment B raw4814 raw4814Labels = mixedMoment B raw4814step0 raw4814step0Labels := by
      have hz : ∀ j, raw4814 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4814step0 = (fun i j => raw4814 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4814step0 raw4814; decide +kernel
      have hl : raw4814step0Labels = raw4814Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4814 raw4814Labels permutation434 hz
    mixedMoment B raw4814step0 raw4814step0Labels = mixedMoment B raw4814step1 raw4814step1Labels := by
      have hz : ∀ j, raw4814step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4814step1 = (fun i j => raw4814step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4814step1 raw4814step0; decide +kernel
      have hl : raw4814step1Labels = raw4814step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4814step0 raw4814step0Labels permutation80 hz
    mixedMoment B raw4814step1 raw4814step1Labels = mixedMoment B raw4814step2 raw4814step2Labels := by
      have ha : raw4814step2 = (fun i j => raw4814step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4814step2 raw4814step1; decide +kernel
      have hl : raw4814step2Labels = raw4814step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4814step1 raw4814step1Labels permutation10 permutation2
    _ = mixedMoment B node4608 node4608Labels := by rfl

theorem canonical4815 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4815 raw4815Labels = mixedMoment B node5075 node5075Labels := by
  calc
    mixedMoment B raw4815 raw4815Labels = mixedMoment B raw4815step0 raw4815step0Labels := by
      have hz : ∀ j, raw4815 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4815step0 = (fun i j => raw4815 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4815step0 raw4815; decide +kernel
      have hl : raw4815step0Labels = raw4815Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4815 raw4815Labels permutation434 hz
    mixedMoment B raw4815step0 raw4815step0Labels = mixedMoment B raw4815step1 raw4815step1Labels := by
      have ha : raw4815step1 = (fun i j => raw4815step0 (permutation139 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4815step1 raw4815step0; decide +kernel
      have hl : raw4815step1Labels = raw4815step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4815step0 raw4815step0Labels permutation139 permutation2
    mixedMoment B raw4815step1 raw4815step1Labels = mixedMoment B raw4815step2 raw4815step2Labels := by
      have ha : raw4815step2 = -raw4815step1 := by apply Matrix.ext; change ∀ i j, raw4815step2 i j = -(raw4815step1 i j); unfold raw4815step2 raw4815step1; decide +kernel
      have hl : raw4815step2Labels = raw4815step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5075 node5075Labels := by rfl

theorem canonical4816 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4816 raw4816Labels = mixedMoment B node5075 node5075Labels := by
  calc
    mixedMoment B raw4816 raw4816Labels = mixedMoment B raw4816step0 raw4816step0Labels := by
      have hz : ∀ j, raw4816 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4816step0 = (fun i j => raw4816 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4816step0 raw4816; decide +kernel
      have hl : raw4816step0Labels = raw4816Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4816 raw4816Labels permutation346 hz
    mixedMoment B raw4816step0 raw4816step0Labels = mixedMoment B raw4816step1 raw4816step1Labels := by
      have ha : raw4816step1 = (fun i j => raw4816step0 (permutation139 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4816step1 raw4816step0; decide +kernel
      have hl : raw4816step1Labels = raw4816step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4816step0 raw4816step0Labels permutation139 permutation2
    mixedMoment B raw4816step1 raw4816step1Labels = mixedMoment B raw4816step2 raw4816step2Labels := by
      have ha : raw4816step2 = -raw4816step1 := by apply Matrix.ext; change ∀ i j, raw4816step2 i j = -(raw4816step1 i j); unfold raw4816step2 raw4816step1; decide +kernel
      have hl : raw4816step2Labels = raw4816step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5075 node5075Labels := by rfl

theorem canonical4817 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4817 raw4817Labels = mixedMoment B node5107 node5107Labels := by
  calc
    mixedMoment B raw4817 raw4817Labels = mixedMoment B raw4817step0 raw4817step0Labels := by
      have hz : ∀ j, raw4817 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4817step0 = (fun i j => raw4817 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4817step0 raw4817; decide +kernel
      have hl : raw4817step0Labels = raw4817Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4817 raw4817Labels permutation434 hz
    mixedMoment B raw4817step0 raw4817step0Labels = mixedMoment B raw4817step1 raw4817step1Labels := by
      have hz : ∀ j, raw4817step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4817step1 = (fun i j => raw4817step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4817step1 raw4817step0; decide +kernel
      have hl : raw4817step1Labels = raw4817step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4817step0 raw4817step0Labels permutation80 hz
    mixedMoment B raw4817step1 raw4817step1Labels = mixedMoment B raw4817step2 raw4817step2Labels := by
      have ha : raw4817step2 = (fun i j => raw4817step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4817step2 raw4817step1; decide +kernel
      have hl : raw4817step2Labels = raw4817step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4817step1 raw4817step1Labels permutation10 permutation2
    _ = mixedMoment B node5107 node5107Labels := by rfl

theorem canonical4818 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4818 raw4818Labels = mixedMoment B node5274 node5274Labels := by
  calc
    mixedMoment B raw4818 raw4818Labels = mixedMoment B raw4818step0 raw4818step0Labels := by
      have hz : ∀ j, raw4818 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4818step0 = (fun i j => raw4818 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4818step0 raw4818; decide +kernel
      have hl : raw4818step0Labels = raw4818Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4818 raw4818Labels permutation434 hz
    mixedMoment B raw4818step0 raw4818step0Labels = mixedMoment B raw4818step1 raw4818step1Labels := by
      have hz : ∀ j, raw4818step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4818step1 = (fun i j => raw4818step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4818step1 raw4818step0; decide +kernel
      have hl : raw4818step1Labels = raw4818step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4818step0 raw4818step0Labels permutation80 hz
    mixedMoment B raw4818step1 raw4818step1Labels = mixedMoment B raw4818step2 raw4818step2Labels := by
      have ha : raw4818step2 = (fun i j => raw4818step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4818step2 raw4818step1; decide +kernel
      have hl : raw4818step2Labels = raw4818step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4818step1 raw4818step1Labels permutation10 permutation2
    _ = mixedMoment B node5274 node5274Labels := by rfl

theorem canonical4819 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4819 raw4819Labels = mixedMoment B node4591 node4591Labels := by
  calc
    mixedMoment B raw4819 raw4819Labels = mixedMoment B raw4819step0 raw4819step0Labels := by
      have hz : ∀ j, raw4819 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4819step0 = (fun i j => raw4819 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4819step0 raw4819; decide +kernel
      have hl : raw4819step0Labels = raw4819Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4819 raw4819Labels permutation434 hz
    mixedMoment B raw4819step0 raw4819step0Labels = mixedMoment B raw4819step1 raw4819step1Labels := by
      have ha : raw4819step1 = (fun i j => raw4819step0 (permutation44 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4819step1 raw4819step0; decide +kernel
      have hl : raw4819step1Labels = raw4819step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4819step0 raw4819step0Labels permutation44 permutation2
    _ = mixedMoment B node4591 node4591Labels := by rfl

theorem canonical4820 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4820 raw4820Labels = mixedMoment B node5147 node5147Labels := by
  calc
    mixedMoment B raw4820 raw4820Labels = mixedMoment B raw4820step0 raw4820step0Labels := by
      have hz : ∀ j, raw4820 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4820step0 = (fun i j => raw4820 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4820step0 raw4820; decide +kernel
      have hl : raw4820step0Labels = raw4820Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4820 raw4820Labels permutation434 hz
    mixedMoment B raw4820step0 raw4820step0Labels = mixedMoment B raw4820step1 raw4820step1Labels := by
      have ha : raw4820step1 = (fun i j => raw4820step0 (permutation145 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4820step1 raw4820step0; decide +kernel
      have hl : raw4820step1Labels = raw4820step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4820step0 raw4820step0Labels permutation145 permutation2
    mixedMoment B raw4820step1 raw4820step1Labels = mixedMoment B raw4820step2 raw4820step2Labels := by
      have ha : raw4820step2 = -raw4820step1 := by apply Matrix.ext; change ∀ i j, raw4820step2 i j = -(raw4820step1 i j); unfold raw4820step2 raw4820step1; decide +kernel
      have hl : raw4820step2Labels = raw4820step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5147 node5147Labels := by rfl

theorem canonical4821 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4821 raw4821Labels = mixedMoment B node5127 node5127Labels := by
  calc
    mixedMoment B raw4821 raw4821Labels = mixedMoment B raw4821step0 raw4821step0Labels := by
      have ha : raw4821step0 = (fun i j => raw4821 (permutation212 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4821step0 raw4821; decide +kernel
      have hl : raw4821step0Labels = raw4821Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4821 raw4821Labels permutation212 permutation2
    _ = mixedMoment B node5127 node5127Labels := by rfl

theorem canonical4822 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4822 raw4822Labels = mixedMoment B node5075 node5075Labels := by
  calc
    mixedMoment B raw4822 raw4822Labels = mixedMoment B raw4822step0 raw4822step0Labels := by
      have hz : ∀ j, raw4822 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4822step0 = (fun i j => raw4822 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4822step0 raw4822; decide +kernel
      have hl : raw4822step0Labels = raw4822Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4822 raw4822Labels permutation434 hz
    mixedMoment B raw4822step0 raw4822step0Labels = mixedMoment B raw4822step1 raw4822step1Labels := by
      have ha : raw4822step1 = (fun i j => raw4822step0 (permutation44 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4822step1 raw4822step0; decide +kernel
      have hl : raw4822step1Labels = raw4822step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4822step0 raw4822step0Labels permutation44 permutation2
    _ = mixedMoment B node5075 node5075Labels := by rfl

theorem canonical4823 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4823 raw4823Labels = mixedMoment B node5258 node5258Labels := by
  calc
    mixedMoment B raw4823 raw4823Labels = mixedMoment B raw4823step0 raw4823step0Labels := by
      have hz : ∀ j, raw4823 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4823step0 = (fun i j => raw4823 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4823step0 raw4823; decide +kernel
      have hl : raw4823step0Labels = raw4823Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4823 raw4823Labels permutation434 hz
    mixedMoment B raw4823step0 raw4823step0Labels = mixedMoment B raw4823step1 raw4823step1Labels := by
      have ha : raw4823step1 = (fun i j => raw4823step0 (permutation44 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4823step1 raw4823step0; decide +kernel
      have hl : raw4823step1Labels = raw4823step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4823step0 raw4823step0Labels permutation44 permutation2
    _ = mixedMoment B node5258 node5258Labels := by rfl

theorem canonical4824 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4824 raw4824Labels = mixedMoment B node4591 node4591Labels := by
  calc
    mixedMoment B raw4824 raw4824Labels = mixedMoment B raw4824step0 raw4824step0Labels := by
      have hz : ∀ j, raw4824 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4824step0 = (fun i j => raw4824 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4824step0 raw4824; decide +kernel
      have hl : raw4824step0Labels = raw4824Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4824 raw4824Labels permutation346 hz
    mixedMoment B raw4824step0 raw4824step0Labels = mixedMoment B raw4824step1 raw4824step1Labels := by
      have ha : raw4824step1 = (fun i j => raw4824step0 (permutation44 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4824step1 raw4824step0; decide +kernel
      have hl : raw4824step1Labels = raw4824step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4824step0 raw4824step0Labels permutation44 permutation2
    _ = mixedMoment B node4591 node4591Labels := by rfl

theorem canonical4825 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4825 raw4825Labels = mixedMoment B node5147 node5147Labels := by
  calc
    mixedMoment B raw4825 raw4825Labels = mixedMoment B raw4825step0 raw4825step0Labels := by
      have hz : ∀ j, raw4825 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4825step0 = (fun i j => raw4825 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4825step0 raw4825; decide +kernel
      have hl : raw4825step0Labels = raw4825Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4825 raw4825Labels permutation346 hz
    mixedMoment B raw4825step0 raw4825step0Labels = mixedMoment B raw4825step1 raw4825step1Labels := by
      have ha : raw4825step1 = (fun i j => raw4825step0 (permutation145 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4825step1 raw4825step0; decide +kernel
      have hl : raw4825step1Labels = raw4825step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4825step0 raw4825step0Labels permutation145 permutation2
    mixedMoment B raw4825step1 raw4825step1Labels = mixedMoment B raw4825step2 raw4825step2Labels := by
      have ha : raw4825step2 = -raw4825step1 := by apply Matrix.ext; change ∀ i j, raw4825step2 i j = -(raw4825step1 i j); unfold raw4825step2 raw4825step1; decide +kernel
      have hl : raw4825step2Labels = raw4825step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5147 node5147Labels := by rfl

theorem canonical4826 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4826 raw4826Labels = mixedMoment B node5127 node5127Labels := by
  calc
    mixedMoment B raw4826 raw4826Labels = mixedMoment B raw4826step0 raw4826step0Labels := by
      have ha : raw4826step0 = (fun i j => raw4826 (permutation188 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4826step0 raw4826; decide +kernel
      have hl : raw4826step0Labels = raw4826Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4826 raw4826Labels permutation188 permutation2
    _ = mixedMoment B node5127 node5127Labels := by rfl

theorem canonical4827 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4827 raw4827Labels = mixedMoment B node5075 node5075Labels := by
  calc
    mixedMoment B raw4827 raw4827Labels = mixedMoment B raw4827step0 raw4827step0Labels := by
      have hz : ∀ j, raw4827 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4827step0 = (fun i j => raw4827 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4827step0 raw4827; decide +kernel
      have hl : raw4827step0Labels = raw4827Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4827 raw4827Labels permutation346 hz
    mixedMoment B raw4827step0 raw4827step0Labels = mixedMoment B raw4827step1 raw4827step1Labels := by
      have ha : raw4827step1 = (fun i j => raw4827step0 (permutation44 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4827step1 raw4827step0; decide +kernel
      have hl : raw4827step1Labels = raw4827step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4827step0 raw4827step0Labels permutation44 permutation2
    _ = mixedMoment B node5075 node5075Labels := by rfl

theorem canonical4828 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4828 raw4828Labels = mixedMoment B node5258 node5258Labels := by
  calc
    mixedMoment B raw4828 raw4828Labels = mixedMoment B raw4828step0 raw4828step0Labels := by
      have hz : ∀ j, raw4828 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4828step0 = (fun i j => raw4828 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4828step0 raw4828; decide +kernel
      have hl : raw4828step0Labels = raw4828Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4828 raw4828Labels permutation346 hz
    mixedMoment B raw4828step0 raw4828step0Labels = mixedMoment B raw4828step1 raw4828step1Labels := by
      have ha : raw4828step1 = (fun i j => raw4828step0 (permutation44 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4828step1 raw4828step0; decide +kernel
      have hl : raw4828step1Labels = raw4828step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4828step0 raw4828step0Labels permutation44 permutation2
    _ = mixedMoment B node5258 node5258Labels := by rfl

theorem canonical4829 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4829 raw4829Labels = mixedMoment B node4609 node4609Labels := by
  calc
    mixedMoment B raw4829 raw4829Labels = mixedMoment B raw4829step0 raw4829step0Labels := by
      have hz : ∀ j, raw4829 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4829step0 = (fun i j => raw4829 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4829step0 raw4829; decide +kernel
      have hl : raw4829step0Labels = raw4829Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4829 raw4829Labels permutation434 hz
    mixedMoment B raw4829step0 raw4829step0Labels = mixedMoment B raw4829step1 raw4829step1Labels := by
      have hz : ∀ j, raw4829step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4829step1 = (fun i j => raw4829step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4829step1 raw4829step0; decide +kernel
      have hl : raw4829step1Labels = raw4829step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4829step0 raw4829step0Labels permutation80 hz
    mixedMoment B raw4829step1 raw4829step1Labels = mixedMoment B raw4829step2 raw4829step2Labels := by
      have ha : raw4829step2 = (fun i j => raw4829step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4829step2 raw4829step1; decide +kernel
      have hl : raw4829step2Labels = raw4829step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4829step1 raw4829step1Labels permutation8 permutation3
    mixedMoment B raw4829step2 raw4829step2Labels = mixedMoment B raw4829step3 raw4829step3Labels := by
      have ha : raw4829step3 = raw4829step2 := by apply Matrix.ext; unfold raw4829step3 raw4829step2; decide +kernel
      have hl : raw4829step2Labels = labelEmbedding6 ∘ raw4829step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4829step2 raw4829step2Labels raw4829step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4609 node4609Labels := by rfl

theorem canonical4830 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4830 raw4830Labels = mixedMoment B node5201 node5201Labels := by
  calc
    mixedMoment B raw4830 raw4830Labels = mixedMoment B raw4830step0 raw4830step0Labels := by
      have hz : ∀ j, raw4830 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4830step0 = (fun i j => raw4830 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4830step0 raw4830; decide +kernel
      have hl : raw4830step0Labels = raw4830Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4830 raw4830Labels permutation434 hz
    mixedMoment B raw4830step0 raw4830step0Labels = mixedMoment B raw4830step1 raw4830step1Labels := by
      have hz : ∀ j, raw4830step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4830step1 = (fun i j => raw4830step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4830step1 raw4830step0; decide +kernel
      have hl : raw4830step1Labels = raw4830step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4830step0 raw4830step0Labels permutation80 hz
    _ = mixedMoment B node5201 node5201Labels := by rfl

theorem canonical4831 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4831 raw4831Labels = mixedMoment B node5147 node5147Labels := by
  calc
    mixedMoment B raw4831 raw4831Labels = mixedMoment B raw4831step0 raw4831step0Labels := by
      have hz : ∀ j, raw4831 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4831step0 = (fun i j => raw4831 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4831step0 raw4831; decide +kernel
      have hl : raw4831step0Labels = raw4831Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4831 raw4831Labels permutation434 hz
    mixedMoment B raw4831step0 raw4831step0Labels = mixedMoment B raw4831step1 raw4831step1Labels := by
      have ha : raw4831step1 = (fun i j => raw4831step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4831step1 raw4831step0; decide +kernel
      have hl : raw4831step1Labels = raw4831step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4831step0 raw4831step0Labels permutation38 permutation2
    _ = mixedMoment B node5147 node5147Labels := by rfl

theorem canonical4832 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4832 raw4832Labels = mixedMoment B node5147 node5147Labels := by
  calc
    mixedMoment B raw4832 raw4832Labels = mixedMoment B raw4832step0 raw4832step0Labels := by
      have hz : ∀ j, raw4832 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4832step0 = (fun i j => raw4832 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4832step0 raw4832; decide +kernel
      have hl : raw4832step0Labels = raw4832Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4832 raw4832Labels permutation346 hz
    mixedMoment B raw4832step0 raw4832step0Labels = mixedMoment B raw4832step1 raw4832step1Labels := by
      have ha : raw4832step1 = (fun i j => raw4832step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4832step1 raw4832step0; decide +kernel
      have hl : raw4832step1Labels = raw4832step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4832step0 raw4832step0Labels permutation38 permutation2
    _ = mixedMoment B node5147 node5147Labels := by rfl

theorem canonical4833 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4833 raw4833Labels = mixedMoment B node5291 node5291Labels := by
  calc
    mixedMoment B raw4833 raw4833Labels = mixedMoment B raw4833step0 raw4833step0Labels := by
      have hz : ∀ j, raw4833 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4833step0 = (fun i j => raw4833 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4833step0 raw4833; decide +kernel
      have hl : raw4833step0Labels = raw4833Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4833 raw4833Labels permutation434 hz
    mixedMoment B raw4833step0 raw4833step0Labels = mixedMoment B raw4833step1 raw4833step1Labels := by
      have hz : ∀ j, raw4833step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4833step1 = (fun i j => raw4833step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4833step1 raw4833step0; decide +kernel
      have hl : raw4833step1Labels = raw4833step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4833step0 raw4833step0Labels permutation80 hz
    _ = mixedMoment B node5291 node5291Labels := by rfl

theorem canonical4834 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4834 raw4834Labels = mixedMoment B node4594 node4594Labels := by
  calc
    mixedMoment B raw4834 raw4834Labels = mixedMoment B raw4834step0 raw4834step0Labels := by
      have hz : ∀ j, raw4834 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4834step0 = (fun i j => raw4834 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4834step0 raw4834; decide +kernel
      have hl : raw4834step0Labels = raw4834Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4834 raw4834Labels permutation434 hz
    mixedMoment B raw4834step0 raw4834step0Labels = mixedMoment B raw4834step1 raw4834step1Labels := by
      have hz : ∀ j, raw4834step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4834step1 = (fun i j => raw4834step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4834step1 raw4834step0; decide +kernel
      have hl : raw4834step1Labels = raw4834step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4834step0 raw4834step0Labels permutation80 hz
    mixedMoment B raw4834step1 raw4834step1Labels = mixedMoment B raw4834step2 raw4834step2Labels := by
      have ha : raw4834step2 = (fun i j => raw4834step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4834step2 raw4834step1; decide +kernel
      have hl : raw4834step2Labels = raw4834step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4834step1 raw4834step1Labels permutation10 permutation2
    _ = mixedMoment B node4594 node4594Labels := by rfl

theorem canonical4835 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4835 raw4835Labels = mixedMoment B node4609 node4609Labels := by
  calc
    mixedMoment B raw4835 raw4835Labels = mixedMoment B raw4835step0 raw4835step0Labels := by
      have hz : ∀ j, raw4835 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4835step0 = (fun i j => raw4835 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4835step0 raw4835; decide +kernel
      have hl : raw4835step0Labels = raw4835Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4835 raw4835Labels permutation434 hz
    mixedMoment B raw4835step0 raw4835step0Labels = mixedMoment B raw4835step1 raw4835step1Labels := by
      have hz : ∀ j, raw4835step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4835step1 = (fun i j => raw4835step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4835step1 raw4835step0; decide +kernel
      have hl : raw4835step1Labels = raw4835step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4835step0 raw4835step0Labels permutation80 hz
    mixedMoment B raw4835step1 raw4835step1Labels = mixedMoment B raw4835step2 raw4835step2Labels := by
      have ha : raw4835step2 = (fun i j => raw4835step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4835step2 raw4835step1; decide +kernel
      have hl : raw4835step2Labels = raw4835step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4835step1 raw4835step1Labels permutation31 permutation3
    mixedMoment B raw4835step2 raw4835step2Labels = mixedMoment B raw4835step3 raw4835step3Labels := by
      have ha : raw4835step3 = -raw4835step2 := by apply Matrix.ext; change ∀ i j, raw4835step3 i j = -(raw4835step2 i j); unfold raw4835step3 raw4835step2; decide +kernel
      have hl : raw4835step3Labels = raw4835step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw4835step3 raw4835step3Labels = mixedMoment B raw4835step4 raw4835step4Labels := by
      have ha : raw4835step4 = raw4835step3 := by apply Matrix.ext; unfold raw4835step4 raw4835step3; decide +kernel
      have hl : raw4835step3Labels = labelEmbedding6 ∘ raw4835step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4835step3 raw4835step3Labels raw4835step4Labels labelEmbedding6 hl
    _ = mixedMoment B node4609 node4609Labels := by rfl

theorem canonical4836 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4836 raw4836Labels = mixedMoment B node4591 node4591Labels := by
  calc
    mixedMoment B raw4836 raw4836Labels = mixedMoment B raw4836step0 raw4836step0Labels := by
      have hz : ∀ j, raw4836 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4836step0 = (fun i j => raw4836 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4836step0 raw4836; decide +kernel
      have hl : raw4836step0Labels = raw4836Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4836 raw4836Labels permutation434 hz
    mixedMoment B raw4836step0 raw4836step0Labels = mixedMoment B raw4836step1 raw4836step1Labels := by
      have ha : raw4836step1 = (fun i j => raw4836step0 (permutation139 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4836step1 raw4836step0; decide +kernel
      have hl : raw4836step1Labels = raw4836step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4836step0 raw4836step0Labels permutation139 permutation2
    mixedMoment B raw4836step1 raw4836step1Labels = mixedMoment B raw4836step2 raw4836step2Labels := by
      have ha : raw4836step2 = -raw4836step1 := by apply Matrix.ext; change ∀ i j, raw4836step2 i j = -(raw4836step1 i j); unfold raw4836step2 raw4836step1; decide +kernel
      have hl : raw4836step2Labels = raw4836step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4591 node4591Labels := by rfl

theorem canonical4837 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4837 raw4837Labels = mixedMoment B node4591 node4591Labels := by
  calc
    mixedMoment B raw4837 raw4837Labels = mixedMoment B raw4837step0 raw4837step0Labels := by
      have hz : ∀ j, raw4837 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4837step0 = (fun i j => raw4837 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4837step0 raw4837; decide +kernel
      have hl : raw4837step0Labels = raw4837Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4837 raw4837Labels permutation346 hz
    mixedMoment B raw4837step0 raw4837step0Labels = mixedMoment B raw4837step1 raw4837step1Labels := by
      have ha : raw4837step1 = (fun i j => raw4837step0 (permutation139 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4837step1 raw4837step0; decide +kernel
      have hl : raw4837step1Labels = raw4837step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4837step0 raw4837step0Labels permutation139 permutation2
    mixedMoment B raw4837step1 raw4837step1Labels = mixedMoment B raw4837step2 raw4837step2Labels := by
      have ha : raw4837step2 = -raw4837step1 := by apply Matrix.ext; change ∀ i j, raw4837step2 i j = -(raw4837step1 i j); unfold raw4837step2 raw4837step1; decide +kernel
      have hl : raw4837step2Labels = raw4837step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4591 node4591Labels := by rfl

theorem canonical4838 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4838 raw4838Labels = mixedMoment B node4608 node4608Labels := by
  calc
    mixedMoment B raw4838 raw4838Labels = mixedMoment B raw4838step0 raw4838step0Labels := by
      have hz : ∀ j, raw4838 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4838step0 = (fun i j => raw4838 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4838step0 raw4838; decide +kernel
      have hl : raw4838step0Labels = raw4838Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4838 raw4838Labels permutation434 hz
    mixedMoment B raw4838step0 raw4838step0Labels = mixedMoment B raw4838step1 raw4838step1Labels := by
      have hz : ∀ j, raw4838step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4838step1 = (fun i j => raw4838step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4838step1 raw4838step0; decide +kernel
      have hl : raw4838step1Labels = raw4838step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4838step0 raw4838step0Labels permutation80 hz
    mixedMoment B raw4838step1 raw4838step1Labels = mixedMoment B raw4838step2 raw4838step2Labels := by
      have ha : raw4838step2 = (fun i j => raw4838step1 (permutation29 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4838step2 raw4838step1; decide +kernel
      have hl : raw4838step2Labels = raw4838step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4838step1 raw4838step1Labels permutation29 permutation2
    mixedMoment B raw4838step2 raw4838step2Labels = mixedMoment B raw4838step3 raw4838step3Labels := by
      have ha : raw4838step3 = -raw4838step2 := by apply Matrix.ext; change ∀ i j, raw4838step3 i j = -(raw4838step2 i j); unfold raw4838step3 raw4838step2; decide +kernel
      have hl : raw4838step3Labels = raw4838step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4608 node4608Labels := by rfl

end MUB6.Certificate.MixedSemantics

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

theorem canonical4869 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4869 raw4869Labels = mixedMoment B node3582 node3582Labels := by
  calc
    mixedMoment B raw4869 raw4869Labels = mixedMoment B raw4869step0 raw4869step0Labels := by
      have hz : ∀ j, raw4869 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4869step0 = (fun i j => raw4869 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4869step0 raw4869; decide +kernel
      have hl : raw4869step0Labels = raw4869Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4869 raw4869Labels permutation434 hz
    mixedMoment B raw4869step0 raw4869step0Labels = mixedMoment B raw4869step1 raw4869step1Labels := by
      have hz : ∀ j, raw4869step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4869step1 = (fun i j => raw4869step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4869step1 raw4869step0; decide +kernel
      have hl : raw4869step1Labels = raw4869step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4869step0 raw4869step0Labels permutation80 hz
    mixedMoment B raw4869step1 raw4869step1Labels = mixedMoment B raw4869step2 raw4869step2Labels := by
      have ha : raw4869step2 = (fun i j => raw4869step1 (permutation29 i) (permutation7 j)) := by apply Matrix.ext; unfold raw4869step2 raw4869step1; decide +kernel
      have hl : raw4869step2Labels = raw4869step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4869step1 raw4869step1Labels permutation29 permutation7
    mixedMoment B raw4869step2 raw4869step2Labels = mixedMoment B raw4869step3 raw4869step3Labels := by
      have ha : raw4869step3 = raw4869step2 := by apply Matrix.ext; unfold raw4869step3 raw4869step2; decide +kernel
      have hl : raw4869step2Labels = labelEmbedding1 ∘ raw4869step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4869step2 raw4869step2Labels raw4869step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3582 node3582Labels := by rfl

theorem canonical4870 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4870 raw4870Labels = mixedMoment B node3533 node3533Labels := by
  calc
    mixedMoment B raw4870 raw4870Labels = mixedMoment B raw4870step0 raw4870step0Labels := by
      have hz : ∀ j, raw4870 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4870step0 = (fun i j => raw4870 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4870step0 raw4870; decide +kernel
      have hl : raw4870step0Labels = raw4870Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4870 raw4870Labels permutation434 hz
    mixedMoment B raw4870step0 raw4870step0Labels = mixedMoment B raw4870step1 raw4870step1Labels := by
      have ha : raw4870step1 = (fun i j => raw4870step0 (permutation137 i) (permutation7 j)) := by apply Matrix.ext; unfold raw4870step1 raw4870step0; decide +kernel
      have hl : raw4870step1Labels = raw4870step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4870step0 raw4870step0Labels permutation137 permutation7
    mixedMoment B raw4870step1 raw4870step1Labels = mixedMoment B raw4870step2 raw4870step2Labels := by
      have ha : raw4870step2 = raw4870step1 := by apply Matrix.ext; unfold raw4870step2 raw4870step1; decide +kernel
      have hl : raw4870step1Labels = labelEmbedding1 ∘ raw4870step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4870step1 raw4870step1Labels raw4870step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3533 node3533Labels := by rfl

theorem canonical4871 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4871 raw4871Labels = mixedMoment B node3533 node3533Labels := by
  calc
    mixedMoment B raw4871 raw4871Labels = mixedMoment B raw4871step0 raw4871step0Labels := by
      have hz : ∀ j, raw4871 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4871step0 = (fun i j => raw4871 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4871step0 raw4871; decide +kernel
      have hl : raw4871step0Labels = raw4871Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4871 raw4871Labels permutation346 hz
    mixedMoment B raw4871step0 raw4871step0Labels = mixedMoment B raw4871step1 raw4871step1Labels := by
      have ha : raw4871step1 = (fun i j => raw4871step0 (permutation137 i) (permutation7 j)) := by apply Matrix.ext; unfold raw4871step1 raw4871step0; decide +kernel
      have hl : raw4871step1Labels = raw4871step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4871step0 raw4871step0Labels permutation137 permutation7
    mixedMoment B raw4871step1 raw4871step1Labels = mixedMoment B raw4871step2 raw4871step2Labels := by
      have ha : raw4871step2 = raw4871step1 := by apply Matrix.ext; unfold raw4871step2 raw4871step1; decide +kernel
      have hl : raw4871step1Labels = labelEmbedding1 ∘ raw4871step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4871step1 raw4871step1Labels raw4871step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3533 node3533Labels := by rfl

theorem canonical4872 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4872 raw4872Labels = mixedMoment B node3547 node3547Labels := by
  calc
    mixedMoment B raw4872 raw4872Labels = mixedMoment B raw4872step0 raw4872step0Labels := by
      have hz : ∀ j, raw4872 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4872step0 = (fun i j => raw4872 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4872step0 raw4872; decide +kernel
      have hl : raw4872step0Labels = raw4872Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4872 raw4872Labels permutation434 hz
    mixedMoment B raw4872step0 raw4872step0Labels = mixedMoment B raw4872step1 raw4872step1Labels := by
      have hz : ∀ j, raw4872step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4872step1 = (fun i j => raw4872step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4872step1 raw4872step0; decide +kernel
      have hl : raw4872step1Labels = raw4872step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4872step0 raw4872step0Labels permutation80 hz
    mixedMoment B raw4872step1 raw4872step1Labels = mixedMoment B raw4872step2 raw4872step2Labels := by
      have ha : raw4872step2 = (fun i j => raw4872step1 (permutation29 i) (permutation7 j)) := by apply Matrix.ext; unfold raw4872step2 raw4872step1; decide +kernel
      have hl : raw4872step2Labels = raw4872step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4872step1 raw4872step1Labels permutation29 permutation7
    mixedMoment B raw4872step2 raw4872step2Labels = mixedMoment B raw4872step3 raw4872step3Labels := by
      have ha : raw4872step3 = raw4872step2 := by apply Matrix.ext; unfold raw4872step3 raw4872step2; decide +kernel
      have hl : raw4872step2Labels = labelEmbedding1 ∘ raw4872step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4872step2 raw4872step2Labels raw4872step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3547 node3547Labels := by rfl

theorem canonical4873 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4873 raw4873Labels = mixedMoment B node3860 node3860Labels := by
  calc
    mixedMoment B raw4873 raw4873Labels = mixedMoment B raw4873step0 raw4873step0Labels := by
      have hz : ∀ j, raw4873 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4873step0 = (fun i j => raw4873 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4873step0 raw4873; decide +kernel
      have hl : raw4873step0Labels = raw4873Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4873 raw4873Labels permutation434 hz
    mixedMoment B raw4873step0 raw4873step0Labels = mixedMoment B raw4873step1 raw4873step1Labels := by
      have hz : ∀ j, raw4873step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4873step1 = (fun i j => raw4873step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4873step1 raw4873step0; decide +kernel
      have hl : raw4873step1Labels = raw4873step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4873step0 raw4873step0Labels permutation80 hz
    mixedMoment B raw4873step1 raw4873step1Labels = mixedMoment B raw4873step2 raw4873step2Labels := by
      have ha : raw4873step2 = (fun i j => raw4873step1 (permutation29 i) (permutation7 j)) := by apply Matrix.ext; unfold raw4873step2 raw4873step1; decide +kernel
      have hl : raw4873step2Labels = raw4873step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4873step1 raw4873step1Labels permutation29 permutation7
    mixedMoment B raw4873step2 raw4873step2Labels = mixedMoment B raw4873step3 raw4873step3Labels := by
      have ha : raw4873step3 = raw4873step2 := by apply Matrix.ext; unfold raw4873step3 raw4873step2; decide +kernel
      have hl : raw4873step2Labels = labelEmbedding1 ∘ raw4873step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4873step2 raw4873step2Labels raw4873step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3860 node3860Labels := by rfl

theorem canonical4874 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4874 raw4874Labels = mixedMoment B node3300 node3300Labels := by
  calc
    mixedMoment B raw4874 raw4874Labels = mixedMoment B raw4874step0 raw4874step0Labels := by
      have hz : ∀ j, raw4874 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4874step0 = (fun i j => raw4874 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4874step0 raw4874; decide +kernel
      have hl : raw4874step0Labels = raw4874Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4874 raw4874Labels permutation434 hz
    mixedMoment B raw4874step0 raw4874step0Labels = mixedMoment B raw4874step1 raw4874step1Labels := by
      have hz : ∀ j, raw4874step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4874step1 = (fun i j => raw4874step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4874step1 raw4874step0; decide +kernel
      have hl : raw4874step1Labels = raw4874step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4874step0 raw4874step0Labels permutation80 hz
    mixedMoment B raw4874step1 raw4874step1Labels = mixedMoment B raw4874step2 raw4874step2Labels := by
      have ha : raw4874step2 = (fun i j => raw4874step1 (permutation10 i) (permutation7 j)) := by apply Matrix.ext; unfold raw4874step2 raw4874step1; decide +kernel
      have hl : raw4874step2Labels = raw4874step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4874step1 raw4874step1Labels permutation10 permutation7
    mixedMoment B raw4874step2 raw4874step2Labels = mixedMoment B raw4874step3 raw4874step3Labels := by
      have ha : raw4874step3 = -raw4874step2 := by apply Matrix.ext; change ∀ i j, raw4874step3 i j = -(raw4874step2 i j); unfold raw4874step3 raw4874step2; decide +kernel
      have hl : raw4874step3Labels = raw4874step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw4874step3 raw4874step3Labels = mixedMoment B raw4874step4 raw4874step4Labels := by
      have ha : raw4874step4 = raw4874step3 := by apply Matrix.ext; unfold raw4874step4 raw4874step3; decide +kernel
      have hl : raw4874step3Labels = labelEmbedding1 ∘ raw4874step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4874step3 raw4874step3Labels raw4874step4Labels labelEmbedding1 hl
    _ = mixedMoment B node3300 node3300Labels := by rfl

theorem canonical4875 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4875 raw4875Labels = mixedMoment B node3468 node3468Labels := by
  calc
    mixedMoment B raw4875 raw4875Labels = mixedMoment B raw4875step0 raw4875step0Labels := by
      have hz : ∀ j, raw4875 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4875step0 = (fun i j => raw4875 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4875step0 raw4875; decide +kernel
      have hl : raw4875step0Labels = raw4875Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4875 raw4875Labels permutation434 hz
    mixedMoment B raw4875step0 raw4875step0Labels = mixedMoment B raw4875step1 raw4875step1Labels := by
      have ha : raw4875step1 = (fun i j => raw4875step0 (permutation137 i) (permutation7 j)) := by apply Matrix.ext; unfold raw4875step1 raw4875step0; decide +kernel
      have hl : raw4875step1Labels = raw4875step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4875step0 raw4875step0Labels permutation137 permutation7
    mixedMoment B raw4875step1 raw4875step1Labels = mixedMoment B raw4875step2 raw4875step2Labels := by
      have ha : raw4875step2 = raw4875step1 := by apply Matrix.ext; unfold raw4875step2 raw4875step1; decide +kernel
      have hl : raw4875step1Labels = labelEmbedding1 ∘ raw4875step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4875step1 raw4875step1Labels raw4875step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3468 node3468Labels := by rfl

theorem canonical4876 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4876 raw4876Labels = mixedMoment B node3468 node3468Labels := by
  calc
    mixedMoment B raw4876 raw4876Labels = mixedMoment B raw4876step0 raw4876step0Labels := by
      have hz : ∀ j, raw4876 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4876step0 = (fun i j => raw4876 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4876step0 raw4876; decide +kernel
      have hl : raw4876step0Labels = raw4876Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4876 raw4876Labels permutation346 hz
    mixedMoment B raw4876step0 raw4876step0Labels = mixedMoment B raw4876step1 raw4876step1Labels := by
      have ha : raw4876step1 = (fun i j => raw4876step0 (permutation137 i) (permutation7 j)) := by apply Matrix.ext; unfold raw4876step1 raw4876step0; decide +kernel
      have hl : raw4876step1Labels = raw4876step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4876step0 raw4876step0Labels permutation137 permutation7
    mixedMoment B raw4876step1 raw4876step1Labels = mixedMoment B raw4876step2 raw4876step2Labels := by
      have ha : raw4876step2 = raw4876step1 := by apply Matrix.ext; unfold raw4876step2 raw4876step1; decide +kernel
      have hl : raw4876step1Labels = labelEmbedding1 ∘ raw4876step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4876step1 raw4876step1Labels raw4876step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3468 node3468Labels := by rfl

theorem canonical4877 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4877 raw4877Labels = mixedMoment B node3484 node3484Labels := by
  calc
    mixedMoment B raw4877 raw4877Labels = mixedMoment B raw4877step0 raw4877step0Labels := by
      have hz : ∀ j, raw4877 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4877step0 = (fun i j => raw4877 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4877step0 raw4877; decide +kernel
      have hl : raw4877step0Labels = raw4877Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4877 raw4877Labels permutation434 hz
    mixedMoment B raw4877step0 raw4877step0Labels = mixedMoment B raw4877step1 raw4877step1Labels := by
      have hz : ∀ j, raw4877step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4877step1 = (fun i j => raw4877step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4877step1 raw4877step0; decide +kernel
      have hl : raw4877step1Labels = raw4877step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4877step0 raw4877step0Labels permutation80 hz
    mixedMoment B raw4877step1 raw4877step1Labels = mixedMoment B raw4877step2 raw4877step2Labels := by
      have ha : raw4877step2 = (fun i j => raw4877step1 (permutation29 i) (permutation7 j)) := by apply Matrix.ext; unfold raw4877step2 raw4877step1; decide +kernel
      have hl : raw4877step2Labels = raw4877step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4877step1 raw4877step1Labels permutation29 permutation7
    mixedMoment B raw4877step2 raw4877step2Labels = mixedMoment B raw4877step3 raw4877step3Labels := by
      have ha : raw4877step3 = raw4877step2 := by apply Matrix.ext; unfold raw4877step3 raw4877step2; decide +kernel
      have hl : raw4877step2Labels = labelEmbedding1 ∘ raw4877step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4877step2 raw4877step2Labels raw4877step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3484 node3484Labels := by rfl

theorem canonical4878 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4878 raw4878Labels = mixedMoment B node3547 node3547Labels := by
  calc
    mixedMoment B raw4878 raw4878Labels = mixedMoment B raw4878step0 raw4878step0Labels := by
      have hz : ∀ j, raw4878 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4878step0 = (fun i j => raw4878 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4878step0 raw4878; decide +kernel
      have hl : raw4878step0Labels = raw4878Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4878 raw4878Labels permutation434 hz
    mixedMoment B raw4878step0 raw4878step0Labels = mixedMoment B raw4878step1 raw4878step1Labels := by
      have hz : ∀ j, raw4878step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4878step1 = (fun i j => raw4878step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4878step1 raw4878step0; decide +kernel
      have hl : raw4878step1Labels = raw4878step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4878step0 raw4878step0Labels permutation80 hz
    mixedMoment B raw4878step1 raw4878step1Labels = mixedMoment B raw4878step2 raw4878step2Labels := by
      have ha : raw4878step2 = (fun i j => raw4878step1 (permutation10 i) (permutation7 j)) := by apply Matrix.ext; unfold raw4878step2 raw4878step1; decide +kernel
      have hl : raw4878step2Labels = raw4878step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4878step1 raw4878step1Labels permutation10 permutation7
    mixedMoment B raw4878step2 raw4878step2Labels = mixedMoment B raw4878step3 raw4878step3Labels := by
      have ha : raw4878step3 = -raw4878step2 := by apply Matrix.ext; change ∀ i j, raw4878step3 i j = -(raw4878step2 i j); unfold raw4878step3 raw4878step2; decide +kernel
      have hl : raw4878step3Labels = raw4878step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw4878step3 raw4878step3Labels = mixedMoment B raw4878step4 raw4878step4Labels := by
      have ha : raw4878step4 = raw4878step3 := by apply Matrix.ext; unfold raw4878step4 raw4878step3; decide +kernel
      have hl : raw4878step3Labels = labelEmbedding1 ∘ raw4878step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4878step3 raw4878step3Labels raw4878step4Labels labelEmbedding1 hl
    _ = mixedMoment B node3547 node3547Labels := by rfl

theorem canonical4879 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4879 raw4879Labels = mixedMoment B node3291 node3291Labels := by
  calc
    mixedMoment B raw4879 raw4879Labels = mixedMoment B raw4879step0 raw4879step0Labels := by
      have hz : ∀ j, raw4879 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4879step0 = (fun i j => raw4879 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4879step0 raw4879; decide +kernel
      have hl : raw4879step0Labels = raw4879Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4879 raw4879Labels permutation434 hz
    mixedMoment B raw4879step0 raw4879step0Labels = mixedMoment B raw4879step1 raw4879step1Labels := by
      have ha : raw4879step1 = (fun i j => raw4879step0 (permutation46 i) (permutation7 j)) := by apply Matrix.ext; unfold raw4879step1 raw4879step0; decide +kernel
      have hl : raw4879step1Labels = raw4879step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4879step0 raw4879step0Labels permutation46 permutation7
    mixedMoment B raw4879step1 raw4879step1Labels = mixedMoment B raw4879step2 raw4879step2Labels := by
      have ha : raw4879step2 = -raw4879step1 := by apply Matrix.ext; change ∀ i j, raw4879step2 i j = -(raw4879step1 i j); unfold raw4879step2 raw4879step1; decide +kernel
      have hl : raw4879step2Labels = raw4879step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw4879step2 raw4879step2Labels = mixedMoment B raw4879step3 raw4879step3Labels := by
      have ha : raw4879step3 = raw4879step2 := by apply Matrix.ext; unfold raw4879step3 raw4879step2; decide +kernel
      have hl : raw4879step2Labels = labelEmbedding1 ∘ raw4879step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4879step2 raw4879step2Labels raw4879step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3291 node3291Labels := by rfl

theorem canonical4880 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4880 raw4880Labels = mixedMoment B node3530 node3530Labels := by
  calc
    mixedMoment B raw4880 raw4880Labels = mixedMoment B raw4880step0 raw4880step0Labels := by
      have hz : ∀ j, raw4880 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4880step0 = (fun i j => raw4880 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4880step0 raw4880; decide +kernel
      have hl : raw4880step0Labels = raw4880Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4880 raw4880Labels permutation434 hz
    mixedMoment B raw4880step0 raw4880step0Labels = mixedMoment B raw4880step1 raw4880step1Labels := by
      have ha : raw4880step1 = (fun i j => raw4880step0 (permutation46 i) (permutation7 j)) := by apply Matrix.ext; unfold raw4880step1 raw4880step0; decide +kernel
      have hl : raw4880step1Labels = raw4880step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4880step0 raw4880step0Labels permutation46 permutation7
    mixedMoment B raw4880step1 raw4880step1Labels = mixedMoment B raw4880step2 raw4880step2Labels := by
      have ha : raw4880step2 = -raw4880step1 := by apply Matrix.ext; change ∀ i j, raw4880step2 i j = -(raw4880step1 i j); unfold raw4880step2 raw4880step1; decide +kernel
      have hl : raw4880step2Labels = raw4880step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw4880step2 raw4880step2Labels = mixedMoment B raw4880step3 raw4880step3Labels := by
      have ha : raw4880step3 = raw4880step2 := by apply Matrix.ext; unfold raw4880step3 raw4880step2; decide +kernel
      have hl : raw4880step2Labels = labelEmbedding1 ∘ raw4880step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4880step2 raw4880step2Labels raw4880step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3530 node3530Labels := by rfl

theorem canonical4881 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4881 raw4881Labels = mixedMoment B node3513 node3513Labels := by
  calc
    mixedMoment B raw4881 raw4881Labels = mixedMoment B raw4881step0 raw4881step0Labels := by
      have ha : raw4881step0 = (fun i j => raw4881 (permutation609 i) (permutation7 j)) := by apply Matrix.ext; unfold raw4881step0 raw4881; decide +kernel
      have hl : raw4881step0Labels = raw4881Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4881 raw4881Labels permutation609 permutation7
    mixedMoment B raw4881step0 raw4881step0Labels = mixedMoment B raw4881step1 raw4881step1Labels := by
      have ha : raw4881step1 = raw4881step0 := by apply Matrix.ext; unfold raw4881step1 raw4881step0; decide +kernel
      have hl : raw4881step0Labels = labelEmbedding1 ∘ raw4881step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4881step0 raw4881step0Labels raw4881step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3513 node3513Labels := by rfl

theorem canonical4882 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4882 raw4882Labels = mixedMoment B node3468 node3468Labels := by
  calc
    mixedMoment B raw4882 raw4882Labels = mixedMoment B raw4882step0 raw4882step0Labels := by
      have hz : ∀ j, raw4882 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4882step0 = (fun i j => raw4882 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4882step0 raw4882; decide +kernel
      have hl : raw4882step0Labels = raw4882Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4882 raw4882Labels permutation434 hz
    mixedMoment B raw4882step0 raw4882step0Labels = mixedMoment B raw4882step1 raw4882step1Labels := by
      have ha : raw4882step1 = (fun i j => raw4882step0 (permutation46 i) (permutation7 j)) := by apply Matrix.ext; unfold raw4882step1 raw4882step0; decide +kernel
      have hl : raw4882step1Labels = raw4882step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4882step0 raw4882step0Labels permutation46 permutation7
    mixedMoment B raw4882step1 raw4882step1Labels = mixedMoment B raw4882step2 raw4882step2Labels := by
      have ha : raw4882step2 = -raw4882step1 := by apply Matrix.ext; change ∀ i j, raw4882step2 i j = -(raw4882step1 i j); unfold raw4882step2 raw4882step1; decide +kernel
      have hl : raw4882step2Labels = raw4882step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw4882step2 raw4882step2Labels = mixedMoment B raw4882step3 raw4882step3Labels := by
      have ha : raw4882step3 = raw4882step2 := by apply Matrix.ext; unfold raw4882step3 raw4882step2; decide +kernel
      have hl : raw4882step2Labels = labelEmbedding1 ∘ raw4882step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4882step2 raw4882step2Labels raw4882step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3468 node3468Labels := by rfl

theorem canonical4883 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4883 raw4883Labels = mixedMoment B node3533 node3533Labels := by
  calc
    mixedMoment B raw4883 raw4883Labels = mixedMoment B raw4883step0 raw4883step0Labels := by
      have hz : ∀ j, raw4883 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4883step0 = (fun i j => raw4883 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4883step0 raw4883; decide +kernel
      have hl : raw4883step0Labels = raw4883Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4883 raw4883Labels permutation434 hz
    mixedMoment B raw4883step0 raw4883step0Labels = mixedMoment B raw4883step1 raw4883step1Labels := by
      have ha : raw4883step1 = (fun i j => raw4883step0 (permutation46 i) (permutation7 j)) := by apply Matrix.ext; unfold raw4883step1 raw4883step0; decide +kernel
      have hl : raw4883step1Labels = raw4883step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4883step0 raw4883step0Labels permutation46 permutation7
    mixedMoment B raw4883step1 raw4883step1Labels = mixedMoment B raw4883step2 raw4883step2Labels := by
      have ha : raw4883step2 = -raw4883step1 := by apply Matrix.ext; change ∀ i j, raw4883step2 i j = -(raw4883step1 i j); unfold raw4883step2 raw4883step1; decide +kernel
      have hl : raw4883step2Labels = raw4883step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw4883step2 raw4883step2Labels = mixedMoment B raw4883step3 raw4883step3Labels := by
      have ha : raw4883step3 = raw4883step2 := by apply Matrix.ext; unfold raw4883step3 raw4883step2; decide +kernel
      have hl : raw4883step2Labels = labelEmbedding1 ∘ raw4883step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4883step2 raw4883step2Labels raw4883step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3533 node3533Labels := by rfl

theorem canonical4884 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4884 raw4884Labels = mixedMoment B node3291 node3291Labels := by
  calc
    mixedMoment B raw4884 raw4884Labels = mixedMoment B raw4884step0 raw4884step0Labels := by
      have hz : ∀ j, raw4884 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4884step0 = (fun i j => raw4884 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4884step0 raw4884; decide +kernel
      have hl : raw4884step0Labels = raw4884Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4884 raw4884Labels permutation346 hz
    mixedMoment B raw4884step0 raw4884step0Labels = mixedMoment B raw4884step1 raw4884step1Labels := by
      have ha : raw4884step1 = (fun i j => raw4884step0 (permutation46 i) (permutation7 j)) := by apply Matrix.ext; unfold raw4884step1 raw4884step0; decide +kernel
      have hl : raw4884step1Labels = raw4884step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4884step0 raw4884step0Labels permutation46 permutation7
    mixedMoment B raw4884step1 raw4884step1Labels = mixedMoment B raw4884step2 raw4884step2Labels := by
      have ha : raw4884step2 = -raw4884step1 := by apply Matrix.ext; change ∀ i j, raw4884step2 i j = -(raw4884step1 i j); unfold raw4884step2 raw4884step1; decide +kernel
      have hl : raw4884step2Labels = raw4884step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw4884step2 raw4884step2Labels = mixedMoment B raw4884step3 raw4884step3Labels := by
      have ha : raw4884step3 = raw4884step2 := by apply Matrix.ext; unfold raw4884step3 raw4884step2; decide +kernel
      have hl : raw4884step2Labels = labelEmbedding1 ∘ raw4884step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4884step2 raw4884step2Labels raw4884step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3291 node3291Labels := by rfl

theorem canonical4885 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4885 raw4885Labels = mixedMoment B node3530 node3530Labels := by
  calc
    mixedMoment B raw4885 raw4885Labels = mixedMoment B raw4885step0 raw4885step0Labels := by
      have hz : ∀ j, raw4885 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4885step0 = (fun i j => raw4885 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4885step0 raw4885; decide +kernel
      have hl : raw4885step0Labels = raw4885Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4885 raw4885Labels permutation346 hz
    mixedMoment B raw4885step0 raw4885step0Labels = mixedMoment B raw4885step1 raw4885step1Labels := by
      have ha : raw4885step1 = (fun i j => raw4885step0 (permutation46 i) (permutation7 j)) := by apply Matrix.ext; unfold raw4885step1 raw4885step0; decide +kernel
      have hl : raw4885step1Labels = raw4885step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4885step0 raw4885step0Labels permutation46 permutation7
    mixedMoment B raw4885step1 raw4885step1Labels = mixedMoment B raw4885step2 raw4885step2Labels := by
      have ha : raw4885step2 = -raw4885step1 := by apply Matrix.ext; change ∀ i j, raw4885step2 i j = -(raw4885step1 i j); unfold raw4885step2 raw4885step1; decide +kernel
      have hl : raw4885step2Labels = raw4885step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw4885step2 raw4885step2Labels = mixedMoment B raw4885step3 raw4885step3Labels := by
      have ha : raw4885step3 = raw4885step2 := by apply Matrix.ext; unfold raw4885step3 raw4885step2; decide +kernel
      have hl : raw4885step2Labels = labelEmbedding1 ∘ raw4885step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4885step2 raw4885step2Labels raw4885step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3530 node3530Labels := by rfl

theorem canonical4886 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4886 raw4886Labels = mixedMoment B node3513 node3513Labels := by
  calc
    mixedMoment B raw4886 raw4886Labels = mixedMoment B raw4886step0 raw4886step0Labels := by
      have ha : raw4886step0 = (fun i j => raw4886 (permutation614 i) (permutation7 j)) := by apply Matrix.ext; unfold raw4886step0 raw4886; decide +kernel
      have hl : raw4886step0Labels = raw4886Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4886 raw4886Labels permutation614 permutation7
    mixedMoment B raw4886step0 raw4886step0Labels = mixedMoment B raw4886step1 raw4886step1Labels := by
      have ha : raw4886step1 = raw4886step0 := by apply Matrix.ext; unfold raw4886step1 raw4886step0; decide +kernel
      have hl : raw4886step0Labels = labelEmbedding1 ∘ raw4886step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4886step0 raw4886step0Labels raw4886step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3513 node3513Labels := by rfl

theorem canonical4887 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4887 raw4887Labels = mixedMoment B node3468 node3468Labels := by
  calc
    mixedMoment B raw4887 raw4887Labels = mixedMoment B raw4887step0 raw4887step0Labels := by
      have hz : ∀ j, raw4887 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4887step0 = (fun i j => raw4887 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4887step0 raw4887; decide +kernel
      have hl : raw4887step0Labels = raw4887Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4887 raw4887Labels permutation346 hz
    mixedMoment B raw4887step0 raw4887step0Labels = mixedMoment B raw4887step1 raw4887step1Labels := by
      have ha : raw4887step1 = (fun i j => raw4887step0 (permutation46 i) (permutation7 j)) := by apply Matrix.ext; unfold raw4887step1 raw4887step0; decide +kernel
      have hl : raw4887step1Labels = raw4887step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4887step0 raw4887step0Labels permutation46 permutation7
    mixedMoment B raw4887step1 raw4887step1Labels = mixedMoment B raw4887step2 raw4887step2Labels := by
      have ha : raw4887step2 = -raw4887step1 := by apply Matrix.ext; change ∀ i j, raw4887step2 i j = -(raw4887step1 i j); unfold raw4887step2 raw4887step1; decide +kernel
      have hl : raw4887step2Labels = raw4887step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw4887step2 raw4887step2Labels = mixedMoment B raw4887step3 raw4887step3Labels := by
      have ha : raw4887step3 = raw4887step2 := by apply Matrix.ext; unfold raw4887step3 raw4887step2; decide +kernel
      have hl : raw4887step2Labels = labelEmbedding1 ∘ raw4887step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4887step2 raw4887step2Labels raw4887step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3468 node3468Labels := by rfl

theorem canonical4888 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4888 raw4888Labels = mixedMoment B node3533 node3533Labels := by
  calc
    mixedMoment B raw4888 raw4888Labels = mixedMoment B raw4888step0 raw4888step0Labels := by
      have hz : ∀ j, raw4888 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4888step0 = (fun i j => raw4888 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4888step0 raw4888; decide +kernel
      have hl : raw4888step0Labels = raw4888Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4888 raw4888Labels permutation346 hz
    mixedMoment B raw4888step0 raw4888step0Labels = mixedMoment B raw4888step1 raw4888step1Labels := by
      have ha : raw4888step1 = (fun i j => raw4888step0 (permutation46 i) (permutation7 j)) := by apply Matrix.ext; unfold raw4888step1 raw4888step0; decide +kernel
      have hl : raw4888step1Labels = raw4888step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4888step0 raw4888step0Labels permutation46 permutation7
    mixedMoment B raw4888step1 raw4888step1Labels = mixedMoment B raw4888step2 raw4888step2Labels := by
      have ha : raw4888step2 = -raw4888step1 := by apply Matrix.ext; change ∀ i j, raw4888step2 i j = -(raw4888step1 i j); unfold raw4888step2 raw4888step1; decide +kernel
      have hl : raw4888step2Labels = raw4888step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw4888step2 raw4888step2Labels = mixedMoment B raw4888step3 raw4888step3Labels := by
      have ha : raw4888step3 = raw4888step2 := by apply Matrix.ext; unfold raw4888step3 raw4888step2; decide +kernel
      have hl : raw4888step2Labels = labelEmbedding1 ∘ raw4888step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4888step2 raw4888step2Labels raw4888step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3533 node3533Labels := by rfl

theorem canonical4889 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4889 raw4889Labels = mixedMoment B node3302 node3302Labels := by
  calc
    mixedMoment B raw4889 raw4889Labels = mixedMoment B raw4889step0 raw4889step0Labels := by
      have hz : ∀ j, raw4889 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4889step0 = (fun i j => raw4889 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4889step0 raw4889; decide +kernel
      have hl : raw4889step0Labels = raw4889Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4889 raw4889Labels permutation434 hz
    mixedMoment B raw4889step0 raw4889step0Labels = mixedMoment B raw4889step1 raw4889step1Labels := by
      have hz : ∀ j, raw4889step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4889step1 = (fun i j => raw4889step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4889step1 raw4889step0; decide +kernel
      have hl : raw4889step1Labels = raw4889step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4889step0 raw4889step0Labels permutation80 hz
    mixedMoment B raw4889step1 raw4889step1Labels = mixedMoment B raw4889step2 raw4889step2Labels := by
      have ha : raw4889step2 = (fun i j => raw4889step1 (permutation9 i) (permutation5 j)) := by apply Matrix.ext; unfold raw4889step2 raw4889step1; decide +kernel
      have hl : raw4889step2Labels = raw4889step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4889step1 raw4889step1Labels permutation9 permutation5
    mixedMoment B raw4889step2 raw4889step2Labels = mixedMoment B raw4889step3 raw4889step3Labels := by
      have ha : raw4889step3 = -raw4889step2 := by apply Matrix.ext; change ∀ i j, raw4889step3 i j = -(raw4889step2 i j); unfold raw4889step3 raw4889step2; decide +kernel
      have hl : raw4889step3Labels = raw4889step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw4889step3 raw4889step3Labels = mixedMoment B raw4889step4 raw4889step4Labels := by
      have ha : raw4889step4 = raw4889step3 := by apply Matrix.ext; unfold raw4889step4 raw4889step3; decide +kernel
      have hl : raw4889step3Labels = labelEmbedding1 ∘ raw4889step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4889step3 raw4889step3Labels raw4889step4Labels labelEmbedding1 hl
    _ = mixedMoment B node3302 node3302Labels := by rfl

theorem canonical4890 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4890 raw4890Labels = mixedMoment B node3579 node3579Labels := by
  calc
    mixedMoment B raw4890 raw4890Labels = mixedMoment B raw4890step0 raw4890step0Labels := by
      have hz : ∀ j, raw4890 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4890step0 = (fun i j => raw4890 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4890step0 raw4890; decide +kernel
      have hl : raw4890step0Labels = raw4890Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4890 raw4890Labels permutation434 hz
    mixedMoment B raw4890step0 raw4890step0Labels = mixedMoment B raw4890step1 raw4890step1Labels := by
      have hz : ∀ j, raw4890step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4890step1 = (fun i j => raw4890step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4890step1 raw4890step0; decide +kernel
      have hl : raw4890step1Labels = raw4890step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4890step0 raw4890step0Labels permutation80 hz
    mixedMoment B raw4890step1 raw4890step1Labels = mixedMoment B raw4890step2 raw4890step2Labels := by
      have ha : raw4890step2 = (fun i j => raw4890step1 (permutation29 i) (permutation7 j)) := by apply Matrix.ext; unfold raw4890step2 raw4890step1; decide +kernel
      have hl : raw4890step2Labels = raw4890step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4890step1 raw4890step1Labels permutation29 permutation7
    mixedMoment B raw4890step2 raw4890step2Labels = mixedMoment B raw4890step3 raw4890step3Labels := by
      have ha : raw4890step3 = raw4890step2 := by apply Matrix.ext; unfold raw4890step3 raw4890step2; decide +kernel
      have hl : raw4890step2Labels = labelEmbedding1 ∘ raw4890step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4890step2 raw4890step2Labels raw4890step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3579 node3579Labels := by rfl

theorem canonical4891 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4891 raw4891Labels = mixedMoment B node3530 node3530Labels := by
  calc
    mixedMoment B raw4891 raw4891Labels = mixedMoment B raw4891step0 raw4891step0Labels := by
      have hz : ∀ j, raw4891 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4891step0 = (fun i j => raw4891 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4891step0 raw4891; decide +kernel
      have hl : raw4891step0Labels = raw4891Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4891 raw4891Labels permutation434 hz
    mixedMoment B raw4891step0 raw4891step0Labels = mixedMoment B raw4891step1 raw4891step1Labels := by
      have ha : raw4891step1 = (fun i j => raw4891step0 (permutation137 i) (permutation7 j)) := by apply Matrix.ext; unfold raw4891step1 raw4891step0; decide +kernel
      have hl : raw4891step1Labels = raw4891step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4891step0 raw4891step0Labels permutation137 permutation7
    mixedMoment B raw4891step1 raw4891step1Labels = mixedMoment B raw4891step2 raw4891step2Labels := by
      have ha : raw4891step2 = raw4891step1 := by apply Matrix.ext; unfold raw4891step2 raw4891step1; decide +kernel
      have hl : raw4891step1Labels = labelEmbedding1 ∘ raw4891step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4891step1 raw4891step1Labels raw4891step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3530 node3530Labels := by rfl

theorem canonical4892 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4892 raw4892Labels = mixedMoment B node3530 node3530Labels := by
  calc
    mixedMoment B raw4892 raw4892Labels = mixedMoment B raw4892step0 raw4892step0Labels := by
      have hz : ∀ j, raw4892 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4892step0 = (fun i j => raw4892 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4892step0 raw4892; decide +kernel
      have hl : raw4892step0Labels = raw4892Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4892 raw4892Labels permutation346 hz
    mixedMoment B raw4892step0 raw4892step0Labels = mixedMoment B raw4892step1 raw4892step1Labels := by
      have ha : raw4892step1 = (fun i j => raw4892step0 (permutation137 i) (permutation7 j)) := by apply Matrix.ext; unfold raw4892step1 raw4892step0; decide +kernel
      have hl : raw4892step1Labels = raw4892step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4892step0 raw4892step0Labels permutation137 permutation7
    mixedMoment B raw4892step1 raw4892step1Labels = mixedMoment B raw4892step2 raw4892step2Labels := by
      have ha : raw4892step2 = raw4892step1 := by apply Matrix.ext; unfold raw4892step2 raw4892step1; decide +kernel
      have hl : raw4892step1Labels = labelEmbedding1 ∘ raw4892step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4892step1 raw4892step1Labels raw4892step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3530 node3530Labels := by rfl

theorem canonical4893 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4893 raw4893Labels = mixedMoment B node3582 node3582Labels := by
  calc
    mixedMoment B raw4893 raw4893Labels = mixedMoment B raw4893step0 raw4893step0Labels := by
      have hz : ∀ j, raw4893 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4893step0 = (fun i j => raw4893 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4893step0 raw4893; decide +kernel
      have hl : raw4893step0Labels = raw4893Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4893 raw4893Labels permutation434 hz
    mixedMoment B raw4893step0 raw4893step0Labels = mixedMoment B raw4893step1 raw4893step1Labels := by
      have hz : ∀ j, raw4893step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4893step1 = (fun i j => raw4893step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4893step1 raw4893step0; decide +kernel
      have hl : raw4893step1Labels = raw4893step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4893step0 raw4893step0Labels permutation80 hz
    mixedMoment B raw4893step1 raw4893step1Labels = mixedMoment B raw4893step2 raw4893step2Labels := by
      have ha : raw4893step2 = (fun i j => raw4893step1 (permutation10 i) (permutation7 j)) := by apply Matrix.ext; unfold raw4893step2 raw4893step1; decide +kernel
      have hl : raw4893step2Labels = raw4893step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4893step1 raw4893step1Labels permutation10 permutation7
    mixedMoment B raw4893step2 raw4893step2Labels = mixedMoment B raw4893step3 raw4893step3Labels := by
      have ha : raw4893step3 = -raw4893step2 := by apply Matrix.ext; change ∀ i j, raw4893step3 i j = -(raw4893step2 i j); unfold raw4893step3 raw4893step2; decide +kernel
      have hl : raw4893step3Labels = raw4893step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw4893step3 raw4893step3Labels = mixedMoment B raw4893step4 raw4893step4Labels := by
      have ha : raw4893step4 = raw4893step3 := by apply Matrix.ext; unfold raw4893step4 raw4893step3; decide +kernel
      have hl : raw4893step3Labels = labelEmbedding1 ∘ raw4893step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4893step3 raw4893step3Labels raw4893step4Labels labelEmbedding1 hl
    _ = mixedMoment B node3582 node3582Labels := by rfl

theorem canonical4894 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4894 raw4894Labels = mixedMoment B node3298 node3298Labels := by
  calc
    mixedMoment B raw4894 raw4894Labels = mixedMoment B raw4894step0 raw4894step0Labels := by
      have hz : ∀ j, raw4894 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4894step0 = (fun i j => raw4894 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4894step0 raw4894; decide +kernel
      have hl : raw4894step0Labels = raw4894Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4894 raw4894Labels permutation434 hz
    mixedMoment B raw4894step0 raw4894step0Labels = mixedMoment B raw4894step1 raw4894step1Labels := by
      have hz : ∀ j, raw4894step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4894step1 = (fun i j => raw4894step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4894step1 raw4894step0; decide +kernel
      have hl : raw4894step1Labels = raw4894step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4894step0 raw4894step0Labels permutation80 hz
    mixedMoment B raw4894step1 raw4894step1Labels = mixedMoment B raw4894step2 raw4894step2Labels := by
      have ha : raw4894step2 = (fun i j => raw4894step1 (permutation31 i) (permutation5 j)) := by apply Matrix.ext; unfold raw4894step2 raw4894step1; decide +kernel
      have hl : raw4894step2Labels = raw4894step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4894step1 raw4894step1Labels permutation31 permutation5
    mixedMoment B raw4894step2 raw4894step2Labels = mixedMoment B raw4894step3 raw4894step3Labels := by
      have ha : raw4894step3 = raw4894step2 := by apply Matrix.ext; unfold raw4894step3 raw4894step2; decide +kernel
      have hl : raw4894step2Labels = labelEmbedding1 ∘ raw4894step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4894step2 raw4894step2Labels raw4894step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3298 node3298Labels := by rfl

theorem canonical4895 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4895 raw4895Labels = mixedMoment B node3302 node3302Labels := by
  calc
    mixedMoment B raw4895 raw4895Labels = mixedMoment B raw4895step0 raw4895step0Labels := by
      have hz : ∀ j, raw4895 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4895step0 = (fun i j => raw4895 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4895step0 raw4895; decide +kernel
      have hl : raw4895step0Labels = raw4895Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4895 raw4895Labels permutation434 hz
    mixedMoment B raw4895step0 raw4895step0Labels = mixedMoment B raw4895step1 raw4895step1Labels := by
      have hz : ∀ j, raw4895step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4895step1 = (fun i j => raw4895step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4895step1 raw4895step0; decide +kernel
      have hl : raw4895step1Labels = raw4895step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4895step0 raw4895step0Labels permutation80 hz
    mixedMoment B raw4895step1 raw4895step1Labels = mixedMoment B raw4895step2 raw4895step2Labels := by
      have ha : raw4895step2 = (fun i j => raw4895step1 (permutation30 i) (permutation5 j)) := by apply Matrix.ext; unfold raw4895step2 raw4895step1; decide +kernel
      have hl : raw4895step2Labels = raw4895step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4895step1 raw4895step1Labels permutation30 permutation5
    mixedMoment B raw4895step2 raw4895step2Labels = mixedMoment B raw4895step3 raw4895step3Labels := by
      have ha : raw4895step3 = raw4895step2 := by apply Matrix.ext; unfold raw4895step3 raw4895step2; decide +kernel
      have hl : raw4895step2Labels = labelEmbedding1 ∘ raw4895step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4895step2 raw4895step2Labels raw4895step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3302 node3302Labels := by rfl

theorem canonical4896 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4896 raw4896Labels = mixedMoment B node3291 node3291Labels := by
  calc
    mixedMoment B raw4896 raw4896Labels = mixedMoment B raw4896step0 raw4896step0Labels := by
      have hz : ∀ j, raw4896 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4896step0 = (fun i j => raw4896 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4896step0 raw4896; decide +kernel
      have hl : raw4896step0Labels = raw4896Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4896 raw4896Labels permutation434 hz
    mixedMoment B raw4896step0 raw4896step0Labels = mixedMoment B raw4896step1 raw4896step1Labels := by
      have ha : raw4896step1 = (fun i j => raw4896step0 (permutation137 i) (permutation7 j)) := by apply Matrix.ext; unfold raw4896step1 raw4896step0; decide +kernel
      have hl : raw4896step1Labels = raw4896step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4896step0 raw4896step0Labels permutation137 permutation7
    mixedMoment B raw4896step1 raw4896step1Labels = mixedMoment B raw4896step2 raw4896step2Labels := by
      have ha : raw4896step2 = raw4896step1 := by apply Matrix.ext; unfold raw4896step2 raw4896step1; decide +kernel
      have hl : raw4896step1Labels = labelEmbedding1 ∘ raw4896step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4896step1 raw4896step1Labels raw4896step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3291 node3291Labels := by rfl

theorem canonical4897 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4897 raw4897Labels = mixedMoment B node3291 node3291Labels := by
  calc
    mixedMoment B raw4897 raw4897Labels = mixedMoment B raw4897step0 raw4897step0Labels := by
      have hz : ∀ j, raw4897 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4897step0 = (fun i j => raw4897 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4897step0 raw4897; decide +kernel
      have hl : raw4897step0Labels = raw4897Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4897 raw4897Labels permutation346 hz
    mixedMoment B raw4897step0 raw4897step0Labels = mixedMoment B raw4897step1 raw4897step1Labels := by
      have ha : raw4897step1 = (fun i j => raw4897step0 (permutation137 i) (permutation7 j)) := by apply Matrix.ext; unfold raw4897step1 raw4897step0; decide +kernel
      have hl : raw4897step1Labels = raw4897step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4897step0 raw4897step0Labels permutation137 permutation7
    mixedMoment B raw4897step1 raw4897step1Labels = mixedMoment B raw4897step2 raw4897step2Labels := by
      have ha : raw4897step2 = raw4897step1 := by apply Matrix.ext; unfold raw4897step2 raw4897step1; decide +kernel
      have hl : raw4897step1Labels = labelEmbedding1 ∘ raw4897step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4897step1 raw4897step1Labels raw4897step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3291 node3291Labels := by rfl

theorem canonical4898 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4898 raw4898Labels = mixedMoment B node3300 node3300Labels := by
  calc
    mixedMoment B raw4898 raw4898Labels = mixedMoment B raw4898step0 raw4898step0Labels := by
      have hz : ∀ j, raw4898 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4898step0 = (fun i j => raw4898 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4898step0 raw4898; decide +kernel
      have hl : raw4898step0Labels = raw4898Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4898 raw4898Labels permutation434 hz
    mixedMoment B raw4898step0 raw4898step0Labels = mixedMoment B raw4898step1 raw4898step1Labels := by
      have hz : ∀ j, raw4898step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4898step1 = (fun i j => raw4898step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4898step1 raw4898step0; decide +kernel
      have hl : raw4898step1Labels = raw4898step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4898step0 raw4898step0Labels permutation80 hz
    mixedMoment B raw4898step1 raw4898step1Labels = mixedMoment B raw4898step2 raw4898step2Labels := by
      have ha : raw4898step2 = (fun i j => raw4898step1 (permutation29 i) (permutation7 j)) := by apply Matrix.ext; unfold raw4898step2 raw4898step1; decide +kernel
      have hl : raw4898step2Labels = raw4898step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4898step1 raw4898step1Labels permutation29 permutation7
    mixedMoment B raw4898step2 raw4898step2Labels = mixedMoment B raw4898step3 raw4898step3Labels := by
      have ha : raw4898step3 = raw4898step2 := by apply Matrix.ext; unfold raw4898step3 raw4898step2; decide +kernel
      have hl : raw4898step2Labels = labelEmbedding1 ∘ raw4898step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4898step2 raw4898step2Labels raw4898step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3300 node3300Labels := by rfl

theorem canonical4899 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4899 raw4899Labels = mixedMoment B node2726 node2726Labels := by
  calc
    mixedMoment B raw4899 raw4899Labels = mixedMoment B raw4899step0 raw4899step0Labels := by
      have hz : ∀ j, raw4899 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4899step0 = (fun i j => raw4899 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4899step0 raw4899; decide +kernel
      have hl : raw4899step0Labels = raw4899Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4899 raw4899Labels permutation434 hz
    mixedMoment B raw4899step0 raw4899step0Labels = mixedMoment B raw4899step1 raw4899step1Labels := by
      have hz : ∀ j, raw4899step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4899step1 = (fun i j => raw4899step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4899step1 raw4899step0; decide +kernel
      have hl : raw4899step1Labels = raw4899step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4899step0 raw4899step0Labels permutation80 hz
    mixedMoment B raw4899step1 raw4899step1Labels = mixedMoment B raw4899step2 raw4899step2Labels := by
      have ha : raw4899step2 = (fun i j => raw4899step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4899step2 raw4899step1; decide +kernel
      have hl : raw4899step2Labels = raw4899step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4899step1 raw4899step1Labels permutation10 permutation2
    _ = mixedMoment B node2726 node2726Labels := by rfl

theorem canonical4900 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4900 raw4900Labels = mixedMoment B node2765 node2765Labels := by
  calc
    mixedMoment B raw4900 raw4900Labels = mixedMoment B raw4900step0 raw4900step0Labels := by
      have hz : ∀ j, raw4900 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4900step0 = (fun i j => raw4900 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4900step0 raw4900; decide +kernel
      have hl : raw4900step0Labels = raw4900Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4900 raw4900Labels permutation434 hz
    mixedMoment B raw4900step0 raw4900step0Labels = mixedMoment B raw4900step1 raw4900step1Labels := by
      have hz : ∀ j, raw4900step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4900step1 = (fun i j => raw4900step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4900step1 raw4900step0; decide +kernel
      have hl : raw4900step1Labels = raw4900step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4900step0 raw4900step0Labels permutation80 hz
    mixedMoment B raw4900step1 raw4900step1Labels = mixedMoment B raw4900step2 raw4900step2Labels := by
      have ha : raw4900step2 = (fun i j => raw4900step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4900step2 raw4900step1; decide +kernel
      have hl : raw4900step2Labels = raw4900step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4900step1 raw4900step1Labels permutation31 permutation2
    mixedMoment B raw4900step2 raw4900step2Labels = mixedMoment B raw4900step3 raw4900step3Labels := by
      have ha : raw4900step3 = -raw4900step2 := by apply Matrix.ext; change ∀ i j, raw4900step3 i j = -(raw4900step2 i j); unfold raw4900step3 raw4900step2; decide +kernel
      have hl : raw4900step3Labels = raw4900step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2765 node2765Labels := by rfl

theorem canonical4901 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4901 raw4901Labels = mixedMoment B node2722 node2722Labels := by
  calc
    mixedMoment B raw4901 raw4901Labels = mixedMoment B raw4901step0 raw4901step0Labels := by
      have hz : ∀ j, raw4901 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4901step0 = (fun i j => raw4901 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4901step0 raw4901; decide +kernel
      have hl : raw4901step0Labels = raw4901Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4901 raw4901Labels permutation434 hz
    mixedMoment B raw4901step0 raw4901step0Labels = mixedMoment B raw4901step1 raw4901step1Labels := by
      have ha : raw4901step1 = (fun i j => raw4901step0 (permutation139 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4901step1 raw4901step0; decide +kernel
      have hl : raw4901step1Labels = raw4901step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4901step0 raw4901step0Labels permutation139 permutation2
    mixedMoment B raw4901step1 raw4901step1Labels = mixedMoment B raw4901step2 raw4901step2Labels := by
      have ha : raw4901step2 = -raw4901step1 := by apply Matrix.ext; change ∀ i j, raw4901step2 i j = -(raw4901step1 i j); unfold raw4901step2 raw4901step1; decide +kernel
      have hl : raw4901step2Labels = raw4901step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2722 node2722Labels := by rfl

theorem canonical4902 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4902 raw4902Labels = mixedMoment B node2722 node2722Labels := by
  calc
    mixedMoment B raw4902 raw4902Labels = mixedMoment B raw4902step0 raw4902step0Labels := by
      have hz : ∀ j, raw4902 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4902step0 = (fun i j => raw4902 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4902step0 raw4902; decide +kernel
      have hl : raw4902step0Labels = raw4902Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4902 raw4902Labels permutation346 hz
    mixedMoment B raw4902step0 raw4902step0Labels = mixedMoment B raw4902step1 raw4902step1Labels := by
      have ha : raw4902step1 = (fun i j => raw4902step0 (permutation139 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4902step1 raw4902step0; decide +kernel
      have hl : raw4902step1Labels = raw4902step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4902step0 raw4902step0Labels permutation139 permutation2
    mixedMoment B raw4902step1 raw4902step1Labels = mixedMoment B raw4902step2 raw4902step2Labels := by
      have ha : raw4902step2 = -raw4902step1 := by apply Matrix.ext; change ∀ i j, raw4902step2 i j = -(raw4902step1 i j); unfold raw4902step2 raw4902step1; decide +kernel
      have hl : raw4902step2Labels = raw4902step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2722 node2722Labels := by rfl

theorem canonical4903 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4903 raw4903Labels = mixedMoment B node2742 node2742Labels := by
  calc
    mixedMoment B raw4903 raw4903Labels = mixedMoment B raw4903step0 raw4903step0Labels := by
      have hz : ∀ j, raw4903 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4903step0 = (fun i j => raw4903 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4903step0 raw4903; decide +kernel
      have hl : raw4903step0Labels = raw4903Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4903 raw4903Labels permutation434 hz
    mixedMoment B raw4903step0 raw4903step0Labels = mixedMoment B raw4903step1 raw4903step1Labels := by
      have hz : ∀ j, raw4903step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4903step1 = (fun i j => raw4903step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4903step1 raw4903step0; decide +kernel
      have hl : raw4903step1Labels = raw4903step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4903step0 raw4903step0Labels permutation80 hz
    mixedMoment B raw4903step1 raw4903step1Labels = mixedMoment B raw4903step2 raw4903step2Labels := by
      have ha : raw4903step2 = (fun i j => raw4903step1 (permutation29 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4903step2 raw4903step1; decide +kernel
      have hl : raw4903step2Labels = raw4903step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4903step1 raw4903step1Labels permutation29 permutation2
    mixedMoment B raw4903step2 raw4903step2Labels = mixedMoment B raw4903step3 raw4903step3Labels := by
      have ha : raw4903step3 = -raw4903step2 := by apply Matrix.ext; change ∀ i j, raw4903step3 i j = -(raw4903step2 i j); unfold raw4903step3 raw4903step2; decide +kernel
      have hl : raw4903step3Labels = raw4903step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2742 node2742Labels := by rfl

theorem canonical4904 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4904 raw4904Labels = mixedMoment B node3905 node3905Labels := by
  calc
    mixedMoment B raw4904 raw4904Labels = mixedMoment B raw4904step0 raw4904step0Labels := by
      have hz : ∀ j, raw4904 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4904step0 = (fun i j => raw4904 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4904step0 raw4904; decide +kernel
      have hl : raw4904step0Labels = raw4904Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4904 raw4904Labels permutation434 hz
    mixedMoment B raw4904step0 raw4904step0Labels = mixedMoment B raw4904step1 raw4904step1Labels := by
      have hz : ∀ j, raw4904step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4904step1 = (fun i j => raw4904step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4904step1 raw4904step0; decide +kernel
      have hl : raw4904step1Labels = raw4904step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4904step0 raw4904step0Labels permutation80 hz
    mixedMoment B raw4904step1 raw4904step1Labels = mixedMoment B raw4904step2 raw4904step2Labels := by
      have ha : raw4904step2 = (fun i j => raw4904step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4904step2 raw4904step1; decide +kernel
      have hl : raw4904step2Labels = raw4904step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4904step1 raw4904step1Labels permutation10 permutation2
    _ = mixedMoment B node3905 node3905Labels := by rfl

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

theorem canonical4906 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4906 raw4906Labels = mixedMoment B node1242 node1242Labels := by
  calc
    mixedMoment B raw4906 raw4906Labels = mixedMoment B raw4906step0 raw4906step0Labels := by
      have hz : ∀ j, raw4906 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4906step0 = (fun i j => raw4906 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4906step0 raw4906; decide +kernel
      have hl : raw4906step0Labels = raw4906Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4906 raw4906Labels permutation434 hz
    mixedMoment B raw4906step0 raw4906step0Labels = mixedMoment B raw4906step1 raw4906step1Labels := by
      have hz : ∀ j, raw4906step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4906step1 = (fun i j => raw4906step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4906step1 raw4906step0; decide +kernel
      have hl : raw4906step1Labels = raw4906step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4906step0 raw4906step0Labels permutation80 hz
    mixedMoment B raw4906step1 raw4906step1Labels = mixedMoment B raw4906step2 raw4906step2Labels := by
      have ha : raw4906step2 = (fun i j => raw4906step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4906step2 raw4906step1; decide +kernel
      have hl : raw4906step2Labels = raw4906step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4906step1 raw4906step1Labels permutation10 permutation2
    _ = mixedMoment B node1242 node1242Labels := by rfl

theorem canonical4907 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4907 raw4907Labels = mixedMoment B node1215 node1215Labels := by
  calc
    mixedMoment B raw4907 raw4907Labels = mixedMoment B raw4907step0 raw4907step0Labels := by
      have hz : ∀ j, raw4907 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4907step0 = (fun i j => raw4907 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4907step0 raw4907; decide +kernel
      have hl : raw4907step0Labels = raw4907Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4907 raw4907Labels permutation434 hz
    mixedMoment B raw4907step0 raw4907step0Labels = mixedMoment B raw4907step1 raw4907step1Labels := by
      have ha : raw4907step1 = (fun i j => raw4907step0 (permutation44 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4907step1 raw4907step0; decide +kernel
      have hl : raw4907step1Labels = raw4907step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4907step0 raw4907step0Labels permutation44 permutation2
    _ = mixedMoment B node1215 node1215Labels := by rfl

theorem canonical4908 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4908 raw4908Labels = mixedMoment B node1215 node1215Labels := by
  calc
    mixedMoment B raw4908 raw4908Labels = mixedMoment B raw4908step0 raw4908step0Labels := by
      have hz : ∀ j, raw4908 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4908step0 = (fun i j => raw4908 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4908step0 raw4908; decide +kernel
      have hl : raw4908step0Labels = raw4908Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4908 raw4908Labels permutation346 hz
    mixedMoment B raw4908step0 raw4908step0Labels = mixedMoment B raw4908step1 raw4908step1Labels := by
      have ha : raw4908step1 = (fun i j => raw4908step0 (permutation44 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4908step1 raw4908step0; decide +kernel
      have hl : raw4908step1Labels = raw4908step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4908step0 raw4908step0Labels permutation44 permutation2
    _ = mixedMoment B node1215 node1215Labels := by rfl

theorem canonical4909 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4909 raw4909Labels = mixedMoment B node1264 node1264Labels := by
  calc
    mixedMoment B raw4909 raw4909Labels = mixedMoment B raw4909step0 raw4909step0Labels := by
      have hz : ∀ j, raw4909 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4909step0 = (fun i j => raw4909 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4909step0 raw4909; decide +kernel
      have hl : raw4909step0Labels = raw4909Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4909 raw4909Labels permutation434 hz
    mixedMoment B raw4909step0 raw4909step0Labels = mixedMoment B raw4909step1 raw4909step1Labels := by
      have hz : ∀ j, raw4909step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4909step1 = (fun i j => raw4909step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4909step1 raw4909step0; decide +kernel
      have hl : raw4909step1Labels = raw4909step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4909step0 raw4909step0Labels permutation80 hz
    _ = mixedMoment B node1264 node1264Labels := by rfl

theorem canonical4910 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4910 raw4910Labels = mixedMoment B node1221 node1221Labels := by
  calc
    mixedMoment B raw4910 raw4910Labels = mixedMoment B raw4910step0 raw4910step0Labels := by
      have hz : ∀ j, raw4910 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4910step0 = (fun i j => raw4910 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4910step0 raw4910; decide +kernel
      have hl : raw4910step0Labels = raw4910Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4910 raw4910Labels permutation434 hz
    mixedMoment B raw4910step0 raw4910step0Labels = mixedMoment B raw4910step1 raw4910step1Labels := by
      have hz : ∀ j, raw4910step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4910step1 = (fun i j => raw4910step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4910step1 raw4910step0; decide +kernel
      have hl : raw4910step1Labels = raw4910step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4910step0 raw4910step0Labels permutation80 hz
    mixedMoment B raw4910step1 raw4910step1Labels = mixedMoment B raw4910step2 raw4910step2Labels := by
      have ha : raw4910step2 = (fun i j => raw4910step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4910step2 raw4910step1; decide +kernel
      have hl : raw4910step2Labels = raw4910step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4910step1 raw4910step1Labels permutation10 permutation2
    _ = mixedMoment B node1221 node1221Labels := by rfl

theorem canonical4911 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4911 raw4911Labels = mixedMoment B node2482 node2482Labels := by
  calc
    mixedMoment B raw4911 raw4911Labels = mixedMoment B raw4911step0 raw4911step0Labels := by
      have hz : ∀ j, raw4911 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4911step0 = (fun i j => raw4911 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4911step0 raw4911; decide +kernel
      have hl : raw4911step0Labels = raw4911Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4911 raw4911Labels permutation434 hz
    mixedMoment B raw4911step0 raw4911step0Labels = mixedMoment B raw4911step1 raw4911step1Labels := by
      have ha : raw4911step1 = (fun i j => raw4911step0 (permutation139 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4911step1 raw4911step0; decide +kernel
      have hl : raw4911step1Labels = raw4911step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4911step0 raw4911step0Labels permutation139 permutation2
    mixedMoment B raw4911step1 raw4911step1Labels = mixedMoment B raw4911step2 raw4911step2Labels := by
      have ha : raw4911step2 = -raw4911step1 := by apply Matrix.ext; change ∀ i j, raw4911step2 i j = -(raw4911step1 i j); unfold raw4911step2 raw4911step1; decide +kernel
      have hl : raw4911step2Labels = raw4911step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2482 node2482Labels := by rfl

theorem canonical4912 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4912 raw4912Labels = mixedMoment B node2482 node2482Labels := by
  calc
    mixedMoment B raw4912 raw4912Labels = mixedMoment B raw4912step0 raw4912step0Labels := by
      have hz : ∀ j, raw4912 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4912step0 = (fun i j => raw4912 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4912step0 raw4912; decide +kernel
      have hl : raw4912step0Labels = raw4912Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4912 raw4912Labels permutation346 hz
    mixedMoment B raw4912step0 raw4912step0Labels = mixedMoment B raw4912step1 raw4912step1Labels := by
      have ha : raw4912step1 = (fun i j => raw4912step0 (permutation139 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4912step1 raw4912step0; decide +kernel
      have hl : raw4912step1Labels = raw4912step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4912step0 raw4912step0Labels permutation139 permutation2
    mixedMoment B raw4912step1 raw4912step1Labels = mixedMoment B raw4912step2 raw4912step2Labels := by
      have ha : raw4912step2 = -raw4912step1 := by apply Matrix.ext; change ∀ i j, raw4912step2 i j = -(raw4912step1 i j); unfold raw4912step2 raw4912step1; decide +kernel
      have hl : raw4912step2Labels = raw4912step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2482 node2482Labels := by rfl

theorem canonical4913 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4913 raw4913Labels = mixedMoment B node2517 node2517Labels := by
  calc
    mixedMoment B raw4913 raw4913Labels = mixedMoment B raw4913step0 raw4913step0Labels := by
      have hz : ∀ j, raw4913 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4913step0 = (fun i j => raw4913 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4913step0 raw4913; decide +kernel
      have hl : raw4913step0Labels = raw4913Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4913 raw4913Labels permutation434 hz
    mixedMoment B raw4913step0 raw4913step0Labels = mixedMoment B raw4913step1 raw4913step1Labels := by
      have hz : ∀ j, raw4913step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4913step1 = (fun i j => raw4913step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4913step1 raw4913step0; decide +kernel
      have hl : raw4913step1Labels = raw4913step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4913step0 raw4913step0Labels permutation80 hz
    mixedMoment B raw4913step1 raw4913step1Labels = mixedMoment B raw4913step2 raw4913step2Labels := by
      have ha : raw4913step2 = (fun i j => raw4913step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4913step2 raw4913step1; decide +kernel
      have hl : raw4913step2Labels = raw4913step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4913step1 raw4913step1Labels permutation10 permutation2
    _ = mixedMoment B node2517 node2517Labels := by rfl

theorem canonical4914 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4914 raw4914Labels = mixedMoment B node2742 node2742Labels := by
  calc
    mixedMoment B raw4914 raw4914Labels = mixedMoment B raw4914step0 raw4914step0Labels := by
      have hz : ∀ j, raw4914 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4914step0 = (fun i j => raw4914 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4914step0 raw4914; decide +kernel
      have hl : raw4914step0Labels = raw4914Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4914 raw4914Labels permutation434 hz
    mixedMoment B raw4914step0 raw4914step0Labels = mixedMoment B raw4914step1 raw4914step1Labels := by
      have hz : ∀ j, raw4914step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4914step1 = (fun i j => raw4914step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4914step1 raw4914step0; decide +kernel
      have hl : raw4914step1Labels = raw4914step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4914step0 raw4914step0Labels permutation80 hz
    mixedMoment B raw4914step1 raw4914step1Labels = mixedMoment B raw4914step2 raw4914step2Labels := by
      have ha : raw4914step2 = (fun i j => raw4914step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4914step2 raw4914step1; decide +kernel
      have hl : raw4914step2Labels = raw4914step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4914step1 raw4914step1Labels permutation10 permutation2
    _ = mixedMoment B node2742 node2742Labels := by rfl

theorem canonical4915 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4915 raw4915Labels = mixedMoment B node2569 node2569Labels := by
  calc
    mixedMoment B raw4915 raw4915Labels = mixedMoment B raw4915step0 raw4915step0Labels := by
      have hz : ∀ j, raw4915 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4915step0 = (fun i j => raw4915 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4915step0 raw4915; decide +kernel
      have hl : raw4915step0Labels = raw4915Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4915 raw4915Labels permutation434 hz
    mixedMoment B raw4915step0 raw4915step0Labels = mixedMoment B raw4915step1 raw4915step1Labels := by
      have ha : raw4915step1 = (fun i j => raw4915step0 (permutation145 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4915step1 raw4915step0; decide +kernel
      have hl : raw4915step1Labels = raw4915step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4915step0 raw4915step0Labels permutation145 permutation2
    mixedMoment B raw4915step1 raw4915step1Labels = mixedMoment B raw4915step2 raw4915step2Labels := by
      have ha : raw4915step2 = -raw4915step1 := by apply Matrix.ext; change ∀ i j, raw4915step2 i j = -(raw4915step1 i j); unfold raw4915step2 raw4915step1; decide +kernel
      have hl : raw4915step2Labels = raw4915step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2569 node2569Labels := by rfl

theorem canonical4916 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4916 raw4916Labels = mixedMoment B node2569 node2569Labels := by
  calc
    mixedMoment B raw4916 raw4916Labels = mixedMoment B raw4916step0 raw4916step0Labels := by
      have hz : ∀ j, raw4916 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4916step0 = (fun i j => raw4916 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4916step0 raw4916; decide +kernel
      have hl : raw4916step0Labels = raw4916Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4916 raw4916Labels permutation346 hz
    mixedMoment B raw4916step0 raw4916step0Labels = mixedMoment B raw4916step1 raw4916step1Labels := by
      have ha : raw4916step1 = (fun i j => raw4916step0 (permutation145 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4916step1 raw4916step0; decide +kernel
      have hl : raw4916step1Labels = raw4916step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4916step0 raw4916step0Labels permutation145 permutation2
    mixedMoment B raw4916step1 raw4916step1Labels = mixedMoment B raw4916step2 raw4916step2Labels := by
      have ha : raw4916step2 = -raw4916step1 := by apply Matrix.ext; change ∀ i j, raw4916step2 i j = -(raw4916step1 i j); unfold raw4916step2 raw4916step1; decide +kernel
      have hl : raw4916step2Labels = raw4916step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2569 node2569Labels := by rfl

theorem canonical4917 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4917 raw4917Labels = mixedMoment B node2635 node2635Labels := by
  calc
    mixedMoment B raw4917 raw4917Labels = mixedMoment B raw4917step0 raw4917step0Labels := by
      have hz : ∀ j, raw4917 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4917step0 = (fun i j => raw4917 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4917step0 raw4917; decide +kernel
      have hl : raw4917step0Labels = raw4917Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4917 raw4917Labels permutation434 hz
    mixedMoment B raw4917step0 raw4917step0Labels = mixedMoment B raw4917step1 raw4917step1Labels := by
      have hz : ∀ j, raw4917step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4917step1 = (fun i j => raw4917step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4917step1 raw4917step0; decide +kernel
      have hl : raw4917step1Labels = raw4917step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4917step0 raw4917step0Labels permutation80 hz
    _ = mixedMoment B node2635 node2635Labels := by rfl

theorem canonical4918 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4918 raw4918Labels = mixedMoment B node1264 node1264Labels := by
  calc
    mixedMoment B raw4918 raw4918Labels = mixedMoment B raw4918step0 raw4918step0Labels := by
      have hz : ∀ j, raw4918 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4918step0 = (fun i j => raw4918 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4918step0 raw4918; decide +kernel
      have hl : raw4918step0Labels = raw4918Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4918 raw4918Labels permutation434 hz
    mixedMoment B raw4918step0 raw4918step0Labels = mixedMoment B raw4918step1 raw4918step1Labels := by
      have hz : ∀ j, raw4918step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4918step1 = (fun i j => raw4918step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4918step1 raw4918step0; decide +kernel
      have hl : raw4918step1Labels = raw4918step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4918step0 raw4918step0Labels permutation80 hz
    mixedMoment B raw4918step1 raw4918step1Labels = mixedMoment B raw4918step2 raw4918step2Labels := by
      have ha : raw4918step2 = (fun i j => raw4918step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4918step2 raw4918step1; decide +kernel
      have hl : raw4918step2Labels = raw4918step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4918step1 raw4918step1Labels permutation31 permutation2
    mixedMoment B raw4918step2 raw4918step2Labels = mixedMoment B raw4918step3 raw4918step3Labels := by
      have ha : raw4918step3 = -raw4918step2 := by apply Matrix.ext; change ∀ i j, raw4918step3 i j = -(raw4918step2 i j); unfold raw4918step3 raw4918step2; decide +kernel
      have hl : raw4918step3Labels = raw4918step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1264 node1264Labels := by rfl

theorem canonical4919 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4919 raw4919Labels = mixedMoment B node2542 node2542Labels := by
  calc
    mixedMoment B raw4919 raw4919Labels = mixedMoment B raw4919step0 raw4919step0Labels := by
      have ha : raw4919step0 = (fun i j => raw4919 (permutation212 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4919step0 raw4919; decide +kernel
      have hl : raw4919step0Labels = raw4919Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4919 raw4919Labels permutation212 permutation2
    _ = mixedMoment B node2542 node2542Labels := by rfl

theorem canonical4920 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4920 raw4920Labels = mixedMoment B node2482 node2482Labels := by
  calc
    mixedMoment B raw4920 raw4920Labels = mixedMoment B raw4920step0 raw4920step0Labels := by
      have hz : ∀ j, raw4920 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4920step0 = (fun i j => raw4920 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4920step0 raw4920; decide +kernel
      have hl : raw4920step0Labels = raw4920Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4920 raw4920Labels permutation434 hz
    mixedMoment B raw4920step0 raw4920step0Labels = mixedMoment B raw4920step1 raw4920step1Labels := by
      have ha : raw4920step1 = (fun i j => raw4920step0 (permutation44 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4920step1 raw4920step0; decide +kernel
      have hl : raw4920step1Labels = raw4920step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4920step0 raw4920step0Labels permutation44 permutation2
    _ = mixedMoment B node2482 node2482Labels := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical39
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical5052 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5052 raw5052Labels = mixedMoment B node3545 node3545Labels := by
  calc
    mixedMoment B raw5052 raw5052Labels = mixedMoment B raw5052step0 raw5052step0Labels := by
      have hz : ∀ j, raw5052 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5052step0 = (fun i j => raw5052 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5052step0 raw5052; decide +kernel
      have hl : raw5052step0Labels = raw5052Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5052 raw5052Labels permutation434 hz
    mixedMoment B raw5052step0 raw5052step0Labels = mixedMoment B raw5052step1 raw5052step1Labels := by
      have hz : ∀ j, raw5052step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5052step1 = (fun i j => raw5052step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5052step1 raw5052step0; decide +kernel
      have hl : raw5052step1Labels = raw5052step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5052step0 raw5052step0Labels permutation80 hz
    mixedMoment B raw5052step1 raw5052step1Labels = mixedMoment B raw5052step2 raw5052step2Labels := by
      have ha : raw5052step2 = (fun i j => raw5052step1 (permutation29 i) (permutation4 j)) := by apply Matrix.ext; unfold raw5052step2 raw5052step1; decide +kernel
      have hl : raw5052step2Labels = raw5052step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5052step1 raw5052step1Labels permutation29 permutation4
    _ = mixedMoment B node3545 node3545Labels := by rfl

theorem canonical5053 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5053 raw5053Labels = mixedMoment B node2065 node2065Labels := by
  calc
    mixedMoment B raw5053 raw5053Labels = mixedMoment B raw5053step0 raw5053step0Labels := by
      have hz : ∀ j, raw5053 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5053step0 = (fun i j => raw5053 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5053step0 raw5053; decide +kernel
      have hl : raw5053step0Labels = raw5053Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5053 raw5053Labels permutation434 hz
    mixedMoment B raw5053step0 raw5053step0Labels = mixedMoment B raw5053step1 raw5053step1Labels := by
      have hz : ∀ j, raw5053step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5053step1 = (fun i j => raw5053step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5053step1 raw5053step0; decide +kernel
      have hl : raw5053step1Labels = raw5053step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5053step0 raw5053step0Labels permutation80 hz
    mixedMoment B raw5053step1 raw5053step1Labels = mixedMoment B raw5053step2 raw5053step2Labels := by
      have ha : raw5053step2 = (fun i j => raw5053step1 (permutation10 i) (permutation4 j)) := by apply Matrix.ext; unfold raw5053step2 raw5053step1; decide +kernel
      have hl : raw5053step2Labels = raw5053step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5053step1 raw5053step1Labels permutation10 permutation4
    mixedMoment B raw5053step2 raw5053step2Labels = mixedMoment B raw5053step3 raw5053step3Labels := by
      have ha : raw5053step3 = -raw5053step2 := by apply Matrix.ext; change ∀ i j, raw5053step3 i j = -(raw5053step2 i j); unfold raw5053step3 raw5053step2; decide +kernel
      have hl : raw5053step3Labels = raw5053step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2065 node2065Labels := by rfl

theorem canonical5054 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5054 raw5054Labels = mixedMoment B node2052 node2052Labels := by
  calc
    mixedMoment B raw5054 raw5054Labels = mixedMoment B raw5054step0 raw5054step0Labels := by
      have hz : ∀ j, raw5054 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5054step0 = (fun i j => raw5054 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5054step0 raw5054; decide +kernel
      have hl : raw5054step0Labels = raw5054Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5054 raw5054Labels permutation434 hz
    mixedMoment B raw5054step0 raw5054step0Labels = mixedMoment B raw5054step1 raw5054step1Labels := by
      have ha : raw5054step1 = (fun i j => raw5054step0 (permutation44 i) (permutation4 j)) := by apply Matrix.ext; unfold raw5054step1 raw5054step0; decide +kernel
      have hl : raw5054step1Labels = raw5054step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5054step0 raw5054step0Labels permutation44 permutation4
    mixedMoment B raw5054step1 raw5054step1Labels = mixedMoment B raw5054step2 raw5054step2Labels := by
      have ha : raw5054step2 = -raw5054step1 := by apply Matrix.ext; change ∀ i j, raw5054step2 i j = -(raw5054step1 i j); unfold raw5054step2 raw5054step1; decide +kernel
      have hl : raw5054step2Labels = raw5054step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2052 node2052Labels := by rfl

theorem canonical5055 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5055 raw5055Labels = mixedMoment B node2052 node2052Labels := by
  calc
    mixedMoment B raw5055 raw5055Labels = mixedMoment B raw5055step0 raw5055step0Labels := by
      have hz : ∀ j, raw5055 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw5055step0 = (fun i j => raw5055 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw5055step0 raw5055; decide +kernel
      have hl : raw5055step0Labels = raw5055Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5055 raw5055Labels permutation346 hz
    mixedMoment B raw5055step0 raw5055step0Labels = mixedMoment B raw5055step1 raw5055step1Labels := by
      have ha : raw5055step1 = (fun i j => raw5055step0 (permutation44 i) (permutation4 j)) := by apply Matrix.ext; unfold raw5055step1 raw5055step0; decide +kernel
      have hl : raw5055step1Labels = raw5055step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5055step0 raw5055step0Labels permutation44 permutation4
    mixedMoment B raw5055step1 raw5055step1Labels = mixedMoment B raw5055step2 raw5055step2Labels := by
      have ha : raw5055step2 = -raw5055step1 := by apply Matrix.ext; change ∀ i j, raw5055step2 i j = -(raw5055step1 i j); unfold raw5055step2 raw5055step1; decide +kernel
      have hl : raw5055step2Labels = raw5055step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2052 node2052Labels := by rfl

theorem canonical5056 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5056 raw5056Labels = mixedMoment B node2292 node2292Labels := by
  calc
    mixedMoment B raw5056 raw5056Labels = mixedMoment B raw5056step0 raw5056step0Labels := by
      have hz : ∀ j, raw5056 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw5056step0 = (fun i j => raw5056 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw5056step0 raw5056; decide +kernel
      have hl : raw5056step0Labels = raw5056Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5056 raw5056Labels permutation520 hz
    mixedMoment B raw5056step0 raw5056step0Labels = mixedMoment B raw5056step1 raw5056step1Labels := by
      have hz : ∀ j, raw5056step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw5056step1 = (fun i j => raw5056step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw5056step1 raw5056step0; decide +kernel
      have hl : raw5056step1Labels = raw5056step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5056step0 raw5056step0Labels permutation104 hz
    mixedMoment B raw5056step1 raw5056step1Labels = mixedMoment B raw5056step2 raw5056step2Labels := by
      have hz : ∀ j, raw5056step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw5056step2 = (fun i j => raw5056step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw5056step2 raw5056step1; decide +kernel
      have hl : raw5056step2Labels = raw5056step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5056step1 raw5056step1Labels permutation20 hz
    mixedMoment B raw5056step2 raw5056step2Labels = mixedMoment B raw5056step3 raw5056step3Labels := by
      have ha : raw5056step3 = (fun i j => raw5056step2 (permutation2 i) (permutation4 j)) := by apply Matrix.ext; unfold raw5056step3 raw5056step2; decide +kernel
      have hl : raw5056step3Labels = raw5056step2Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5056step2 raw5056step2Labels permutation2 permutation4
    mixedMoment B raw5056step3 raw5056step3Labels = mixedMoment B raw5056step4 raw5056step4Labels := by
      have ha : raw5056step4 = -raw5056step3 := by apply Matrix.ext; change ∀ i j, raw5056step4 i j = -(raw5056step3 i j); unfold raw5056step4 raw5056step3; decide +kernel
      have hl : raw5056step4Labels = raw5056step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2292 node2292Labels := by rfl

theorem canonical5057 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5057 raw5057Labels = mixedMoment B node2056 node2056Labels := by
  calc
    mixedMoment B raw5057 raw5057Labels = mixedMoment B raw5057step0 raw5057step0Labels := by
      have hz : ∀ j, raw5057 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5057step0 = (fun i j => raw5057 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5057step0 raw5057; decide +kernel
      have hl : raw5057step0Labels = raw5057Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5057 raw5057Labels permutation434 hz
    mixedMoment B raw5057step0 raw5057step0Labels = mixedMoment B raw5057step1 raw5057step1Labels := by
      have hz : ∀ j, raw5057step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5057step1 = (fun i j => raw5057step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5057step1 raw5057step0; decide +kernel
      have hl : raw5057step1Labels = raw5057step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5057step0 raw5057step0Labels permutation80 hz
    mixedMoment B raw5057step1 raw5057step1Labels = mixedMoment B raw5057step2 raw5057step2Labels := by
      have ha : raw5057step2 = (fun i j => raw5057step1 (permutation29 i) (permutation4 j)) := by apply Matrix.ext; unfold raw5057step2 raw5057step1; decide +kernel
      have hl : raw5057step2Labels = raw5057step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5057step1 raw5057step1Labels permutation29 permutation4
    _ = mixedMoment B node2056 node2056Labels := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons72
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singleton4608 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4608 node4608Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1242 node1242Labels + mixedMoment B node3300 node3300Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1434 singletonSmall4608
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4608) = raw1434Labels := by decide +kernel
  rw [hl, canonical1434 B hB] at h
  have hc0 : mixedMoment B raw1434 (Fin.cases (0 : Fin 2) singletonSmall4608) =
      mixedMoment B node1242 node1242Labels := by
    have ha : raw1434 = raw1435 := by apply Matrix.ext; unfold raw1434 raw1435; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4608 = raw1435Labels := by decide +kernel
    rw [ha, hj, canonical1435 B hB]
  have hc1 : mixedMoment B raw1434 (Fin.cases (1 : Fin 2) singletonSmall4608) =
      mixedMoment B node3300 node3300Labels := by
    have ha : raw1434 = raw1436 := by apply Matrix.ext; unfold raw1434 raw1436; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4608 = raw1436Labels := by decide +kernel
    rw [ha, hj, canonical1436 B hB]
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

theorem singleton5075 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5075 node5075Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2482 node2482Labels + mixedMoment B node3468 node3468Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2097 singletonSmall5075
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5075) = raw2097Labels := by decide +kernel
  rw [hl, canonical2097 B hB] at h
  have hc0 : mixedMoment B raw2097 (Fin.cases (0 : Fin 2) singletonSmall5075) =
      mixedMoment B node2482 node2482Labels := by
    have ha : raw2097 = raw2098 := by apply Matrix.ext; unfold raw2097 raw2098; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5075 = raw2098Labels := by decide +kernel
    rw [ha, hj, canonical2098 B hB]
  have hc1 : mixedMoment B raw2097 (Fin.cases (1 : Fin 2) singletonSmall5075) =
      mixedMoment B node3468 node3468Labels := by
    have ha : raw2097 = raw2099 := by apply Matrix.ext; unfold raw2097 raw2099; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5075 = raw2099Labels := by decide +kernel
    rw [ha, hj, canonical2099 B hB]
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

theorem singleton5258 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5258 node5258Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2722 node2722Labels + mixedMoment B node3533 node3533Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2271 singletonSmall5258
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5258) = raw2271Labels := by decide +kernel
  rw [hl, canonical2271 B hB] at h
  have hc0 : mixedMoment B raw2271 (Fin.cases (0 : Fin 2) singletonSmall5258) =
      mixedMoment B node2722 node2722Labels := by
    have ha : raw2271 = raw2272 := by apply Matrix.ext; unfold raw2271 raw2272; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5258 = raw2272Labels := by decide +kernel
    rw [ha, hj, canonical2272 B hB]
  have hc1 : mixedMoment B raw2271 (Fin.cases (1 : Fin 2) singletonSmall5258) =
      mixedMoment B node3533 node3533Labels := by
    have ha : raw2271 = raw2273 := by apply Matrix.ext; unfold raw2271 raw2273; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5258 = raw2273Labels := by decide +kernel
    rw [ha, hj, canonical2273 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton5291 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5291 node5291Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2765 node2765Labels + mixedMoment B node3582 node3582Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2295 singletonSmall5291
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5291) = raw2295Labels := by decide +kernel
  rw [hl, canonical2295 B hB] at h
  have hc0 : mixedMoment B raw2295 (Fin.cases (0 : Fin 2) singletonSmall5291) =
      mixedMoment B node2765 node2765Labels := by
    have ha : raw2295 = raw2296 := by apply Matrix.ext; unfold raw2295 raw2296; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5291 = raw2296Labels := by decide +kernel
    rw [ha, hj, canonical2296 B hB]
  have hc1 : mixedMoment B raw2295 (Fin.cases (1 : Fin 2) singletonSmall5291) =
      mixedMoment B node3582 node3582Labels := by
    have ha : raw2295 = raw2297 := by apply Matrix.ext; unfold raw2295 raw2297; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5291 = raw2297Labels := by decide +kernel
    rw [ha, hj, canonical2297 B hB]
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

theorem zero5441 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5441 node5441Labels = 0 := by
  exact mixedMoment_order_one B hB node5441 node5441Labels 1
    (by decide +kernel) (by decide +kernel)

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

theorem sound1080 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1080 node1080Labels = Sparse.eval nodeValue1080 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1080) = mixedMoment B node1080 node1080Labels := rfl
  simpa [nodeValue1080, Sparse.eval] using hc.symm

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

theorem sound1215 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1215 node1215Labels = Sparse.eval nodeValue1215 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1215) = mixedMoment B node1215 node1215Labels := rfl
  simpa [nodeValue1215, Sparse.eval] using hc.symm

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

theorem sound1221 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1221 node1221Labels = Sparse.eval nodeValue1221 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1221) = mixedMoment B node1221 node1221Labels := rfl
  simpa [nodeValue1221, Sparse.eval] using hc.symm

theorem sound1242 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1242 node1242Labels = Sparse.eval nodeValue1242 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1242) = mixedMoment B node1242 node1242Labels := rfl
  simpa [nodeValue1242, Sparse.eval] using hc.symm

theorem sound1264 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1264 node1264Labels = Sparse.eval nodeValue1264 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1264) = mixedMoment B node1264 node1264Labels := rfl
  simpa [nodeValue1264, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros32
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero2056 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2056 node2056Labels = 0 := by
  exact mixedMoment_order_one B hB node2056 node2056Labels 1
    (by decide +kernel) (by decide +kernel)

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

theorem sound2052 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2052 node2052Labels = Sparse.eval nodeValue2052 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2052) = mixedMoment B node2052 node2052Labels := rfl
  simpa [nodeValue2052, Sparse.eval] using hc.symm

theorem sound2056 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2056 node2056Labels = Sparse.eval nodeValue2056 (mixedVector B) := by
  simpa only [nodeValue2056, Sparse.eval_nil] using zero2056 B _hB _hF

theorem sound2065 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2065 node2065Labels = Sparse.eval nodeValue2065 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2065) = mixedMoment B node2065 node2065Labels := rfl
  simpa [nodeValue2065, Sparse.eval] using hc.symm

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

theorem sound2482 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2482 node2482Labels = Sparse.eval nodeValue2482 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2482) = mixedMoment B node2482 node2482Labels := rfl
  simpa [nodeValue2482, Sparse.eval] using hc.symm

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

theorem zero2517 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2517 node2517Labels = 0 := by
  exact mixedMoment_order_one B hB node2517 node2517Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero2542 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node2542 node2542Labels = 0 := by
  exact mixedMoment_alpha B hF node2542 node2542Labels 1 permutation158
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

theorem sound2517 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2517 node2517Labels = Sparse.eval nodeValue2517 (mixedVector B) := by
  simpa only [nodeValue2517, Sparse.eval_nil] using zero2517 B _hB _hF

theorem sound2542 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2542 node2542Labels = Sparse.eval nodeValue2542 (mixedVector B) := by
  simpa only [nodeValue2542, Sparse.eval_nil] using zero2542 B _hB _hF

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

theorem sound2569 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2569 node2569Labels = Sparse.eval nodeValue2569 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2569) = mixedMoment B node2569 node2569Labels := rfl
  simpa [nodeValue2569, Sparse.eval] using hc.symm

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

theorem sound2635 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2635 node2635Labels = Sparse.eval nodeValue2635 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2635) = mixedMoment B node2635 node2635Labels := rfl
  simpa [nodeValue2635, Sparse.eval] using hc.symm

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

theorem zero2742 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2742 node2742Labels = 0 := by
  exact mixedMoment_order_one B hB node2742 node2742Labels 1
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

theorem sound2726 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2726 node2726Labels = Sparse.eval nodeValue2726 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2726) = mixedMoment B node2726 node2726Labels := rfl
  simpa [nodeValue2726, Sparse.eval] using hc.symm

theorem sound2742 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2742 node2742Labels = Sparse.eval nodeValue2742 (mixedVector B) := by
  simpa only [nodeValue2742, Sparse.eval_nil] using zero2742 B _hB _hF

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

theorem sound3291 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3291 node3291Labels = Sparse.eval nodeValue3291 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3291) = mixedMoment B node3291 node3291Labels := rfl
  simpa [nodeValue3291, Sparse.eval] using hc.symm

theorem sound3298 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3298 node3298Labels = Sparse.eval nodeValue3298 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3298) = mixedMoment B node3298 node3298Labels := rfl
  simpa [nodeValue3298, Sparse.eval] using hc.symm

theorem sound3300 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3300 node3300Labels = Sparse.eval nodeValue3300 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3300) = mixedMoment B node3300 node3300Labels := rfl
  simpa [nodeValue3300, Sparse.eval] using hc.symm

theorem sound3302 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3302 node3302Labels = Sparse.eval nodeValue3302 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3302) = mixedMoment B node3302 node3302Labels := rfl
  simpa [nodeValue3302, Sparse.eval] using hc.symm

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

theorem zero3484 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3484 node3484Labels = 0 := by
  exact mixedMoment_order_one B hB node3484 node3484Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero3513 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node3513 node3513Labels = 0 := by
  exact mixedMoment_alpha B hF node3513 node3513Labels 1 permutation444
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

theorem sound3468 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3468 node3468Labels = Sparse.eval nodeValue3468 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3468) = mixedMoment B node3468 node3468Labels := rfl
  simpa [nodeValue3468, Sparse.eval] using hc.symm

theorem sound3484 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3484 node3484Labels = Sparse.eval nodeValue3484 (mixedVector B) := by
  simpa only [nodeValue3484, Sparse.eval_nil] using zero3484 B _hB _hF

theorem sound3513 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3513 node3513Labels = Sparse.eval nodeValue3513 (mixedVector B) := by
  simpa only [nodeValue3513, Sparse.eval_nil] using zero3513 B _hB _hF

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

theorem zero3547 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3547 node3547Labels = 0 := by
  exact mixedMoment_order_one B hB node3547 node3547Labels 1
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

theorem sound3530 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3530 node3530Labels = Sparse.eval nodeValue3530 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3530) = mixedMoment B node3530 node3530Labels := rfl
  simpa [nodeValue3530, Sparse.eval] using hc.symm

theorem sound3533 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3533 node3533Labels = Sparse.eval nodeValue3533 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3533) = mixedMoment B node3533 node3533Labels := rfl
  simpa [nodeValue3533, Sparse.eval] using hc.symm

theorem sound3545 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3545 node3545Labels = Sparse.eval nodeValue3545 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3545) = mixedMoment B node3545 node3545Labels := rfl
  simpa [nodeValue3545, Sparse.eval] using hc.symm

theorem sound3547 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3547 node3547Labels = Sparse.eval nodeValue3547 (mixedVector B) := by
  simpa only [nodeValue3547, Sparse.eval_nil] using zero3547 B _hB _hF

theorem sound3579 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3579 node3579Labels = Sparse.eval nodeValue3579 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3579) = mixedMoment B node3579 node3579Labels := rfl
  simpa [nodeValue3579, Sparse.eval] using hc.symm

theorem sound3582 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3582 node3582Labels = Sparse.eval nodeValue3582 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3582) = mixedMoment B node3582 node3582Labels := rfl
  simpa [nodeValue3582, Sparse.eval] using hc.symm

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

theorem zero3860 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3860 node3860Labels = 0 := by
  exact mixedMoment_order_one B hB node3860 node3860Labels 1
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

theorem sound3860 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3860 node3860Labels = Sparse.eval nodeValue3860 (mixedVector B) := by
  simpa only [nodeValue3860, Sparse.eval_nil] using zero3860 B _hB _hF

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

theorem zero3905 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3905 node3905Labels = 0 := by
  exact mixedMoment_order_one B hB node3905 node3905Labels 1
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

theorem sound3905 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3905 node3905Labels = Sparse.eval nodeValue3905 (mixedVector B) := by
  simpa only [nodeValue3905, Sparse.eval_nil] using zero3905 B _hB _hF

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

theorem sound4092 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4092 node4092Labels = Sparse.eval nodeValue4092 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4092) = mixedMoment B node4092 node4092Labels := rfl
  simpa [nodeValue4092, Sparse.eval] using hc.symm

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

theorem sound4591 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4591 node4591Labels = Sparse.eval nodeValue4591 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4591) = mixedMoment B node4591 node4591Labels := rfl
  simpa [nodeValue4591, Sparse.eval] using hc.symm

theorem sound4594 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4594 node4594Labels = Sparse.eval nodeValue4594 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4594) = mixedMoment B node4594 node4594Labels := rfl
  simpa [nodeValue4594, Sparse.eval] using hc.symm

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

theorem sound4608 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4608 node4608Labels = Sparse.eval nodeValue4608 (mixedVector B) := by
  have h := singleton4608 B _hB
  rw [sound1242 B _hB _hF, sound3300 B _hB _hF] at h
  norm_num [nodeValue4608, nodeValue1242, nodeValue3300, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4609 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4609 node4609Labels = Sparse.eval nodeValue4609 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4609) = mixedMoment B node4609 node4609Labels := rfl
  simpa [nodeValue4609, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros79
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero5107 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5107 node5107Labels = 0 := by
  exact mixedMoment_order_one B hB node5107 node5107Labels 1
    (by decide +kernel) (by decide +kernel)

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

theorem sound5075 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5075 node5075Labels = Sparse.eval nodeValue5075 (mixedVector B) := by
  have h := singleton5075 B _hB
  rw [sound2482 B _hB _hF, sound3468 B _hB _hF] at h
  norm_num [nodeValue5075, nodeValue2482, nodeValue3468, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5107 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5107 node5107Labels = Sparse.eval nodeValue5107 (mixedVector B) := by
  simpa only [nodeValue5107, Sparse.eval_nil] using zero5107 B _hB _hF

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros80
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero5127 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node5127 node5127Labels = 0 := by
  exact mixedMoment_alpha B hF node5127 node5127Labels 1 permutation158
    (by decide +kernel)

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

theorem sound5127 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5127 node5127Labels = Sparse.eval nodeValue5127 (mixedVector B) := by
  simpa only [nodeValue5127, Sparse.eval_nil] using zero5127 B _hB _hF

theorem sound5147 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5147 node5147Labels = Sparse.eval nodeValue5147 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5147) = mixedMoment B node5147 node5147Labels := rfl
  simpa [nodeValue5147, Sparse.eval] using hc.symm

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

theorem sound5201 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5201 node5201Labels = Sparse.eval nodeValue5201 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5201) = mixedMoment B node5201 node5201Labels := rfl
  simpa [nodeValue5201, Sparse.eval] using hc.symm

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

theorem zero5274 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5274 node5274Labels = 0 := by
  exact mixedMoment_order_one B hB node5274 node5274Labels 1
    (by decide +kernel) (by decide +kernel)

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

theorem sound5258 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5258 node5258Labels = Sparse.eval nodeValue5258 (mixedVector B) := by
  have h := singleton5258 B _hB
  rw [sound2722 B _hB _hF, sound3533 B _hB _hF] at h
  norm_num [nodeValue5258, nodeValue2722, nodeValue3533, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5274 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5274 node5274Labels = Sparse.eval nodeValue5274 (mixedVector B) := by
  simpa only [nodeValue5274, Sparse.eval_nil] using zero5274 B _hB _hF

theorem sound5291 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5291 node5291Labels = Sparse.eval nodeValue5291 (mixedVector B) := by
  have h := singleton5291 B _hB
  rw [sound2765 B _hB _hF, sound3582 B _hB _hF] at h
  norm_num [nodeValue5291, nodeValue2765, nodeValue3582, Sparse.eval] at h ⊢
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

theorem sound5441 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5441 node5441Labels = Sparse.eval nodeValue5441 (mixedVector B) := by
  simpa only [nodeValue5441, Sparse.eval_nil] using zero5441 B _hB _hF

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources4
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sourceEq148 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm148 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA148 + difference 0 0) (sourceB148 + difference 0 0) sourceC148) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2290) := by
    have ha : (tripleCharges (sourceA148 + difference 0 0) (sourceB148 + difference 0 0) sourceC148) = raw3719 := by
      apply Matrix.ext; unfold tripleCharges sourceA148 sourceB148 sourceC148 difference raw3719; decide +kernel
    rw [ha]
    exact (canonical3719 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA148 + difference 0 1) (sourceB148 + difference 1 0) sourceC148) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2052) := by
    have ha : (tripleCharges (sourceA148 + difference 0 1) (sourceB148 + difference 1 0) sourceC148) = raw4271 := by
      apply Matrix.ext; unfold tripleCharges sourceA148 sourceB148 sourceC148 difference raw4271; decide +kernel
    rw [ha]
    exact (canonical4271 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA148 + difference 0 2) (sourceB148 + difference 2 0) sourceC148) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2052) := by
    have ha : (tripleCharges (sourceA148 + difference 0 2) (sourceB148 + difference 2 0) sourceC148) = raw4806 := by
      apply Matrix.ext; unfold tripleCharges sourceA148 sourceB148 sourceC148 difference raw4806; decide +kernel
    rw [ha]
    exact (canonical4806 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA148 + difference 0 3) (sourceB148 + difference 3 0) sourceC148) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2292) := by
    have ha : (tripleCharges (sourceA148 + difference 0 3) (sourceB148 + difference 3 0) sourceC148) = raw4375 := by
      apply Matrix.ext; unfold tripleCharges sourceA148 sourceB148 sourceC148 difference raw4375; decide +kernel
    rw [ha]
    exact (canonical4375 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA148 + difference 0 4) (sourceB148 + difference 4 0) sourceC148) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2292) := by
    have ha : (tripleCharges (sourceA148 + difference 0 4) (sourceB148 + difference 4 0) sourceC148) = raw4807 := by
      apply Matrix.ext; unfold tripleCharges sourceA148 sourceB148 sourceC148 difference raw4807; decide +kernel
    rw [ha]
    exact (canonical4807 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA148 + difference 0 5) (sourceB148 + difference 5 0) sourceC148) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1080) := by
    have ha : (tripleCharges (sourceA148 + difference 0 5) (sourceB148 + difference 5 0) sourceC148) = raw4808 := by
      apply Matrix.ext; unfold tripleCharges sourceA148 sourceB148 sourceC148 difference raw4808; decide +kernel
    rw [ha]
    exact (canonical4808 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA148 + sourceB148) sourceC148) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4085) := by
    have ha : (doubleCharges (sourceA148 + sourceB148) sourceC148) = raw3721 := by
      apply Matrix.ext; unfold doubleCharges sourceA148 sourceB148 sourceC148 raw3721; decide +kernel
    rw [ha]
    exact (canonical3721 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA148 sourceB148 sourceC148
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm148, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq149 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm149 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA149 + difference 0 1) (sourceB149 + difference 1 0) sourceC149) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5291) := by
    have ha : (tripleCharges (sourceA149 + difference 0 1) (sourceB149 + difference 1 0) sourceC149) = raw4809 := by
      apply Matrix.ext; unfold tripleCharges sourceA149 sourceB149 sourceC149 difference raw4809; decide +kernel
    rw [ha]
    exact (canonical4809 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA149 + difference 0 2) (sourceB149 + difference 2 0) sourceC149) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5258) := by
    have ha : (tripleCharges (sourceA149 + difference 0 2) (sourceB149 + difference 2 0) sourceC149) = raw4810 := by
      apply Matrix.ext; unfold tripleCharges sourceA149 sourceB149 sourceC149 difference raw4810; decide +kernel
    rw [ha]
    exact (canonical4810 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA149 + difference 0 3) (sourceB149 + difference 3 0) sourceC149) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5258) := by
    have ha : (tripleCharges (sourceA149 + difference 0 3) (sourceB149 + difference 3 0) sourceC149) = raw4811 := by
      apply Matrix.ext; unfold tripleCharges sourceA149 sourceB149 sourceC149 difference raw4811; decide +kernel
    rw [ha]
    exact (canonical4811 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA149 + difference 0 4) (sourceB149 + difference 4 0) sourceC149) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5274) := by
    have ha : (tripleCharges (sourceA149 + difference 0 4) (sourceB149 + difference 4 0) sourceC149) = raw4812 := by
      apply Matrix.ext; unfold tripleCharges sourceA149 sourceB149 sourceC149 difference raw4812; decide +kernel
    rw [ha]
    exact (canonical4812 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA149 + difference 0 5) (sourceB149 + difference 5 0) sourceC149) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5441) := by
    have ha : (tripleCharges (sourceA149 + difference 0 5) (sourceB149 + difference 5 0) sourceC149) = raw4813 := by
      apply Matrix.ext; unfold tripleCharges sourceA149 sourceB149 sourceC149 difference raw4813; decide +kernel
    rw [ha]
    exact (canonical4813 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA149 + difference 1 0) (sourceB149 + difference 0 1) sourceC149) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4608) := by
    have ha : (tripleCharges (sourceA149 + difference 1 0) (sourceB149 + difference 0 1) sourceC149) = raw4814 := by
      apply Matrix.ext; unfold tripleCharges sourceA149 sourceB149 sourceC149 difference raw4814; decide +kernel
    rw [ha]
    exact (canonical4814 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA149 + difference 1 2) (sourceB149 + difference 2 1) sourceC149) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5075) := by
    have ha : (tripleCharges (sourceA149 + difference 1 2) (sourceB149 + difference 2 1) sourceC149) = raw4815 := by
      apply Matrix.ext; unfold tripleCharges sourceA149 sourceB149 sourceC149 difference raw4815; decide +kernel
    rw [ha]
    exact (canonical4815 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA149 + difference 1 3) (sourceB149 + difference 3 1) sourceC149) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5075) := by
    have ha : (tripleCharges (sourceA149 + difference 1 3) (sourceB149 + difference 3 1) sourceC149) = raw4816 := by
      apply Matrix.ext; unfold tripleCharges sourceA149 sourceB149 sourceC149 difference raw4816; decide +kernel
    rw [ha]
    exact (canonical4816 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA149 + difference 1 4) (sourceB149 + difference 4 1) sourceC149) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5107) := by
    have ha : (tripleCharges (sourceA149 + difference 1 4) (sourceB149 + difference 4 1) sourceC149) = raw4817 := by
      apply Matrix.ext; unfold tripleCharges sourceA149 sourceB149 sourceC149 difference raw4817; decide +kernel
    rw [ha]
    exact (canonical4817 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA149 + difference 1 5) (sourceB149 + difference 5 1) sourceC149) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5274) := by
    have ha : (tripleCharges (sourceA149 + difference 1 5) (sourceB149 + difference 5 1) sourceC149) = raw4818 := by
      apply Matrix.ext; unfold tripleCharges sourceA149 sourceB149 sourceC149 difference raw4818; decide +kernel
    rw [ha]
    exact (canonical4818 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA149 + difference 2 0) (sourceB149 + difference 0 2) sourceC149) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4591) := by
    have ha : (tripleCharges (sourceA149 + difference 2 0) (sourceB149 + difference 0 2) sourceC149) = raw4819 := by
      apply Matrix.ext; unfold tripleCharges sourceA149 sourceB149 sourceC149 difference raw4819; decide +kernel
    rw [ha]
    exact (canonical4819 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA149 + difference 2 1) (sourceB149 + difference 1 2) sourceC149) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5147) := by
    have ha : (tripleCharges (sourceA149 + difference 2 1) (sourceB149 + difference 1 2) sourceC149) = raw4820 := by
      apply Matrix.ext; unfold tripleCharges sourceA149 sourceB149 sourceC149 difference raw4820; decide +kernel
    rw [ha]
    exact (canonical4820 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA149 + difference 2 3) (sourceB149 + difference 3 2) sourceC149) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5127) := by
    have ha : (tripleCharges (sourceA149 + difference 2 3) (sourceB149 + difference 3 2) sourceC149) = raw4821 := by
      apply Matrix.ext; unfold tripleCharges sourceA149 sourceB149 sourceC149 difference raw4821; decide +kernel
    rw [ha]
    exact (canonical4821 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA149 + difference 2 4) (sourceB149 + difference 4 2) sourceC149) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5075) := by
    have ha : (tripleCharges (sourceA149 + difference 2 4) (sourceB149 + difference 4 2) sourceC149) = raw4822 := by
      apply Matrix.ext; unfold tripleCharges sourceA149 sourceB149 sourceC149 difference raw4822; decide +kernel
    rw [ha]
    exact (canonical4822 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA149 + difference 2 5) (sourceB149 + difference 5 2) sourceC149) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5258) := by
    have ha : (tripleCharges (sourceA149 + difference 2 5) (sourceB149 + difference 5 2) sourceC149) = raw4823 := by
      apply Matrix.ext; unfold tripleCharges sourceA149 sourceB149 sourceC149 difference raw4823; decide +kernel
    rw [ha]
    exact (canonical4823 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA149 + difference 3 0) (sourceB149 + difference 0 3) sourceC149) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4591) := by
    have ha : (tripleCharges (sourceA149 + difference 3 0) (sourceB149 + difference 0 3) sourceC149) = raw4824 := by
      apply Matrix.ext; unfold tripleCharges sourceA149 sourceB149 sourceC149 difference raw4824; decide +kernel
    rw [ha]
    exact (canonical4824 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA149 + difference 3 1) (sourceB149 + difference 1 3) sourceC149) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5147) := by
    have ha : (tripleCharges (sourceA149 + difference 3 1) (sourceB149 + difference 1 3) sourceC149) = raw4825 := by
      apply Matrix.ext; unfold tripleCharges sourceA149 sourceB149 sourceC149 difference raw4825; decide +kernel
    rw [ha]
    exact (canonical4825 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA149 + difference 3 2) (sourceB149 + difference 2 3) sourceC149) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5127) := by
    have ha : (tripleCharges (sourceA149 + difference 3 2) (sourceB149 + difference 2 3) sourceC149) = raw4826 := by
      apply Matrix.ext; unfold tripleCharges sourceA149 sourceB149 sourceC149 difference raw4826; decide +kernel
    rw [ha]
    exact (canonical4826 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA149 + difference 3 4) (sourceB149 + difference 4 3) sourceC149) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5075) := by
    have ha : (tripleCharges (sourceA149 + difference 3 4) (sourceB149 + difference 4 3) sourceC149) = raw4827 := by
      apply Matrix.ext; unfold tripleCharges sourceA149 sourceB149 sourceC149 difference raw4827; decide +kernel
    rw [ha]
    exact (canonical4827 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA149 + difference 3 5) (sourceB149 + difference 5 3) sourceC149) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5258) := by
    have ha : (tripleCharges (sourceA149 + difference 3 5) (sourceB149 + difference 5 3) sourceC149) = raw4828 := by
      apply Matrix.ext; unfold tripleCharges sourceA149 sourceB149 sourceC149 difference raw4828; decide +kernel
    rw [ha]
    exact (canonical4828 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA149 + difference 4 0) (sourceB149 + difference 0 4) sourceC149) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4609) := by
    have ha : (tripleCharges (sourceA149 + difference 4 0) (sourceB149 + difference 0 4) sourceC149) = raw4829 := by
      apply Matrix.ext; unfold tripleCharges sourceA149 sourceB149 sourceC149 difference raw4829; decide +kernel
    rw [ha]
    exact (canonical4829 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA149 + difference 4 1) (sourceB149 + difference 1 4) sourceC149) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5201) := by
    have ha : (tripleCharges (sourceA149 + difference 4 1) (sourceB149 + difference 1 4) sourceC149) = raw4830 := by
      apply Matrix.ext; unfold tripleCharges sourceA149 sourceB149 sourceC149 difference raw4830; decide +kernel
    rw [ha]
    exact (canonical4830 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA149 + difference 4 2) (sourceB149 + difference 2 4) sourceC149) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5147) := by
    have ha : (tripleCharges (sourceA149 + difference 4 2) (sourceB149 + difference 2 4) sourceC149) = raw4831 := by
      apply Matrix.ext; unfold tripleCharges sourceA149 sourceB149 sourceC149 difference raw4831; decide +kernel
    rw [ha]
    exact (canonical4831 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA149 + difference 4 3) (sourceB149 + difference 3 4) sourceC149) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5147) := by
    have ha : (tripleCharges (sourceA149 + difference 4 3) (sourceB149 + difference 3 4) sourceC149) = raw4832 := by
      apply Matrix.ext; unfold tripleCharges sourceA149 sourceB149 sourceC149 difference raw4832; decide +kernel
    rw [ha]
    exact (canonical4832 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA149 + difference 4 5) (sourceB149 + difference 5 4) sourceC149) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5291) := by
    have ha : (tripleCharges (sourceA149 + difference 4 5) (sourceB149 + difference 5 4) sourceC149) = raw4833 := by
      apply Matrix.ext; unfold tripleCharges sourceA149 sourceB149 sourceC149 difference raw4833; decide +kernel
    rw [ha]
    exact (canonical4833 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA149 + difference 5 0) (sourceB149 + difference 0 5) sourceC149) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4594) := by
    have ha : (tripleCharges (sourceA149 + difference 5 0) (sourceB149 + difference 0 5) sourceC149) = raw4834 := by
      apply Matrix.ext; unfold tripleCharges sourceA149 sourceB149 sourceC149 difference raw4834; decide +kernel
    rw [ha]
    exact (canonical4834 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA149 + difference 5 1) (sourceB149 + difference 1 5) sourceC149) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4609) := by
    have ha : (tripleCharges (sourceA149 + difference 5 1) (sourceB149 + difference 1 5) sourceC149) = raw4835 := by
      apply Matrix.ext; unfold tripleCharges sourceA149 sourceB149 sourceC149 difference raw4835; decide +kernel
    rw [ha]
    exact (canonical4835 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA149 + difference 5 2) (sourceB149 + difference 2 5) sourceC149) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4591) := by
    have ha : (tripleCharges (sourceA149 + difference 5 2) (sourceB149 + difference 2 5) sourceC149) = raw4836 := by
      apply Matrix.ext; unfold tripleCharges sourceA149 sourceB149 sourceC149 difference raw4836; decide +kernel
    rw [ha]
    exact (canonical4836 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA149 + difference 5 3) (sourceB149 + difference 3 5) sourceC149) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4591) := by
    have ha : (tripleCharges (sourceA149 + difference 5 3) (sourceB149 + difference 3 5) sourceC149) = raw4837 := by
      apply Matrix.ext; unfold tripleCharges sourceA149 sourceB149 sourceC149 difference raw4837; decide +kernel
    rw [ha]
    exact (canonical4837 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA149 + difference 5 4) (sourceB149 + difference 4 5) sourceC149) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4608) := by
    have ha : (tripleCharges (sourceA149 + difference 5 4) (sourceB149 + difference 4 5) sourceC149) = raw4838 := by
      apply Matrix.ext; unfold tripleCharges sourceA149 sourceB149 sourceC149 difference raw4838; decide +kernel
    rw [ha]
    exact (canonical4838 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA149 sourceB149 sourceC149
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm149, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq151 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm151 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA151 + difference 0 1) (sourceB151 + difference 1 0) sourceC151) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3582) := by
    have ha : (tripleCharges (sourceA151 + difference 0 1) (sourceB151 + difference 1 0) sourceC151) = raw4869 := by
      apply Matrix.ext; unfold tripleCharges sourceA151 sourceB151 sourceC151 difference raw4869; decide +kernel
    rw [ha]
    exact (canonical4869 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA151 + difference 0 2) (sourceB151 + difference 2 0) sourceC151) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3533) := by
    have ha : (tripleCharges (sourceA151 + difference 0 2) (sourceB151 + difference 2 0) sourceC151) = raw4870 := by
      apply Matrix.ext; unfold tripleCharges sourceA151 sourceB151 sourceC151 difference raw4870; decide +kernel
    rw [ha]
    exact (canonical4870 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA151 + difference 0 3) (sourceB151 + difference 3 0) sourceC151) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3533) := by
    have ha : (tripleCharges (sourceA151 + difference 0 3) (sourceB151 + difference 3 0) sourceC151) = raw4871 := by
      apply Matrix.ext; unfold tripleCharges sourceA151 sourceB151 sourceC151 difference raw4871; decide +kernel
    rw [ha]
    exact (canonical4871 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA151 + difference 0 4) (sourceB151 + difference 4 0) sourceC151) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3547) := by
    have ha : (tripleCharges (sourceA151 + difference 0 4) (sourceB151 + difference 4 0) sourceC151) = raw4872 := by
      apply Matrix.ext; unfold tripleCharges sourceA151 sourceB151 sourceC151 difference raw4872; decide +kernel
    rw [ha]
    exact (canonical4872 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA151 + difference 0 5) (sourceB151 + difference 5 0) sourceC151) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3860) := by
    have ha : (tripleCharges (sourceA151 + difference 0 5) (sourceB151 + difference 5 0) sourceC151) = raw4873 := by
      apply Matrix.ext; unfold tripleCharges sourceA151 sourceB151 sourceC151 difference raw4873; decide +kernel
    rw [ha]
    exact (canonical4873 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA151 + difference 1 0) (sourceB151 + difference 0 1) sourceC151) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3300) := by
    have ha : (tripleCharges (sourceA151 + difference 1 0) (sourceB151 + difference 0 1) sourceC151) = raw4874 := by
      apply Matrix.ext; unfold tripleCharges sourceA151 sourceB151 sourceC151 difference raw4874; decide +kernel
    rw [ha]
    exact (canonical4874 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA151 + difference 1 2) (sourceB151 + difference 2 1) sourceC151) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3468) := by
    have ha : (tripleCharges (sourceA151 + difference 1 2) (sourceB151 + difference 2 1) sourceC151) = raw4875 := by
      apply Matrix.ext; unfold tripleCharges sourceA151 sourceB151 sourceC151 difference raw4875; decide +kernel
    rw [ha]
    exact (canonical4875 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA151 + difference 1 3) (sourceB151 + difference 3 1) sourceC151) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3468) := by
    have ha : (tripleCharges (sourceA151 + difference 1 3) (sourceB151 + difference 3 1) sourceC151) = raw4876 := by
      apply Matrix.ext; unfold tripleCharges sourceA151 sourceB151 sourceC151 difference raw4876; decide +kernel
    rw [ha]
    exact (canonical4876 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA151 + difference 1 4) (sourceB151 + difference 4 1) sourceC151) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3484) := by
    have ha : (tripleCharges (sourceA151 + difference 1 4) (sourceB151 + difference 4 1) sourceC151) = raw4877 := by
      apply Matrix.ext; unfold tripleCharges sourceA151 sourceB151 sourceC151 difference raw4877; decide +kernel
    rw [ha]
    exact (canonical4877 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA151 + difference 1 5) (sourceB151 + difference 5 1) sourceC151) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3547) := by
    have ha : (tripleCharges (sourceA151 + difference 1 5) (sourceB151 + difference 5 1) sourceC151) = raw4878 := by
      apply Matrix.ext; unfold tripleCharges sourceA151 sourceB151 sourceC151 difference raw4878; decide +kernel
    rw [ha]
    exact (canonical4878 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA151 + difference 2 0) (sourceB151 + difference 0 2) sourceC151) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3291) := by
    have ha : (tripleCharges (sourceA151 + difference 2 0) (sourceB151 + difference 0 2) sourceC151) = raw4879 := by
      apply Matrix.ext; unfold tripleCharges sourceA151 sourceB151 sourceC151 difference raw4879; decide +kernel
    rw [ha]
    exact (canonical4879 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA151 + difference 2 1) (sourceB151 + difference 1 2) sourceC151) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3530) := by
    have ha : (tripleCharges (sourceA151 + difference 2 1) (sourceB151 + difference 1 2) sourceC151) = raw4880 := by
      apply Matrix.ext; unfold tripleCharges sourceA151 sourceB151 sourceC151 difference raw4880; decide +kernel
    rw [ha]
    exact (canonical4880 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA151 + difference 2 3) (sourceB151 + difference 3 2) sourceC151) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3513) := by
    have ha : (tripleCharges (sourceA151 + difference 2 3) (sourceB151 + difference 3 2) sourceC151) = raw4881 := by
      apply Matrix.ext; unfold tripleCharges sourceA151 sourceB151 sourceC151 difference raw4881; decide +kernel
    rw [ha]
    exact (canonical4881 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA151 + difference 2 4) (sourceB151 + difference 4 2) sourceC151) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3468) := by
    have ha : (tripleCharges (sourceA151 + difference 2 4) (sourceB151 + difference 4 2) sourceC151) = raw4882 := by
      apply Matrix.ext; unfold tripleCharges sourceA151 sourceB151 sourceC151 difference raw4882; decide +kernel
    rw [ha]
    exact (canonical4882 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA151 + difference 2 5) (sourceB151 + difference 5 2) sourceC151) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3533) := by
    have ha : (tripleCharges (sourceA151 + difference 2 5) (sourceB151 + difference 5 2) sourceC151) = raw4883 := by
      apply Matrix.ext; unfold tripleCharges sourceA151 sourceB151 sourceC151 difference raw4883; decide +kernel
    rw [ha]
    exact (canonical4883 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA151 + difference 3 0) (sourceB151 + difference 0 3) sourceC151) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3291) := by
    have ha : (tripleCharges (sourceA151 + difference 3 0) (sourceB151 + difference 0 3) sourceC151) = raw4884 := by
      apply Matrix.ext; unfold tripleCharges sourceA151 sourceB151 sourceC151 difference raw4884; decide +kernel
    rw [ha]
    exact (canonical4884 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA151 + difference 3 1) (sourceB151 + difference 1 3) sourceC151) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3530) := by
    have ha : (tripleCharges (sourceA151 + difference 3 1) (sourceB151 + difference 1 3) sourceC151) = raw4885 := by
      apply Matrix.ext; unfold tripleCharges sourceA151 sourceB151 sourceC151 difference raw4885; decide +kernel
    rw [ha]
    exact (canonical4885 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA151 + difference 3 2) (sourceB151 + difference 2 3) sourceC151) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3513) := by
    have ha : (tripleCharges (sourceA151 + difference 3 2) (sourceB151 + difference 2 3) sourceC151) = raw4886 := by
      apply Matrix.ext; unfold tripleCharges sourceA151 sourceB151 sourceC151 difference raw4886; decide +kernel
    rw [ha]
    exact (canonical4886 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA151 + difference 3 4) (sourceB151 + difference 4 3) sourceC151) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3468) := by
    have ha : (tripleCharges (sourceA151 + difference 3 4) (sourceB151 + difference 4 3) sourceC151) = raw4887 := by
      apply Matrix.ext; unfold tripleCharges sourceA151 sourceB151 sourceC151 difference raw4887; decide +kernel
    rw [ha]
    exact (canonical4887 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA151 + difference 3 5) (sourceB151 + difference 5 3) sourceC151) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3533) := by
    have ha : (tripleCharges (sourceA151 + difference 3 5) (sourceB151 + difference 5 3) sourceC151) = raw4888 := by
      apply Matrix.ext; unfold tripleCharges sourceA151 sourceB151 sourceC151 difference raw4888; decide +kernel
    rw [ha]
    exact (canonical4888 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA151 + difference 4 0) (sourceB151 + difference 0 4) sourceC151) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3302) := by
    have ha : (tripleCharges (sourceA151 + difference 4 0) (sourceB151 + difference 0 4) sourceC151) = raw4889 := by
      apply Matrix.ext; unfold tripleCharges sourceA151 sourceB151 sourceC151 difference raw4889; decide +kernel
    rw [ha]
    exact (canonical4889 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA151 + difference 4 1) (sourceB151 + difference 1 4) sourceC151) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3579) := by
    have ha : (tripleCharges (sourceA151 + difference 4 1) (sourceB151 + difference 1 4) sourceC151) = raw4890 := by
      apply Matrix.ext; unfold tripleCharges sourceA151 sourceB151 sourceC151 difference raw4890; decide +kernel
    rw [ha]
    exact (canonical4890 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA151 + difference 4 2) (sourceB151 + difference 2 4) sourceC151) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3530) := by
    have ha : (tripleCharges (sourceA151 + difference 4 2) (sourceB151 + difference 2 4) sourceC151) = raw4891 := by
      apply Matrix.ext; unfold tripleCharges sourceA151 sourceB151 sourceC151 difference raw4891; decide +kernel
    rw [ha]
    exact (canonical4891 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA151 + difference 4 3) (sourceB151 + difference 3 4) sourceC151) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3530) := by
    have ha : (tripleCharges (sourceA151 + difference 4 3) (sourceB151 + difference 3 4) sourceC151) = raw4892 := by
      apply Matrix.ext; unfold tripleCharges sourceA151 sourceB151 sourceC151 difference raw4892; decide +kernel
    rw [ha]
    exact (canonical4892 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA151 + difference 4 5) (sourceB151 + difference 5 4) sourceC151) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3582) := by
    have ha : (tripleCharges (sourceA151 + difference 4 5) (sourceB151 + difference 5 4) sourceC151) = raw4893 := by
      apply Matrix.ext; unfold tripleCharges sourceA151 sourceB151 sourceC151 difference raw4893; decide +kernel
    rw [ha]
    exact (canonical4893 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA151 + difference 5 0) (sourceB151 + difference 0 5) sourceC151) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3298) := by
    have ha : (tripleCharges (sourceA151 + difference 5 0) (sourceB151 + difference 0 5) sourceC151) = raw4894 := by
      apply Matrix.ext; unfold tripleCharges sourceA151 sourceB151 sourceC151 difference raw4894; decide +kernel
    rw [ha]
    exact (canonical4894 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA151 + difference 5 1) (sourceB151 + difference 1 5) sourceC151) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3302) := by
    have ha : (tripleCharges (sourceA151 + difference 5 1) (sourceB151 + difference 1 5) sourceC151) = raw4895 := by
      apply Matrix.ext; unfold tripleCharges sourceA151 sourceB151 sourceC151 difference raw4895; decide +kernel
    rw [ha]
    exact (canonical4895 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA151 + difference 5 2) (sourceB151 + difference 2 5) sourceC151) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3291) := by
    have ha : (tripleCharges (sourceA151 + difference 5 2) (sourceB151 + difference 2 5) sourceC151) = raw4896 := by
      apply Matrix.ext; unfold tripleCharges sourceA151 sourceB151 sourceC151 difference raw4896; decide +kernel
    rw [ha]
    exact (canonical4896 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA151 + difference 5 3) (sourceB151 + difference 3 5) sourceC151) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3291) := by
    have ha : (tripleCharges (sourceA151 + difference 5 3) (sourceB151 + difference 3 5) sourceC151) = raw4897 := by
      apply Matrix.ext; unfold tripleCharges sourceA151 sourceB151 sourceC151 difference raw4897; decide +kernel
    rw [ha]
    exact (canonical4897 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA151 + difference 5 4) (sourceB151 + difference 4 5) sourceC151) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3300) := by
    have ha : (tripleCharges (sourceA151 + difference 5 4) (sourceB151 + difference 4 5) sourceC151) = raw4898 := by
      apply Matrix.ext; unfold tripleCharges sourceA151 sourceB151 sourceC151 difference raw4898; decide +kernel
    rw [ha]
    exact (canonical4898 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA151 sourceB151 sourceC151
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm151, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq152 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm152 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA152 + difference 0 0) (sourceB152 + difference 0 0) sourceC152) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2726) := by
    have ha : (tripleCharges (sourceA152 + difference 0 0) (sourceB152 + difference 0 0) sourceC152) = raw4899 := by
      apply Matrix.ext; unfold tripleCharges sourceA152 sourceB152 sourceC152 difference raw4899; decide +kernel
    rw [ha]
    exact (canonical4899 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA152 + difference 0 1) (sourceB152 + difference 1 0) sourceC152) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2765) := by
    have ha : (tripleCharges (sourceA152 + difference 0 1) (sourceB152 + difference 1 0) sourceC152) = raw4900 := by
      apply Matrix.ext; unfold tripleCharges sourceA152 sourceB152 sourceC152 difference raw4900; decide +kernel
    rw [ha]
    exact (canonical4900 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA152 + difference 0 2) (sourceB152 + difference 2 0) sourceC152) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2722) := by
    have ha : (tripleCharges (sourceA152 + difference 0 2) (sourceB152 + difference 2 0) sourceC152) = raw4901 := by
      apply Matrix.ext; unfold tripleCharges sourceA152 sourceB152 sourceC152 difference raw4901; decide +kernel
    rw [ha]
    exact (canonical4901 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA152 + difference 0 3) (sourceB152 + difference 3 0) sourceC152) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2722) := by
    have ha : (tripleCharges (sourceA152 + difference 0 3) (sourceB152 + difference 3 0) sourceC152) = raw4902 := by
      apply Matrix.ext; unfold tripleCharges sourceA152 sourceB152 sourceC152 difference raw4902; decide +kernel
    rw [ha]
    exact (canonical4902 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA152 + difference 0 4) (sourceB152 + difference 4 0) sourceC152) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2742) := by
    have ha : (tripleCharges (sourceA152 + difference 0 4) (sourceB152 + difference 4 0) sourceC152) = raw4903 := by
      apply Matrix.ext; unfold tripleCharges sourceA152 sourceB152 sourceC152 difference raw4903; decide +kernel
    rw [ha]
    exact (canonical4903 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA152 + difference 0 5) (sourceB152 + difference 5 0) sourceC152) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3905) := by
    have ha : (tripleCharges (sourceA152 + difference 0 5) (sourceB152 + difference 5 0) sourceC152) = raw4904 := by
      apply Matrix.ext; unfold tripleCharges sourceA152 sourceB152 sourceC152 difference raw4904; decide +kernel
    rw [ha]
    exact (canonical4904 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA152 + sourceB152) sourceC152) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA152 + sourceB152) sourceC152) = raw4905 := by
      apply Matrix.ext; unfold doubleCharges sourceA152 sourceB152 sourceC152 raw4905; decide +kernel
    rw [ha]
    exact (canonical4905 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA152 sourceB152 sourceC152
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm152, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq153 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm153 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA153 + difference 0 0) (sourceB153 + difference 0 0) sourceC153) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2726) := by
    have ha : (tripleCharges (sourceA153 + difference 0 0) (sourceB153 + difference 0 0) sourceC153) = raw4899 := by
      apply Matrix.ext; unfold tripleCharges sourceA153 sourceB153 sourceC153 difference raw4899; decide +kernel
    rw [ha]
    exact (canonical4899 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA153 + difference 1 0) (sourceB153 + difference 0 1) sourceC153) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1242) := by
    have ha : (tripleCharges (sourceA153 + difference 1 0) (sourceB153 + difference 0 1) sourceC153) = raw4906 := by
      apply Matrix.ext; unfold tripleCharges sourceA153 sourceB153 sourceC153 difference raw4906; decide +kernel
    rw [ha]
    exact (canonical4906 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA153 + difference 2 0) (sourceB153 + difference 0 2) sourceC153) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1215) := by
    have ha : (tripleCharges (sourceA153 + difference 2 0) (sourceB153 + difference 0 2) sourceC153) = raw4907 := by
      apply Matrix.ext; unfold tripleCharges sourceA153 sourceB153 sourceC153 difference raw4907; decide +kernel
    rw [ha]
    exact (canonical4907 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA153 + difference 3 0) (sourceB153 + difference 0 3) sourceC153) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1215) := by
    have ha : (tripleCharges (sourceA153 + difference 3 0) (sourceB153 + difference 0 3) sourceC153) = raw4908 := by
      apply Matrix.ext; unfold tripleCharges sourceA153 sourceB153 sourceC153 difference raw4908; decide +kernel
    rw [ha]
    exact (canonical4908 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA153 + difference 4 0) (sourceB153 + difference 0 4) sourceC153) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1264) := by
    have ha : (tripleCharges (sourceA153 + difference 4 0) (sourceB153 + difference 0 4) sourceC153) = raw4909 := by
      apply Matrix.ext; unfold tripleCharges sourceA153 sourceB153 sourceC153 difference raw4909; decide +kernel
    rw [ha]
    exact (canonical4909 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA153 + difference 5 0) (sourceB153 + difference 0 5) sourceC153) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1221) := by
    have ha : (tripleCharges (sourceA153 + difference 5 0) (sourceB153 + difference 0 5) sourceC153) = raw4910 := by
      apply Matrix.ext; unfold tripleCharges sourceA153 sourceB153 sourceC153 difference raw4910; decide +kernel
    rw [ha]
    exact (canonical4910 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA153 + sourceB153) sourceC153) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA153 + sourceB153) sourceC153) = raw4905 := by
      apply Matrix.ext; unfold doubleCharges sourceA153 sourceB153 sourceC153 raw4905; decide +kernel
    rw [ha]
    exact (canonical4905 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA153 sourceB153 sourceC153
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm153, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq154 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm154 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA154 + difference 1 0) (sourceB154 + difference 0 1) sourceC154) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1242) := by
    have ha : (tripleCharges (sourceA154 + difference 1 0) (sourceB154 + difference 0 1) sourceC154) = raw4906 := by
      apply Matrix.ext; unfold tripleCharges sourceA154 sourceB154 sourceC154 difference raw4906; decide +kernel
    rw [ha]
    exact (canonical4906 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA154 + difference 1 1) (sourceB154 + difference 1 1) sourceC154) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2726) := by
    have ha : (tripleCharges (sourceA154 + difference 1 1) (sourceB154 + difference 1 1) sourceC154) = raw4899 := by
      apply Matrix.ext; unfold tripleCharges sourceA154 sourceB154 sourceC154 difference raw4899; decide +kernel
    rw [ha]
    exact (canonical4899 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA154 + difference 1 2) (sourceB154 + difference 2 1) sourceC154) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2482) := by
    have ha : (tripleCharges (sourceA154 + difference 1 2) (sourceB154 + difference 2 1) sourceC154) = raw4911 := by
      apply Matrix.ext; unfold tripleCharges sourceA154 sourceB154 sourceC154 difference raw4911; decide +kernel
    rw [ha]
    exact (canonical4911 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA154 + difference 1 3) (sourceB154 + difference 3 1) sourceC154) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2482) := by
    have ha : (tripleCharges (sourceA154 + difference 1 3) (sourceB154 + difference 3 1) sourceC154) = raw4912 := by
      apply Matrix.ext; unfold tripleCharges sourceA154 sourceB154 sourceC154 difference raw4912; decide +kernel
    rw [ha]
    exact (canonical4912 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA154 + difference 1 4) (sourceB154 + difference 4 1) sourceC154) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2517) := by
    have ha : (tripleCharges (sourceA154 + difference 1 4) (sourceB154 + difference 4 1) sourceC154) = raw4913 := by
      apply Matrix.ext; unfold tripleCharges sourceA154 sourceB154 sourceC154 difference raw4913; decide +kernel
    rw [ha]
    exact (canonical4913 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA154 + difference 1 5) (sourceB154 + difference 5 1) sourceC154) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2742) := by
    have ha : (tripleCharges (sourceA154 + difference 1 5) (sourceB154 + difference 5 1) sourceC154) = raw4914 := by
      apply Matrix.ext; unfold tripleCharges sourceA154 sourceB154 sourceC154 difference raw4914; decide +kernel
    rw [ha]
    exact (canonical4914 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA154 + sourceB154) sourceC154) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA154 + sourceB154) sourceC154) = raw4905 := by
      apply Matrix.ext; unfold doubleCharges sourceA154 sourceB154 sourceC154 raw4905; decide +kernel
    rw [ha]
    exact (canonical4905 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA154 sourceB154 sourceC154
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm154, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq155 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm155 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA155 + difference 0 1) (sourceB155 + difference 1 0) sourceC155) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2765) := by
    have ha : (tripleCharges (sourceA155 + difference 0 1) (sourceB155 + difference 1 0) sourceC155) = raw4900 := by
      apply Matrix.ext; unfold tripleCharges sourceA155 sourceB155 sourceC155 difference raw4900; decide +kernel
    rw [ha]
    exact (canonical4900 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA155 + difference 1 1) (sourceB155 + difference 1 1) sourceC155) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2726) := by
    have ha : (tripleCharges (sourceA155 + difference 1 1) (sourceB155 + difference 1 1) sourceC155) = raw4899 := by
      apply Matrix.ext; unfold tripleCharges sourceA155 sourceB155 sourceC155 difference raw4899; decide +kernel
    rw [ha]
    exact (canonical4899 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA155 + difference 2 1) (sourceB155 + difference 1 2) sourceC155) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2569) := by
    have ha : (tripleCharges (sourceA155 + difference 2 1) (sourceB155 + difference 1 2) sourceC155) = raw4915 := by
      apply Matrix.ext; unfold tripleCharges sourceA155 sourceB155 sourceC155 difference raw4915; decide +kernel
    rw [ha]
    exact (canonical4915 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA155 + difference 3 1) (sourceB155 + difference 1 3) sourceC155) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2569) := by
    have ha : (tripleCharges (sourceA155 + difference 3 1) (sourceB155 + difference 1 3) sourceC155) = raw4916 := by
      apply Matrix.ext; unfold tripleCharges sourceA155 sourceB155 sourceC155 difference raw4916; decide +kernel
    rw [ha]
    exact (canonical4916 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA155 + difference 4 1) (sourceB155 + difference 1 4) sourceC155) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2635) := by
    have ha : (tripleCharges (sourceA155 + difference 4 1) (sourceB155 + difference 1 4) sourceC155) = raw4917 := by
      apply Matrix.ext; unfold tripleCharges sourceA155 sourceB155 sourceC155 difference raw4917; decide +kernel
    rw [ha]
    exact (canonical4917 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA155 + difference 5 1) (sourceB155 + difference 1 5) sourceC155) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1264) := by
    have ha : (tripleCharges (sourceA155 + difference 5 1) (sourceB155 + difference 1 5) sourceC155) = raw4918 := by
      apply Matrix.ext; unfold tripleCharges sourceA155 sourceB155 sourceC155 difference raw4918; decide +kernel
    rw [ha]
    exact (canonical4918 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA155 + sourceB155) sourceC155) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA155 + sourceB155) sourceC155) = raw4905 := by
      apply Matrix.ext; unfold doubleCharges sourceA155 sourceB155 sourceC155 raw4905; decide +kernel
    rw [ha]
    exact (canonical4905 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA155 sourceB155 sourceC155
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm155, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq156 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm156 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA156 + difference 2 0) (sourceB156 + difference 0 2) sourceC156) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1215) := by
    have ha : (tripleCharges (sourceA156 + difference 2 0) (sourceB156 + difference 0 2) sourceC156) = raw4907 := by
      apply Matrix.ext; unfold tripleCharges sourceA156 sourceB156 sourceC156 difference raw4907; decide +kernel
    rw [ha]
    exact (canonical4907 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA156 + difference 2 1) (sourceB156 + difference 1 2) sourceC156) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2569) := by
    have ha : (tripleCharges (sourceA156 + difference 2 1) (sourceB156 + difference 1 2) sourceC156) = raw4915 := by
      apply Matrix.ext; unfold tripleCharges sourceA156 sourceB156 sourceC156 difference raw4915; decide +kernel
    rw [ha]
    exact (canonical4915 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA156 + difference 2 2) (sourceB156 + difference 2 2) sourceC156) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2726) := by
    have ha : (tripleCharges (sourceA156 + difference 2 2) (sourceB156 + difference 2 2) sourceC156) = raw4899 := by
      apply Matrix.ext; unfold tripleCharges sourceA156 sourceB156 sourceC156 difference raw4899; decide +kernel
    rw [ha]
    exact (canonical4899 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA156 + difference 2 3) (sourceB156 + difference 3 2) sourceC156) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2542) := by
    have ha : (tripleCharges (sourceA156 + difference 2 3) (sourceB156 + difference 3 2) sourceC156) = raw4919 := by
      apply Matrix.ext; unfold tripleCharges sourceA156 sourceB156 sourceC156 difference raw4919; decide +kernel
    rw [ha]
    exact (canonical4919 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA156 + difference 2 4) (sourceB156 + difference 4 2) sourceC156) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2482) := by
    have ha : (tripleCharges (sourceA156 + difference 2 4) (sourceB156 + difference 4 2) sourceC156) = raw4920 := by
      apply Matrix.ext; unfold tripleCharges sourceA156 sourceB156 sourceC156 difference raw4920; decide +kernel
    rw [ha]
    exact (canonical4920 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA156 + difference 2 5) (sourceB156 + difference 5 2) sourceC156) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2722) := by
    have ha : (tripleCharges (sourceA156 + difference 2 5) (sourceB156 + difference 5 2) sourceC156) = raw4921 := by
      apply Matrix.ext; unfold tripleCharges sourceA156 sourceB156 sourceC156 difference raw4921; decide +kernel
    rw [ha]
    exact (canonical4921 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA156 + sourceB156) sourceC156) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA156 + sourceB156) sourceC156) = raw4905 := by
      apply Matrix.ext; unfold doubleCharges sourceA156 sourceB156 sourceC156 raw4905; decide +kernel
    rw [ha]
    exact (canonical4905 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA156 sourceB156 sourceC156
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm156, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources5
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sourceEq162 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm162 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA162 + difference 0 0) (sourceB162 + difference 0 0) sourceC162) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3545) := by
    have ha : (tripleCharges (sourceA162 + difference 0 0) (sourceB162 + difference 0 0) sourceC162) = raw5052 := by
      apply Matrix.ext; unfold tripleCharges sourceA162 sourceB162 sourceC162 difference raw5052; decide +kernel
    rw [ha]
    exact (canonical5052 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA162 + difference 1 0) (sourceB162 + difference 0 1) sourceC162) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2065) := by
    have ha : (tripleCharges (sourceA162 + difference 1 0) (sourceB162 + difference 0 1) sourceC162) = raw5053 := by
      apply Matrix.ext; unfold tripleCharges sourceA162 sourceB162 sourceC162 difference raw5053; decide +kernel
    rw [ha]
    exact (canonical5053 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA162 + difference 2 0) (sourceB162 + difference 0 2) sourceC162) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2052) := by
    have ha : (tripleCharges (sourceA162 + difference 2 0) (sourceB162 + difference 0 2) sourceC162) = raw5054 := by
      apply Matrix.ext; unfold tripleCharges sourceA162 sourceB162 sourceC162 difference raw5054; decide +kernel
    rw [ha]
    exact (canonical5054 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA162 + difference 3 0) (sourceB162 + difference 0 3) sourceC162) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2052) := by
    have ha : (tripleCharges (sourceA162 + difference 3 0) (sourceB162 + difference 0 3) sourceC162) = raw5055 := by
      apply Matrix.ext; unfold tripleCharges sourceA162 sourceB162 sourceC162 difference raw5055; decide +kernel
    rw [ha]
    exact (canonical5055 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA162 + difference 4 0) (sourceB162 + difference 0 4) sourceC162) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2292) := by
    have ha : (tripleCharges (sourceA162 + difference 4 0) (sourceB162 + difference 0 4) sourceC162) = raw5056 := by
      apply Matrix.ext; unfold tripleCharges sourceA162 sourceB162 sourceC162 difference raw5056; decide +kernel
    rw [ha]
    exact (canonical5056 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA162 + difference 5 0) (sourceB162 + difference 0 5) sourceC162) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2056) := by
    have ha : (tripleCharges (sourceA162 + difference 5 0) (sourceB162 + difference 0 5) sourceC162) = raw5057 := by
      apply Matrix.ext; unfold tripleCharges sourceA162 sourceB162 sourceC162 difference raw5057; decide +kernel
    rw [ha]
    exact (canonical5057 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA162 + sourceB162) sourceC162) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4085) := by
    have ha : (doubleCharges (sourceA162 + sourceB162) sourceC162) = raw3721 := by
      apply Matrix.ext; unfold doubleCharges sourceA162 sourceB162 sourceC162 raw3721; decide +kernel
    rw [ha]
    exact (canonical3721 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA162 sourceB162 sourceC162
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm162, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic8
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reindexCheck128 : Integer.Sparse.reindex keyMap MixedData.row128 = numericRow128 := by decide +kernel

theorem numericCheck128 (x : Master → ℝ) : Integer.Sparse.eval numericRow128 x =
    (1 : ℝ) * reducedSource128 x := by
  norm_num [numericRow128, reducedSource128, Integer.Sparse.eval, Sparse.eval, nodeValue1080, nodeValue2052, nodeValue2290, nodeValue2292, nodeValue4085]

theorem reindexCheck129 : Integer.Sparse.reindex keyMap MixedData.row129 = numericRow129 := by decide +kernel

theorem numericCheck129 (x : Master → ℝ) : Integer.Sparse.eval numericRow129 x =
    (2 : ℝ) * reducedSource129 x := by
  norm_num [numericRow129, reducedSource129, Integer.Sparse.eval, Sparse.eval, nodeValue4591, nodeValue4594, nodeValue4608, nodeValue4609, nodeValue5075, nodeValue5107, nodeValue5127, nodeValue5147, nodeValue5201, nodeValue5258, nodeValue5274, nodeValue5291, nodeValue5441]
  ring

theorem reindexCheck131 : Integer.Sparse.reindex keyMap MixedData.row131 = numericRow131 := by decide +kernel

theorem numericCheck131 (x : Master → ℝ) : Integer.Sparse.eval numericRow131 x =
    (1 : ℝ) * reducedSource131 x := by
  norm_num [numericRow131, reducedSource131, Integer.Sparse.eval, Sparse.eval, nodeValue3291, nodeValue3298, nodeValue3300, nodeValue3302, nodeValue3468, nodeValue3484, nodeValue3513, nodeValue3530, nodeValue3533, nodeValue3547, nodeValue3579, nodeValue3582, nodeValue3860]

theorem reindexCheck132 : Integer.Sparse.reindex keyMap MixedData.row132 = numericRow132 := by decide +kernel

theorem numericCheck132 (x : Master → ℝ) : Integer.Sparse.eval numericRow132 x =
    (1 : ℝ) * reducedSource132 x := by
  norm_num [numericRow132, reducedSource132, Integer.Sparse.eval, Sparse.eval, nodeValue2722, nodeValue2726, nodeValue2742, nodeValue2765, nodeValue3905, nodeValue4092]

theorem reindexCheck133 : Integer.Sparse.reindex keyMap MixedData.row133 = numericRow133 := by decide +kernel

theorem numericCheck133 (x : Master → ℝ) : Integer.Sparse.eval numericRow133 x =
    (1 : ℝ) * reducedSource133 x := by
  norm_num [numericRow133, reducedSource133, Integer.Sparse.eval, Sparse.eval, nodeValue1215, nodeValue1221, nodeValue1242, nodeValue1264, nodeValue2726, nodeValue4092]

theorem reindexCheck134 : Integer.Sparse.reindex keyMap MixedData.row134 = numericRow134 := by decide +kernel

theorem numericCheck134 (x : Master → ℝ) : Integer.Sparse.eval numericRow134 x =
    (1 : ℝ) * reducedSource134 x := by
  norm_num [numericRow134, reducedSource134, Integer.Sparse.eval, Sparse.eval, nodeValue1242, nodeValue2482, nodeValue2517, nodeValue2726, nodeValue2742, nodeValue4092]

theorem reindexCheck135 : Integer.Sparse.reindex keyMap MixedData.row135 = numericRow135 := by decide +kernel

theorem numericCheck135 (x : Master → ℝ) : Integer.Sparse.eval numericRow135 x =
    (1 : ℝ) * reducedSource135 x := by
  norm_num [numericRow135, reducedSource135, Integer.Sparse.eval, Sparse.eval, nodeValue1264, nodeValue2569, nodeValue2635, nodeValue2726, nodeValue2765, nodeValue4092]

theorem reindexCheck136 : Integer.Sparse.reindex keyMap MixedData.row136 = numericRow136 := by decide +kernel

theorem numericCheck136 (x : Master → ℝ) : Integer.Sparse.eval numericRow136 x =
    (1 : ℝ) * reducedSource136 x := by
  norm_num [numericRow136, reducedSource136, Integer.Sparse.eval, Sparse.eval, nodeValue1215, nodeValue2482, nodeValue2542, nodeValue2569, nodeValue2722, nodeValue2726, nodeValue4092]

theorem reindexCheck142 : Integer.Sparse.reindex keyMap MixedData.row142 = numericRow142 := by decide +kernel

theorem numericCheck142 (x : Master → ℝ) : Integer.Sparse.eval numericRow142 x =
    (1 : ℝ) * reducedSource142 x := by
  norm_num [numericRow142, reducedSource142, Integer.Sparse.eval, Sparse.eval, nodeValue2052, nodeValue2056, nodeValue2065, nodeValue2292, nodeValue3545, nodeValue4085]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Rows8
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero128 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource128 (mixedVector B) = 0 := by
  have h1080 : mixedVector B (Sum.inr 1080) = Sparse.eval nodeValue1080 (mixedVector B) := by
    change mixedMoment B node1080 node1080Labels = _
    exact sound1080 B hB hF
  have h2052 : mixedVector B (Sum.inr 2052) = Sparse.eval nodeValue2052 (mixedVector B) := by
    change mixedMoment B node2052 node2052Labels = _
    exact sound2052 B hB hF
  have h2290 : mixedVector B (Sum.inr 2290) = Sparse.eval nodeValue2290 (mixedVector B) := by
    change mixedMoment B node2290 node2290Labels = _
    exact sound2290 B hB hF
  have h2292 : mixedVector B (Sum.inr 2292) = Sparse.eval nodeValue2292 (mixedVector B) := by
    change mixedMoment B node2292 node2292Labels = _
    exact sound2292 B hB hF
  have h4085 : mixedVector B (Sum.inr 4085) = Sparse.eval nodeValue4085 (mixedVector B) := by
    change mixedMoment B node4085 node4085Labels = _
    exact sound4085 B hB hF
  simpa only [sourceForm148, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1080, h2052, h2290, h2292, h4085, reducedSource128] using sourceEq148 B hB

theorem rowSound128 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row128 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck128, numericCheck128, reducedZero128 B hB hF, mul_zero]

theorem reducedZero129 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource129 (mixedVector B) = 0 := by
  have h4591 : mixedVector B (Sum.inr 4591) = Sparse.eval nodeValue4591 (mixedVector B) := by
    change mixedMoment B node4591 node4591Labels = _
    exact sound4591 B hB hF
  have h4594 : mixedVector B (Sum.inr 4594) = Sparse.eval nodeValue4594 (mixedVector B) := by
    change mixedMoment B node4594 node4594Labels = _
    exact sound4594 B hB hF
  have h4608 : mixedVector B (Sum.inr 4608) = Sparse.eval nodeValue4608 (mixedVector B) := by
    change mixedMoment B node4608 node4608Labels = _
    exact sound4608 B hB hF
  have h4609 : mixedVector B (Sum.inr 4609) = Sparse.eval nodeValue4609 (mixedVector B) := by
    change mixedMoment B node4609 node4609Labels = _
    exact sound4609 B hB hF
  have h5075 : mixedVector B (Sum.inr 5075) = Sparse.eval nodeValue5075 (mixedVector B) := by
    change mixedMoment B node5075 node5075Labels = _
    exact sound5075 B hB hF
  have h5107 : mixedVector B (Sum.inr 5107) = Sparse.eval nodeValue5107 (mixedVector B) := by
    change mixedMoment B node5107 node5107Labels = _
    exact sound5107 B hB hF
  have h5127 : mixedVector B (Sum.inr 5127) = Sparse.eval nodeValue5127 (mixedVector B) := by
    change mixedMoment B node5127 node5127Labels = _
    exact sound5127 B hB hF
  have h5147 : mixedVector B (Sum.inr 5147) = Sparse.eval nodeValue5147 (mixedVector B) := by
    change mixedMoment B node5147 node5147Labels = _
    exact sound5147 B hB hF
  have h5201 : mixedVector B (Sum.inr 5201) = Sparse.eval nodeValue5201 (mixedVector B) := by
    change mixedMoment B node5201 node5201Labels = _
    exact sound5201 B hB hF
  have h5258 : mixedVector B (Sum.inr 5258) = Sparse.eval nodeValue5258 (mixedVector B) := by
    change mixedMoment B node5258 node5258Labels = _
    exact sound5258 B hB hF
  have h5274 : mixedVector B (Sum.inr 5274) = Sparse.eval nodeValue5274 (mixedVector B) := by
    change mixedMoment B node5274 node5274Labels = _
    exact sound5274 B hB hF
  have h5291 : mixedVector B (Sum.inr 5291) = Sparse.eval nodeValue5291 (mixedVector B) := by
    change mixedMoment B node5291 node5291Labels = _
    exact sound5291 B hB hF
  have h5441 : mixedVector B (Sum.inr 5441) = Sparse.eval nodeValue5441 (mixedVector B) := by
    change mixedMoment B node5441 node5441Labels = _
    exact sound5441 B hB hF
  simpa only [sourceForm149, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4591, h4594, h4608, h4609, h5075, h5107, h5127, h5147, h5201, h5258, h5274, h5291, h5441, reducedSource129] using sourceEq149 B hB

theorem rowSound129 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row129 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck129, numericCheck129, reducedZero129 B hB hF, mul_zero]

theorem reducedZero131 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource131 (mixedVector B) = 0 := by
  have h3291 : mixedVector B (Sum.inr 3291) = Sparse.eval nodeValue3291 (mixedVector B) := by
    change mixedMoment B node3291 node3291Labels = _
    exact sound3291 B hB hF
  have h3298 : mixedVector B (Sum.inr 3298) = Sparse.eval nodeValue3298 (mixedVector B) := by
    change mixedMoment B node3298 node3298Labels = _
    exact sound3298 B hB hF
  have h3300 : mixedVector B (Sum.inr 3300) = Sparse.eval nodeValue3300 (mixedVector B) := by
    change mixedMoment B node3300 node3300Labels = _
    exact sound3300 B hB hF
  have h3302 : mixedVector B (Sum.inr 3302) = Sparse.eval nodeValue3302 (mixedVector B) := by
    change mixedMoment B node3302 node3302Labels = _
    exact sound3302 B hB hF
  have h3468 : mixedVector B (Sum.inr 3468) = Sparse.eval nodeValue3468 (mixedVector B) := by
    change mixedMoment B node3468 node3468Labels = _
    exact sound3468 B hB hF
  have h3484 : mixedVector B (Sum.inr 3484) = Sparse.eval nodeValue3484 (mixedVector B) := by
    change mixedMoment B node3484 node3484Labels = _
    exact sound3484 B hB hF
  have h3513 : mixedVector B (Sum.inr 3513) = Sparse.eval nodeValue3513 (mixedVector B) := by
    change mixedMoment B node3513 node3513Labels = _
    exact sound3513 B hB hF
  have h3530 : mixedVector B (Sum.inr 3530) = Sparse.eval nodeValue3530 (mixedVector B) := by
    change mixedMoment B node3530 node3530Labels = _
    exact sound3530 B hB hF
  have h3533 : mixedVector B (Sum.inr 3533) = Sparse.eval nodeValue3533 (mixedVector B) := by
    change mixedMoment B node3533 node3533Labels = _
    exact sound3533 B hB hF
  have h3547 : mixedVector B (Sum.inr 3547) = Sparse.eval nodeValue3547 (mixedVector B) := by
    change mixedMoment B node3547 node3547Labels = _
    exact sound3547 B hB hF
  have h3579 : mixedVector B (Sum.inr 3579) = Sparse.eval nodeValue3579 (mixedVector B) := by
    change mixedMoment B node3579 node3579Labels = _
    exact sound3579 B hB hF
  have h3582 : mixedVector B (Sum.inr 3582) = Sparse.eval nodeValue3582 (mixedVector B) := by
    change mixedMoment B node3582 node3582Labels = _
    exact sound3582 B hB hF
  have h3860 : mixedVector B (Sum.inr 3860) = Sparse.eval nodeValue3860 (mixedVector B) := by
    change mixedMoment B node3860 node3860Labels = _
    exact sound3860 B hB hF
  simpa only [sourceForm151, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h3291, h3298, h3300, h3302, h3468, h3484, h3513, h3530, h3533, h3547, h3579, h3582, h3860, reducedSource131] using sourceEq151 B hB

theorem rowSound131 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row131 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck131, numericCheck131, reducedZero131 B hB hF, mul_zero]

theorem reducedZero132 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource132 (mixedVector B) = 0 := by
  have h2722 : mixedVector B (Sum.inr 2722) = Sparse.eval nodeValue2722 (mixedVector B) := by
    change mixedMoment B node2722 node2722Labels = _
    exact sound2722 B hB hF
  have h2726 : mixedVector B (Sum.inr 2726) = Sparse.eval nodeValue2726 (mixedVector B) := by
    change mixedMoment B node2726 node2726Labels = _
    exact sound2726 B hB hF
  have h2742 : mixedVector B (Sum.inr 2742) = Sparse.eval nodeValue2742 (mixedVector B) := by
    change mixedMoment B node2742 node2742Labels = _
    exact sound2742 B hB hF
  have h2765 : mixedVector B (Sum.inr 2765) = Sparse.eval nodeValue2765 (mixedVector B) := by
    change mixedMoment B node2765 node2765Labels = _
    exact sound2765 B hB hF
  have h3905 : mixedVector B (Sum.inr 3905) = Sparse.eval nodeValue3905 (mixedVector B) := by
    change mixedMoment B node3905 node3905Labels = _
    exact sound3905 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm152, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2722, h2726, h2742, h2765, h3905, h4092, reducedSource132] using sourceEq152 B hB

theorem rowSound132 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row132 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck132, numericCheck132, reducedZero132 B hB hF, mul_zero]

theorem reducedZero133 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource133 (mixedVector B) = 0 := by
  have h1215 : mixedVector B (Sum.inr 1215) = Sparse.eval nodeValue1215 (mixedVector B) := by
    change mixedMoment B node1215 node1215Labels = _
    exact sound1215 B hB hF
  have h1221 : mixedVector B (Sum.inr 1221) = Sparse.eval nodeValue1221 (mixedVector B) := by
    change mixedMoment B node1221 node1221Labels = _
    exact sound1221 B hB hF
  have h1242 : mixedVector B (Sum.inr 1242) = Sparse.eval nodeValue1242 (mixedVector B) := by
    change mixedMoment B node1242 node1242Labels = _
    exact sound1242 B hB hF
  have h1264 : mixedVector B (Sum.inr 1264) = Sparse.eval nodeValue1264 (mixedVector B) := by
    change mixedMoment B node1264 node1264Labels = _
    exact sound1264 B hB hF
  have h2726 : mixedVector B (Sum.inr 2726) = Sparse.eval nodeValue2726 (mixedVector B) := by
    change mixedMoment B node2726 node2726Labels = _
    exact sound2726 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm153, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1215, h1221, h1242, h1264, h2726, h4092, reducedSource133] using sourceEq153 B hB

theorem rowSound133 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row133 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck133, numericCheck133, reducedZero133 B hB hF, mul_zero]

theorem reducedZero134 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource134 (mixedVector B) = 0 := by
  have h1242 : mixedVector B (Sum.inr 1242) = Sparse.eval nodeValue1242 (mixedVector B) := by
    change mixedMoment B node1242 node1242Labels = _
    exact sound1242 B hB hF
  have h2482 : mixedVector B (Sum.inr 2482) = Sparse.eval nodeValue2482 (mixedVector B) := by
    change mixedMoment B node2482 node2482Labels = _
    exact sound2482 B hB hF
  have h2517 : mixedVector B (Sum.inr 2517) = Sparse.eval nodeValue2517 (mixedVector B) := by
    change mixedMoment B node2517 node2517Labels = _
    exact sound2517 B hB hF
  have h2726 : mixedVector B (Sum.inr 2726) = Sparse.eval nodeValue2726 (mixedVector B) := by
    change mixedMoment B node2726 node2726Labels = _
    exact sound2726 B hB hF
  have h2742 : mixedVector B (Sum.inr 2742) = Sparse.eval nodeValue2742 (mixedVector B) := by
    change mixedMoment B node2742 node2742Labels = _
    exact sound2742 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm154, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1242, h2482, h2517, h2726, h2742, h4092, reducedSource134] using sourceEq154 B hB

theorem rowSound134 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row134 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck134, numericCheck134, reducedZero134 B hB hF, mul_zero]

theorem reducedZero135 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource135 (mixedVector B) = 0 := by
  have h1264 : mixedVector B (Sum.inr 1264) = Sparse.eval nodeValue1264 (mixedVector B) := by
    change mixedMoment B node1264 node1264Labels = _
    exact sound1264 B hB hF
  have h2569 : mixedVector B (Sum.inr 2569) = Sparse.eval nodeValue2569 (mixedVector B) := by
    change mixedMoment B node2569 node2569Labels = _
    exact sound2569 B hB hF
  have h2635 : mixedVector B (Sum.inr 2635) = Sparse.eval nodeValue2635 (mixedVector B) := by
    change mixedMoment B node2635 node2635Labels = _
    exact sound2635 B hB hF
  have h2726 : mixedVector B (Sum.inr 2726) = Sparse.eval nodeValue2726 (mixedVector B) := by
    change mixedMoment B node2726 node2726Labels = _
    exact sound2726 B hB hF
  have h2765 : mixedVector B (Sum.inr 2765) = Sparse.eval nodeValue2765 (mixedVector B) := by
    change mixedMoment B node2765 node2765Labels = _
    exact sound2765 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm155, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1264, h2569, h2635, h2726, h2765, h4092, reducedSource135] using sourceEq155 B hB

theorem rowSound135 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row135 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck135, numericCheck135, reducedZero135 B hB hF, mul_zero]

theorem reducedZero136 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource136 (mixedVector B) = 0 := by
  have h1215 : mixedVector B (Sum.inr 1215) = Sparse.eval nodeValue1215 (mixedVector B) := by
    change mixedMoment B node1215 node1215Labels = _
    exact sound1215 B hB hF
  have h2482 : mixedVector B (Sum.inr 2482) = Sparse.eval nodeValue2482 (mixedVector B) := by
    change mixedMoment B node2482 node2482Labels = _
    exact sound2482 B hB hF
  have h2542 : mixedVector B (Sum.inr 2542) = Sparse.eval nodeValue2542 (mixedVector B) := by
    change mixedMoment B node2542 node2542Labels = _
    exact sound2542 B hB hF
  have h2569 : mixedVector B (Sum.inr 2569) = Sparse.eval nodeValue2569 (mixedVector B) := by
    change mixedMoment B node2569 node2569Labels = _
    exact sound2569 B hB hF
  have h2722 : mixedVector B (Sum.inr 2722) = Sparse.eval nodeValue2722 (mixedVector B) := by
    change mixedMoment B node2722 node2722Labels = _
    exact sound2722 B hB hF
  have h2726 : mixedVector B (Sum.inr 2726) = Sparse.eval nodeValue2726 (mixedVector B) := by
    change mixedMoment B node2726 node2726Labels = _
    exact sound2726 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm156, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1215, h2482, h2542, h2569, h2722, h2726, h4092, reducedSource136] using sourceEq156 B hB

theorem rowSound136 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row136 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck136, numericCheck136, reducedZero136 B hB hF, mul_zero]

theorem reducedZero142 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource142 (mixedVector B) = 0 := by
  have h2052 : mixedVector B (Sum.inr 2052) = Sparse.eval nodeValue2052 (mixedVector B) := by
    change mixedMoment B node2052 node2052Labels = _
    exact sound2052 B hB hF
  have h2056 : mixedVector B (Sum.inr 2056) = Sparse.eval nodeValue2056 (mixedVector B) := by
    change mixedMoment B node2056 node2056Labels = _
    exact sound2056 B hB hF
  have h2065 : mixedVector B (Sum.inr 2065) = Sparse.eval nodeValue2065 (mixedVector B) := by
    change mixedMoment B node2065 node2065Labels = _
    exact sound2065 B hB hF
  have h2292 : mixedVector B (Sum.inr 2292) = Sparse.eval nodeValue2292 (mixedVector B) := by
    change mixedMoment B node2292 node2292Labels = _
    exact sound2292 B hB hF
  have h3545 : mixedVector B (Sum.inr 3545) = Sparse.eval nodeValue3545 (mixedVector B) := by
    change mixedMoment B node3545 node3545Labels = _
    exact sound3545 B hB hF
  have h4085 : mixedVector B (Sum.inr 4085) = Sparse.eval nodeValue4085 (mixedVector B) := by
    change mixedMoment B node4085 node4085Labels = _
    exact sound4085 B hB hF
  simpa only [sourceForm162, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2052, h2056, h2065, h2292, h3545, h4085, reducedSource142] using sourceEq162 B hB

theorem rowSound142 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row142 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck142, numericCheck142, reducedZero142 B hB hF, mul_zero]

theorem sourceRowsAt128 : MixedData.sourceRows (128 : Fin 2425) =
    MixedData.row128 := by decide +kernel

theorem sourceRowsAt129 : MixedData.sourceRows (129 : Fin 2425) =
    MixedData.row129 := by decide +kernel

theorem sourceRowsAt130 : MixedData.sourceRows (130 : Fin 2425) =
    MixedData.row130 := by decide +kernel

theorem sourceRowsAt131 : MixedData.sourceRows (131 : Fin 2425) =
    MixedData.row131 := by decide +kernel

theorem sourceRowsAt132 : MixedData.sourceRows (132 : Fin 2425) =
    MixedData.row132 := by decide +kernel

theorem sourceRowsAt133 : MixedData.sourceRows (133 : Fin 2425) =
    MixedData.row133 := by decide +kernel

theorem sourceRowsAt134 : MixedData.sourceRows (134 : Fin 2425) =
    MixedData.row134 := by decide +kernel

theorem sourceRowsAt135 : MixedData.sourceRows (135 : Fin 2425) =
    MixedData.row135 := by decide +kernel

theorem sourceRowsAt136 : MixedData.sourceRows (136 : Fin 2425) =
    MixedData.row136 := by decide +kernel

theorem sourceRowsAt137 : MixedData.sourceRows (137 : Fin 2425) =
    MixedData.row137 := by decide +kernel

theorem sourceRowsAt138 : MixedData.sourceRows (138 : Fin 2425) =
    MixedData.row138 := by decide +kernel

theorem sourceRowsAt139 : MixedData.sourceRows (139 : Fin 2425) =
    MixedData.row139 := by decide +kernel

theorem sourceRowsAt140 : MixedData.sourceRows (140 : Fin 2425) =
    MixedData.row140 := by decide +kernel

theorem sourceRowsAt141 : MixedData.sourceRows (141 : Fin 2425) =
    MixedData.row141 := by decide +kernel

theorem sourceRowsAt142 : MixedData.sourceRows (142 : Fin 2425) =
    MixedData.row142 := by decide +kernel

theorem sourceRowsAt143 : MixedData.sourceRows (143 : Fin 2425) =
    MixedData.row143 := by decide +kernel

theorem chunkSound8_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) (k : Fin 2425)
    (hk : k.val / 16 = 8) :
    Integer.Sparse.eval (MixedData.sourceRows k) (numericVector B) = 0 := by
  have heq : k.val = 128 ∨ k.val = 129 ∨ k.val = 130 ∨ k.val = 131 ∨ k.val = 132 ∨ k.val = 133 ∨ k.val = 134 ∨ k.val = 135 ∨ k.val = 136 ∨ k.val = 137 ∨ k.val = 138 ∨ k.val = 139 ∨ k.val = 140 ∨ k.val = 141 ∨ k.val = 142 ∨ k.val = 143 := by omega
  rcases heq with h128 | h129 | h130 | h131 | h132 | h133 | h134 | h135 | h136 | h137 | h138 | h139 | h140 | h141 | h142 | h143
  · have he : k = (128 : Fin 2425) := Fin.ext h128
    subst k
    rw [sourceRowsAt128]
    exact rowSound128 B hB hF
  · have he : k = (129 : Fin 2425) := Fin.ext h129
    subst k
    rw [sourceRowsAt129]
    exact rowSound129 B hB hF
  · have he : k = (130 : Fin 2425) := Fin.ext h130
    subst k
    rw [sourceRowsAt130]
    exact rowSound130_e B hB hF
  · have he : k = (131 : Fin 2425) := Fin.ext h131
    subst k
    rw [sourceRowsAt131]
    exact rowSound131 B hB hF
  · have he : k = (132 : Fin 2425) := Fin.ext h132
    subst k
    rw [sourceRowsAt132]
    exact rowSound132 B hB hF
  · have he : k = (133 : Fin 2425) := Fin.ext h133
    subst k
    rw [sourceRowsAt133]
    exact rowSound133 B hB hF
  · have he : k = (134 : Fin 2425) := Fin.ext h134
    subst k
    rw [sourceRowsAt134]
    exact rowSound134 B hB hF
  · have he : k = (135 : Fin 2425) := Fin.ext h135
    subst k
    rw [sourceRowsAt135]
    exact rowSound135 B hB hF
  · have he : k = (136 : Fin 2425) := Fin.ext h136
    subst k
    rw [sourceRowsAt136]
    exact rowSound136 B hB hF
  · have he : k = (137 : Fin 2425) := Fin.ext h137
    subst k
    rw [sourceRowsAt137]
    exact rowSound137_e B hB hF
  · have he : k = (138 : Fin 2425) := Fin.ext h138
    subst k
    rw [sourceRowsAt138]
    exact rowSound138_e B hB hF
  · have he : k = (139 : Fin 2425) := Fin.ext h139
    subst k
    rw [sourceRowsAt139]
    exact rowSound139_e B hB hF
  · have he : k = (140 : Fin 2425) := Fin.ext h140
    subst k
    rw [sourceRowsAt140]
    exact rowSound140_e B hB hF
  · have he : k = (141 : Fin 2425) := Fin.ext h141
    subst k
    rw [sourceRowsAt141]
    exact rowSound141_e B hB hF
  · have he : k = (142 : Fin 2425) := Fin.ext h142
    subst k
    rw [sourceRowsAt142]
    exact rowSound142 B hB hF
  · have he : k = (143 : Fin 2425) := Fin.ext h143
    subst k
    rw [sourceRowsAt143]
    exact rowSound143_e B hB hF

end MUB6.Certificate.MixedSourceBridge

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedSourceBridge.chunkSound8_e_oai := @OAI.MUB6.Certificate.MixedSourceBridge.chunkSound8_e_oai
