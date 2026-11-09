-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedSourceBridge.chunkSound31_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T04:08:41.449196+00:00
-- url     : https://prove2.me/submissions/d47f88b5-6523-4f52-bb02-c4bc794e4776

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E077
import Definitions.Def_OAIQ106E086
import Definitions.Def_OAIQ106E090
import Definitions.Def_OAIQ106E187
import Definitions.Def_OAIQ106E097
import Definitions.Def_OAIQ106E188
import Definitions.Def_OAIQ106E190
import Definitions.Def_OAIQ106E191
import Definitions.Def_OAIQ106E194
import Definitions.Def_OAIQ106E195
import Definitions.Def_OAIQ106E115
import Definitions.Def_OAIQ106E119
import Definitions.Def_OAIQ106E121
import Definitions.Def_OAIQ106E127
import Definitions.Def_OAIQ106E140
import Definitions.Def_OAIQ106E147
import Definitions.Def_OAIQ106E170
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound5434_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound497_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound498_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound499_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound500_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound501_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound504_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound505_e

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

theorem canonical1425 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1425 raw1425Labels = mixedMoment B node4602 node4602Labels := by
  calc
    mixedMoment B raw1425 raw1425Labels = mixedMoment B raw1425step0 raw1425step0Labels := by
      have ha : raw1425step0 = (fun i j => raw1425 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1425step0 raw1425; decide +kernel
      have hl : raw1425step0Labels = raw1425Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1425 raw1425Labels permutation32 permutation4
    mixedMoment B raw1425step0 raw1425step0Labels = mixedMoment B raw1425step1 raw1425step1Labels := by
      have ha : raw1425step1 = raw1425step0 := by apply Matrix.ext; unfold raw1425step1 raw1425step0; decide +kernel
      have hl : raw1425step0Labels = labelEmbedding7 ∘ raw1425step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1425step0 raw1425step0Labels raw1425step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4602 node4602Labels := by rfl

theorem canonical1426 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1426 raw1426Labels = mixedMoment B node1236 node1236Labels := by
  calc
    mixedMoment B raw1426 raw1426Labels = mixedMoment B raw1426step0 raw1426step0Labels := by
      have ha : raw1426step0 = (fun i j => raw1426 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1426step0 raw1426; decide +kernel
      have hl : raw1426step0Labels = raw1426Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1426 raw1426Labels permutation32 permutation4
    _ = mixedMoment B node1236 node1236Labels := by rfl

theorem canonical1427 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1427 raw1427Labels = mixedMoment B node3293 node3293Labels := by
  calc
    mixedMoment B raw1427 raw1427Labels = mixedMoment B raw1427step0 raw1427step0Labels := by
      have ha : raw1427step0 = (fun i j => raw1427 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1427step0 raw1427; decide +kernel
      have hl : raw1427step0Labels = raw1427Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1427 raw1427Labels permutation32 permutation6
    mixedMoment B raw1427step0 raw1427step0Labels = mixedMoment B raw1427step1 raw1427step1Labels := by
      have ha : raw1427step1 = -raw1427step0 := by apply Matrix.ext; change ∀ i j, raw1427step1 i j = -(raw1427step0 i j); unfold raw1427step1 raw1427step0; decide +kernel
      have hl : raw1427step1Labels = raw1427step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1427step1 raw1427step1Labels = mixedMoment B raw1427step2 raw1427step2Labels := by
      have ha : raw1427step2 = raw1427step1 := by apply Matrix.ext; unfold raw1427step2 raw1427step1; decide +kernel
      have hl : raw1427step1Labels = labelEmbedding1 ∘ raw1427step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1427step1 raw1427step1Labels raw1427step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3293 node3293Labels := by rfl

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

theorem canonical2091 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2091 raw2091Labels = mixedMoment B node5072 node5072Labels := by
  calc
    mixedMoment B raw2091 raw2091Labels = mixedMoment B raw2091step0 raw2091step0Labels := by
      have ha : raw2091step0 = (fun i j => raw2091 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2091step0 raw2091; decide +kernel
      have hl : raw2091step0Labels = raw2091Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2091 raw2091Labels permutation152 permutation4
    mixedMoment B raw2091step0 raw2091step0Labels = mixedMoment B raw2091step1 raw2091step1Labels := by
      have ha : raw2091step1 = raw2091step0 := by apply Matrix.ext; unfold raw2091step1 raw2091step0; decide +kernel
      have hl : raw2091step0Labels = labelEmbedding7 ∘ raw2091step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2091step0 raw2091step0Labels raw2091step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5072 node5072Labels := by rfl

theorem canonical2092 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2092 raw2092Labels = mixedMoment B node2479 node2479Labels := by
  calc
    mixedMoment B raw2092 raw2092Labels = mixedMoment B raw2092step0 raw2092step0Labels := by
      have ha : raw2092step0 = (fun i j => raw2092 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2092step0 raw2092; decide +kernel
      have hl : raw2092step0Labels = raw2092Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2092 raw2092Labels permutation152 permutation4
    _ = mixedMoment B node2479 node2479Labels := by rfl

theorem canonical2093 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2093 raw2093Labels = mixedMoment B node3459 node3459Labels := by
  calc
    mixedMoment B raw2093 raw2093Labels = mixedMoment B raw2093step0 raw2093step0Labels := by
      have ha : raw2093step0 = (fun i j => raw2093 (permutation160 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2093step0 raw2093; decide +kernel
      have hl : raw2093step0Labels = raw2093Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2093 raw2093Labels permutation160 permutation6
    mixedMoment B raw2093step0 raw2093step0Labels = mixedMoment B raw2093step1 raw2093step1Labels := by
      have ha : raw2093step1 = -raw2093step0 := by apply Matrix.ext; change ∀ i j, raw2093step1 i j = -(raw2093step0 i j); unfold raw2093step1 raw2093step0; decide +kernel
      have hl : raw2093step1Labels = raw2093step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2093step1 raw2093step1Labels = mixedMoment B raw2093step2 raw2093step2Labels := by
      have ha : raw2093step2 = raw2093step1 := by apply Matrix.ext; unfold raw2093step2 raw2093step1; decide +kernel
      have hl : raw2093step1Labels = labelEmbedding1 ∘ raw2093step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2093step1 raw2093step1Labels raw2093step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3459 node3459Labels := by rfl

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

theorem canonical2106 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2106 raw2106Labels = mixedMoment B node5080 node5080Labels := by
  calc
    mixedMoment B raw2106 raw2106Labels = mixedMoment B raw2106step0 raw2106step0Labels := by
      have ha : raw2106step0 = (fun i j => raw2106 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2106step0 raw2106; decide +kernel
      have hl : raw2106step0Labels = raw2106Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2106 raw2106Labels permutation32 permutation4
    mixedMoment B raw2106step0 raw2106step0Labels = mixedMoment B raw2106step1 raw2106step1Labels := by
      have ha : raw2106step1 = raw2106step0 := by apply Matrix.ext; unfold raw2106step1 raw2106step0; decide +kernel
      have hl : raw2106step0Labels = labelEmbedding7 ∘ raw2106step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2106step0 raw2106step0Labels raw2106step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5080 node5080Labels := by rfl

theorem canonical2107 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2107 raw2107Labels = mixedMoment B node2488 node2488Labels := by
  calc
    mixedMoment B raw2107 raw2107Labels = mixedMoment B raw2107step0 raw2107step0Labels := by
      have ha : raw2107step0 = (fun i j => raw2107 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2107step0 raw2107; decide +kernel
      have hl : raw2107step0Labels = raw2107Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2107 raw2107Labels permutation32 permutation4
    _ = mixedMoment B node2488 node2488Labels := by rfl

theorem canonical2108 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2108 raw2108Labels = mixedMoment B node3478 node3478Labels := by
  calc
    mixedMoment B raw2108 raw2108Labels = mixedMoment B raw2108step0 raw2108step0Labels := by
      have ha : raw2108step0 = (fun i j => raw2108 (permutation34 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2108step0 raw2108; decide +kernel
      have hl : raw2108step0Labels = raw2108Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2108 raw2108Labels permutation34 permutation6
    mixedMoment B raw2108step0 raw2108step0Labels = mixedMoment B raw2108step1 raw2108step1Labels := by
      have ha : raw2108step1 = -raw2108step0 := by apply Matrix.ext; change ∀ i j, raw2108step1 i j = -(raw2108step0 i j); unfold raw2108step1 raw2108step0; decide +kernel
      have hl : raw2108step1Labels = raw2108step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2108step1 raw2108step1Labels = mixedMoment B raw2108step2 raw2108step2Labels := by
      have ha : raw2108step2 = raw2108step1 := by apply Matrix.ext; unfold raw2108step2 raw2108step1; decide +kernel
      have hl : raw2108step1Labels = labelEmbedding1 ∘ raw2108step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2108step1 raw2108step1Labels raw2108step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3478 node3478Labels := by rfl

theorem canonical2163 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2163 raw2163Labels = mixedMoment B node5134 node5134Labels := by
  calc
    mixedMoment B raw2163 raw2163Labels = mixedMoment B raw2163step0 raw2163step0Labels := by
      have ha : raw2163step0 = (fun i j => raw2163 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2163step0 raw2163; decide +kernel
      have hl : raw2163step0Labels = raw2163Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2163 raw2163Labels permutation152 permutation4
    mixedMoment B raw2163step0 raw2163step0Labels = mixedMoment B raw2163step1 raw2163step1Labels := by
      have ha : raw2163step1 = raw2163step0 := by apply Matrix.ext; unfold raw2163step1 raw2163step0; decide +kernel
      have hl : raw2163step0Labels = labelEmbedding7 ∘ raw2163step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2163step0 raw2163step0Labels raw2163step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5134 node5134Labels := by rfl

theorem canonical2164 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2164 raw2164Labels = mixedMoment B node2553 node2553Labels := by
  calc
    mixedMoment B raw2164 raw2164Labels = mixedMoment B raw2164step0 raw2164step0Labels := by
      have ha : raw2164step0 = (fun i j => raw2164 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2164step0 raw2164; decide +kernel
      have hl : raw2164step0Labels = raw2164Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2164 raw2164Labels permutation152 permutation4
    _ = mixedMoment B node2553 node2553Labels := by rfl

theorem canonical2165 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2165 raw2165Labels = mixedMoment B node3514 node3514Labels := by
  calc
    mixedMoment B raw2165 raw2165Labels = mixedMoment B raw2165step0 raw2165step0Labels := by
      have ha : raw2165step0 = (fun i j => raw2165 (permutation176 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2165step0 raw2165; decide +kernel
      have hl : raw2165step0Labels = raw2165Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2165 raw2165Labels permutation176 permutation6
    mixedMoment B raw2165step0 raw2165step0Labels = mixedMoment B raw2165step1 raw2165step1Labels := by
      have ha : raw2165step1 = -raw2165step0 := by apply Matrix.ext; change ∀ i j, raw2165step1 i j = -(raw2165step0 i j); unfold raw2165step1 raw2165step0; decide +kernel
      have hl : raw2165step1Labels = raw2165step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2165step1 raw2165step1Labels = mixedMoment B raw2165step2 raw2165step2Labels := by
      have ha : raw2165step2 = raw2165step1 := by apply Matrix.ext; unfold raw2165step2 raw2165step1; decide +kernel
      have hl : raw2165step1Labels = labelEmbedding1 ∘ raw2165step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2165step1 raw2165step1Labels raw2165step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3514 node3514Labels := by rfl

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

theorem canonical2280 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2280 raw2280Labels = mixedMoment B node5271 node5271Labels := by
  calc
    mixedMoment B raw2280 raw2280Labels = mixedMoment B raw2280step0 raw2280step0Labels := by
      have ha : raw2280step0 = (fun i j => raw2280 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2280step0 raw2280; decide +kernel
      have hl : raw2280step0Labels = raw2280Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2280 raw2280Labels permutation32 permutation4
    mixedMoment B raw2280step0 raw2280step0Labels = mixedMoment B raw2280step1 raw2280step1Labels := by
      have ha : raw2280step1 = raw2280step0 := by apply Matrix.ext; unfold raw2280step1 raw2280step0; decide +kernel
      have hl : raw2280step0Labels = labelEmbedding7 ∘ raw2280step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2280step0 raw2280step0Labels raw2280step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5271 node5271Labels := by rfl

theorem canonical2281 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2281 raw2281Labels = mixedMoment B node2739 node2739Labels := by
  calc
    mixedMoment B raw2281 raw2281Labels = mixedMoment B raw2281step0 raw2281step0Labels := by
      have ha : raw2281step0 = (fun i j => raw2281 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2281step0 raw2281; decide +kernel
      have hl : raw2281step0Labels = raw2281Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2281 raw2281Labels permutation32 permutation4
    _ = mixedMoment B node2739 node2739Labels := by rfl

theorem canonical2282 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2282 raw2282Labels = mixedMoment B node3534 node3534Labels := by
  calc
    mixedMoment B raw2282 raw2282Labels = mixedMoment B raw2282step0 raw2282step0Labels := by
      have ha : raw2282step0 = (fun i j => raw2282 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2282step0 raw2282; decide +kernel
      have hl : raw2282step0Labels = raw2282Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2282 raw2282Labels permutation32 permutation6
    mixedMoment B raw2282step0 raw2282step0Labels = mixedMoment B raw2282step1 raw2282step1Labels := by
      have ha : raw2282step1 = -raw2282step0 := by apply Matrix.ext; change ∀ i j, raw2282step1 i j = -(raw2282step0 i j); unfold raw2282step1 raw2282step0; decide +kernel
      have hl : raw2282step1Labels = raw2282step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2282step1 raw2282step1Labels = mixedMoment B raw2282step2 raw2282step2Labels := by
      have ha : raw2282step2 = raw2282step1 := by apply Matrix.ext; unfold raw2282step2 raw2282step1; decide +kernel
      have hl : raw2282step1Labels = labelEmbedding1 ∘ raw2282step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2282step1 raw2282step1Labels raw2282step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3534 node3534Labels := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical19
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical2511 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2511 raw2511Labels = mixedMoment B node5423 node5423Labels := by
  calc
    mixedMoment B raw2511 raw2511Labels = mixedMoment B raw2511step0 raw2511step0Labels := by
      have ha : raw2511step0 = (fun i j => raw2511 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2511step0 raw2511; decide +kernel
      have hl : raw2511step0Labels = raw2511Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2511 raw2511Labels permutation152 permutation4
    mixedMoment B raw2511step0 raw2511step0Labels = mixedMoment B raw2511step1 raw2511step1Labels := by
      have ha : raw2511step1 = raw2511step0 := by apply Matrix.ext; unfold raw2511step1 raw2511step0; decide +kernel
      have hl : raw2511step0Labels = labelEmbedding7 ∘ raw2511step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2511step0 raw2511step0Labels raw2511step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5423 node5423Labels := by rfl

theorem canonical2512 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2512 raw2512Labels = mixedMoment B node3837 node3837Labels := by
  calc
    mixedMoment B raw2512 raw2512Labels = mixedMoment B raw2512step0 raw2512step0Labels := by
      have ha : raw2512step0 = (fun i j => raw2512 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2512step0 raw2512; decide +kernel
      have hl : raw2512step0Labels = raw2512Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2512 raw2512Labels permutation152 permutation4
    _ = mixedMoment B node3837 node3837Labels := by rfl

theorem canonical2513 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2513 raw2513Labels = mixedMoment B node3837 node3837Labels := by
  calc
    mixedMoment B raw2513 raw2513Labels = mixedMoment B raw2513step0 raw2513step0Labels := by
      have ha : raw2513step0 = (fun i j => raw2513 (permutation662 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2513step0 raw2513; decide +kernel
      have hl : raw2513step0Labels = raw2513Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2513 raw2513Labels permutation662 permutation6
    mixedMoment B raw2513step0 raw2513step0Labels = mixedMoment B raw2513step1 raw2513step1Labels := by
      have ha : raw2513step1 = raw2513step0 := by apply Matrix.ext; unfold raw2513step1 raw2513step0; decide +kernel
      have hl : raw2513step0Labels = labelEmbedding1 ∘ raw2513step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2513step0 raw2513step0Labels raw2513step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3837 node3837Labels := by rfl

theorem canonical2523 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2523 raw2523Labels = mixedMoment B node5432 node5432Labels := by
  calc
    mixedMoment B raw2523 raw2523Labels = mixedMoment B raw2523step0 raw2523step0Labels := by
      have ha : raw2523step0 = (fun i j => raw2523 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2523step0 raw2523; decide +kernel
      have hl : raw2523step0Labels = raw2523Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2523 raw2523Labels permutation32 permutation4
    mixedMoment B raw2523step0 raw2523step0Labels = mixedMoment B raw2523step1 raw2523step1Labels := by
      have ha : raw2523step1 = raw2523step0 := by apply Matrix.ext; unfold raw2523step1 raw2523step0; decide +kernel
      have hl : raw2523step0Labels = labelEmbedding7 ∘ raw2523step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2523step0 raw2523step0Labels raw2523step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5432 node5432Labels := by rfl

theorem canonical2524 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2524 raw2524Labels = mixedMoment B node3850 node3850Labels := by
  calc
    mixedMoment B raw2524 raw2524Labels = mixedMoment B raw2524step0 raw2524step0Labels := by
      have ha : raw2524step0 = (fun i j => raw2524 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2524step0 raw2524; decide +kernel
      have hl : raw2524step0Labels = raw2524Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2524 raw2524Labels permutation32 permutation4
    _ = mixedMoment B node3850 node3850Labels := by rfl

theorem canonical2525 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2525 raw2525Labels = mixedMoment B node3850 node3850Labels := by
  calc
    mixedMoment B raw2525 raw2525Labels = mixedMoment B raw2525step0 raw2525step0Labels := by
      have ha : raw2525step0 = (fun i j => raw2525 (permutation143 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2525step0 raw2525; decide +kernel
      have hl : raw2525step0Labels = raw2525Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2525 raw2525Labels permutation143 permutation6
    mixedMoment B raw2525step0 raw2525step0Labels = mixedMoment B raw2525step1 raw2525step1Labels := by
      have ha : raw2525step1 = raw2525step0 := by apply Matrix.ext; unfold raw2525step1 raw2525step0; decide +kernel
      have hl : raw2525step0Labels = labelEmbedding1 ∘ raw2525step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2525step0 raw2525step0Labels raw2525step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3850 node3850Labels := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical76
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

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

theorem canonical9841 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9841 raw9841Labels = mixedMoment B node2546 node2546Labels := by
  calc
    mixedMoment B raw9841 raw9841Labels = mixedMoment B raw9841step0 raw9841step0Labels := by
      have ha : raw9841step0 = (fun i j => raw9841 (permutation182 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9841step0 raw9841; decide +kernel
      have hl : raw9841step0Labels = raw9841Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9841 raw9841Labels permutation182 permutation2
    _ = mixedMoment B node2546 node2546Labels := by rfl

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

theorem canonical9846 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9846 raw9846Labels = mixedMoment B node2723 node2723Labels := by
  calc
    mixedMoment B raw9846 raw9846Labels = mixedMoment B raw9846step0 raw9846step0Labels := by
      have hz : ∀ j, raw9846 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw9846step0 = (fun i j => raw9846 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw9846step0 raw9846; decide +kernel
      have hl : raw9846step0Labels = raw9846Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9846 raw9846Labels permutation346 hz
    mixedMoment B raw9846step0 raw9846step0Labels = mixedMoment B raw9846step1 raw9846step1Labels := by
      have ha : raw9846step1 = (fun i j => raw9846step0 (permutation39 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9846step1 raw9846step0; decide +kernel
      have hl : raw9846step1Labels = raw9846step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9846step0 raw9846step0Labels permutation39 permutation2
    _ = mixedMoment B node2723 node2723Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical77
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical9963 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9963 raw9963Labels = mixedMoment B node3544 node3544Labels := by
  calc
    mixedMoment B raw9963 raw9963Labels = mixedMoment B raw9963step0 raw9963step0Labels := by
      have hz : ∀ j, raw9963 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw9963step0 = (fun i j => raw9963 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw9963step0 raw9963; decide +kernel
      have hl : raw9963step0Labels = raw9963Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9963 raw9963Labels permutation346 hz
    mixedMoment B raw9963step0 raw9963step0Labels = mixedMoment B raw9963step1 raw9963step1Labels := by
      have ha : raw9963step1 = (fun i j => raw9963step0 (permutation38 i) (permutation4 j)) := by apply Matrix.ext; unfold raw9963step1 raw9963step0; decide +kernel
      have hl : raw9963step1Labels = raw9963step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9963step0 raw9963step0Labels permutation38 permutation4
    mixedMoment B raw9963step1 raw9963step1Labels = mixedMoment B raw9963step2 raw9963step2Labels := by
      have ha : raw9963step2 = -raw9963step1 := by apply Matrix.ext; change ∀ i j, raw9963step2 i j = -(raw9963step1 i j); unfold raw9963step2 raw9963step1; decide +kernel
      have hl : raw9963step2Labels = raw9963step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3544 node3544Labels := by rfl

theorem canonical9964 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9964 raw9964Labels = mixedMoment B node2058 node2058Labels := by
  calc
    mixedMoment B raw9964 raw9964Labels = mixedMoment B raw9964step0 raw9964step0Labels := by
      have hz : ∀ j, raw9964 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw9964step0 = (fun i j => raw9964 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw9964step0 raw9964; decide +kernel
      have hl : raw9964step0Labels = raw9964Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9964 raw9964Labels permutation346 hz
    mixedMoment B raw9964step0 raw9964step0Labels = mixedMoment B raw9964step1 raw9964step1Labels := by
      have ha : raw9964step1 = (fun i j => raw9964step0 (permutation41 i) (permutation4 j)) := by apply Matrix.ext; unfold raw9964step1 raw9964step0; decide +kernel
      have hl : raw9964step1Labels = raw9964step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9964step0 raw9964step0Labels permutation41 permutation4
    mixedMoment B raw9964step1 raw9964step1Labels = mixedMoment B raw9964step2 raw9964step2Labels := by
      have ha : raw9964step2 = -raw9964step1 := by apply Matrix.ext; change ∀ i j, raw9964step2 i j = -(raw9964step1 i j); unfold raw9964step2 raw9964step1; decide +kernel
      have hl : raw9964step2Labels = raw9964step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2058 node2058Labels := by rfl

theorem canonical9965 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9965 raw9965Labels = mixedMoment B node2051 node2051Labels := by
  calc
    mixedMoment B raw9965 raw9965Labels = mixedMoment B raw9965step0 raw9965step0Labels := by
      have ha : raw9965step0 = (fun i j => raw9965 (permutation200 i) (permutation4 j)) := by apply Matrix.ext; unfold raw9965step0 raw9965; decide +kernel
      have hl : raw9965step0Labels = raw9965Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9965 raw9965Labels permutation200 permutation4
    mixedMoment B raw9965step0 raw9965step0Labels = mixedMoment B raw9965step1 raw9965step1Labels := by
      have ha : raw9965step1 = -raw9965step0 := by apply Matrix.ext; change ∀ i j, raw9965step1 i j = -(raw9965step0 i j); unfold raw9965step1 raw9965step0; decide +kernel
      have hl : raw9965step1Labels = raw9965step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2051 node2051Labels := by rfl

theorem canonical9966 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9966 raw9966Labels = mixedMoment B node2291 node2291Labels := by
  calc
    mixedMoment B raw9966 raw9966Labels = mixedMoment B raw9966step0 raw9966step0Labels := by
      have hz : ∀ j, raw9966 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw9966step0 = (fun i j => raw9966 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw9966step0 raw9966; decide +kernel
      have hl : raw9966step0Labels = raw9966Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9966 raw9966Labels permutation434 hz
    mixedMoment B raw9966step0 raw9966step0Labels = mixedMoment B raw9966step1 raw9966step1Labels := by
      have hz : ∀ j, raw9966step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw9966step1 = (fun i j => raw9966step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw9966step1 raw9966step0; decide +kernel
      have hl : raw9966step1Labels = raw9966step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9966step0 raw9966step0Labels permutation80 hz
    mixedMoment B raw9966step1 raw9966step1Labels = mixedMoment B raw9966step2 raw9966step2Labels := by
      have ha : raw9966step2 = (fun i j => raw9966step1 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw9966step2 raw9966step1; decide +kernel
      have hl : raw9966step2Labels = raw9966step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9966step1 raw9966step1Labels permutation8 permutation4
    mixedMoment B raw9966step2 raw9966step2Labels = mixedMoment B raw9966step3 raw9966step3Labels := by
      have ha : raw9966step3 = -raw9966step2 := by apply Matrix.ext; change ∀ i j, raw9966step3 i j = -(raw9966step2 i j); unfold raw9966step3 raw9966step2; decide +kernel
      have hl : raw9966step3Labels = raw9966step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2291 node2291Labels := by rfl

theorem canonical9967 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9967 raw9967Labels = mixedMoment B node2054 node2054Labels := by
  calc
    mixedMoment B raw9967 raw9967Labels = mixedMoment B raw9967step0 raw9967step0Labels := by
      have hz : ∀ j, raw9967 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw9967step0 = (fun i j => raw9967 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw9967step0 raw9967; decide +kernel
      have hl : raw9967step0Labels = raw9967Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9967 raw9967Labels permutation346 hz
    mixedMoment B raw9967step0 raw9967step0Labels = mixedMoment B raw9967step1 raw9967step1Labels := by
      have ha : raw9967step1 = (fun i j => raw9967step0 (permutation39 i) (permutation4 j)) := by apply Matrix.ext; unfold raw9967step1 raw9967step0; decide +kernel
      have hl : raw9967step1Labels = raw9967step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9967step0 raw9967step0Labels permutation39 permutation4
    mixedMoment B raw9967step1 raw9967step1Labels = mixedMoment B raw9967step2 raw9967step2Labels := by
      have ha : raw9967step2 = -raw9967step1 := by apply Matrix.ext; change ∀ i j, raw9967step2 i j = -(raw9967step1 i j); unfold raw9967step2 raw9967step1; decide +kernel
      have hl : raw9967step2Labels = raw9967step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2054 node2054Labels := by rfl

theorem canonical9968 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9968 raw9968Labels = mixedMoment B node2053 node2053Labels := by
  calc
    mixedMoment B raw9968 raw9968Labels = mixedMoment B raw9968step0 raw9968step0Labels := by
      have hz : ∀ j, raw9968 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw9968step0 = (fun i j => raw9968 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw9968step0 raw9968; decide +kernel
      have hl : raw9968step0Labels = raw9968Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9968 raw9968Labels permutation346 hz
    mixedMoment B raw9968step0 raw9968step0Labels = mixedMoment B raw9968step1 raw9968step1Labels := by
      have ha : raw9968step1 = (fun i j => raw9968step0 (permutation38 i) (permutation4 j)) := by apply Matrix.ext; unfold raw9968step1 raw9968step0; decide +kernel
      have hl : raw9968step1Labels = raw9968step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9968step0 raw9968step0Labels permutation38 permutation4
    mixedMoment B raw9968step1 raw9968step1Labels = mixedMoment B raw9968step2 raw9968step2Labels := by
      have ha : raw9968step2 = -raw9968step1 := by apply Matrix.ext; change ∀ i j, raw9968step2 i j = -(raw9968step1 i j); unfold raw9968step2 raw9968step1; decide +kernel
      have hl : raw9968step2Labels = raw9968step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2053 node2053Labels := by rfl

theorem canonical9969 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9969 raw9969Labels = mixedMoment B node5432 node5432Labels := by
  calc
    mixedMoment B raw9969 raw9969Labels = mixedMoment B raw9969step0 raw9969step0Labels := by
      have hz : ∀ j, raw9969 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw9969step0 = (fun i j => raw9969 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw9969step0 raw9969; decide +kernel
      have hl : raw9969step0Labels = raw9969Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9969 raw9969Labels permutation346 hz
    mixedMoment B raw9969step0 raw9969step0Labels = mixedMoment B raw9969step1 raw9969step1Labels := by
      have ha : raw9969step1 = (fun i j => raw9969step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9969step1 raw9969step0; decide +kernel
      have hl : raw9969step1Labels = raw9969step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9969step0 raw9969step0Labels permutation151 permutation2
    mixedMoment B raw9969step1 raw9969step1Labels = mixedMoment B raw9969step2 raw9969step2Labels := by
      have ha : raw9969step2 = -raw9969step1 := by apply Matrix.ext; change ∀ i j, raw9969step2 i j = -(raw9969step1 i j); unfold raw9969step2 raw9969step1; decide +kernel
      have hl : raw9969step2Labels = raw9969step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5432 node5432Labels := by rfl

theorem canonical9970 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9970 raw9970Labels = mixedMoment B node5423 node5423Labels := by
  calc
    mixedMoment B raw9970 raw9970Labels = mixedMoment B raw9970step0 raw9970step0Labels := by
      have ha : raw9970step0 = (fun i j => raw9970 (permutation182 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9970step0 raw9970; decide +kernel
      have hl : raw9970step0Labels = raw9970Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9970 raw9970Labels permutation182 permutation2
    _ = mixedMoment B node5423 node5423Labels := by rfl

theorem canonical9971 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9971 raw9971Labels = mixedMoment B node5409 node5409Labels := by
  calc
    mixedMoment B raw9971 raw9971Labels = mixedMoment B raw9971step0 raw9971step0Labels := by
      have hz : ∀ j, raw9971 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw9971step0 = (fun i j => raw9971 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw9971step0 raw9971; decide +kernel
      have hl : raw9971step0Labels = raw9971Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9971 raw9971Labels permutation346 hz
    mixedMoment B raw9971step0 raw9971step0Labels = mixedMoment B raw9971step1 raw9971step1Labels := by
      have ha : raw9971step1 = (fun i j => raw9971step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9971step1 raw9971step0; decide +kernel
      have hl : raw9971step1Labels = raw9971step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9971step0 raw9971step0Labels permutation38 permutation2
    _ = mixedMoment B node5409 node5409Labels := by rfl

theorem canonical9972 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9972 raw9972Labels = mixedMoment B node5441 node5441Labels := by
  calc
    mixedMoment B raw9972 raw9972Labels = mixedMoment B raw9972step0 raw9972step0Labels := by
      have hz : ∀ j, raw9972 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw9972step0 = (fun i j => raw9972 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw9972step0 raw9972; decide +kernel
      have hl : raw9972step0Labels = raw9972Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9972 raw9972Labels permutation520 hz
    mixedMoment B raw9972step0 raw9972step0Labels = mixedMoment B raw9972step1 raw9972step1Labels := by
      have hz : ∀ j, raw9972step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw9972step1 = (fun i j => raw9972step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw9972step1 raw9972step0; decide +kernel
      have hl : raw9972step1Labels = raw9972step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9972step0 raw9972step0Labels permutation80 hz
    mixedMoment B raw9972step1 raw9972step1Labels = mixedMoment B raw9972step2 raw9972step2Labels := by
      have ha : raw9972step2 = (fun i j => raw9972step1 (permutation29 i) (permutation7 j)) := by apply Matrix.ext; unfold raw9972step2 raw9972step1; decide +kernel
      have hl : raw9972step2Labels = raw9972step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9972step1 raw9972step1Labels permutation29 permutation7
    mixedMoment B raw9972step2 raw9972step2Labels = mixedMoment B raw9972step3 raw9972step3Labels := by
      have ha : raw9972step3 = raw9972step2 := by apply Matrix.ext; unfold raw9972step3 raw9972step2; decide +kernel
      have hl : raw9972step2Labels = labelEmbedding10 ∘ raw9972step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9972step2 raw9972step2Labels raw9972step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5441 node5441Labels := by rfl

theorem canonical9973 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9973 raw9973Labels = mixedMoment B node5434 node5434Labels := by
  calc
    mixedMoment B raw9973 raw9973Labels = mixedMoment B raw9973step0 raw9973step0Labels := by
      have hz : ∀ j, raw9973 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw9973step0 = (fun i j => raw9973 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw9973step0 raw9973; decide +kernel
      have hl : raw9973step0Labels = raw9973Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9973 raw9973Labels permutation346 hz
    mixedMoment B raw9973step0 raw9973step0Labels = mixedMoment B raw9973step1 raw9973step1Labels := by
      have ha : raw9973step1 = (fun i j => raw9973step0 (permutation40 i) (permutation7 j)) := by apply Matrix.ext; unfold raw9973step1 raw9973step0; decide +kernel
      have hl : raw9973step1Labels = raw9973step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9973step0 raw9973step0Labels permutation40 permutation7
    mixedMoment B raw9973step1 raw9973step1Labels = mixedMoment B raw9973step2 raw9973step2Labels := by
      have ha : raw9973step2 = -raw9973step1 := by apply Matrix.ext; change ∀ i j, raw9973step2 i j = -(raw9973step1 i j); unfold raw9973step2 raw9973step1; decide +kernel
      have hl : raw9973step2Labels = raw9973step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw9973step2 raw9973step2Labels = mixedMoment B raw9973step3 raw9973step3Labels := by
      have ha : raw9973step3 = raw9973step2 := by apply Matrix.ext; unfold raw9973step3 raw9973step2; decide +kernel
      have hl : raw9973step2Labels = labelEmbedding10 ∘ raw9973step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9973step2 raw9973step2Labels raw9973step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5434 node5434Labels := by rfl

theorem canonical9974 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9974 raw9974Labels = mixedMoment B node4602 node4602Labels := by
  calc
    mixedMoment B raw9974 raw9974Labels = mixedMoment B raw9974step0 raw9974step0Labels := by
      have hz : ∀ j, raw9974 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw9974step0 = (fun i j => raw9974 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw9974step0 raw9974; decide +kernel
      have hl : raw9974step0Labels = raw9974Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9974 raw9974Labels permutation346 hz
    mixedMoment B raw9974step0 raw9974step0Labels = mixedMoment B raw9974step1 raw9974step1Labels := by
      have ha : raw9974step1 = (fun i j => raw9974step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9974step1 raw9974step0; decide +kernel
      have hl : raw9974step1Labels = raw9974step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9974step0 raw9974step0Labels permutation40 permutation2
    _ = mixedMoment B node4602 node4602Labels := by rfl

theorem canonical9975 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9975 raw9975Labels = mixedMoment B node5134 node5134Labels := by
  calc
    mixedMoment B raw9975 raw9975Labels = mixedMoment B raw9975step0 raw9975step0Labels := by
      have ha : raw9975step0 = (fun i j => raw9975 (permutation184 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9975step0 raw9975; decide +kernel
      have hl : raw9975step0Labels = raw9975Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9975 raw9975Labels permutation184 permutation2
    _ = mixedMoment B node5134 node5134Labels := by rfl

theorem canonical9976 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9976 raw9976Labels = mixedMoment B node5101 node5101Labels := by
  calc
    mixedMoment B raw9976 raw9976Labels = mixedMoment B raw9976step0 raw9976step0Labels := by
      have hz : ∀ j, raw9976 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw9976step0 = (fun i j => raw9976 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw9976step0 raw9976; decide +kernel
      have hl : raw9976step0Labels = raw9976Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9976 raw9976Labels permutation346 hz
    mixedMoment B raw9976step0 raw9976step0Labels = mixedMoment B raw9976step1 raw9976step1Labels := by
      have ha : raw9976step1 = (fun i j => raw9976step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9976step1 raw9976step0; decide +kernel
      have hl : raw9976step1Labels = raw9976step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9976step0 raw9976step0Labels permutation40 permutation2
    _ = mixedMoment B node5101 node5101Labels := by rfl

theorem canonical9977 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9977 raw9977Labels = mixedMoment B node5274 node5274Labels := by
  calc
    mixedMoment B raw9977 raw9977Labels = mixedMoment B raw9977step0 raw9977step0Labels := by
      have hz : ∀ j, raw9977 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw9977step0 = (fun i j => raw9977 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw9977step0 raw9977; decide +kernel
      have hl : raw9977step0Labels = raw9977Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9977 raw9977Labels permutation520 hz
    mixedMoment B raw9977step0 raw9977step0Labels = mixedMoment B raw9977step1 raw9977step1Labels := by
      have hz : ∀ j, raw9977step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw9977step1 = (fun i j => raw9977step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw9977step1 raw9977step0; decide +kernel
      have hl : raw9977step1Labels = raw9977step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9977step0 raw9977step0Labels permutation80 hz
    mixedMoment B raw9977step1 raw9977step1Labels = mixedMoment B raw9977step2 raw9977step2Labels := by
      have ha : raw9977step2 = (fun i j => raw9977step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9977step2 raw9977step1; decide +kernel
      have hl : raw9977step2Labels = raw9977step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9977step1 raw9977step1Labels permutation10 permutation2
    _ = mixedMoment B node5274 node5274Labels := by rfl

theorem canonical9978 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9978 raw9978Labels = mixedMoment B node5271 node5271Labels := by
  calc
    mixedMoment B raw9978 raw9978Labels = mixedMoment B raw9978step0 raw9978step0Labels := by
      have hz : ∀ j, raw9978 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw9978step0 = (fun i j => raw9978 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw9978step0 raw9978; decide +kernel
      have hl : raw9978step0Labels = raw9978Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9978 raw9978Labels permutation346 hz
    mixedMoment B raw9978step0 raw9978step0Labels = mixedMoment B raw9978step1 raw9978step1Labels := by
      have ha : raw9978step1 = (fun i j => raw9978step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9978step1 raw9978step0; decide +kernel
      have hl : raw9978step1Labels = raw9978step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9978step0 raw9978step0Labels permutation40 permutation2
    _ = mixedMoment B node5271 node5271Labels := by rfl

theorem canonical9979 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9979 raw9979Labels = mixedMoment B node4589 node4589Labels := by
  calc
    mixedMoment B raw9979 raw9979Labels = mixedMoment B raw9979step0 raw9979step0Labels := by
      have ha : raw9979step0 = (fun i j => raw9979 (permutation200 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9979step0 raw9979; decide +kernel
      have hl : raw9979step0Labels = raw9979Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9979 raw9979Labels permutation200 permutation2
    _ = mixedMoment B node4589 node4589Labels := by rfl

theorem canonical9980 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9980 raw9980Labels = mixedMoment B node5184 node5184Labels := by
  calc
    mixedMoment B raw9980 raw9980Labels = mixedMoment B raw9980step0 raw9980step0Labels := by
      have ha : raw9980step0 = (fun i j => raw9980 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9980step0 raw9980; decide +kernel
      have hl : raw9980step0Labels = raw9980Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9980 raw9980Labels permutation158 permutation2
    _ = mixedMoment B node5184 node5184Labels := by rfl

theorem canonical9981 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9981 raw9981Labels = mixedMoment B node5072 node5072Labels := by
  calc
    mixedMoment B raw9981 raw9981Labels = mixedMoment B raw9981step0 raw9981step0Labels := by
      have ha : raw9981step0 = (fun i j => raw9981 (permutation200 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9981step0 raw9981; decide +kernel
      have hl : raw9981step0Labels = raw9981Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9981 raw9981Labels permutation200 permutation2
    _ = mixedMoment B node5072 node5072Labels := by rfl

theorem canonical9982 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9982 raw9982Labels = mixedMoment B node5258 node5258Labels := by
  calc
    mixedMoment B raw9982 raw9982Labels = mixedMoment B raw9982step0 raw9982step0Labels := by
      have hz : ∀ j, raw9982 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw9982step0 = (fun i j => raw9982 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw9982step0 raw9982; decide +kernel
      have hl : raw9982step0Labels = raw9982Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9982 raw9982Labels permutation520 hz
    mixedMoment B raw9982step0 raw9982step0Labels = mixedMoment B raw9982step1 raw9982step1Labels := by
      have ha : raw9982step1 = (fun i j => raw9982step0 (permutation44 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9982step1 raw9982step0; decide +kernel
      have hl : raw9982step1Labels = raw9982step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9982step0 raw9982step0Labels permutation44 permutation2
    _ = mixedMoment B node5258 node5258Labels := by rfl

theorem canonical9983 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9983 raw9983Labels = mixedMoment B node5256 node5256Labels := by
  calc
    mixedMoment B raw9983 raw9983Labels = mixedMoment B raw9983step0 raw9983step0Labels := by
      have ha : raw9983step0 = (fun i j => raw9983 (permutation200 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9983step0 raw9983; decide +kernel
      have hl : raw9983step0Labels = raw9983Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9983 raw9983Labels permutation200 permutation2
    _ = mixedMoment B node5256 node5256Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical78
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical9984 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9984 raw9984Labels = mixedMoment B node4607 node4607Labels := by
  calc
    mixedMoment B raw9984 raw9984Labels = mixedMoment B raw9984step0 raw9984step0Labels := by
      have hz : ∀ j, raw9984 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw9984step0 = (fun i j => raw9984 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw9984step0 raw9984; decide +kernel
      have hl : raw9984step0Labels = raw9984Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9984 raw9984Labels permutation346 hz
    mixedMoment B raw9984step0 raw9984step0Labels = mixedMoment B raw9984step1 raw9984step1Labels := by
      have ha : raw9984step1 = (fun i j => raw9984step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9984step1 raw9984step0; decide +kernel
      have hl : raw9984step1Labels = raw9984step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9984step0 raw9984step0Labels permutation34 permutation3
    mixedMoment B raw9984step1 raw9984step1Labels = mixedMoment B raw9984step2 raw9984step2Labels := by
      have ha : raw9984step2 = raw9984step1 := by apply Matrix.ext; unfold raw9984step2 raw9984step1; decide +kernel
      have hl : raw9984step1Labels = labelEmbedding6 ∘ raw9984step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9984step1 raw9984step1Labels raw9984step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4607 node4607Labels := by rfl

theorem canonical9985 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9985 raw9985Labels = mixedMoment B node5198 node5198Labels := by
  calc
    mixedMoment B raw9985 raw9985Labels = mixedMoment B raw9985step0 raw9985step0Labels := by
      have hz : ∀ j, raw9985 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw9985step0 = (fun i j => raw9985 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw9985step0 raw9985; decide +kernel
      have hl : raw9985step0Labels = raw9985Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9985 raw9985Labels permutation346 hz
    _ = mixedMoment B node5198 node5198Labels := by rfl

theorem canonical9986 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9986 raw9986Labels = mixedMoment B node5144 node5144Labels := by
  calc
    mixedMoment B raw9986 raw9986Labels = mixedMoment B raw9986step0 raw9986step0Labels := by
      have ha : raw9986step0 = (fun i j => raw9986 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9986step0 raw9986; decide +kernel
      have hl : raw9986step0Labels = raw9986Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9986 raw9986Labels permutation176 permutation2
    _ = mixedMoment B node5144 node5144Labels := by rfl

theorem canonical9987 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9987 raw9987Labels = mixedMoment B node5291 node5291Labels := by
  calc
    mixedMoment B raw9987 raw9987Labels = mixedMoment B raw9987step0 raw9987step0Labels := by
      have hz : ∀ j, raw9987 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw9987step0 = (fun i j => raw9987 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw9987step0 raw9987; decide +kernel
      have hl : raw9987step0Labels = raw9987Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9987 raw9987Labels permutation520 hz
    mixedMoment B raw9987step0 raw9987step0Labels = mixedMoment B raw9987step1 raw9987step1Labels := by
      have hz : ∀ j, raw9987step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw9987step1 = (fun i j => raw9987step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw9987step1 raw9987step0; decide +kernel
      have hl : raw9987step1Labels = raw9987step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9987step0 raw9987step0Labels permutation80 hz
    _ = mixedMoment B node5291 node5291Labels := by rfl

theorem canonical9988 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9988 raw9988Labels = mixedMoment B node5289 node5289Labels := by
  calc
    mixedMoment B raw9988 raw9988Labels = mixedMoment B raw9988step0 raw9988step0Labels := by
      have hz : ∀ j, raw9988 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw9988step0 = (fun i j => raw9988 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw9988step0 raw9988; decide +kernel
      have hl : raw9988step0Labels = raw9988Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9988 raw9988Labels permutation346 hz
    _ = mixedMoment B node5289 node5289Labels := by rfl

theorem canonical9989 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9989 raw9989Labels = mixedMoment B node4592 node4592Labels := by
  calc
    mixedMoment B raw9989 raw9989Labels = mixedMoment B raw9989step0 raw9989step0Labels := by
      have hz : ∀ j, raw9989 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw9989step0 = (fun i j => raw9989 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw9989step0 raw9989; decide +kernel
      have hl : raw9989step0Labels = raw9989Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9989 raw9989Labels permutation346 hz
    mixedMoment B raw9989step0 raw9989step0Labels = mixedMoment B raw9989step1 raw9989step1Labels := by
      have ha : raw9989step1 = (fun i j => raw9989step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9989step1 raw9989step0; decide +kernel
      have hl : raw9989step1Labels = raw9989step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9989step0 raw9989step0Labels permutation38 permutation2
    _ = mixedMoment B node4592 node4592Labels := by rfl

theorem canonical9990 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9990 raw9990Labels = mixedMoment B node5188 node5188Labels := by
  calc
    mixedMoment B raw9990 raw9990Labels = mixedMoment B raw9990step0 raw9990step0Labels := by
      have hz : ∀ j, raw9990 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw9990step0 = (fun i j => raw9990 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw9990step0 raw9990; decide +kernel
      have hl : raw9990step0Labels = raw9990Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9990 raw9990Labels permutation346 hz
    _ = mixedMoment B node5188 node5188Labels := by rfl

theorem canonical9991 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9991 raw9991Labels = mixedMoment B node5129 node5129Labels := by
  calc
    mixedMoment B raw9991 raw9991Labels = mixedMoment B raw9991step0 raw9991step0Labels := by
      have ha : raw9991step0 = (fun i j => raw9991 (permutation182 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9991step0 raw9991; decide +kernel
      have hl : raw9991step0Labels = raw9991Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9991 raw9991Labels permutation182 permutation2
    _ = mixedMoment B node5129 node5129Labels := by rfl

theorem canonical9992 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9992 raw9992Labels = mixedMoment B node5080 node5080Labels := by
  calc
    mixedMoment B raw9992 raw9992Labels = mixedMoment B raw9992step0 raw9992step0Labels := by
      have hz : ∀ j, raw9992 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw9992step0 = (fun i j => raw9992 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw9992step0 raw9992; decide +kernel
      have hl : raw9992step0Labels = raw9992Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9992 raw9992Labels permutation346 hz
    mixedMoment B raw9992step0 raw9992step0Labels = mixedMoment B raw9992step1 raw9992step1Labels := by
      have ha : raw9992step1 = (fun i j => raw9992step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9992step1 raw9992step0; decide +kernel
      have hl : raw9992step1Labels = raw9992step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9992step0 raw9992step0Labels permutation38 permutation2
    _ = mixedMoment B node5080 node5080Labels := by rfl

theorem canonical9993 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9993 raw9993Labels = mixedMoment B node5260 node5260Labels := by
  calc
    mixedMoment B raw9993 raw9993Labels = mixedMoment B raw9993step0 raw9993step0Labels := by
      have hz : ∀ j, raw9993 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw9993step0 = (fun i j => raw9993 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw9993step0 raw9993; decide +kernel
      have hl : raw9993step0Labels = raw9993Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9993 raw9993Labels permutation346 hz
    mixedMoment B raw9993step0 raw9993step0Labels = mixedMoment B raw9993step1 raw9993step1Labels := by
      have ha : raw9993step1 = (fun i j => raw9993step0 (permutation39 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9993step1 raw9993step0; decide +kernel
      have hl : raw9993step1Labels = raw9993step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9993step0 raw9993step0Labels permutation39 permutation2
    _ = mixedMoment B node5260 node5260Labels := by rfl

theorem canonical9994 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9994 raw9994Labels = mixedMoment B node4591 node4591Labels := by
  calc
    mixedMoment B raw9994 raw9994Labels = mixedMoment B raw9994step0 raw9994step0Labels := by
      have hz : ∀ j, raw9994 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw9994step0 = (fun i j => raw9994 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw9994step0 raw9994; decide +kernel
      have hl : raw9994step0Labels = raw9994Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9994 raw9994Labels permutation346 hz
    mixedMoment B raw9994step0 raw9994step0Labels = mixedMoment B raw9994step1 raw9994step1Labels := by
      have ha : raw9994step1 = (fun i j => raw9994step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9994step1 raw9994step0; decide +kernel
      have hl : raw9994step1Labels = raw9994step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9994step0 raw9994step0Labels permutation38 permutation2
    _ = mixedMoment B node4591 node4591Labels := by rfl

theorem canonical9995 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9995 raw9995Labels = mixedMoment B node5147 node5147Labels := by
  calc
    mixedMoment B raw9995 raw9995Labels = mixedMoment B raw9995step0 raw9995step0Labels := by
      have hz : ∀ j, raw9995 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw9995step0 = (fun i j => raw9995 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw9995step0 raw9995; decide +kernel
      have hl : raw9995step0Labels = raw9995Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9995 raw9995Labels permutation346 hz
    mixedMoment B raw9995step0 raw9995step0Labels = mixedMoment B raw9995step1 raw9995step1Labels := by
      have ha : raw9995step1 = (fun i j => raw9995step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9995step1 raw9995step0; decide +kernel
      have hl : raw9995step1Labels = raw9995step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9995step0 raw9995step0Labels permutation151 permutation2
    mixedMoment B raw9995step1 raw9995step1Labels = mixedMoment B raw9995step2 raw9995step2Labels := by
      have ha : raw9995step2 = -raw9995step1 := by apply Matrix.ext; change ∀ i j, raw9995step2 i j = -(raw9995step1 i j); unfold raw9995step2 raw9995step1; decide +kernel
      have hl : raw9995step2Labels = raw9995step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5147 node5147Labels := by rfl

theorem canonical9996 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9996 raw9996Labels = mixedMoment B node5127 node5127Labels := by
  calc
    mixedMoment B raw9996 raw9996Labels = mixedMoment B raw9996step0 raw9996step0Labels := by
      have ha : raw9996step0 = (fun i j => raw9996 (permutation182 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9996step0 raw9996; decide +kernel
      have hl : raw9996step0Labels = raw9996Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9996 raw9996Labels permutation182 permutation2
    _ = mixedMoment B node5127 node5127Labels := by rfl

theorem canonical9997 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9997 raw9997Labels = mixedMoment B node5075 node5075Labels := by
  calc
    mixedMoment B raw9997 raw9997Labels = mixedMoment B raw9997step0 raw9997step0Labels := by
      have hz : ∀ j, raw9997 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw9997step0 = (fun i j => raw9997 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw9997step0 raw9997; decide +kernel
      have hl : raw9997step0Labels = raw9997Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9997 raw9997Labels permutation346 hz
    mixedMoment B raw9997step0 raw9997step0Labels = mixedMoment B raw9997step1 raw9997step1Labels := by
      have ha : raw9997step1 = (fun i j => raw9997step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9997step1 raw9997step0; decide +kernel
      have hl : raw9997step1Labels = raw9997step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9997step0 raw9997step0Labels permutation38 permutation2
    _ = mixedMoment B node5075 node5075Labels := by rfl

theorem canonical9998 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9998 raw9998Labels = mixedMoment B node5261 node5261Labels := by
  calc
    mixedMoment B raw9998 raw9998Labels = mixedMoment B raw9998step0 raw9998step0Labels := by
      have hz : ∀ j, raw9998 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw9998step0 = (fun i j => raw9998 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw9998step0 raw9998; decide +kernel
      have hl : raw9998step0Labels = raw9998Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9998 raw9998Labels permutation520 hz
    mixedMoment B raw9998step0 raw9998step0Labels = mixedMoment B raw9998step1 raw9998step1Labels := by
      have hz : ∀ j, raw9998step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw9998step1 = (fun i j => raw9998step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw9998step1 raw9998step0; decide +kernel
      have hl : raw9998step1Labels = raw9998step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9998step0 raw9998step0Labels permutation80 hz
    mixedMoment B raw9998step1 raw9998step1Labels = mixedMoment B raw9998step2 raw9998step2Labels := by
      have ha : raw9998step2 = (fun i j => raw9998step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9998step2 raw9998step1; decide +kernel
      have hl : raw9998step2Labels = raw9998step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9998step1 raw9998step1Labels permutation10 permutation2
    _ = mixedMoment B node5261 node5261Labels := by rfl

theorem canonical10059 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10059 raw10059Labels = mixedMoment B node2722 node2722Labels := by
  calc
    mixedMoment B raw10059 raw10059Labels = mixedMoment B raw10059step0 raw10059step0Labels := by
      have hz : ∀ j, raw10059 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10059step0 = (fun i j => raw10059 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10059step0 raw10059; decide +kernel
      have hl : raw10059step0Labels = raw10059Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10059 raw10059Labels permutation346 hz
    mixedMoment B raw10059step0 raw10059step0Labels = mixedMoment B raw10059step1 raw10059step1Labels := by
      have ha : raw10059step1 = (fun i j => raw10059step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw10059step1 raw10059step0; decide +kernel
      have hl : raw10059step1Labels = raw10059step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10059step0 raw10059step0Labels permutation38 permutation2
    _ = mixedMoment B node2722 node2722Labels := by rfl

theorem canonical10060 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10060 raw10060Labels = mixedMoment B node3850 node3850Labels := by
  calc
    mixedMoment B raw10060 raw10060Labels = mixedMoment B raw10060step0 raw10060step0Labels := by
      have hz : ∀ j, raw10060 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10060step0 = (fun i j => raw10060 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10060step0 raw10060; decide +kernel
      have hl : raw10060step0Labels = raw10060Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10060 raw10060Labels permutation346 hz
    mixedMoment B raw10060step0 raw10060step0Labels = mixedMoment B raw10060step1 raw10060step1Labels := by
      have ha : raw10060step1 = (fun i j => raw10060step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw10060step1 raw10060step0; decide +kernel
      have hl : raw10060step1Labels = raw10060step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10060step0 raw10060step0Labels permutation151 permutation2
    mixedMoment B raw10060step1 raw10060step1Labels = mixedMoment B raw10060step2 raw10060step2Labels := by
      have ha : raw10060step2 = -raw10060step1 := by apply Matrix.ext; change ∀ i j, raw10060step2 i j = -(raw10060step1 i j); unfold raw10060step2 raw10060step1; decide +kernel
      have hl : raw10060step2Labels = raw10060step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3850 node3850Labels := by rfl

theorem canonical10061 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10061 raw10061Labels = mixedMoment B node3837 node3837Labels := by
  calc
    mixedMoment B raw10061 raw10061Labels = mixedMoment B raw10061step0 raw10061step0Labels := by
      have ha : raw10061step0 = (fun i j => raw10061 (permutation182 i) (permutation2 j)) := by apply Matrix.ext; unfold raw10061step0 raw10061; decide +kernel
      have hl : raw10061step0Labels = raw10061Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10061 raw10061Labels permutation182 permutation2
    _ = mixedMoment B node3837 node3837Labels := by rfl

theorem canonical10062 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10062 raw10062Labels = mixedMoment B node3807 node3807Labels := by
  calc
    mixedMoment B raw10062 raw10062Labels = mixedMoment B raw10062step0 raw10062step0Labels := by
      have hz : ∀ j, raw10062 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10062step0 = (fun i j => raw10062 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10062step0 raw10062; decide +kernel
      have hl : raw10062step0Labels = raw10062Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10062 raw10062Labels permutation346 hz
    mixedMoment B raw10062step0 raw10062step0Labels = mixedMoment B raw10062step1 raw10062step1Labels := by
      have ha : raw10062step1 = (fun i j => raw10062step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw10062step1 raw10062step0; decide +kernel
      have hl : raw10062step1Labels = raw10062step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10062step0 raw10062step0Labels permutation38 permutation2
    _ = mixedMoment B node3807 node3807Labels := by rfl

theorem canonical10063 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10063 raw10063Labels = mixedMoment B node3905 node3905Labels := by
  calc
    mixedMoment B raw10063 raw10063Labels = mixedMoment B raw10063step0 raw10063step0Labels := by
      have hz : ∀ j, raw10063 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw10063step0 = (fun i j => raw10063 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw10063step0 raw10063; decide +kernel
      have hl : raw10063step0Labels = raw10063Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10063 raw10063Labels permutation520 hz
    mixedMoment B raw10063step0 raw10063step0Labels = mixedMoment B raw10063step1 raw10063step1Labels := by
      have hz : ∀ j, raw10063step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw10063step1 = (fun i j => raw10063step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw10063step1 raw10063step0; decide +kernel
      have hl : raw10063step1Labels = raw10063step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10063step0 raw10063step0Labels permutation80 hz
    mixedMoment B raw10063step1 raw10063step1Labels = mixedMoment B raw10063step2 raw10063step2Labels := by
      have ha : raw10063step2 = (fun i j => raw10063step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw10063step2 raw10063step1; decide +kernel
      have hl : raw10063step2Labels = raw10063step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10063step1 raw10063step1Labels permutation10 permutation2
    _ = mixedMoment B node3905 node3905Labels := by rfl

theorem canonical10064 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10064 raw10064Labels = mixedMoment B node3903 node3903Labels := by
  calc
    mixedMoment B raw10064 raw10064Labels = mixedMoment B raw10064step0 raw10064step0Labels := by
      have hz : ∀ j, raw10064 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10064step0 = (fun i j => raw10064 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10064step0 raw10064; decide +kernel
      have hl : raw10064step0Labels = raw10064Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10064 raw10064Labels permutation346 hz
    mixedMoment B raw10064step0 raw10064step0Labels = mixedMoment B raw10064step1 raw10064step1Labels := by
      have ha : raw10064step1 = (fun i j => raw10064step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw10064step1 raw10064step0; decide +kernel
      have hl : raw10064step1Labels = raw10064step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10064step0 raw10064step0Labels permutation38 permutation2
    _ = mixedMoment B node3903 node3903Labels := by rfl

theorem canonical10065 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10065 raw10065Labels = mixedMoment B node4092 node4092Labels := by
  calc
    mixedMoment B raw10065 raw10065Labels = mixedMoment B raw10065step0 raw10065step0Labels := by
      have hz : ∀ j, raw10065 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw10065step0 = (fun i j => raw10065 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw10065step0 raw10065; decide +kernel
      have hl : raw10065step0Labels = raw10065Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10065 raw10065Labels permutation520 hz
    mixedMoment B raw10065step0 raw10065step0Labels = mixedMoment B raw10065step1 raw10065step1Labels := by
      have hz : ∀ j, raw10065step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw10065step1 = (fun i j => raw10065step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw10065step1 raw10065step0; decide +kernel
      have hl : raw10065step1Labels = raw10065step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10065step0 raw10065step0Labels permutation80 hz
    mixedMoment B raw10065step1 raw10065step1Labels = mixedMoment B raw10065step2 raw10065step2Labels := by
      have ha : raw10065step2 = (fun i j => raw10065step1 (permutation10 i) (permutation0 j)) := by apply Matrix.ext; unfold raw10065step2 raw10065step1; decide +kernel
      have hl : raw10065step2Labels = raw10065step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10065step1 raw10065step1Labels permutation10 permutation0
    _ = mixedMoment B node4092 node4092Labels := by rfl

theorem canonical10066 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10066 raw10066Labels = mixedMoment B node1236 node1236Labels := by
  calc
    mixedMoment B raw10066 raw10066Labels = mixedMoment B raw10066step0 raw10066step0Labels := by
      have hz : ∀ j, raw10066 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10066step0 = (fun i j => raw10066 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10066step0 raw10066; decide +kernel
      have hl : raw10066step0Labels = raw10066Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10066 raw10066Labels permutation346 hz
    mixedMoment B raw10066step0 raw10066step0Labels = mixedMoment B raw10066step1 raw10066step1Labels := by
      have ha : raw10066step1 = (fun i j => raw10066step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw10066step1 raw10066step0; decide +kernel
      have hl : raw10066step1Labels = raw10066step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10066step0 raw10066step0Labels permutation40 permutation2
    _ = mixedMoment B node1236 node1236Labels := by rfl

theorem canonical10067 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10067 raw10067Labels = mixedMoment B node1212 node1212Labels := by
  calc
    mixedMoment B raw10067 raw10067Labels = mixedMoment B raw10067step0 raw10067step0Labels := by
      have ha : raw10067step0 = (fun i j => raw10067 (permutation200 i) (permutation2 j)) := by apply Matrix.ext; unfold raw10067step0 raw10067; decide +kernel
      have hl : raw10067step0Labels = raw10067Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10067 raw10067Labels permutation200 permutation2
    _ = mixedMoment B node1212 node1212Labels := by rfl

theorem canonical10068 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10068 raw10068Labels = mixedMoment B node1261 node1261Labels := by
  calc
    mixedMoment B raw10068 raw10068Labels = mixedMoment B raw10068step0 raw10068step0Labels := by
      have hz : ∀ j, raw10068 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10068step0 = (fun i j => raw10068 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10068step0 raw10068; decide +kernel
      have hl : raw10068step0Labels = raw10068Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10068 raw10068Labels permutation346 hz
    _ = mixedMoment B node1261 node1261Labels := by rfl

theorem canonical10069 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10069 raw10069Labels = mixedMoment B node1219 node1219Labels := by
  calc
    mixedMoment B raw10069 raw10069Labels = mixedMoment B raw10069step0 raw10069step0Labels := by
      have hz : ∀ j, raw10069 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10069step0 = (fun i j => raw10069 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10069step0 raw10069; decide +kernel
      have hl : raw10069step0Labels = raw10069Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10069 raw10069Labels permutation346 hz
    mixedMoment B raw10069step0 raw10069step0Labels = mixedMoment B raw10069step1 raw10069step1Labels := by
      have ha : raw10069step1 = (fun i j => raw10069step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw10069step1 raw10069step0; decide +kernel
      have hl : raw10069step1Labels = raw10069step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10069step0 raw10069step0Labels permutation38 permutation2
    _ = mixedMoment B node1219 node1219Labels := by rfl

theorem canonical10070 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10070 raw10070Labels = mixedMoment B node1215 node1215Labels := by
  calc
    mixedMoment B raw10070 raw10070Labels = mixedMoment B raw10070step0 raw10070step0Labels := by
      have hz : ∀ j, raw10070 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10070step0 = (fun i j => raw10070 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10070step0 raw10070; decide +kernel
      have hl : raw10070step0Labels = raw10070Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10070 raw10070Labels permutation346 hz
    mixedMoment B raw10070step0 raw10070step0Labels = mixedMoment B raw10070step1 raw10070step1Labels := by
      have ha : raw10070step1 = (fun i j => raw10070step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw10070step1 raw10070step0; decide +kernel
      have hl : raw10070step1Labels = raw10070step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10070step0 raw10070step0Labels permutation38 permutation2
    _ = mixedMoment B node1215 node1215Labels := by rfl

theorem canonical10071 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10071 raw10071Labels = mixedMoment B node2553 node2553Labels := by
  calc
    mixedMoment B raw10071 raw10071Labels = mixedMoment B raw10071step0 raw10071step0Labels := by
      have ha : raw10071step0 = (fun i j => raw10071 (permutation184 i) (permutation2 j)) := by apply Matrix.ext; unfold raw10071step0 raw10071; decide +kernel
      have hl : raw10071step0Labels = raw10071Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10071 raw10071Labels permutation184 permutation2
    _ = mixedMoment B node2553 node2553Labels := by rfl

theorem canonical10072 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10072 raw10072Labels = mixedMoment B node2511 node2511Labels := by
  calc
    mixedMoment B raw10072 raw10072Labels = mixedMoment B raw10072step0 raw10072step0Labels := by
      have hz : ∀ j, raw10072 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10072step0 = (fun i j => raw10072 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10072step0 raw10072; decide +kernel
      have hl : raw10072step0Labels = raw10072Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10072 raw10072Labels permutation346 hz
    mixedMoment B raw10072step0 raw10072step0Labels = mixedMoment B raw10072step1 raw10072step1Labels := by
      have ha : raw10072step1 = (fun i j => raw10072step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw10072step1 raw10072step0; decide +kernel
      have hl : raw10072step1Labels = raw10072step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10072step0 raw10072step0Labels permutation40 permutation2
    _ = mixedMoment B node2511 node2511Labels := by rfl

theorem canonical10073 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10073 raw10073Labels = mixedMoment B node2742 node2742Labels := by
  calc
    mixedMoment B raw10073 raw10073Labels = mixedMoment B raw10073step0 raw10073step0Labels := by
      have hz : ∀ j, raw10073 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw10073step0 = (fun i j => raw10073 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw10073step0 raw10073; decide +kernel
      have hl : raw10073step0Labels = raw10073Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10073 raw10073Labels permutation520 hz
    mixedMoment B raw10073step0 raw10073step0Labels = mixedMoment B raw10073step1 raw10073step1Labels := by
      have hz : ∀ j, raw10073step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw10073step1 = (fun i j => raw10073step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw10073step1 raw10073step0; decide +kernel
      have hl : raw10073step1Labels = raw10073step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10073step0 raw10073step0Labels permutation80 hz
    mixedMoment B raw10073step1 raw10073step1Labels = mixedMoment B raw10073step2 raw10073step2Labels := by
      have ha : raw10073step2 = (fun i j => raw10073step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw10073step2 raw10073step1; decide +kernel
      have hl : raw10073step2Labels = raw10073step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10073step1 raw10073step1Labels permutation10 permutation2
    _ = mixedMoment B node2742 node2742Labels := by rfl

theorem canonical10074 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10074 raw10074Labels = mixedMoment B node2739 node2739Labels := by
  calc
    mixedMoment B raw10074 raw10074Labels = mixedMoment B raw10074step0 raw10074step0Labels := by
      have hz : ∀ j, raw10074 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10074step0 = (fun i j => raw10074 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10074step0 raw10074; decide +kernel
      have hl : raw10074step0Labels = raw10074Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10074 raw10074Labels permutation346 hz
    mixedMoment B raw10074step0 raw10074step0Labels = mixedMoment B raw10074step1 raw10074step1Labels := by
      have ha : raw10074step1 = (fun i j => raw10074step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw10074step1 raw10074step0; decide +kernel
      have hl : raw10074step1Labels = raw10074step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10074step0 raw10074step0Labels permutation40 permutation2
    _ = mixedMoment B node2739 node2739Labels := by rfl

theorem canonical10075 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10075 raw10075Labels = mixedMoment B node2614 node2614Labels := by
  calc
    mixedMoment B raw10075 raw10075Labels = mixedMoment B raw10075step0 raw10075step0Labels := by
      have ha : raw10075step0 = (fun i j => raw10075 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw10075step0 raw10075; decide +kernel
      have hl : raw10075step0Labels = raw10075Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10075 raw10075Labels permutation158 permutation2
    _ = mixedMoment B node2614 node2614Labels := by rfl

theorem canonical10076 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10076 raw10076Labels = mixedMoment B node2632 node2632Labels := by
  calc
    mixedMoment B raw10076 raw10076Labels = mixedMoment B raw10076step0 raw10076step0Labels := by
      have hz : ∀ j, raw10076 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10076step0 = (fun i j => raw10076 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10076step0 raw10076; decide +kernel
      have hl : raw10076step0Labels = raw10076Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10076 raw10076Labels permutation346 hz
    _ = mixedMoment B node2632 node2632Labels := by rfl

theorem canonical10077 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10077 raw10077Labels = mixedMoment B node2620 node2620Labels := by
  calc
    mixedMoment B raw10077 raw10077Labels = mixedMoment B raw10077step0 raw10077step0Labels := by
      have hz : ∀ j, raw10077 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10077step0 = (fun i j => raw10077 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10077step0 raw10077; decide +kernel
      have hl : raw10077step0Labels = raw10077Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10077 raw10077Labels permutation346 hz
    _ = mixedMoment B node2620 node2620Labels := by rfl

theorem canonical10078 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10078 raw10078Labels = mixedMoment B node2569 node2569Labels := by
  calc
    mixedMoment B raw10078 raw10078Labels = mixedMoment B raw10078step0 raw10078step0Labels := by
      have hz : ∀ j, raw10078 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10078step0 = (fun i j => raw10078 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10078step0 raw10078; decide +kernel
      have hl : raw10078step0Labels = raw10078Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10078 raw10078Labels permutation346 hz
    mixedMoment B raw10078step0 raw10078step0Labels = mixedMoment B raw10078step1 raw10078step1Labels := by
      have ha : raw10078step1 = (fun i j => raw10078step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw10078step1 raw10078step0; decide +kernel
      have hl : raw10078step1Labels = raw10078step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10078step0 raw10078step0Labels permutation151 permutation2
    mixedMoment B raw10078step1 raw10078step1Labels = mixedMoment B raw10078step2 raw10078step2Labels := by
      have ha : raw10078step2 = -raw10078step1 := by apply Matrix.ext; change ∀ i j, raw10078step2 i j = -(raw10078step1 i j); unfold raw10078step2 raw10078step1; decide +kernel
      have hl : raw10078step2Labels = raw10078step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2569 node2569Labels := by rfl

theorem canonical10079 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10079 raw10079Labels = mixedMoment B node2479 node2479Labels := by
  calc
    mixedMoment B raw10079 raw10079Labels = mixedMoment B raw10079step0 raw10079step0Labels := by
      have ha : raw10079step0 = (fun i j => raw10079 (permutation200 i) (permutation2 j)) := by apply Matrix.ext; unfold raw10079step0 raw10079; decide +kernel
      have hl : raw10079step0Labels = raw10079Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10079 raw10079Labels permutation200 permutation2
    _ = mixedMoment B node2479 node2479Labels := by rfl

theorem canonical10080 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10080 raw10080Labels = mixedMoment B node2722 node2722Labels := by
  calc
    mixedMoment B raw10080 raw10080Labels = mixedMoment B raw10080step0 raw10080step0Labels := by
      have hz : ∀ j, raw10080 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw10080step0 = (fun i j => raw10080 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw10080step0 raw10080; decide +kernel
      have hl : raw10080step0Labels = raw10080Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10080 raw10080Labels permutation520 hz
    mixedMoment B raw10080step0 raw10080step0Labels = mixedMoment B raw10080step1 raw10080step1Labels := by
      have ha : raw10080step1 = (fun i j => raw10080step0 (permutation44 i) (permutation2 j)) := by apply Matrix.ext; unfold raw10080step1 raw10080step0; decide +kernel
      have hl : raw10080step1Labels = raw10080step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10080step0 raw10080step0Labels permutation44 permutation2
    _ = mixedMoment B node2722 node2722Labels := by rfl

theorem canonical10081 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10081 raw10081Labels = mixedMoment B node2720 node2720Labels := by
  calc
    mixedMoment B raw10081 raw10081Labels = mixedMoment B raw10081step0 raw10081step0Labels := by
      have ha : raw10081step0 = (fun i j => raw10081 (permutation200 i) (permutation2 j)) := by apply Matrix.ext; unfold raw10081step0 raw10081; decide +kernel
      have hl : raw10081step0Labels = raw10081Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10081 raw10081Labels permutation200 permutation2
    _ = mixedMoment B node2720 node2720Labels := by rfl

theorem canonical10082 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10082 raw10082Labels = mixedMoment B node2566 node2566Labels := by
  calc
    mixedMoment B raw10082 raw10082Labels = mixedMoment B raw10082step0 raw10082step0Labels := by
      have ha : raw10082step0 = (fun i j => raw10082 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw10082step0 raw10082; decide +kernel
      have hl : raw10082step0Labels = raw10082Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10082 raw10082Labels permutation176 permutation2
    _ = mixedMoment B node2566 node2566Labels := by rfl

theorem canonical10083 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10083 raw10083Labels = mixedMoment B node2545 node2545Labels := by
  calc
    mixedMoment B raw10083 raw10083Labels = mixedMoment B raw10083step0 raw10083step0Labels := by
      have ha : raw10083step0 = (fun i j => raw10083 (permutation182 i) (permutation2 j)) := by apply Matrix.ext; unfold raw10083step0 raw10083; decide +kernel
      have hl : raw10083step0Labels = raw10083Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10083 raw10083Labels permutation182 permutation2
    _ = mixedMoment B node2545 node2545Labels := by rfl

theorem canonical10084 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10084 raw10084Labels = mixedMoment B node2542 node2542Labels := by
  calc
    mixedMoment B raw10084 raw10084Labels = mixedMoment B raw10084step0 raw10084step0Labels := by
      have ha : raw10084step0 = (fun i j => raw10084 (permutation182 i) (permutation2 j)) := by apply Matrix.ext; unfold raw10084step0 raw10084; decide +kernel
      have hl : raw10084step0Labels = raw10084Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10084 raw10084Labels permutation182 permutation2
    _ = mixedMoment B node2542 node2542Labels := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons71
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singleton4602 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4602 node4602Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1236 node1236Labels + mixedMoment B node3293 node3293Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1425 singletonSmall4602
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4602) = raw1425Labels := by decide +kernel
  rw [hl, canonical1425 B hB] at h
  have hc0 : mixedMoment B raw1425 (Fin.cases (0 : Fin 2) singletonSmall4602) =
      mixedMoment B node1236 node1236Labels := by
    have ha : raw1425 = raw1426 := by apply Matrix.ext; unfold raw1425 raw1426; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4602 = raw1426Labels := by decide +kernel
    rw [ha, hj, canonical1426 B hB]
  have hc1 : mixedMoment B raw1425 (Fin.cases (1 : Fin 2) singletonSmall4602) =
      mixedMoment B node3293 node3293Labels := by
    have ha : raw1425 = raw1427 := by apply Matrix.ext; unfold raw1425 raw1427; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4602 = raw1427Labels := by decide +kernel
    rw [ha, hj, canonical1427 B hB]
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

theorem singleton5072 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5072 node5072Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2479 node2479Labels + mixedMoment B node3459 node3459Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2091 singletonSmall5072
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5072) = raw2091Labels := by decide +kernel
  rw [hl, canonical2091 B hB] at h
  have hc0 : mixedMoment B raw2091 (Fin.cases (0 : Fin 2) singletonSmall5072) =
      mixedMoment B node2479 node2479Labels := by
    have ha : raw2091 = raw2092 := by apply Matrix.ext; unfold raw2091 raw2092; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5072 = raw2092Labels := by decide +kernel
    rw [ha, hj, canonical2092 B hB]
  have hc1 : mixedMoment B raw2091 (Fin.cases (1 : Fin 2) singletonSmall5072) =
      mixedMoment B node3459 node3459Labels := by
    have ha : raw2091 = raw2093 := by apply Matrix.ext; unfold raw2091 raw2093; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5072 = raw2093Labels := by decide +kernel
    rw [ha, hj, canonical2093 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

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

theorem singleton5080 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5080 node5080Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2488 node2488Labels + mixedMoment B node3478 node3478Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2106 singletonSmall5080
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5080) = raw2106Labels := by decide +kernel
  rw [hl, canonical2106 B hB] at h
  have hc0 : mixedMoment B raw2106 (Fin.cases (0 : Fin 2) singletonSmall5080) =
      mixedMoment B node2488 node2488Labels := by
    have ha : raw2106 = raw2107 := by apply Matrix.ext; unfold raw2106 raw2107; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5080 = raw2107Labels := by decide +kernel
    rw [ha, hj, canonical2107 B hB]
  have hc1 : mixedMoment B raw2106 (Fin.cases (1 : Fin 2) singletonSmall5080) =
      mixedMoment B node3478 node3478Labels := by
    have ha : raw2106 = raw2108 := by apply Matrix.ext; unfold raw2106 raw2108; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5080 = raw2108Labels := by decide +kernel
    rw [ha, hj, canonical2108 B hB]
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

theorem singleton5134 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5134 node5134Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2553 node2553Labels + mixedMoment B node3514 node3514Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2163 singletonSmall5134
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5134) = raw2163Labels := by decide +kernel
  rw [hl, canonical2163 B hB] at h
  have hc0 : mixedMoment B raw2163 (Fin.cases (0 : Fin 2) singletonSmall5134) =
      mixedMoment B node2553 node2553Labels := by
    have ha : raw2163 = raw2164 := by apply Matrix.ext; unfold raw2163 raw2164; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5134 = raw2164Labels := by decide +kernel
    rw [ha, hj, canonical2164 B hB]
  have hc1 : mixedMoment B raw2163 (Fin.cases (1 : Fin 2) singletonSmall5134) =
      mixedMoment B node3514 node3514Labels := by
    have ha : raw2163 = raw2165 := by apply Matrix.ext; unfold raw2163 raw2165; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5134 = raw2165Labels := by decide +kernel
    rw [ha, hj, canonical2165 B hB]
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

theorem singleton5271 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5271 node5271Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2739 node2739Labels + mixedMoment B node3534 node3534Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2280 singletonSmall5271
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5271) = raw2280Labels := by decide +kernel
  rw [hl, canonical2280 B hB] at h
  have hc0 : mixedMoment B raw2280 (Fin.cases (0 : Fin 2) singletonSmall5271) =
      mixedMoment B node2739 node2739Labels := by
    have ha : raw2280 = raw2281 := by apply Matrix.ext; unfold raw2280 raw2281; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5271 = raw2281Labels := by decide +kernel
    rw [ha, hj, canonical2281 B hB]
  have hc1 : mixedMoment B raw2280 (Fin.cases (1 : Fin 2) singletonSmall5271) =
      mixedMoment B node3534 node3534Labels := by
    have ha : raw2280 = raw2282 := by apply Matrix.ext; unfold raw2280 raw2282; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5271 = raw2282Labels := by decide +kernel
    rw [ha, hj, canonical2282 B hB]
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons84
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singleton5423 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5423 node5423Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3837 node3837Labels + mixedMoment B node3837 node3837Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2511 singletonSmall5423
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5423) = raw2511Labels := by decide +kernel
  rw [hl, canonical2511 B hB] at h
  have hc0 : mixedMoment B raw2511 (Fin.cases (0 : Fin 2) singletonSmall5423) =
      mixedMoment B node3837 node3837Labels := by
    have ha : raw2511 = raw2512 := by apply Matrix.ext; unfold raw2511 raw2512; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5423 = raw2512Labels := by decide +kernel
    rw [ha, hj, canonical2512 B hB]
  have hc1 : mixedMoment B raw2511 (Fin.cases (1 : Fin 2) singletonSmall5423) =
      mixedMoment B node3837 node3837Labels := by
    have ha : raw2511 = raw2513 := by apply Matrix.ext; unfold raw2511 raw2513; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5423 = raw2513Labels := by decide +kernel
    rw [ha, hj, canonical2513 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton5432 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5432 node5432Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3850 node3850Labels + mixedMoment B node3850 node3850Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2523 singletonSmall5432
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5432) = raw2523Labels := by decide +kernel
  rw [hl, canonical2523 B hB] at h
  have hc0 : mixedMoment B raw2523 (Fin.cases (0 : Fin 2) singletonSmall5432) =
      mixedMoment B node3850 node3850Labels := by
    have ha : raw2523 = raw2524 := by apply Matrix.ext; unfold raw2523 raw2524; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5432 = raw2524Labels := by decide +kernel
    rw [ha, hj, canonical2524 B hB]
  have hc1 : mixedMoment B raw2523 (Fin.cases (1 : Fin 2) singletonSmall5432) =
      mixedMoment B node3850 node3850Labels := by
    have ha : raw2523 = raw2525 := by apply Matrix.ext; unfold raw2523 raw2525; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5432 = raw2525Labels := by decide +kernel
    rw [ha, hj, canonical2525 B hB]
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound18
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound1212 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1212 node1212Labels = Sparse.eval nodeValue1212 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1212) = mixedMoment B node1212 node1212Labels := rfl
  simpa [nodeValue1212, Sparse.eval] using hc.symm

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

theorem sound1219 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1219 node1219Labels = Sparse.eval nodeValue1219 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1219) = mixedMoment B node1219 node1219Labels := rfl
  simpa [nodeValue1219, Sparse.eval] using hc.symm

theorem sound1220 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1220 node1220Labels = Sparse.eval nodeValue1220 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1220) = mixedMoment B node1220 node1220Labels := rfl
  simpa [nodeValue1220, Sparse.eval] using hc.symm

theorem sound1236 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1236 node1236Labels = Sparse.eval nodeValue1236 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1236) = mixedMoment B node1236 node1236Labels := rfl
  simpa [nodeValue1236, Sparse.eval] using hc.symm

theorem sound1261 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1261 node1261Labels = Sparse.eval nodeValue1261 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1261) = mixedMoment B node1261 node1261Labels := rfl
  simpa [nodeValue1261, Sparse.eval] using hc.symm

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

theorem zero2053 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2053 node2053Labels = 0 := by
  exact mixedMoment_order_one B hB node2053 node2053Labels 1
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

theorem sound2051 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2051 node2051Labels = Sparse.eval nodeValue2051 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2051) = mixedMoment B node2051 node2051Labels := rfl
  simpa [nodeValue2051, Sparse.eval] using hc.symm

theorem sound2053 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2053 node2053Labels = Sparse.eval nodeValue2053 (mixedVector B) := by
  simpa only [nodeValue2053, Sparse.eval_nil] using zero2053 B _hB _hF

theorem sound2054 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2054 node2054Labels = Sparse.eval nodeValue2054 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2054) = mixedMoment B node2054 node2054Labels := rfl
  simpa [nodeValue2054, Sparse.eval] using hc.symm

theorem sound2058 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2058 node2058Labels = Sparse.eval nodeValue2058 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2058) = mixedMoment B node2058 node2058Labels := rfl
  simpa [nodeValue2058, Sparse.eval] using hc.symm

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

theorem zero2291 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2291 node2291Labels = 0 := by
  exact mixedMoment_order_one B hB node2291 node2291Labels 1
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

theorem sound2291 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2291 node2291Labels = Sparse.eval nodeValue2291 (mixedVector B) := by
  simpa only [nodeValue2291, Sparse.eval_nil] using zero2291 B _hB _hF

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

theorem sound2479 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2479 node2479Labels = Sparse.eval nodeValue2479 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2479) = mixedMoment B node2479 node2479Labels := rfl
  simpa [nodeValue2479, Sparse.eval] using hc.symm

theorem sound2482 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2482 node2482Labels = Sparse.eval nodeValue2482 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2482) = mixedMoment B node2482 node2482Labels := rfl
  simpa [nodeValue2482, Sparse.eval] using hc.symm

theorem sound2488 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2488 node2488Labels = Sparse.eval nodeValue2488 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2488) = mixedMoment B node2488 node2488Labels := rfl
  simpa [nodeValue2488, Sparse.eval] using hc.symm

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

theorem zero2511 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2511 node2511Labels = 0 := by
  exact mixedMoment_order_one B hB node2511 node2511Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero2542 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node2542 node2542Labels = 0 := by
  exact mixedMoment_alpha B hF node2542 node2542Labels 1 permutation158
    (by decide +kernel)

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

theorem sound2511 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2511 node2511Labels = Sparse.eval nodeValue2511 (mixedVector B) := by
  simpa only [nodeValue2511, Sparse.eval_nil] using zero2511 B _hB _hF

theorem sound2542 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2542 node2542Labels = Sparse.eval nodeValue2542 (mixedVector B) := by
  simpa only [nodeValue2542, Sparse.eval_nil] using zero2542 B _hB _hF

theorem sound2545 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2545 node2545Labels = Sparse.eval nodeValue2545 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2545) = mixedMoment B node2545 node2545Labels := rfl
  simpa [nodeValue2545, Sparse.eval] using hc.symm

theorem sound2546 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2546 node2546Labels = Sparse.eval nodeValue2546 (mixedVector B) := by
  simpa only [nodeValue2546, Sparse.eval_nil] using zero2546 B _hB _hF

theorem sound2553 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2553 node2553Labels = Sparse.eval nodeValue2553 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2553) = mixedMoment B node2553 node2553Labels := rfl
  simpa [nodeValue2553, Sparse.eval] using hc.symm

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

theorem sound2569 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2569 node2569Labels = Sparse.eval nodeValue2569 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2569) = mixedMoment B node2569 node2569Labels := rfl
  simpa [nodeValue2569, Sparse.eval] using hc.symm

theorem sound2614 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2614 node2614Labels = Sparse.eval nodeValue2614 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2614) = mixedMoment B node2614 node2614Labels := rfl
  simpa [nodeValue2614, Sparse.eval] using hc.symm

theorem sound2620 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2620 node2620Labels = Sparse.eval nodeValue2620 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2620) = mixedMoment B node2620 node2620Labels := rfl
  simpa [nodeValue2620, Sparse.eval] using hc.symm

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

theorem zero2720 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node2720 node2720Labels = 0 := by
  exact mixedMoment_alpha B hF node2720 node2720Labels 1 permutation203
    (by decide +kernel)

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

theorem sound2720 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2720 node2720Labels = Sparse.eval nodeValue2720 (mixedVector B) := by
  simpa only [nodeValue2720, Sparse.eval_nil] using zero2720 B _hB _hF

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

theorem sound2726 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2726 node2726Labels = Sparse.eval nodeValue2726 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2726) = mixedMoment B node2726 node2726Labels := rfl
  simpa [nodeValue2726, Sparse.eval] using hc.symm

theorem sound2739 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2739 node2739Labels = Sparse.eval nodeValue2739 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2739) = mixedMoment B node2739 node2739Labels := rfl
  simpa [nodeValue2739, Sparse.eval] using hc.symm

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

theorem sound3293 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3293 node3293Labels = Sparse.eval nodeValue3293 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3293) = mixedMoment B node3293 node3293Labels := rfl
  simpa [nodeValue3293, Sparse.eval] using hc.symm

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

theorem sound3459 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3459 node3459Labels = Sparse.eval nodeValue3459 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3459) = mixedMoment B node3459 node3459Labels := rfl
  simpa [nodeValue3459, Sparse.eval] using hc.symm

theorem sound3468 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3468 node3468Labels = Sparse.eval nodeValue3468 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3468) = mixedMoment B node3468 node3468Labels := rfl
  simpa [nodeValue3468, Sparse.eval] using hc.symm

theorem sound3478 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3478 node3478Labels = Sparse.eval nodeValue3478 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3478) = mixedMoment B node3478 node3478Labels := rfl
  simpa [nodeValue3478, Sparse.eval] using hc.symm

theorem sound3514 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3514 node3514Labels = Sparse.eval nodeValue3514 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3514) = mixedMoment B node3514 node3514Labels := rfl
  simpa [nodeValue3514, Sparse.eval] using hc.symm

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

theorem sound3533 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3533 node3533Labels = Sparse.eval nodeValue3533 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3533) = mixedMoment B node3533 node3533Labels := rfl
  simpa [nodeValue3533, Sparse.eval] using hc.symm

theorem sound3534 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3534 node3534Labels = Sparse.eval nodeValue3534 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3534) = mixedMoment B node3534 node3534Labels := rfl
  simpa [nodeValue3534, Sparse.eval] using hc.symm

theorem sound3544 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3544 node3544Labels = Sparse.eval nodeValue3544 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3544) = mixedMoment B node3544 node3544Labels := rfl
  simpa [nodeValue3544, Sparse.eval] using hc.symm

theorem sound3545 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3545 node3545Labels = Sparse.eval nodeValue3545 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3545) = mixedMoment B node3545 node3545Labels := rfl
  simpa [nodeValue3545, Sparse.eval] using hc.symm

theorem sound3582 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3582 node3582Labels = Sparse.eval nodeValue3582 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3582) = mixedMoment B node3582 node3582Labels := rfl
  simpa [nodeValue3582, Sparse.eval] using hc.symm

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

theorem zero3807 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3807 node3807Labels = 0 := by
  exact mixedMoment_order_one B hB node3807 node3807Labels 1
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

theorem sound3807 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3807 node3807Labels = Sparse.eval nodeValue3807 (mixedVector B) := by
  simpa only [nodeValue3807, Sparse.eval_nil] using zero3807 B _hB _hF

theorem sound3837 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3837 node3837Labels = Sparse.eval nodeValue3837 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3837) = mixedMoment B node3837 node3837Labels := rfl
  simpa [nodeValue3837, Sparse.eval] using hc.symm

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

theorem sound3850 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3850 node3850Labels = Sparse.eval nodeValue3850 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3850) = mixedMoment B node3850 node3850Labels := rfl
  simpa [nodeValue3850, Sparse.eval] using hc.symm

theorem sound3903 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3903 node3903Labels = Sparse.eval nodeValue3903 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3903) = mixedMoment B node3903 node3903Labels := rfl
  simpa [nodeValue3903, Sparse.eval] using hc.symm

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound71
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound4589 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4589 node4589Labels = Sparse.eval nodeValue4589 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4589) = mixedMoment B node4589 node4589Labels := rfl
  simpa [nodeValue4589, Sparse.eval] using hc.symm

theorem sound4591 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4591 node4591Labels = Sparse.eval nodeValue4591 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4591) = mixedMoment B node4591 node4591Labels := rfl
  simpa [nodeValue4591, Sparse.eval] using hc.symm

theorem sound4592 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4592 node4592Labels = Sparse.eval nodeValue4592 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4592) = mixedMoment B node4592 node4592Labels := rfl
  simpa [nodeValue4592, Sparse.eval] using hc.symm

theorem sound4602 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4602 node4602Labels = Sparse.eval nodeValue4602 (mixedVector B) := by
  have h := singleton4602 B _hB
  rw [sound1236 B _hB _hF, sound3293 B _hB _hF] at h
  norm_num [nodeValue4602, nodeValue1236, nodeValue3293, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4607 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4607 node4607Labels = Sparse.eval nodeValue4607 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4607) = mixedMoment B node4607 node4607Labels := rfl
  simpa [nodeValue4607, Sparse.eval] using hc.symm

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

theorem zero5101 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5101 node5101Labels = 0 := by
  exact mixedMoment_order_one B hB node5101 node5101Labels 1
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

theorem sound5072 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5072 node5072Labels = Sparse.eval nodeValue5072 (mixedVector B) := by
  have h := singleton5072 B _hB
  rw [sound2479 B _hB _hF, sound3459 B _hB _hF] at h
  norm_num [nodeValue5072, nodeValue2479, nodeValue3459, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5075 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5075 node5075Labels = Sparse.eval nodeValue5075 (mixedVector B) := by
  have h := singleton5075 B _hB
  rw [sound2482 B _hB _hF, sound3468 B _hB _hF] at h
  norm_num [nodeValue5075, nodeValue2482, nodeValue3468, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5080 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5080 node5080Labels = Sparse.eval nodeValue5080 (mixedVector B) := by
  have h := singleton5080 B _hB
  rw [sound2488 B _hB _hF, sound3478 B _hB _hF] at h
  norm_num [nodeValue5080, nodeValue2488, nodeValue3478, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5101 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5101 node5101Labels = Sparse.eval nodeValue5101 (mixedVector B) := by
  simpa only [nodeValue5101, Sparse.eval_nil] using zero5101 B _hB _hF

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

theorem sound5129 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5129 node5129Labels = Sparse.eval nodeValue5129 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5129) = mixedMoment B node5129 node5129Labels := rfl
  simpa [nodeValue5129, Sparse.eval] using hc.symm

theorem sound5134 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5134 node5134Labels = Sparse.eval nodeValue5134 (mixedVector B) := by
  have h := singleton5134 B _hB
  rw [sound2553 B _hB _hF, sound3514 B _hB _hF] at h
  norm_num [nodeValue5134, nodeValue2553, nodeValue3514, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5144 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5144 node5144Labels = Sparse.eval nodeValue5144 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5144) = mixedMoment B node5144 node5144Labels := rfl
  simpa [nodeValue5144, Sparse.eval] using hc.symm

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

theorem sound5184 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5184 node5184Labels = Sparse.eval nodeValue5184 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5184) = mixedMoment B node5184 node5184Labels := rfl
  simpa [nodeValue5184, Sparse.eval] using hc.symm

theorem sound5188 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5188 node5188Labels = Sparse.eval nodeValue5188 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5188) = mixedMoment B node5188 node5188Labels := rfl
  simpa [nodeValue5188, Sparse.eval] using hc.symm

theorem sound5198 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5198 node5198Labels = Sparse.eval nodeValue5198 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5198) = mixedMoment B node5198 node5198Labels := rfl
  simpa [nodeValue5198, Sparse.eval] using hc.symm

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

theorem zero5256 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node5256 node5256Labels = 0 := by
  exact mixedMoment_alpha B hF node5256 node5256Labels 1 permutation203
    (by decide +kernel)

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

theorem sound5256 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5256 node5256Labels = Sparse.eval nodeValue5256 (mixedVector B) := by
  simpa only [nodeValue5256, Sparse.eval_nil] using zero5256 B _hB _hF

theorem sound5258 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5258 node5258Labels = Sparse.eval nodeValue5258 (mixedVector B) := by
  have h := singleton5258 B _hB
  rw [sound2722 B _hB _hF, sound3533 B _hB _hF] at h
  norm_num [nodeValue5258, nodeValue2722, nodeValue3533, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5260 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5260 node5260Labels = Sparse.eval nodeValue5260 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5260) = mixedMoment B node5260 node5260Labels := rfl
  simpa [nodeValue5260, Sparse.eval] using hc.symm

theorem sound5261 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5261 node5261Labels = Sparse.eval nodeValue5261 (mixedVector B) := by
  have h := singleton5261 B _hB
  rw [sound2726 B _hB _hF, sound3545 B _hB _hF] at h
  norm_num [nodeValue5261, nodeValue2726, nodeValue3545, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5271 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5271 node5271Labels = Sparse.eval nodeValue5271 (mixedVector B) := by
  have h := singleton5271 B _hB
  rw [sound2739 B _hB _hF, sound3534 B _hB _hF] at h
  norm_num [nodeValue5271, nodeValue2739, nodeValue3534, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5274 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5274 node5274Labels = Sparse.eval nodeValue5274 (mixedVector B) := by
  simpa only [nodeValue5274, Sparse.eval_nil] using zero5274 B _hB _hF

theorem sound5289 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5289 node5289Labels = Sparse.eval nodeValue5289 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5289) = mixedMoment B node5289 node5289Labels := rfl
  simpa [nodeValue5289, Sparse.eval] using hc.symm

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros84
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero5409 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5409 node5409Labels = 0 := by
  exact mixedMoment_order_one B hB node5409 node5409Labels 1
    (by decide +kernel) (by decide +kernel)

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

theorem sound5409 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5409 node5409Labels = Sparse.eval nodeValue5409 (mixedVector B) := by
  simpa only [nodeValue5409, Sparse.eval_nil] using zero5409 B _hB _hF

theorem sound5423 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5423 node5423Labels = Sparse.eval nodeValue5423 (mixedVector B) := by
  have h := singleton5423 B _hB
  rw [sound3837 B _hB _hF] at h
  norm_num [nodeValue5423, nodeValue3837, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5432 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5432 node5432Labels = Sparse.eval nodeValue5432 (mixedVector B) := by
  have h := singleton5432 B _hB
  rw [sound3850 B _hB _hF] at h
  norm_num [nodeValue5432, nodeValue3850, Sparse.eval] at h ⊢
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources18
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sourceEq587 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm587 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA587 + difference 4 0) (sourceB587 + difference 0 4) sourceC587) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1220) := by
    have ha : (tripleCharges (sourceA587 + difference 4 0) (sourceB587 + difference 0 4) sourceC587) = raw9830 := by
      apply Matrix.ext; unfold tripleCharges sourceA587 sourceB587 sourceC587 difference raw9830; decide +kernel
    rw [ha]
    exact (canonical9830 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA587 + difference 4 1) (sourceB587 + difference 1 4) sourceC587) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2621) := by
    have ha : (tripleCharges (sourceA587 + difference 4 1) (sourceB587 + difference 1 4) sourceC587) = raw9838 := by
      apply Matrix.ext; unfold tripleCharges sourceA587 sourceB587 sourceC587 difference raw9838; decide +kernel
    rw [ha]
    exact (canonical9838 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA587 + difference 4 2) (sourceB587 + difference 2 4) sourceC587) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2546) := by
    have ha : (tripleCharges (sourceA587 + difference 4 2) (sourceB587 + difference 2 4) sourceC587) = raw9841 := by
      apply Matrix.ext; unfold tripleCharges sourceA587 sourceB587 sourceC587 difference raw9841; decide +kernel
    rw [ha]
    exact (canonical9841 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA587 + difference 4 3) (sourceB587 + difference 3 4) sourceC587) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2489) := by
    have ha : (tripleCharges (sourceA587 + difference 4 3) (sourceB587 + difference 3 4) sourceC587) = raw9844 := by
      apply Matrix.ext; unfold tripleCharges sourceA587 sourceB587 sourceC587 difference raw9844; decide +kernel
    rw [ha]
    exact (canonical9844 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA587 + difference 4 4) (sourceB587 + difference 4 4) sourceC587) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2723) := by
    have ha : (tripleCharges (sourceA587 + difference 4 4) (sourceB587 + difference 4 4) sourceC587) = raw9820 := by
      apply Matrix.ext; unfold tripleCharges sourceA587 sourceB587 sourceC587 difference raw9820; decide +kernel
    rw [ha]
    exact (canonical9820 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA587 + difference 4 5) (sourceB587 + difference 5 4) sourceC587) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2723) := by
    have ha : (tripleCharges (sourceA587 + difference 4 5) (sourceB587 + difference 5 4) sourceC587) = raw9846 := by
      apply Matrix.ext; unfold tripleCharges sourceA587 sourceB587 sourceC587 difference raw9846; decide +kernel
    rw [ha]
    exact (canonical9846 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA587 + sourceB587) sourceC587) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA587 + sourceB587) sourceC587) = raw9826 := by
      apply Matrix.ext; unfold doubleCharges sourceA587 sourceB587 sourceC587 raw9826; decide +kernel
    rw [ha]
    exact (canonical9826 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA587 sourceB587 sourceC587
    (0 : Fin 2) 1 (4 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm587, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq593 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm593 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA593 + difference 0 0) (sourceB593 + difference 0 0) sourceC593) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3544) := by
    have ha : (tripleCharges (sourceA593 + difference 0 0) (sourceB593 + difference 0 0) sourceC593) = raw9963 := by
      apply Matrix.ext; unfold tripleCharges sourceA593 sourceB593 sourceC593 difference raw9963; decide +kernel
    rw [ha]
    exact (canonical9963 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA593 + difference 1 0) (sourceB593 + difference 0 1) sourceC593) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2058) := by
    have ha : (tripleCharges (sourceA593 + difference 1 0) (sourceB593 + difference 0 1) sourceC593) = raw9964 := by
      apply Matrix.ext; unfold tripleCharges sourceA593 sourceB593 sourceC593 difference raw9964; decide +kernel
    rw [ha]
    exact (canonical9964 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA593 + difference 2 0) (sourceB593 + difference 0 2) sourceC593) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2051) := by
    have ha : (tripleCharges (sourceA593 + difference 2 0) (sourceB593 + difference 0 2) sourceC593) = raw9965 := by
      apply Matrix.ext; unfold tripleCharges sourceA593 sourceB593 sourceC593 difference raw9965; decide +kernel
    rw [ha]
    exact (canonical9965 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA593 + difference 3 0) (sourceB593 + difference 0 3) sourceC593) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2291) := by
    have ha : (tripleCharges (sourceA593 + difference 3 0) (sourceB593 + difference 0 3) sourceC593) = raw9966 := by
      apply Matrix.ext; unfold tripleCharges sourceA593 sourceB593 sourceC593 difference raw9966; decide +kernel
    rw [ha]
    exact (canonical9966 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA593 + difference 4 0) (sourceB593 + difference 0 4) sourceC593) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2054) := by
    have ha : (tripleCharges (sourceA593 + difference 4 0) (sourceB593 + difference 0 4) sourceC593) = raw9967 := by
      apply Matrix.ext; unfold tripleCharges sourceA593 sourceB593 sourceC593 difference raw9967; decide +kernel
    rw [ha]
    exact (canonical9967 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA593 + difference 5 0) (sourceB593 + difference 0 5) sourceC593) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2053) := by
    have ha : (tripleCharges (sourceA593 + difference 5 0) (sourceB593 + difference 0 5) sourceC593) = raw9968 := by
      apply Matrix.ext; unfold tripleCharges sourceA593 sourceB593 sourceC593 difference raw9968; decide +kernel
    rw [ha]
    exact (canonical9968 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA593 + sourceB593) sourceC593) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA593 + sourceB593) sourceC593) = raw5754 := by
      apply Matrix.ext; unfold doubleCharges sourceA593 sourceB593 sourceC593 raw5754; decide +kernel
    rw [ha]
    exact (canonical5754 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA593 sourceB593 sourceC593
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm593, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq594 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm594 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA594 + difference 0 1) (sourceB594 + difference 1 0) sourceC594) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5432) := by
    have ha : (tripleCharges (sourceA594 + difference 0 1) (sourceB594 + difference 1 0) sourceC594) = raw9969 := by
      apply Matrix.ext; unfold tripleCharges sourceA594 sourceB594 sourceC594 difference raw9969; decide +kernel
    rw [ha]
    exact (canonical9969 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA594 + difference 0 2) (sourceB594 + difference 2 0) sourceC594) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5423) := by
    have ha : (tripleCharges (sourceA594 + difference 0 2) (sourceB594 + difference 2 0) sourceC594) = raw9970 := by
      apply Matrix.ext; unfold tripleCharges sourceA594 sourceB594 sourceC594 difference raw9970; decide +kernel
    rw [ha]
    exact (canonical9970 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA594 + difference 0 3) (sourceB594 + difference 3 0) sourceC594) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5409) := by
    have ha : (tripleCharges (sourceA594 + difference 0 3) (sourceB594 + difference 3 0) sourceC594) = raw9971 := by
      apply Matrix.ext; unfold tripleCharges sourceA594 sourceB594 sourceC594 difference raw9971; decide +kernel
    rw [ha]
    exact (canonical9971 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA594 + difference 0 4) (sourceB594 + difference 4 0) sourceC594) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5441) := by
    have ha : (tripleCharges (sourceA594 + difference 0 4) (sourceB594 + difference 4 0) sourceC594) = raw9972 := by
      apply Matrix.ext; unfold tripleCharges sourceA594 sourceB594 sourceC594 difference raw9972; decide +kernel
    rw [ha]
    exact (canonical9972 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA594 + difference 0 5) (sourceB594 + difference 5 0) sourceC594) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5434) := by
    have ha : (tripleCharges (sourceA594 + difference 0 5) (sourceB594 + difference 5 0) sourceC594) = raw9973 := by
      apply Matrix.ext; unfold tripleCharges sourceA594 sourceB594 sourceC594 difference raw9973; decide +kernel
    rw [ha]
    exact (canonical9973 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA594 + difference 1 0) (sourceB594 + difference 0 1) sourceC594) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4602) := by
    have ha : (tripleCharges (sourceA594 + difference 1 0) (sourceB594 + difference 0 1) sourceC594) = raw9974 := by
      apply Matrix.ext; unfold tripleCharges sourceA594 sourceB594 sourceC594 difference raw9974; decide +kernel
    rw [ha]
    exact (canonical9974 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA594 + difference 1 2) (sourceB594 + difference 2 1) sourceC594) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5134) := by
    have ha : (tripleCharges (sourceA594 + difference 1 2) (sourceB594 + difference 2 1) sourceC594) = raw9975 := by
      apply Matrix.ext; unfold tripleCharges sourceA594 sourceB594 sourceC594 difference raw9975; decide +kernel
    rw [ha]
    exact (canonical9975 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA594 + difference 1 3) (sourceB594 + difference 3 1) sourceC594) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5101) := by
    have ha : (tripleCharges (sourceA594 + difference 1 3) (sourceB594 + difference 3 1) sourceC594) = raw9976 := by
      apply Matrix.ext; unfold tripleCharges sourceA594 sourceB594 sourceC594 difference raw9976; decide +kernel
    rw [ha]
    exact (canonical9976 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA594 + difference 1 4) (sourceB594 + difference 4 1) sourceC594) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5274) := by
    have ha : (tripleCharges (sourceA594 + difference 1 4) (sourceB594 + difference 4 1) sourceC594) = raw9977 := by
      apply Matrix.ext; unfold tripleCharges sourceA594 sourceB594 sourceC594 difference raw9977; decide +kernel
    rw [ha]
    exact (canonical9977 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA594 + difference 1 5) (sourceB594 + difference 5 1) sourceC594) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5271) := by
    have ha : (tripleCharges (sourceA594 + difference 1 5) (sourceB594 + difference 5 1) sourceC594) = raw9978 := by
      apply Matrix.ext; unfold tripleCharges sourceA594 sourceB594 sourceC594 difference raw9978; decide +kernel
    rw [ha]
    exact (canonical9978 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA594 + difference 2 0) (sourceB594 + difference 0 2) sourceC594) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4589) := by
    have ha : (tripleCharges (sourceA594 + difference 2 0) (sourceB594 + difference 0 2) sourceC594) = raw9979 := by
      apply Matrix.ext; unfold tripleCharges sourceA594 sourceB594 sourceC594 difference raw9979; decide +kernel
    rw [ha]
    exact (canonical9979 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA594 + difference 2 1) (sourceB594 + difference 1 2) sourceC594) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5184) := by
    have ha : (tripleCharges (sourceA594 + difference 2 1) (sourceB594 + difference 1 2) sourceC594) = raw9980 := by
      apply Matrix.ext; unfold tripleCharges sourceA594 sourceB594 sourceC594 difference raw9980; decide +kernel
    rw [ha]
    exact (canonical9980 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA594 + difference 2 3) (sourceB594 + difference 3 2) sourceC594) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5072) := by
    have ha : (tripleCharges (sourceA594 + difference 2 3) (sourceB594 + difference 3 2) sourceC594) = raw9981 := by
      apply Matrix.ext; unfold tripleCharges sourceA594 sourceB594 sourceC594 difference raw9981; decide +kernel
    rw [ha]
    exact (canonical9981 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA594 + difference 2 4) (sourceB594 + difference 4 2) sourceC594) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5258) := by
    have ha : (tripleCharges (sourceA594 + difference 2 4) (sourceB594 + difference 4 2) sourceC594) = raw9982 := by
      apply Matrix.ext; unfold tripleCharges sourceA594 sourceB594 sourceC594 difference raw9982; decide +kernel
    rw [ha]
    exact (canonical9982 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA594 + difference 2 5) (sourceB594 + difference 5 2) sourceC594) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5256) := by
    have ha : (tripleCharges (sourceA594 + difference 2 5) (sourceB594 + difference 5 2) sourceC594) = raw9983 := by
      apply Matrix.ext; unfold tripleCharges sourceA594 sourceB594 sourceC594 difference raw9983; decide +kernel
    rw [ha]
    exact (canonical9983 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA594 + difference 3 0) (sourceB594 + difference 0 3) sourceC594) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4607) := by
    have ha : (tripleCharges (sourceA594 + difference 3 0) (sourceB594 + difference 0 3) sourceC594) = raw9984 := by
      apply Matrix.ext; unfold tripleCharges sourceA594 sourceB594 sourceC594 difference raw9984; decide +kernel
    rw [ha]
    exact (canonical9984 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA594 + difference 3 1) (sourceB594 + difference 1 3) sourceC594) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5198) := by
    have ha : (tripleCharges (sourceA594 + difference 3 1) (sourceB594 + difference 1 3) sourceC594) = raw9985 := by
      apply Matrix.ext; unfold tripleCharges sourceA594 sourceB594 sourceC594 difference raw9985; decide +kernel
    rw [ha]
    exact (canonical9985 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA594 + difference 3 2) (sourceB594 + difference 2 3) sourceC594) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5144) := by
    have ha : (tripleCharges (sourceA594 + difference 3 2) (sourceB594 + difference 2 3) sourceC594) = raw9986 := by
      apply Matrix.ext; unfold tripleCharges sourceA594 sourceB594 sourceC594 difference raw9986; decide +kernel
    rw [ha]
    exact (canonical9986 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA594 + difference 3 4) (sourceB594 + difference 4 3) sourceC594) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5291) := by
    have ha : (tripleCharges (sourceA594 + difference 3 4) (sourceB594 + difference 4 3) sourceC594) = raw9987 := by
      apply Matrix.ext; unfold tripleCharges sourceA594 sourceB594 sourceC594 difference raw9987; decide +kernel
    rw [ha]
    exact (canonical9987 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA594 + difference 3 5) (sourceB594 + difference 5 3) sourceC594) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5289) := by
    have ha : (tripleCharges (sourceA594 + difference 3 5) (sourceB594 + difference 5 3) sourceC594) = raw9988 := by
      apply Matrix.ext; unfold tripleCharges sourceA594 sourceB594 sourceC594 difference raw9988; decide +kernel
    rw [ha]
    exact (canonical9988 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA594 + difference 4 0) (sourceB594 + difference 0 4) sourceC594) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4592) := by
    have ha : (tripleCharges (sourceA594 + difference 4 0) (sourceB594 + difference 0 4) sourceC594) = raw9989 := by
      apply Matrix.ext; unfold tripleCharges sourceA594 sourceB594 sourceC594 difference raw9989; decide +kernel
    rw [ha]
    exact (canonical9989 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA594 + difference 4 1) (sourceB594 + difference 1 4) sourceC594) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5188) := by
    have ha : (tripleCharges (sourceA594 + difference 4 1) (sourceB594 + difference 1 4) sourceC594) = raw9990 := by
      apply Matrix.ext; unfold tripleCharges sourceA594 sourceB594 sourceC594 difference raw9990; decide +kernel
    rw [ha]
    exact (canonical9990 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA594 + difference 4 2) (sourceB594 + difference 2 4) sourceC594) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5129) := by
    have ha : (tripleCharges (sourceA594 + difference 4 2) (sourceB594 + difference 2 4) sourceC594) = raw9991 := by
      apply Matrix.ext; unfold tripleCharges sourceA594 sourceB594 sourceC594 difference raw9991; decide +kernel
    rw [ha]
    exact (canonical9991 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA594 + difference 4 3) (sourceB594 + difference 3 4) sourceC594) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5080) := by
    have ha : (tripleCharges (sourceA594 + difference 4 3) (sourceB594 + difference 3 4) sourceC594) = raw9992 := by
      apply Matrix.ext; unfold tripleCharges sourceA594 sourceB594 sourceC594 difference raw9992; decide +kernel
    rw [ha]
    exact (canonical9992 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA594 + difference 4 5) (sourceB594 + difference 5 4) sourceC594) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5260) := by
    have ha : (tripleCharges (sourceA594 + difference 4 5) (sourceB594 + difference 5 4) sourceC594) = raw9993 := by
      apply Matrix.ext; unfold tripleCharges sourceA594 sourceB594 sourceC594 difference raw9993; decide +kernel
    rw [ha]
    exact (canonical9993 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA594 + difference 5 0) (sourceB594 + difference 0 5) sourceC594) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4591) := by
    have ha : (tripleCharges (sourceA594 + difference 5 0) (sourceB594 + difference 0 5) sourceC594) = raw9994 := by
      apply Matrix.ext; unfold tripleCharges sourceA594 sourceB594 sourceC594 difference raw9994; decide +kernel
    rw [ha]
    exact (canonical9994 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA594 + difference 5 1) (sourceB594 + difference 1 5) sourceC594) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5147) := by
    have ha : (tripleCharges (sourceA594 + difference 5 1) (sourceB594 + difference 1 5) sourceC594) = raw9995 := by
      apply Matrix.ext; unfold tripleCharges sourceA594 sourceB594 sourceC594 difference raw9995; decide +kernel
    rw [ha]
    exact (canonical9995 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA594 + difference 5 2) (sourceB594 + difference 2 5) sourceC594) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5127) := by
    have ha : (tripleCharges (sourceA594 + difference 5 2) (sourceB594 + difference 2 5) sourceC594) = raw9996 := by
      apply Matrix.ext; unfold tripleCharges sourceA594 sourceB594 sourceC594 difference raw9996; decide +kernel
    rw [ha]
    exact (canonical9996 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA594 + difference 5 3) (sourceB594 + difference 3 5) sourceC594) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5075) := by
    have ha : (tripleCharges (sourceA594 + difference 5 3) (sourceB594 + difference 3 5) sourceC594) = raw9997 := by
      apply Matrix.ext; unfold tripleCharges sourceA594 sourceB594 sourceC594 difference raw9997; decide +kernel
    rw [ha]
    exact (canonical9997 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA594 + difference 5 4) (sourceB594 + difference 4 5) sourceC594) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5261) := by
    have ha : (tripleCharges (sourceA594 + difference 5 4) (sourceB594 + difference 4 5) sourceC594) = raw9998 := by
      apply Matrix.ext; unfold tripleCharges sourceA594 sourceB594 sourceC594 difference raw9998; decide +kernel
    rw [ha]
    exact (canonical9998 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA594 sourceB594 sourceC594
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm594, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq597 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm597 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA597 + difference 0 0) (sourceB597 + difference 0 0) sourceC597) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2722) := by
    have ha : (tripleCharges (sourceA597 + difference 0 0) (sourceB597 + difference 0 0) sourceC597) = raw10059 := by
      apply Matrix.ext; unfold tripleCharges sourceA597 sourceB597 sourceC597 difference raw10059; decide +kernel
    rw [ha]
    exact (canonical10059 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA597 + difference 0 1) (sourceB597 + difference 1 0) sourceC597) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3850) := by
    have ha : (tripleCharges (sourceA597 + difference 0 1) (sourceB597 + difference 1 0) sourceC597) = raw10060 := by
      apply Matrix.ext; unfold tripleCharges sourceA597 sourceB597 sourceC597 difference raw10060; decide +kernel
    rw [ha]
    exact (canonical10060 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA597 + difference 0 2) (sourceB597 + difference 2 0) sourceC597) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3837) := by
    have ha : (tripleCharges (sourceA597 + difference 0 2) (sourceB597 + difference 2 0) sourceC597) = raw10061 := by
      apply Matrix.ext; unfold tripleCharges sourceA597 sourceB597 sourceC597 difference raw10061; decide +kernel
    rw [ha]
    exact (canonical10061 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA597 + difference 0 3) (sourceB597 + difference 3 0) sourceC597) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3807) := by
    have ha : (tripleCharges (sourceA597 + difference 0 3) (sourceB597 + difference 3 0) sourceC597) = raw10062 := by
      apply Matrix.ext; unfold tripleCharges sourceA597 sourceB597 sourceC597 difference raw10062; decide +kernel
    rw [ha]
    exact (canonical10062 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA597 + difference 0 4) (sourceB597 + difference 4 0) sourceC597) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3905) := by
    have ha : (tripleCharges (sourceA597 + difference 0 4) (sourceB597 + difference 4 0) sourceC597) = raw10063 := by
      apply Matrix.ext; unfold tripleCharges sourceA597 sourceB597 sourceC597 difference raw10063; decide +kernel
    rw [ha]
    exact (canonical10063 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA597 + difference 0 5) (sourceB597 + difference 5 0) sourceC597) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3903) := by
    have ha : (tripleCharges (sourceA597 + difference 0 5) (sourceB597 + difference 5 0) sourceC597) = raw10064 := by
      apply Matrix.ext; unfold tripleCharges sourceA597 sourceB597 sourceC597 difference raw10064; decide +kernel
    rw [ha]
    exact (canonical10064 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA597 + sourceB597) sourceC597) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA597 + sourceB597) sourceC597) = raw10065 := by
      apply Matrix.ext; unfold doubleCharges sourceA597 sourceB597 sourceC597 raw10065; decide +kernel
    rw [ha]
    exact (canonical10065 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA597 sourceB597 sourceC597
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm597, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq598 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm598 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA598 + difference 0 0) (sourceB598 + difference 0 0) sourceC598) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2722) := by
    have ha : (tripleCharges (sourceA598 + difference 0 0) (sourceB598 + difference 0 0) sourceC598) = raw10059 := by
      apply Matrix.ext; unfold tripleCharges sourceA598 sourceB598 sourceC598 difference raw10059; decide +kernel
    rw [ha]
    exact (canonical10059 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA598 + difference 1 0) (sourceB598 + difference 0 1) sourceC598) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1236) := by
    have ha : (tripleCharges (sourceA598 + difference 1 0) (sourceB598 + difference 0 1) sourceC598) = raw10066 := by
      apply Matrix.ext; unfold tripleCharges sourceA598 sourceB598 sourceC598 difference raw10066; decide +kernel
    rw [ha]
    exact (canonical10066 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA598 + difference 2 0) (sourceB598 + difference 0 2) sourceC598) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1212) := by
    have ha : (tripleCharges (sourceA598 + difference 2 0) (sourceB598 + difference 0 2) sourceC598) = raw10067 := by
      apply Matrix.ext; unfold tripleCharges sourceA598 sourceB598 sourceC598 difference raw10067; decide +kernel
    rw [ha]
    exact (canonical10067 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA598 + difference 3 0) (sourceB598 + difference 0 3) sourceC598) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1261) := by
    have ha : (tripleCharges (sourceA598 + difference 3 0) (sourceB598 + difference 0 3) sourceC598) = raw10068 := by
      apply Matrix.ext; unfold tripleCharges sourceA598 sourceB598 sourceC598 difference raw10068; decide +kernel
    rw [ha]
    exact (canonical10068 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA598 + difference 4 0) (sourceB598 + difference 0 4) sourceC598) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1219) := by
    have ha : (tripleCharges (sourceA598 + difference 4 0) (sourceB598 + difference 0 4) sourceC598) = raw10069 := by
      apply Matrix.ext; unfold tripleCharges sourceA598 sourceB598 sourceC598 difference raw10069; decide +kernel
    rw [ha]
    exact (canonical10069 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA598 + difference 5 0) (sourceB598 + difference 0 5) sourceC598) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1215) := by
    have ha : (tripleCharges (sourceA598 + difference 5 0) (sourceB598 + difference 0 5) sourceC598) = raw10070 := by
      apply Matrix.ext; unfold tripleCharges sourceA598 sourceB598 sourceC598 difference raw10070; decide +kernel
    rw [ha]
    exact (canonical10070 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA598 + sourceB598) sourceC598) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA598 + sourceB598) sourceC598) = raw10065 := by
      apply Matrix.ext; unfold doubleCharges sourceA598 sourceB598 sourceC598 raw10065; decide +kernel
    rw [ha]
    exact (canonical10065 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA598 sourceB598 sourceC598
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm598, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq599 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm599 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA599 + difference 1 0) (sourceB599 + difference 0 1) sourceC599) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1236) := by
    have ha : (tripleCharges (sourceA599 + difference 1 0) (sourceB599 + difference 0 1) sourceC599) = raw10066 := by
      apply Matrix.ext; unfold tripleCharges sourceA599 sourceB599 sourceC599 difference raw10066; decide +kernel
    rw [ha]
    exact (canonical10066 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA599 + difference 1 1) (sourceB599 + difference 1 1) sourceC599) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2722) := by
    have ha : (tripleCharges (sourceA599 + difference 1 1) (sourceB599 + difference 1 1) sourceC599) = raw10059 := by
      apply Matrix.ext; unfold tripleCharges sourceA599 sourceB599 sourceC599 difference raw10059; decide +kernel
    rw [ha]
    exact (canonical10059 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA599 + difference 1 2) (sourceB599 + difference 2 1) sourceC599) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2553) := by
    have ha : (tripleCharges (sourceA599 + difference 1 2) (sourceB599 + difference 2 1) sourceC599) = raw10071 := by
      apply Matrix.ext; unfold tripleCharges sourceA599 sourceB599 sourceC599 difference raw10071; decide +kernel
    rw [ha]
    exact (canonical10071 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA599 + difference 1 3) (sourceB599 + difference 3 1) sourceC599) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2511) := by
    have ha : (tripleCharges (sourceA599 + difference 1 3) (sourceB599 + difference 3 1) sourceC599) = raw10072 := by
      apply Matrix.ext; unfold tripleCharges sourceA599 sourceB599 sourceC599 difference raw10072; decide +kernel
    rw [ha]
    exact (canonical10072 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA599 + difference 1 4) (sourceB599 + difference 4 1) sourceC599) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2742) := by
    have ha : (tripleCharges (sourceA599 + difference 1 4) (sourceB599 + difference 4 1) sourceC599) = raw10073 := by
      apply Matrix.ext; unfold tripleCharges sourceA599 sourceB599 sourceC599 difference raw10073; decide +kernel
    rw [ha]
    exact (canonical10073 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA599 + difference 1 5) (sourceB599 + difference 5 1) sourceC599) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2739) := by
    have ha : (tripleCharges (sourceA599 + difference 1 5) (sourceB599 + difference 5 1) sourceC599) = raw10074 := by
      apply Matrix.ext; unfold tripleCharges sourceA599 sourceB599 sourceC599 difference raw10074; decide +kernel
    rw [ha]
    exact (canonical10074 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA599 + sourceB599) sourceC599) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA599 + sourceB599) sourceC599) = raw10065 := by
      apply Matrix.ext; unfold doubleCharges sourceA599 sourceB599 sourceC599 raw10065; decide +kernel
    rw [ha]
    exact (canonical10065 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA599 sourceB599 sourceC599
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm599, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq600 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm600 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA600 + difference 0 1) (sourceB600 + difference 1 0) sourceC600) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3850) := by
    have ha : (tripleCharges (sourceA600 + difference 0 1) (sourceB600 + difference 1 0) sourceC600) = raw10060 := by
      apply Matrix.ext; unfold tripleCharges sourceA600 sourceB600 sourceC600 difference raw10060; decide +kernel
    rw [ha]
    exact (canonical10060 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA600 + difference 1 1) (sourceB600 + difference 1 1) sourceC600) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2722) := by
    have ha : (tripleCharges (sourceA600 + difference 1 1) (sourceB600 + difference 1 1) sourceC600) = raw10059 := by
      apply Matrix.ext; unfold tripleCharges sourceA600 sourceB600 sourceC600 difference raw10059; decide +kernel
    rw [ha]
    exact (canonical10059 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA600 + difference 2 1) (sourceB600 + difference 1 2) sourceC600) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2614) := by
    have ha : (tripleCharges (sourceA600 + difference 2 1) (sourceB600 + difference 1 2) sourceC600) = raw10075 := by
      apply Matrix.ext; unfold tripleCharges sourceA600 sourceB600 sourceC600 difference raw10075; decide +kernel
    rw [ha]
    exact (canonical10075 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA600 + difference 3 1) (sourceB600 + difference 1 3) sourceC600) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2632) := by
    have ha : (tripleCharges (sourceA600 + difference 3 1) (sourceB600 + difference 1 3) sourceC600) = raw10076 := by
      apply Matrix.ext; unfold tripleCharges sourceA600 sourceB600 sourceC600 difference raw10076; decide +kernel
    rw [ha]
    exact (canonical10076 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA600 + difference 4 1) (sourceB600 + difference 1 4) sourceC600) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2620) := by
    have ha : (tripleCharges (sourceA600 + difference 4 1) (sourceB600 + difference 1 4) sourceC600) = raw10077 := by
      apply Matrix.ext; unfold tripleCharges sourceA600 sourceB600 sourceC600 difference raw10077; decide +kernel
    rw [ha]
    exact (canonical10077 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA600 + difference 5 1) (sourceB600 + difference 1 5) sourceC600) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2569) := by
    have ha : (tripleCharges (sourceA600 + difference 5 1) (sourceB600 + difference 1 5) sourceC600) = raw10078 := by
      apply Matrix.ext; unfold tripleCharges sourceA600 sourceB600 sourceC600 difference raw10078; decide +kernel
    rw [ha]
    exact (canonical10078 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA600 + sourceB600) sourceC600) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA600 + sourceB600) sourceC600) = raw10065 := by
      apply Matrix.ext; unfold doubleCharges sourceA600 sourceB600 sourceC600 raw10065; decide +kernel
    rw [ha]
    exact (canonical10065 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA600 sourceB600 sourceC600
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm600, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq601 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm601 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA601 + difference 2 0) (sourceB601 + difference 0 2) sourceC601) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1212) := by
    have ha : (tripleCharges (sourceA601 + difference 2 0) (sourceB601 + difference 0 2) sourceC601) = raw10067 := by
      apply Matrix.ext; unfold tripleCharges sourceA601 sourceB601 sourceC601 difference raw10067; decide +kernel
    rw [ha]
    exact (canonical10067 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA601 + difference 2 1) (sourceB601 + difference 1 2) sourceC601) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2614) := by
    have ha : (tripleCharges (sourceA601 + difference 2 1) (sourceB601 + difference 1 2) sourceC601) = raw10075 := by
      apply Matrix.ext; unfold tripleCharges sourceA601 sourceB601 sourceC601 difference raw10075; decide +kernel
    rw [ha]
    exact (canonical10075 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA601 + difference 2 2) (sourceB601 + difference 2 2) sourceC601) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2722) := by
    have ha : (tripleCharges (sourceA601 + difference 2 2) (sourceB601 + difference 2 2) sourceC601) = raw10059 := by
      apply Matrix.ext; unfold tripleCharges sourceA601 sourceB601 sourceC601 difference raw10059; decide +kernel
    rw [ha]
    exact (canonical10059 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA601 + difference 2 3) (sourceB601 + difference 3 2) sourceC601) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2479) := by
    have ha : (tripleCharges (sourceA601 + difference 2 3) (sourceB601 + difference 3 2) sourceC601) = raw10079 := by
      apply Matrix.ext; unfold tripleCharges sourceA601 sourceB601 sourceC601 difference raw10079; decide +kernel
    rw [ha]
    exact (canonical10079 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA601 + difference 2 4) (sourceB601 + difference 4 2) sourceC601) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2722) := by
    have ha : (tripleCharges (sourceA601 + difference 2 4) (sourceB601 + difference 4 2) sourceC601) = raw10080 := by
      apply Matrix.ext; unfold tripleCharges sourceA601 sourceB601 sourceC601 difference raw10080; decide +kernel
    rw [ha]
    exact (canonical10080 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA601 + difference 2 5) (sourceB601 + difference 5 2) sourceC601) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2720) := by
    have ha : (tripleCharges (sourceA601 + difference 2 5) (sourceB601 + difference 5 2) sourceC601) = raw10081 := by
      apply Matrix.ext; unfold tripleCharges sourceA601 sourceB601 sourceC601 difference raw10081; decide +kernel
    rw [ha]
    exact (canonical10081 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA601 + sourceB601) sourceC601) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA601 + sourceB601) sourceC601) = raw10065 := by
      apply Matrix.ext; unfold doubleCharges sourceA601 sourceB601 sourceC601 raw10065; decide +kernel
    rw [ha]
    exact (canonical10065 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA601 sourceB601 sourceC601
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm601, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq602 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm602 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA602 + difference 0 2) (sourceB602 + difference 2 0) sourceC602) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3837) := by
    have ha : (tripleCharges (sourceA602 + difference 0 2) (sourceB602 + difference 2 0) sourceC602) = raw10061 := by
      apply Matrix.ext; unfold tripleCharges sourceA602 sourceB602 sourceC602 difference raw10061; decide +kernel
    rw [ha]
    exact (canonical10061 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA602 + difference 1 2) (sourceB602 + difference 2 1) sourceC602) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2553) := by
    have ha : (tripleCharges (sourceA602 + difference 1 2) (sourceB602 + difference 2 1) sourceC602) = raw10071 := by
      apply Matrix.ext; unfold tripleCharges sourceA602 sourceB602 sourceC602 difference raw10071; decide +kernel
    rw [ha]
    exact (canonical10071 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA602 + difference 2 2) (sourceB602 + difference 2 2) sourceC602) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2722) := by
    have ha : (tripleCharges (sourceA602 + difference 2 2) (sourceB602 + difference 2 2) sourceC602) = raw10059 := by
      apply Matrix.ext; unfold tripleCharges sourceA602 sourceB602 sourceC602 difference raw10059; decide +kernel
    rw [ha]
    exact (canonical10059 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA602 + difference 3 2) (sourceB602 + difference 2 3) sourceC602) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2566) := by
    have ha : (tripleCharges (sourceA602 + difference 3 2) (sourceB602 + difference 2 3) sourceC602) = raw10082 := by
      apply Matrix.ext; unfold tripleCharges sourceA602 sourceB602 sourceC602 difference raw10082; decide +kernel
    rw [ha]
    exact (canonical10082 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA602 + difference 4 2) (sourceB602 + difference 2 4) sourceC602) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2545) := by
    have ha : (tripleCharges (sourceA602 + difference 4 2) (sourceB602 + difference 2 4) sourceC602) = raw10083 := by
      apply Matrix.ext; unfold tripleCharges sourceA602 sourceB602 sourceC602 difference raw10083; decide +kernel
    rw [ha]
    exact (canonical10083 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA602 + difference 5 2) (sourceB602 + difference 2 5) sourceC602) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2542) := by
    have ha : (tripleCharges (sourceA602 + difference 5 2) (sourceB602 + difference 2 5) sourceC602) = raw10084 := by
      apply Matrix.ext; unfold tripleCharges sourceA602 sourceB602 sourceC602 difference raw10084; decide +kernel
    rw [ha]
    exact (canonical10084 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA602 + sourceB602) sourceC602) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA602 + sourceB602) sourceC602) = raw10065 := by
      apply Matrix.ext; unfold doubleCharges sourceA602 sourceB602 sourceC602 raw10065; decide +kernel
    rw [ha]
    exact (canonical10065 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA602 sourceB602 sourceC602
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm602, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic31
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reindexCheck496 : Integer.Sparse.reindex keyMap MixedData.row496 = numericRow496 := by decide +kernel

theorem numericCheck496 (x : Master → ℝ) : Integer.Sparse.eval numericRow496 x =
    (1 : ℝ) * reducedSource496 x := by
  norm_num [numericRow496, reducedSource496, Integer.Sparse.eval, Sparse.eval, nodeValue1220, nodeValue2489, nodeValue2546, nodeValue2621, nodeValue2723, nodeValue4091]

theorem reindexCheck502 : Integer.Sparse.reindex keyMap MixedData.row502 = numericRow502 := by decide +kernel

theorem numericCheck502 (x : Master → ℝ) : Integer.Sparse.eval numericRow502 x =
    (1 : ℝ) * reducedSource502 x := by
  norm_num [numericRow502, reducedSource502, Integer.Sparse.eval, Sparse.eval, nodeValue2051, nodeValue2053, nodeValue2054, nodeValue2058, nodeValue2291, nodeValue3544, nodeValue4084]

theorem reindexCheck503 : Integer.Sparse.reindex keyMap MixedData.row503 = numericRow503 := by decide +kernel

theorem numericCheck503 (x : Master → ℝ) : Integer.Sparse.eval numericRow503 x =
    (17280 : ℝ) * reducedSource503 x := by
  norm_num [numericRow503, reducedSource503, Integer.Sparse.eval, Sparse.eval, nodeValue4589, nodeValue4591, nodeValue4592, nodeValue4602, nodeValue4607, nodeValue5072, nodeValue5075, nodeValue5080, nodeValue5101, nodeValue5127, nodeValue5129, nodeValue5134, nodeValue5144, nodeValue5147, nodeValue5184, nodeValue5188, nodeValue5198, nodeValue5256, nodeValue5258, nodeValue5260, nodeValue5261, nodeValue5271, nodeValue5274, nodeValue5289, nodeValue5291, nodeValue5409, nodeValue5423, nodeValue5432, nodeValue5434, nodeValue5441]
  ring

theorem reindexCheck506 : Integer.Sparse.reindex keyMap MixedData.row506 = numericRow506 := by decide +kernel

theorem numericCheck506 (x : Master → ℝ) : Integer.Sparse.eval numericRow506 x =
    (1 : ℝ) * reducedSource506 x := by
  norm_num [numericRow506, reducedSource506, Integer.Sparse.eval, Sparse.eval, nodeValue2722, nodeValue3807, nodeValue3837, nodeValue3850, nodeValue3903, nodeValue3905, nodeValue4092]

theorem reindexCheck507 : Integer.Sparse.reindex keyMap MixedData.row507 = numericRow507 := by decide +kernel

theorem numericCheck507 (x : Master → ℝ) : Integer.Sparse.eval numericRow507 x =
    (1 : ℝ) * reducedSource507 x := by
  norm_num [numericRow507, reducedSource507, Integer.Sparse.eval, Sparse.eval, nodeValue1212, nodeValue1215, nodeValue1219, nodeValue1236, nodeValue1261, nodeValue2722, nodeValue4092]

theorem reindexCheck508 : Integer.Sparse.reindex keyMap MixedData.row508 = numericRow508 := by decide +kernel

theorem numericCheck508 (x : Master → ℝ) : Integer.Sparse.eval numericRow508 x =
    (1 : ℝ) * reducedSource508 x := by
  norm_num [numericRow508, reducedSource508, Integer.Sparse.eval, Sparse.eval, nodeValue1236, nodeValue2511, nodeValue2553, nodeValue2722, nodeValue2739, nodeValue2742, nodeValue4092]

theorem reindexCheck509 : Integer.Sparse.reindex keyMap MixedData.row509 = numericRow509 := by decide +kernel

theorem numericCheck509 (x : Master → ℝ) : Integer.Sparse.eval numericRow509 x =
    (1 : ℝ) * reducedSource509 x := by
  norm_num [numericRow509, reducedSource509, Integer.Sparse.eval, Sparse.eval, nodeValue2569, nodeValue2614, nodeValue2620, nodeValue2632, nodeValue2722, nodeValue3850, nodeValue4092]

theorem reindexCheck510 : Integer.Sparse.reindex keyMap MixedData.row510 = numericRow510 := by decide +kernel

theorem numericCheck510 (x : Master → ℝ) : Integer.Sparse.eval numericRow510 x =
    (1 : ℝ) * reducedSource510 x := by
  norm_num [numericRow510, reducedSource510, Integer.Sparse.eval, Sparse.eval, nodeValue1212, nodeValue2479, nodeValue2614, nodeValue2720, nodeValue2722, nodeValue4092]

theorem reindexCheck511 : Integer.Sparse.reindex keyMap MixedData.row511 = numericRow511 := by decide +kernel

theorem numericCheck511 (x : Master → ℝ) : Integer.Sparse.eval numericRow511 x =
    (1 : ℝ) * reducedSource511 x := by
  norm_num [numericRow511, reducedSource511, Integer.Sparse.eval, Sparse.eval, nodeValue2542, nodeValue2545, nodeValue2553, nodeValue2566, nodeValue2722, nodeValue3837, nodeValue4092]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Rows31
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero496 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource496 (mixedVector B) = 0 := by
  have h1220 : mixedVector B (Sum.inr 1220) = Sparse.eval nodeValue1220 (mixedVector B) := by
    change mixedMoment B node1220 node1220Labels = _
    exact sound1220 B hB hF
  have h2489 : mixedVector B (Sum.inr 2489) = Sparse.eval nodeValue2489 (mixedVector B) := by
    change mixedMoment B node2489 node2489Labels = _
    exact sound2489 B hB hF
  have h2546 : mixedVector B (Sum.inr 2546) = Sparse.eval nodeValue2546 (mixedVector B) := by
    change mixedMoment B node2546 node2546Labels = _
    exact sound2546 B hB hF
  have h2621 : mixedVector B (Sum.inr 2621) = Sparse.eval nodeValue2621 (mixedVector B) := by
    change mixedMoment B node2621 node2621Labels = _
    exact sound2621 B hB hF
  have h2723 : mixedVector B (Sum.inr 2723) = Sparse.eval nodeValue2723 (mixedVector B) := by
    change mixedMoment B node2723 node2723Labels = _
    exact sound2723 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm587, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1220, h2489, h2546, h2621, h2723, h4091, reducedSource496] using sourceEq587 B hB

theorem rowSound496 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row496 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck496, numericCheck496, reducedZero496 B hB hF, mul_zero]

theorem reducedZero502 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource502 (mixedVector B) = 0 := by
  have h2051 : mixedVector B (Sum.inr 2051) = Sparse.eval nodeValue2051 (mixedVector B) := by
    change mixedMoment B node2051 node2051Labels = _
    exact sound2051 B hB hF
  have h2053 : mixedVector B (Sum.inr 2053) = Sparse.eval nodeValue2053 (mixedVector B) := by
    change mixedMoment B node2053 node2053Labels = _
    exact sound2053 B hB hF
  have h2054 : mixedVector B (Sum.inr 2054) = Sparse.eval nodeValue2054 (mixedVector B) := by
    change mixedMoment B node2054 node2054Labels = _
    exact sound2054 B hB hF
  have h2058 : mixedVector B (Sum.inr 2058) = Sparse.eval nodeValue2058 (mixedVector B) := by
    change mixedMoment B node2058 node2058Labels = _
    exact sound2058 B hB hF
  have h2291 : mixedVector B (Sum.inr 2291) = Sparse.eval nodeValue2291 (mixedVector B) := by
    change mixedMoment B node2291 node2291Labels = _
    exact sound2291 B hB hF
  have h3544 : mixedVector B (Sum.inr 3544) = Sparse.eval nodeValue3544 (mixedVector B) := by
    change mixedMoment B node3544 node3544Labels = _
    exact sound3544 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm593, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2051, h2053, h2054, h2058, h2291, h3544, h4084, reducedSource502] using sourceEq593 B hB

theorem rowSound502 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row502 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck502, numericCheck502, reducedZero502 B hB hF, mul_zero]

theorem reducedZero503 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource503 (mixedVector B) = 0 := by
  have h4589 : mixedVector B (Sum.inr 4589) = Sparse.eval nodeValue4589 (mixedVector B) := by
    change mixedMoment B node4589 node4589Labels = _
    exact sound4589 B hB hF
  have h4591 : mixedVector B (Sum.inr 4591) = Sparse.eval nodeValue4591 (mixedVector B) := by
    change mixedMoment B node4591 node4591Labels = _
    exact sound4591 B hB hF
  have h4592 : mixedVector B (Sum.inr 4592) = Sparse.eval nodeValue4592 (mixedVector B) := by
    change mixedMoment B node4592 node4592Labels = _
    exact sound4592 B hB hF
  have h4602 : mixedVector B (Sum.inr 4602) = Sparse.eval nodeValue4602 (mixedVector B) := by
    change mixedMoment B node4602 node4602Labels = _
    exact sound4602 B hB hF
  have h4607 : mixedVector B (Sum.inr 4607) = Sparse.eval nodeValue4607 (mixedVector B) := by
    change mixedMoment B node4607 node4607Labels = _
    exact sound4607 B hB hF
  have h5072 : mixedVector B (Sum.inr 5072) = Sparse.eval nodeValue5072 (mixedVector B) := by
    change mixedMoment B node5072 node5072Labels = _
    exact sound5072 B hB hF
  have h5075 : mixedVector B (Sum.inr 5075) = Sparse.eval nodeValue5075 (mixedVector B) := by
    change mixedMoment B node5075 node5075Labels = _
    exact sound5075 B hB hF
  have h5080 : mixedVector B (Sum.inr 5080) = Sparse.eval nodeValue5080 (mixedVector B) := by
    change mixedMoment B node5080 node5080Labels = _
    exact sound5080 B hB hF
  have h5101 : mixedVector B (Sum.inr 5101) = Sparse.eval nodeValue5101 (mixedVector B) := by
    change mixedMoment B node5101 node5101Labels = _
    exact sound5101 B hB hF
  have h5127 : mixedVector B (Sum.inr 5127) = Sparse.eval nodeValue5127 (mixedVector B) := by
    change mixedMoment B node5127 node5127Labels = _
    exact sound5127 B hB hF
  have h5129 : mixedVector B (Sum.inr 5129) = Sparse.eval nodeValue5129 (mixedVector B) := by
    change mixedMoment B node5129 node5129Labels = _
    exact sound5129 B hB hF
  have h5134 : mixedVector B (Sum.inr 5134) = Sparse.eval nodeValue5134 (mixedVector B) := by
    change mixedMoment B node5134 node5134Labels = _
    exact sound5134 B hB hF
  have h5144 : mixedVector B (Sum.inr 5144) = Sparse.eval nodeValue5144 (mixedVector B) := by
    change mixedMoment B node5144 node5144Labels = _
    exact sound5144 B hB hF
  have h5147 : mixedVector B (Sum.inr 5147) = Sparse.eval nodeValue5147 (mixedVector B) := by
    change mixedMoment B node5147 node5147Labels = _
    exact sound5147 B hB hF
  have h5184 : mixedVector B (Sum.inr 5184) = Sparse.eval nodeValue5184 (mixedVector B) := by
    change mixedMoment B node5184 node5184Labels = _
    exact sound5184 B hB hF
  have h5188 : mixedVector B (Sum.inr 5188) = Sparse.eval nodeValue5188 (mixedVector B) := by
    change mixedMoment B node5188 node5188Labels = _
    exact sound5188 B hB hF
  have h5198 : mixedVector B (Sum.inr 5198) = Sparse.eval nodeValue5198 (mixedVector B) := by
    change mixedMoment B node5198 node5198Labels = _
    exact sound5198 B hB hF
  have h5256 : mixedVector B (Sum.inr 5256) = Sparse.eval nodeValue5256 (mixedVector B) := by
    change mixedMoment B node5256 node5256Labels = _
    exact sound5256 B hB hF
  have h5258 : mixedVector B (Sum.inr 5258) = Sparse.eval nodeValue5258 (mixedVector B) := by
    change mixedMoment B node5258 node5258Labels = _
    exact sound5258 B hB hF
  have h5260 : mixedVector B (Sum.inr 5260) = Sparse.eval nodeValue5260 (mixedVector B) := by
    change mixedMoment B node5260 node5260Labels = _
    exact sound5260 B hB hF
  have h5261 : mixedVector B (Sum.inr 5261) = Sparse.eval nodeValue5261 (mixedVector B) := by
    change mixedMoment B node5261 node5261Labels = _
    exact sound5261 B hB hF
  have h5271 : mixedVector B (Sum.inr 5271) = Sparse.eval nodeValue5271 (mixedVector B) := by
    change mixedMoment B node5271 node5271Labels = _
    exact sound5271 B hB hF
  have h5274 : mixedVector B (Sum.inr 5274) = Sparse.eval nodeValue5274 (mixedVector B) := by
    change mixedMoment B node5274 node5274Labels = _
    exact sound5274 B hB hF
  have h5289 : mixedVector B (Sum.inr 5289) = Sparse.eval nodeValue5289 (mixedVector B) := by
    change mixedMoment B node5289 node5289Labels = _
    exact sound5289 B hB hF
  have h5291 : mixedVector B (Sum.inr 5291) = Sparse.eval nodeValue5291 (mixedVector B) := by
    change mixedMoment B node5291 node5291Labels = _
    exact sound5291 B hB hF
  have h5409 : mixedVector B (Sum.inr 5409) = Sparse.eval nodeValue5409 (mixedVector B) := by
    change mixedMoment B node5409 node5409Labels = _
    exact sound5409 B hB hF
  have h5423 : mixedVector B (Sum.inr 5423) = Sparse.eval nodeValue5423 (mixedVector B) := by
    change mixedMoment B node5423 node5423Labels = _
    exact sound5423 B hB hF
  have h5432 : mixedVector B (Sum.inr 5432) = Sparse.eval nodeValue5432 (mixedVector B) := by
    change mixedMoment B node5432 node5432Labels = _
    exact sound5432 B hB hF
  have h5434 : mixedVector B (Sum.inr 5434) = Sparse.eval nodeValue5434 (mixedVector B) := by
    change mixedMoment B node5434 node5434Labels = _
    exact sound5434_e B hB hF
  have h5441 : mixedVector B (Sum.inr 5441) = Sparse.eval nodeValue5441 (mixedVector B) := by
    change mixedMoment B node5441 node5441Labels = _
    exact sound5441 B hB hF
  simpa only [sourceForm594, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4589, h4591, h4592, h4602, h4607, h5072, h5075, h5080, h5101, h5127, h5129, h5134, h5144, h5147, h5184, h5188, h5198, h5256, h5258, h5260, h5261, h5271, h5274, h5289, h5291, h5409, h5423, h5432, h5434, h5441, reducedSource503] using sourceEq594 B hB

theorem rowSound503 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row503 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck503, numericCheck503, reducedZero503 B hB hF, mul_zero]

theorem reducedZero506 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource506 (mixedVector B) = 0 := by
  have h2722 : mixedVector B (Sum.inr 2722) = Sparse.eval nodeValue2722 (mixedVector B) := by
    change mixedMoment B node2722 node2722Labels = _
    exact sound2722 B hB hF
  have h3807 : mixedVector B (Sum.inr 3807) = Sparse.eval nodeValue3807 (mixedVector B) := by
    change mixedMoment B node3807 node3807Labels = _
    exact sound3807 B hB hF
  have h3837 : mixedVector B (Sum.inr 3837) = Sparse.eval nodeValue3837 (mixedVector B) := by
    change mixedMoment B node3837 node3837Labels = _
    exact sound3837 B hB hF
  have h3850 : mixedVector B (Sum.inr 3850) = Sparse.eval nodeValue3850 (mixedVector B) := by
    change mixedMoment B node3850 node3850Labels = _
    exact sound3850 B hB hF
  have h3903 : mixedVector B (Sum.inr 3903) = Sparse.eval nodeValue3903 (mixedVector B) := by
    change mixedMoment B node3903 node3903Labels = _
    exact sound3903 B hB hF
  have h3905 : mixedVector B (Sum.inr 3905) = Sparse.eval nodeValue3905 (mixedVector B) := by
    change mixedMoment B node3905 node3905Labels = _
    exact sound3905 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm597, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2722, h3807, h3837, h3850, h3903, h3905, h4092, reducedSource506] using sourceEq597 B hB

theorem rowSound506 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row506 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck506, numericCheck506, reducedZero506 B hB hF, mul_zero]

theorem reducedZero507 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource507 (mixedVector B) = 0 := by
  have h1212 : mixedVector B (Sum.inr 1212) = Sparse.eval nodeValue1212 (mixedVector B) := by
    change mixedMoment B node1212 node1212Labels = _
    exact sound1212 B hB hF
  have h1215 : mixedVector B (Sum.inr 1215) = Sparse.eval nodeValue1215 (mixedVector B) := by
    change mixedMoment B node1215 node1215Labels = _
    exact sound1215 B hB hF
  have h1219 : mixedVector B (Sum.inr 1219) = Sparse.eval nodeValue1219 (mixedVector B) := by
    change mixedMoment B node1219 node1219Labels = _
    exact sound1219 B hB hF
  have h1236 : mixedVector B (Sum.inr 1236) = Sparse.eval nodeValue1236 (mixedVector B) := by
    change mixedMoment B node1236 node1236Labels = _
    exact sound1236 B hB hF
  have h1261 : mixedVector B (Sum.inr 1261) = Sparse.eval nodeValue1261 (mixedVector B) := by
    change mixedMoment B node1261 node1261Labels = _
    exact sound1261 B hB hF
  have h2722 : mixedVector B (Sum.inr 2722) = Sparse.eval nodeValue2722 (mixedVector B) := by
    change mixedMoment B node2722 node2722Labels = _
    exact sound2722 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm598, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1212, h1215, h1219, h1236, h1261, h2722, h4092, reducedSource507] using sourceEq598 B hB

theorem rowSound507 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row507 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck507, numericCheck507, reducedZero507 B hB hF, mul_zero]

theorem reducedZero508 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource508 (mixedVector B) = 0 := by
  have h1236 : mixedVector B (Sum.inr 1236) = Sparse.eval nodeValue1236 (mixedVector B) := by
    change mixedMoment B node1236 node1236Labels = _
    exact sound1236 B hB hF
  have h2511 : mixedVector B (Sum.inr 2511) = Sparse.eval nodeValue2511 (mixedVector B) := by
    change mixedMoment B node2511 node2511Labels = _
    exact sound2511 B hB hF
  have h2553 : mixedVector B (Sum.inr 2553) = Sparse.eval nodeValue2553 (mixedVector B) := by
    change mixedMoment B node2553 node2553Labels = _
    exact sound2553 B hB hF
  have h2722 : mixedVector B (Sum.inr 2722) = Sparse.eval nodeValue2722 (mixedVector B) := by
    change mixedMoment B node2722 node2722Labels = _
    exact sound2722 B hB hF
  have h2739 : mixedVector B (Sum.inr 2739) = Sparse.eval nodeValue2739 (mixedVector B) := by
    change mixedMoment B node2739 node2739Labels = _
    exact sound2739 B hB hF
  have h2742 : mixedVector B (Sum.inr 2742) = Sparse.eval nodeValue2742 (mixedVector B) := by
    change mixedMoment B node2742 node2742Labels = _
    exact sound2742 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm599, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1236, h2511, h2553, h2722, h2739, h2742, h4092, reducedSource508] using sourceEq599 B hB

theorem rowSound508 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row508 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck508, numericCheck508, reducedZero508 B hB hF, mul_zero]

theorem reducedZero509 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource509 (mixedVector B) = 0 := by
  have h2569 : mixedVector B (Sum.inr 2569) = Sparse.eval nodeValue2569 (mixedVector B) := by
    change mixedMoment B node2569 node2569Labels = _
    exact sound2569 B hB hF
  have h2614 : mixedVector B (Sum.inr 2614) = Sparse.eval nodeValue2614 (mixedVector B) := by
    change mixedMoment B node2614 node2614Labels = _
    exact sound2614 B hB hF
  have h2620 : mixedVector B (Sum.inr 2620) = Sparse.eval nodeValue2620 (mixedVector B) := by
    change mixedMoment B node2620 node2620Labels = _
    exact sound2620 B hB hF
  have h2632 : mixedVector B (Sum.inr 2632) = Sparse.eval nodeValue2632 (mixedVector B) := by
    change mixedMoment B node2632 node2632Labels = _
    exact sound2632 B hB hF
  have h2722 : mixedVector B (Sum.inr 2722) = Sparse.eval nodeValue2722 (mixedVector B) := by
    change mixedMoment B node2722 node2722Labels = _
    exact sound2722 B hB hF
  have h3850 : mixedVector B (Sum.inr 3850) = Sparse.eval nodeValue3850 (mixedVector B) := by
    change mixedMoment B node3850 node3850Labels = _
    exact sound3850 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm600, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2569, h2614, h2620, h2632, h2722, h3850, h4092, reducedSource509] using sourceEq600 B hB

theorem rowSound509 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row509 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck509, numericCheck509, reducedZero509 B hB hF, mul_zero]

theorem reducedZero510 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource510 (mixedVector B) = 0 := by
  have h1212 : mixedVector B (Sum.inr 1212) = Sparse.eval nodeValue1212 (mixedVector B) := by
    change mixedMoment B node1212 node1212Labels = _
    exact sound1212 B hB hF
  have h2479 : mixedVector B (Sum.inr 2479) = Sparse.eval nodeValue2479 (mixedVector B) := by
    change mixedMoment B node2479 node2479Labels = _
    exact sound2479 B hB hF
  have h2614 : mixedVector B (Sum.inr 2614) = Sparse.eval nodeValue2614 (mixedVector B) := by
    change mixedMoment B node2614 node2614Labels = _
    exact sound2614 B hB hF
  have h2720 : mixedVector B (Sum.inr 2720) = Sparse.eval nodeValue2720 (mixedVector B) := by
    change mixedMoment B node2720 node2720Labels = _
    exact sound2720 B hB hF
  have h2722 : mixedVector B (Sum.inr 2722) = Sparse.eval nodeValue2722 (mixedVector B) := by
    change mixedMoment B node2722 node2722Labels = _
    exact sound2722 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm601, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1212, h2479, h2614, h2720, h2722, h4092, reducedSource510] using sourceEq601 B hB

theorem rowSound510 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row510 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck510, numericCheck510, reducedZero510 B hB hF, mul_zero]

theorem reducedZero511 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource511 (mixedVector B) = 0 := by
  have h2542 : mixedVector B (Sum.inr 2542) = Sparse.eval nodeValue2542 (mixedVector B) := by
    change mixedMoment B node2542 node2542Labels = _
    exact sound2542 B hB hF
  have h2545 : mixedVector B (Sum.inr 2545) = Sparse.eval nodeValue2545 (mixedVector B) := by
    change mixedMoment B node2545 node2545Labels = _
    exact sound2545 B hB hF
  have h2553 : mixedVector B (Sum.inr 2553) = Sparse.eval nodeValue2553 (mixedVector B) := by
    change mixedMoment B node2553 node2553Labels = _
    exact sound2553 B hB hF
  have h2566 : mixedVector B (Sum.inr 2566) = Sparse.eval nodeValue2566 (mixedVector B) := by
    change mixedMoment B node2566 node2566Labels = _
    exact sound2566 B hB hF
  have h2722 : mixedVector B (Sum.inr 2722) = Sparse.eval nodeValue2722 (mixedVector B) := by
    change mixedMoment B node2722 node2722Labels = _
    exact sound2722 B hB hF
  have h3837 : mixedVector B (Sum.inr 3837) = Sparse.eval nodeValue3837 (mixedVector B) := by
    change mixedMoment B node3837 node3837Labels = _
    exact sound3837 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm602, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2542, h2545, h2553, h2566, h2722, h3837, h4092, reducedSource511] using sourceEq602 B hB

theorem rowSound511 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row511 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck511, numericCheck511, reducedZero511 B hB hF, mul_zero]

theorem sourceRowsAt496 : MixedData.sourceRows (496 : Fin 2425) =
    MixedData.row496 := by decide +kernel

theorem sourceRowsAt497 : MixedData.sourceRows (497 : Fin 2425) =
    MixedData.row497 := by decide +kernel

theorem sourceRowsAt498 : MixedData.sourceRows (498 : Fin 2425) =
    MixedData.row498 := by decide +kernel

theorem sourceRowsAt499 : MixedData.sourceRows (499 : Fin 2425) =
    MixedData.row499 := by decide +kernel

theorem sourceRowsAt500 : MixedData.sourceRows (500 : Fin 2425) =
    MixedData.row500 := by decide +kernel

theorem sourceRowsAt501 : MixedData.sourceRows (501 : Fin 2425) =
    MixedData.row501 := by decide +kernel

theorem sourceRowsAt502 : MixedData.sourceRows (502 : Fin 2425) =
    MixedData.row502 := by decide +kernel

theorem sourceRowsAt503 : MixedData.sourceRows (503 : Fin 2425) =
    MixedData.row503 := by decide +kernel

theorem sourceRowsAt504 : MixedData.sourceRows (504 : Fin 2425) =
    MixedData.row504 := by decide +kernel

theorem sourceRowsAt505 : MixedData.sourceRows (505 : Fin 2425) =
    MixedData.row505 := by decide +kernel

theorem sourceRowsAt506 : MixedData.sourceRows (506 : Fin 2425) =
    MixedData.row506 := by decide +kernel

theorem sourceRowsAt507 : MixedData.sourceRows (507 : Fin 2425) =
    MixedData.row507 := by decide +kernel

theorem sourceRowsAt508 : MixedData.sourceRows (508 : Fin 2425) =
    MixedData.row508 := by decide +kernel

theorem sourceRowsAt509 : MixedData.sourceRows (509 : Fin 2425) =
    MixedData.row509 := by decide +kernel

theorem sourceRowsAt510 : MixedData.sourceRows (510 : Fin 2425) =
    MixedData.row510 := by decide +kernel

theorem sourceRowsAt511 : MixedData.sourceRows (511 : Fin 2425) =
    MixedData.row511 := by decide +kernel

theorem chunkSound31_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) (k : Fin 2425)
    (hk : k.val / 16 = 31) :
    Integer.Sparse.eval (MixedData.sourceRows k) (numericVector B) = 0 := by
  have heq : k.val = 496 ∨ k.val = 497 ∨ k.val = 498 ∨ k.val = 499 ∨ k.val = 500 ∨ k.val = 501 ∨ k.val = 502 ∨ k.val = 503 ∨ k.val = 504 ∨ k.val = 505 ∨ k.val = 506 ∨ k.val = 507 ∨ k.val = 508 ∨ k.val = 509 ∨ k.val = 510 ∨ k.val = 511 := by omega
  rcases heq with h496 | h497 | h498 | h499 | h500 | h501 | h502 | h503 | h504 | h505 | h506 | h507 | h508 | h509 | h510 | h511
  · have he : k = (496 : Fin 2425) := Fin.ext h496
    subst k
    rw [sourceRowsAt496]
    exact rowSound496 B hB hF
  · have he : k = (497 : Fin 2425) := Fin.ext h497
    subst k
    rw [sourceRowsAt497]
    exact rowSound497_e B hB hF
  · have he : k = (498 : Fin 2425) := Fin.ext h498
    subst k
    rw [sourceRowsAt498]
    exact rowSound498_e B hB hF
  · have he : k = (499 : Fin 2425) := Fin.ext h499
    subst k
    rw [sourceRowsAt499]
    exact rowSound499_e B hB hF
  · have he : k = (500 : Fin 2425) := Fin.ext h500
    subst k
    rw [sourceRowsAt500]
    exact rowSound500_e B hB hF
  · have he : k = (501 : Fin 2425) := Fin.ext h501
    subst k
    rw [sourceRowsAt501]
    exact rowSound501_e B hB hF
  · have he : k = (502 : Fin 2425) := Fin.ext h502
    subst k
    rw [sourceRowsAt502]
    exact rowSound502 B hB hF
  · have he : k = (503 : Fin 2425) := Fin.ext h503
    subst k
    rw [sourceRowsAt503]
    exact rowSound503 B hB hF
  · have he : k = (504 : Fin 2425) := Fin.ext h504
    subst k
    rw [sourceRowsAt504]
    exact rowSound504_e B hB hF
  · have he : k = (505 : Fin 2425) := Fin.ext h505
    subst k
    rw [sourceRowsAt505]
    exact rowSound505_e B hB hF
  · have he : k = (506 : Fin 2425) := Fin.ext h506
    subst k
    rw [sourceRowsAt506]
    exact rowSound506 B hB hF
  · have he : k = (507 : Fin 2425) := Fin.ext h507
    subst k
    rw [sourceRowsAt507]
    exact rowSound507 B hB hF
  · have he : k = (508 : Fin 2425) := Fin.ext h508
    subst k
    rw [sourceRowsAt508]
    exact rowSound508 B hB hF
  · have he : k = (509 : Fin 2425) := Fin.ext h509
    subst k
    rw [sourceRowsAt509]
    exact rowSound509 B hB hF
  · have he : k = (510 : Fin 2425) := Fin.ext h510
    subst k
    rw [sourceRowsAt510]
    exact rowSound510 B hB hF
  · have he : k = (511 : Fin 2425) := Fin.ext h511
    subst k
    rw [sourceRowsAt511]
    exact rowSound511 B hB hF

end MUB6.Certificate.MixedSourceBridge

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedSourceBridge.chunkSound31_e_oai := @OAI.MUB6.Certificate.MixedSourceBridge.chunkSound31_e_oai
