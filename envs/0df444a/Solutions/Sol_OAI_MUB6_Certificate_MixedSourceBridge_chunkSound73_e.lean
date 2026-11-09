-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedSourceBridge.chunkSound73_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T04:33:44.281933+00:00
-- url     : https://prove2.me/submissions/530749b7-aad0-4781-bfd6-0febdd3ad88a

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E077
import Definitions.Def_OAIQ106E086
import Definitions.Def_OAIQ106E088
import Definitions.Def_OAIQ106E089
import Definitions.Def_OAIQ106E093
import Definitions.Def_OAIQ106E095
import Definitions.Def_OAIQ106E096
import Definitions.Def_OAIQ106E187
import Definitions.Def_OAIQ106E188
import Definitions.Def_OAIQ106E117
import Definitions.Def_OAIQ106E119
import Definitions.Def_OAIQ106E120
import Definitions.Def_OAIQ106E124
import Definitions.Def_OAIQ106E140
import Definitions.Def_OAIQ106E147
import Definitions.Def_OAIQ106E170
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound1170_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound1177_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound1178_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound1179_e

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical13
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

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

theorem canonical1797 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1797 raw1797Labels = mixedMoment B node4868 node4868Labels := by
  calc
    mixedMoment B raw1797 raw1797Labels = mixedMoment B raw1797step0 raw1797step0Labels := by
      have ha : raw1797step0 = (fun i j => raw1797 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1797step0 raw1797; decide +kernel
      have hl : raw1797step0Labels = raw1797Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1797 raw1797Labels permutation8 permutation4
    mixedMoment B raw1797step0 raw1797step0Labels = mixedMoment B raw1797step1 raw1797step1Labels := by
      have ha : raw1797step1 = raw1797step0 := by apply Matrix.ext; unfold raw1797step1 raw1797step0; decide +kernel
      have hl : raw1797step0Labels = labelEmbedding7 ∘ raw1797step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1797step0 raw1797step0Labels raw1797step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4868 node4868Labels := by rfl

theorem canonical1798 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1798 raw1798Labels = mixedMoment B node2109 node2109Labels := by
  calc
    mixedMoment B raw1798 raw1798Labels = mixedMoment B raw1798step0 raw1798step0Labels := by
      have ha : raw1798step0 = (fun i j => raw1798 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1798step0 raw1798; decide +kernel
      have hl : raw1798step0Labels = raw1798Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1798 raw1798Labels permutation8 permutation4
    _ = mixedMoment B node2109 node2109Labels := by rfl

theorem canonical1799 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1799 raw1799Labels = mixedMoment B node2261 node2261Labels := by
  calc
    mixedMoment B raw1799 raw1799Labels = mixedMoment B raw1799step0 raw1799step0Labels := by
      have ha : raw1799step0 = (fun i j => raw1799 (permutation10 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1799step0 raw1799; decide +kernel
      have hl : raw1799step0Labels = raw1799Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1799 raw1799Labels permutation10 permutation6
    mixedMoment B raw1799step0 raw1799step0Labels = mixedMoment B raw1799step1 raw1799step1Labels := by
      have ha : raw1799step1 = -raw1799step0 := by apply Matrix.ext; change ∀ i j, raw1799step1 i j = -(raw1799step0 i j); unfold raw1799step1 raw1799step0; decide +kernel
      have hl : raw1799step1Labels = raw1799step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1799step1 raw1799step1Labels = mixedMoment B raw1799step2 raw1799step2Labels := by
      have ha : raw1799step2 = raw1799step1 := by apply Matrix.ext; unfold raw1799step2 raw1799step1; decide +kernel
      have hl : raw1799step1Labels = labelEmbedding1 ∘ raw1799step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1799step1 raw1799step1Labels raw1799step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2261 node2261Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical155
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical19875 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19875 raw19875Labels = mixedMoment B node2208 node2208Labels := by
  calc
    mixedMoment B raw19875 raw19875Labels = mixedMoment B raw19875step0 raw19875step0Labels := by
      have hz : ∀ j, raw19875 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19875step0 = (fun i j => raw19875 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19875step0 raw19875; decide +kernel
      have hl : raw19875step0Labels = raw19875Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19875 raw19875Labels permutation434 hz
    mixedMoment B raw19875step0 raw19875step0Labels = mixedMoment B raw19875step1 raw19875step1Labels := by
      have hz : ∀ j, raw19875step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19875step1 = (fun i j => raw19875step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19875step1 raw19875step0; decide +kernel
      have hl : raw19875step1Labels = raw19875step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19875step0 raw19875step0Labels permutation80 hz
    mixedMoment B raw19875step1 raw19875step1Labels = mixedMoment B raw19875step2 raw19875step2Labels := by
      have ha : raw19875step2 = (fun i j => raw19875step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19875step2 raw19875step1; decide +kernel
      have hl : raw19875step2Labels = raw19875step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19875step1 raw19875step1Labels permutation10 permutation2
    _ = mixedMoment B node2208 node2208Labels := by rfl

theorem canonical19876 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19876 raw19876Labels = mixedMoment B node4081 node4081Labels := by
  calc
    mixedMoment B raw19876 raw19876Labels = mixedMoment B raw19876step0 raw19876step0Labels := by
      have hz : ∀ j, raw19876 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19876step0 = (fun i j => raw19876 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19876step0 raw19876; decide +kernel
      have hl : raw19876step0Labels = raw19876Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19876 raw19876Labels permutation434 hz
    mixedMoment B raw19876step0 raw19876step0Labels = mixedMoment B raw19876step1 raw19876step1Labels := by
      have hz : ∀ j, raw19876step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19876step1 = (fun i j => raw19876step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19876step1 raw19876step0; decide +kernel
      have hl : raw19876step1Labels = raw19876step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19876step0 raw19876step0Labels permutation80 hz
    mixedMoment B raw19876step1 raw19876step1Labels = mixedMoment B raw19876step2 raw19876step2Labels := by
      have ha : raw19876step2 = (fun i j => raw19876step1 (permutation10 i) (permutation0 j)) := by apply Matrix.ext; unfold raw19876step2 raw19876step1; decide +kernel
      have hl : raw19876step2Labels = raw19876step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19876step1 raw19876step1Labels permutation10 permutation0
    _ = mixedMoment B node4081 node4081Labels := by rfl

theorem canonical19881 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19881 raw19881Labels = mixedMoment B node1007 node1007Labels := by
  calc
    mixedMoment B raw19881 raw19881Labels = mixedMoment B raw19881step0 raw19881step0Labels := by
      have hz : ∀ j, raw19881 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19881step0 = (fun i j => raw19881 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19881step0 raw19881; decide +kernel
      have hl : raw19881step0Labels = raw19881Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19881 raw19881Labels permutation434 hz
    mixedMoment B raw19881step0 raw19881step0Labels = mixedMoment B raw19881step1 raw19881step1Labels := by
      have hz : ∀ j, raw19881step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19881step1 = (fun i j => raw19881step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19881step1 raw19881step0; decide +kernel
      have hl : raw19881step1Labels = raw19881step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19881step0 raw19881step0Labels permutation80 hz
    mixedMoment B raw19881step1 raw19881step1Labels = mixedMoment B raw19881step2 raw19881step2Labels := by
      have ha : raw19881step2 = (fun i j => raw19881step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19881step2 raw19881step1; decide +kernel
      have hl : raw19881step2Labels = raw19881step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19881step1 raw19881step1Labels permutation10 permutation2
    _ = mixedMoment B node1007 node1007Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical157
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical20099 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20099 raw20099Labels = mixedMoment B node4070 node4070Labels := by
  calc
    mixedMoment B raw20099 raw20099Labels = mixedMoment B raw20099step0 raw20099step0Labels := by
      have hz : ∀ j, raw20099 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20099step0 = (fun i j => raw20099 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20099step0 raw20099; decide +kernel
      have hl : raw20099step0Labels = raw20099Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20099 raw20099Labels permutation434 hz
    mixedMoment B raw20099step0 raw20099step0Labels = mixedMoment B raw20099step1 raw20099step1Labels := by
      have hz : ∀ j, raw20099step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20099step1 = (fun i j => raw20099step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20099step1 raw20099step0; decide +kernel
      have hl : raw20099step1Labels = raw20099step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20099step0 raw20099step0Labels permutation80 hz
    mixedMoment B raw20099step1 raw20099step1Labels = mixedMoment B raw20099step2 raw20099step2Labels := by
      have hz : ∀ j, raw20099step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw20099step2 = (fun i j => raw20099step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw20099step2 raw20099step1; decide +kernel
      have hl : raw20099step2Labels = raw20099step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20099step1 raw20099step1Labels permutation14 hz
    mixedMoment B raw20099step2 raw20099step2Labels = mixedMoment B raw20099step3 raw20099step3Labels := by
      have ha : raw20099step3 = -raw20099step2 := by apply Matrix.ext; change ∀ i j, raw20099step3 i j = -(raw20099step2 i j); unfold raw20099step3 raw20099step2; decide +kernel
      have hl : raw20099step3Labels = raw20099step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4070 node4070Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical161
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical20643 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20643 raw20643Labels = mixedMoment B node1647 node1647Labels := by
  calc
    mixedMoment B raw20643 raw20643Labels = mixedMoment B raw20643step0 raw20643step0Labels := by
      have hz : ∀ j, raw20643 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20643step0 = (fun i j => raw20643 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20643step0 raw20643; decide +kernel
      have hl : raw20643step0Labels = raw20643Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20643 raw20643Labels permutation434 hz
    mixedMoment B raw20643step0 raw20643step0Labels = mixedMoment B raw20643step1 raw20643step1Labels := by
      have hz : ∀ j, raw20643step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20643step1 = (fun i j => raw20643step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20643step1 raw20643step0; decide +kernel
      have hl : raw20643step1Labels = raw20643step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20643step0 raw20643step0Labels permutation80 hz
    mixedMoment B raw20643step1 raw20643step1Labels = mixedMoment B raw20643step2 raw20643step2Labels := by
      have ha : raw20643step2 = (fun i j => raw20643step1 (permutation10 i) (permutation4 j)) := by apply Matrix.ext; unfold raw20643step2 raw20643step1; decide +kernel
      have hl : raw20643step2Labels = raw20643step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20643step1 raw20643step1Labels permutation10 permutation4
    mixedMoment B raw20643step2 raw20643step2Labels = mixedMoment B raw20643step3 raw20643step3Labels := by
      have ha : raw20643step3 = -raw20643step2 := by apply Matrix.ext; change ∀ i j, raw20643step3 i j = -(raw20643step2 i j); unfold raw20643step3 raw20643step2; decide +kernel
      have hl : raw20643step3Labels = raw20643step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1647 node1647Labels := by rfl

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

theorem canonical21367 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21367 raw21367Labels = mixedMoment B node1750 node1750Labels := by
  calc
    mixedMoment B raw21367 raw21367Labels = mixedMoment B raw21367step0 raw21367step0Labels := by
      have hz : ∀ j, raw21367 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21367step0 = (fun i j => raw21367 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21367step0 raw21367; decide +kernel
      have hl : raw21367step0Labels = raw21367Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21367 raw21367Labels permutation434 hz
    mixedMoment B raw21367step0 raw21367step0Labels = mixedMoment B raw21367step1 raw21367step1Labels := by
      have hz : ∀ j, raw21367step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21367step1 = (fun i j => raw21367step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21367step1 raw21367step0; decide +kernel
      have hl : raw21367step1Labels = raw21367step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21367step0 raw21367step0Labels permutation80 hz
    mixedMoment B raw21367step1 raw21367step1Labels = mixedMoment B raw21367step2 raw21367step2Labels := by
      have ha : raw21367step2 = (fun i j => raw21367step1 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw21367step2 raw21367step1; decide +kernel
      have hl : raw21367step2Labels = raw21367step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21367step1 raw21367step1Labels permutation8 permutation4
    mixedMoment B raw21367step2 raw21367step2Labels = mixedMoment B raw21367step3 raw21367step3Labels := by
      have ha : raw21367step3 = -raw21367step2 := by apply Matrix.ext; change ∀ i j, raw21367step3 i j = -(raw21367step2 i j); unfold raw21367step3 raw21367step2; decide +kernel
      have hl : raw21367step3Labels = raw21367step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1750 node1750Labels := by rfl

theorem canonical21368 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21368 raw21368Labels = mixedMoment B node857 node857Labels := by
  calc
    mixedMoment B raw21368 raw21368Labels = mixedMoment B raw21368step0 raw21368step0Labels := by
      have hz : ∀ j, raw21368 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21368step0 = (fun i j => raw21368 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21368step0 raw21368; decide +kernel
      have hl : raw21368step0Labels = raw21368Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21368 raw21368Labels permutation434 hz
    mixedMoment B raw21368step0 raw21368step0Labels = mixedMoment B raw21368step1 raw21368step1Labels := by
      have hz : ∀ j, raw21368step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21368step1 = (fun i j => raw21368step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21368step1 raw21368step0; decide +kernel
      have hl : raw21368step1Labels = raw21368step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21368step0 raw21368step0Labels permutation80 hz
    mixedMoment B raw21368step1 raw21368step1Labels = mixedMoment B raw21368step2 raw21368step2Labels := by
      have ha : raw21368step2 = (fun i j => raw21368step1 (permutation11 i) (permutation4 j)) := by apply Matrix.ext; unfold raw21368step2 raw21368step1; decide +kernel
      have hl : raw21368step2Labels = raw21368step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21368step1 raw21368step1Labels permutation11 permutation4
    mixedMoment B raw21368step2 raw21368step2Labels = mixedMoment B raw21368step3 raw21368step3Labels := by
      have ha : raw21368step3 = -raw21368step2 := by apply Matrix.ext; change ∀ i j, raw21368step3 i j = -(raw21368step2 i j); unfold raw21368step3 raw21368step2; decide +kernel
      have hl : raw21368step3Labels = raw21368step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node857 node857Labels := by rfl

theorem canonical21369 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21369 raw21369Labels = mixedMoment B node847 node847Labels := by
  calc
    mixedMoment B raw21369 raw21369Labels = mixedMoment B raw21369step0 raw21369step0Labels := by
      have hz : ∀ j, raw21369 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21369step0 = (fun i j => raw21369 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21369step0 raw21369; decide +kernel
      have hl : raw21369step0Labels = raw21369Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21369 raw21369Labels permutation434 hz
    mixedMoment B raw21369step0 raw21369step0Labels = mixedMoment B raw21369step1 raw21369step1Labels := by
      have ha : raw21369step1 = (fun i j => raw21369step0 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw21369step1 raw21369step0; decide +kernel
      have hl : raw21369step1Labels = raw21369step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21369step0 raw21369step0Labels permutation32 permutation4
    mixedMoment B raw21369step1 raw21369step1Labels = mixedMoment B raw21369step2 raw21369step2Labels := by
      have ha : raw21369step2 = -raw21369step1 := by apply Matrix.ext; change ∀ i j, raw21369step2 i j = -(raw21369step1 i j); unfold raw21369step2 raw21369step1; decide +kernel
      have hl : raw21369step2Labels = raw21369step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node847 node847Labels := by rfl

theorem canonical21370 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21370 raw21370Labels = mixedMoment B node847 node847Labels := by
  calc
    mixedMoment B raw21370 raw21370Labels = mixedMoment B raw21370step0 raw21370step0Labels := by
      have hz : ∀ j, raw21370 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21370step0 = (fun i j => raw21370 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21370step0 raw21370; decide +kernel
      have hl : raw21370step0Labels = raw21370Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21370 raw21370Labels permutation346 hz
    mixedMoment B raw21370step0 raw21370step0Labels = mixedMoment B raw21370step1 raw21370step1Labels := by
      have ha : raw21370step1 = (fun i j => raw21370step0 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw21370step1 raw21370step0; decide +kernel
      have hl : raw21370step1Labels = raw21370step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21370step0 raw21370step0Labels permutation32 permutation4
    mixedMoment B raw21370step1 raw21370step1Labels = mixedMoment B raw21370step2 raw21370step2Labels := by
      have ha : raw21370step2 = -raw21370step1 := by apply Matrix.ext; change ∀ i j, raw21370step2 i j = -(raw21370step1 i j); unfold raw21370step2 raw21370step1; decide +kernel
      have hl : raw21370step2Labels = raw21370step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node847 node847Labels := by rfl

theorem canonical21371 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21371 raw21371Labels = mixedMoment B node853 node853Labels := by
  calc
    mixedMoment B raw21371 raw21371Labels = mixedMoment B raw21371step0 raw21371step0Labels := by
      have hz : ∀ j, raw21371 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21371step0 = (fun i j => raw21371 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21371step0 raw21371; decide +kernel
      have hl : raw21371step0Labels = raw21371Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21371 raw21371Labels permutation434 hz
    mixedMoment B raw21371step0 raw21371step0Labels = mixedMoment B raw21371step1 raw21371step1Labels := by
      have hz : ∀ j, raw21371step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21371step1 = (fun i j => raw21371step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21371step1 raw21371step0; decide +kernel
      have hl : raw21371step1Labels = raw21371step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21371step0 raw21371step0Labels permutation80 hz
    mixedMoment B raw21371step1 raw21371step1Labels = mixedMoment B raw21371step2 raw21371step2Labels := by
      have ha : raw21371step2 = (fun i j => raw21371step1 (permutation9 i) (permutation4 j)) := by apply Matrix.ext; unfold raw21371step2 raw21371step1; decide +kernel
      have hl : raw21371step2Labels = raw21371step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21371step1 raw21371step1Labels permutation9 permutation4
    mixedMoment B raw21371step2 raw21371step2Labels = mixedMoment B raw21371step3 raw21371step3Labels := by
      have ha : raw21371step3 = -raw21371step2 := by apply Matrix.ext; change ∀ i j, raw21371step3 i j = -(raw21371step2 i j); unfold raw21371step3 raw21371step2; decide +kernel
      have hl : raw21371step3Labels = raw21371step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node853 node853Labels := by rfl

theorem canonical21372 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21372 raw21372Labels = mixedMoment B node851 node851Labels := by
  calc
    mixedMoment B raw21372 raw21372Labels = mixedMoment B raw21372step0 raw21372step0Labels := by
      have hz : ∀ j, raw21372 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21372step0 = (fun i j => raw21372 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21372step0 raw21372; decide +kernel
      have hl : raw21372step0Labels = raw21372Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21372 raw21372Labels permutation434 hz
    mixedMoment B raw21372step0 raw21372step0Labels = mixedMoment B raw21372step1 raw21372step1Labels := by
      have hz : ∀ j, raw21372step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21372step1 = (fun i j => raw21372step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21372step1 raw21372step0; decide +kernel
      have hl : raw21372step1Labels = raw21372step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21372step0 raw21372step0Labels permutation80 hz
    mixedMoment B raw21372step1 raw21372step1Labels = mixedMoment B raw21372step2 raw21372step2Labels := by
      have ha : raw21372step2 = (fun i j => raw21372step1 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw21372step2 raw21372step1; decide +kernel
      have hl : raw21372step2Labels = raw21372step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21372step1 raw21372step1Labels permutation8 permutation4
    mixedMoment B raw21372step2 raw21372step2Labels = mixedMoment B raw21372step3 raw21372step3Labels := by
      have ha : raw21372step3 = -raw21372step2 := by apply Matrix.ext; change ∀ i j, raw21372step3 i j = -(raw21372step2 i j); unfold raw21372step3 raw21372step2; decide +kernel
      have hl : raw21372step3Labels = raw21372step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node851 node851Labels := by rfl

theorem canonical21373 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21373 raw21373Labels = mixedMoment B node4894 node4894Labels := by
  calc
    mixedMoment B raw21373 raw21373Labels = mixedMoment B raw21373step0 raw21373step0Labels := by
      have hz : ∀ j, raw21373 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21373step0 = (fun i j => raw21373 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21373step0 raw21373; decide +kernel
      have hl : raw21373step0Labels = raw21373Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21373 raw21373Labels permutation434 hz
    mixedMoment B raw21373step0 raw21373step0Labels = mixedMoment B raw21373step1 raw21373step1Labels := by
      have hz : ∀ j, raw21373step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21373step1 = (fun i j => raw21373step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21373step1 raw21373step0; decide +kernel
      have hl : raw21373step1Labels = raw21373step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21373step0 raw21373step0Labels permutation80 hz
    _ = mixedMoment B node4894 node4894Labels := by rfl

theorem canonical21374 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21374 raw21374Labels = mixedMoment B node4177 node4177Labels := by
  calc
    mixedMoment B raw21374 raw21374Labels = mixedMoment B raw21374step0 raw21374step0Labels := by
      have hz : ∀ j, raw21374 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21374step0 = (fun i j => raw21374 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21374step0 raw21374; decide +kernel
      have hl : raw21374step0Labels = raw21374Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21374 raw21374Labels permutation434 hz
    mixedMoment B raw21374step0 raw21374step0Labels = mixedMoment B raw21374step1 raw21374step1Labels := by
      have hz : ∀ j, raw21374step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21374step1 = (fun i j => raw21374step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21374step1 raw21374step0; decide +kernel
      have hl : raw21374step1Labels = raw21374step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21374step0 raw21374step0Labels permutation80 hz
    mixedMoment B raw21374step1 raw21374step1Labels = mixedMoment B raw21374step2 raw21374step2Labels := by
      have ha : raw21374step2 = (fun i j => raw21374step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21374step2 raw21374step1; decide +kernel
      have hl : raw21374step2Labels = raw21374step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21374step1 raw21374step1Labels permutation10 permutation2
    _ = mixedMoment B node4177 node4177Labels := by rfl

theorem canonical21375 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21375 raw21375Labels = mixedMoment B node4346 node4346Labels := by
  calc
    mixedMoment B raw21375 raw21375Labels = mixedMoment B raw21375step0 raw21375step0Labels := by
      have hz : ∀ j, raw21375 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21375step0 = (fun i j => raw21375 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21375step0 raw21375; decide +kernel
      have hl : raw21375step0Labels = raw21375Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21375 raw21375Labels permutation434 hz
    mixedMoment B raw21375step0 raw21375step0Labels = mixedMoment B raw21375step1 raw21375step1Labels := by
      have ha : raw21375step1 = (fun i j => raw21375step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21375step1 raw21375step0; decide +kernel
      have hl : raw21375step1Labels = raw21375step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21375step0 raw21375step0Labels permutation40 permutation2
    _ = mixedMoment B node4346 node4346Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical167
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical21376 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21376 raw21376Labels = mixedMoment B node4346 node4346Labels := by
  calc
    mixedMoment B raw21376 raw21376Labels = mixedMoment B raw21376step0 raw21376step0Labels := by
      have hz : ∀ j, raw21376 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21376step0 = (fun i j => raw21376 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21376step0 raw21376; decide +kernel
      have hl : raw21376step0Labels = raw21376Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21376 raw21376Labels permutation346 hz
    mixedMoment B raw21376step0 raw21376step0Labels = mixedMoment B raw21376step1 raw21376step1Labels := by
      have ha : raw21376step1 = (fun i j => raw21376step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21376step1 raw21376step0; decide +kernel
      have hl : raw21376step1Labels = raw21376step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21376step0 raw21376step0Labels permutation40 permutation2
    _ = mixedMoment B node4346 node4346Labels := by rfl

theorem canonical21377 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21377 raw21377Labels = mixedMoment B node4505 node4505Labels := by
  calc
    mixedMoment B raw21377 raw21377Labels = mixedMoment B raw21377step0 raw21377step0Labels := by
      have hz : ∀ j, raw21377 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw21377step0 = (fun i j => raw21377 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw21377step0 raw21377; decide +kernel
      have hl : raw21377step0Labels = raw21377Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21377 raw21377Labels permutation520 hz
    mixedMoment B raw21377step0 raw21377step0Labels = mixedMoment B raw21377step1 raw21377step1Labels := by
      have hz : ∀ j, raw21377step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw21377step1 = (fun i j => raw21377step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw21377step1 raw21377step0; decide +kernel
      have hl : raw21377step1Labels = raw21377step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21377step0 raw21377step0Labels permutation104 hz
    mixedMoment B raw21377step1 raw21377step1Labels = mixedMoment B raw21377step2 raw21377step2Labels := by
      have hz : ∀ j, raw21377step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw21377step2 = (fun i j => raw21377step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw21377step2 raw21377step1; decide +kernel
      have hl : raw21377step2Labels = raw21377step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21377step1 raw21377step1Labels permutation20 hz
    _ = mixedMoment B node4505 node4505Labels := by rfl

theorem canonical21378 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21378 raw21378Labels = mixedMoment B node4151 node4151Labels := by
  calc
    mixedMoment B raw21378 raw21378Labels = mixedMoment B raw21378step0 raw21378step0Labels := by
      have hz : ∀ j, raw21378 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21378step0 = (fun i j => raw21378 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21378step0 raw21378; decide +kernel
      have hl : raw21378step0Labels = raw21378Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21378 raw21378Labels permutation434 hz
    _ = mixedMoment B node4151 node4151Labels := by rfl

theorem canonical21379 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21379 raw21379Labels = mixedMoment B node4365 node4365Labels := by
  calc
    mixedMoment B raw21379 raw21379Labels = mixedMoment B raw21379step0 raw21379step0Labels := by
      have hz : ∀ j, raw21379 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21379step0 = (fun i j => raw21379 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21379step0 raw21379; decide +kernel
      have hl : raw21379step0Labels = raw21379Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21379 raw21379Labels permutation434 hz
    _ = mixedMoment B node4365 node4365Labels := by rfl

theorem canonical21380 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21380 raw21380Labels = mixedMoment B node4326 node4326Labels := by
  calc
    mixedMoment B raw21380 raw21380Labels = mixedMoment B raw21380step0 raw21380step0Labels := by
      have ha : raw21380step0 = (fun i j => raw21380 (permutation200 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21380step0 raw21380; decide +kernel
      have hl : raw21380step0Labels = raw21380Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21380 raw21380Labels permutation200 permutation2
    _ = mixedMoment B node4326 node4326Labels := by rfl

theorem canonical21381 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21381 raw21381Labels = mixedMoment B node4460 node4460Labels := by
  calc
    mixedMoment B raw21381 raw21381Labels = mixedMoment B raw21381step0 raw21381step0Labels := by
      have hz : ∀ j, raw21381 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw21381step0 = (fun i j => raw21381 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw21381step0 raw21381; decide +kernel
      have hl : raw21381step0Labels = raw21381Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21381 raw21381Labels permutation520 hz
    mixedMoment B raw21381step0 raw21381step0Labels = mixedMoment B raw21381step1 raw21381step1Labels := by
      have hz : ∀ j, raw21381step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw21381step1 = (fun i j => raw21381step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw21381step1 raw21381step0; decide +kernel
      have hl : raw21381step1Labels = raw21381step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21381step0 raw21381step0Labels permutation104 hz
    _ = mixedMoment B node4460 node4460Labels := by rfl

theorem canonical21382 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21382 raw21382Labels = mixedMoment B node4151 node4151Labels := by
  calc
    mixedMoment B raw21382 raw21382Labels = mixedMoment B raw21382step0 raw21382step0Labels := by
      have hz : ∀ j, raw21382 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21382step0 = (fun i j => raw21382 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21382step0 raw21382; decide +kernel
      have hl : raw21382step0Labels = raw21382Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21382 raw21382Labels permutation346 hz
    _ = mixedMoment B node4151 node4151Labels := by rfl

theorem canonical21383 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21383 raw21383Labels = mixedMoment B node4365 node4365Labels := by
  calc
    mixedMoment B raw21383 raw21383Labels = mixedMoment B raw21383step0 raw21383step0Labels := by
      have hz : ∀ j, raw21383 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21383step0 = (fun i j => raw21383 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21383step0 raw21383; decide +kernel
      have hl : raw21383step0Labels = raw21383Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21383 raw21383Labels permutation346 hz
    _ = mixedMoment B node4365 node4365Labels := by rfl

theorem canonical21384 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21384 raw21384Labels = mixedMoment B node4326 node4326Labels := by
  calc
    mixedMoment B raw21384 raw21384Labels = mixedMoment B raw21384step0 raw21384step0Labels := by
      have ha : raw21384step0 = (fun i j => raw21384 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21384step0 raw21384; decide +kernel
      have hl : raw21384step0Labels = raw21384Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21384 raw21384Labels permutation176 permutation2
    _ = mixedMoment B node4326 node4326Labels := by rfl

theorem canonical21385 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21385 raw21385Labels = mixedMoment B node4460 node4460Labels := by
  calc
    mixedMoment B raw21385 raw21385Labels = mixedMoment B raw21385step0 raw21385step0Labels := by
      have hz : ∀ j, raw21385 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw21385step0 = (fun i j => raw21385 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw21385step0 raw21385; decide +kernel
      have hl : raw21385step0Labels = raw21385Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21385 raw21385Labels permutation520 hz
    mixedMoment B raw21385step0 raw21385step0Labels = mixedMoment B raw21385step1 raw21385step1Labels := by
      have hz : ∀ j, raw21385step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21385step1 = (fun i j => raw21385step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21385step1 raw21385step0; decide +kernel
      have hl : raw21385step1Labels = raw21385step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21385step0 raw21385step0Labels permutation80 hz
    _ = mixedMoment B node4460 node4460Labels := by rfl

theorem canonical21386 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21386 raw21386Labels = mixedMoment B node4160 node4160Labels := by
  calc
    mixedMoment B raw21386 raw21386Labels = mixedMoment B raw21386step0 raw21386step0Labels := by
      have hz : ∀ j, raw21386 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21386step0 = (fun i j => raw21386 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21386step0 raw21386; decide +kernel
      have hl : raw21386step0Labels = raw21386Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21386 raw21386Labels permutation434 hz
    mixedMoment B raw21386step0 raw21386step0Labels = mixedMoment B raw21386step1 raw21386step1Labels := by
      have hz : ∀ j, raw21386step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21386step1 = (fun i j => raw21386step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21386step1 raw21386step0; decide +kernel
      have hl : raw21386step1Labels = raw21386step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21386step0 raw21386step0Labels permutation80 hz
    _ = mixedMoment B node4160 node4160Labels := by rfl

theorem canonical21387 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21387 raw21387Labels = mixedMoment B node4373 node4373Labels := by
  calc
    mixedMoment B raw21387 raw21387Labels = mixedMoment B raw21387step0 raw21387step0Labels := by
      have hz : ∀ j, raw21387 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21387step0 = (fun i j => raw21387 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21387step0 raw21387; decide +kernel
      have hl : raw21387step0Labels = raw21387Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21387 raw21387Labels permutation434 hz
    mixedMoment B raw21387step0 raw21387step0Labels = mixedMoment B raw21387step1 raw21387step1Labels := by
      have hz : ∀ j, raw21387step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21387step1 = (fun i j => raw21387step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21387step1 raw21387step0; decide +kernel
      have hl : raw21387step1Labels = raw21387step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21387step0 raw21387step0Labels permutation80 hz
    _ = mixedMoment B node4373 node4373Labels := by rfl

theorem canonical21388 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21388 raw21388Labels = mixedMoment B node4334 node4334Labels := by
  calc
    mixedMoment B raw21388 raw21388Labels = mixedMoment B raw21388step0 raw21388step0Labels := by
      have hz : ∀ j, raw21388 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21388step0 = (fun i j => raw21388 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21388step0 raw21388; decide +kernel
      have hl : raw21388step0Labels = raw21388Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21388 raw21388Labels permutation434 hz
    mixedMoment B raw21388step0 raw21388step0Labels = mixedMoment B raw21388step1 raw21388step1Labels := by
      have ha : raw21388step1 = (fun i j => raw21388step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21388step1 raw21388step0; decide +kernel
      have hl : raw21388step1Labels = raw21388step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21388step0 raw21388step0Labels permutation38 permutation2
    _ = mixedMoment B node4334 node4334Labels := by rfl

theorem canonical21389 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21389 raw21389Labels = mixedMoment B node4334 node4334Labels := by
  calc
    mixedMoment B raw21389 raw21389Labels = mixedMoment B raw21389step0 raw21389step0Labels := by
      have hz : ∀ j, raw21389 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21389step0 = (fun i j => raw21389 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21389step0 raw21389; decide +kernel
      have hl : raw21389step0Labels = raw21389Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21389 raw21389Labels permutation346 hz
    mixedMoment B raw21389step0 raw21389step0Labels = mixedMoment B raw21389step1 raw21389step1Labels := by
      have ha : raw21389step1 = (fun i j => raw21389step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21389step1 raw21389step0; decide +kernel
      have hl : raw21389step1Labels = raw21389step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21389step0 raw21389step0Labels permutation38 permutation2
    _ = mixedMoment B node4334 node4334Labels := by rfl

theorem canonical21390 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21390 raw21390Labels = mixedMoment B node4156 node4156Labels := by
  calc
    mixedMoment B raw21390 raw21390Labels = mixedMoment B raw21390step0 raw21390step0Labels := by
      have hz : ∀ j, raw21390 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21390step0 = (fun i j => raw21390 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21390step0 raw21390; decide +kernel
      have hl : raw21390step0Labels = raw21390Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21390 raw21390Labels permutation434 hz
    mixedMoment B raw21390step0 raw21390step0Labels = mixedMoment B raw21390step1 raw21390step1Labels := by
      have hz : ∀ j, raw21390step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21390step1 = (fun i j => raw21390step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21390step1 raw21390step0; decide +kernel
      have hl : raw21390step1Labels = raw21390step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21390step0 raw21390step0Labels permutation80 hz
    _ = mixedMoment B node4156 node4156Labels := by rfl

theorem canonical21391 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21391 raw21391Labels = mixedMoment B node4370 node4370Labels := by
  calc
    mixedMoment B raw21391 raw21391Labels = mixedMoment B raw21391step0 raw21391step0Labels := by
      have hz : ∀ j, raw21391 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21391step0 = (fun i j => raw21391 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21391step0 raw21391; decide +kernel
      have hl : raw21391step0Labels = raw21391Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21391 raw21391Labels permutation434 hz
    mixedMoment B raw21391step0 raw21391step0Labels = mixedMoment B raw21391step1 raw21391step1Labels := by
      have hz : ∀ j, raw21391step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21391step1 = (fun i j => raw21391step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21391step1 raw21391step0; decide +kernel
      have hl : raw21391step1Labels = raw21391step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21391step0 raw21391step0Labels permutation80 hz
    _ = mixedMoment B node4370 node4370Labels := by rfl

theorem canonical21392 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21392 raw21392Labels = mixedMoment B node4330 node4330Labels := by
  calc
    mixedMoment B raw21392 raw21392Labels = mixedMoment B raw21392step0 raw21392step0Labels := by
      have hz : ∀ j, raw21392 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21392step0 = (fun i j => raw21392 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21392step0 raw21392; decide +kernel
      have hl : raw21392step0Labels = raw21392Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21392 raw21392Labels permutation434 hz
    mixedMoment B raw21392step0 raw21392step0Labels = mixedMoment B raw21392step1 raw21392step1Labels := by
      have ha : raw21392step1 = (fun i j => raw21392step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21392step1 raw21392step0; decide +kernel
      have hl : raw21392step1Labels = raw21392step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21392step0 raw21392step0Labels permutation38 permutation2
    _ = mixedMoment B node4330 node4330Labels := by rfl

theorem canonical21393 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21393 raw21393Labels = mixedMoment B node4330 node4330Labels := by
  calc
    mixedMoment B raw21393 raw21393Labels = mixedMoment B raw21393step0 raw21393step0Labels := by
      have hz : ∀ j, raw21393 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21393step0 = (fun i j => raw21393 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21393step0 raw21393; decide +kernel
      have hl : raw21393step0Labels = raw21393Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21393 raw21393Labels permutation346 hz
    mixedMoment B raw21393step0 raw21393step0Labels = mixedMoment B raw21393step1 raw21393step1Labels := by
      have ha : raw21393step1 = (fun i j => raw21393step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21393step1 raw21393step0; decide +kernel
      have hl : raw21393step1Labels = raw21393step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21393step0 raw21393step0Labels permutation38 permutation2
    _ = mixedMoment B node4330 node4330Labels := by rfl

theorem canonical21394 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21394 raw21394Labels = mixedMoment B node4468 node4468Labels := by
  calc
    mixedMoment B raw21394 raw21394Labels = mixedMoment B raw21394step0 raw21394step0Labels := by
      have hz : ∀ j, raw21394 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw21394step0 = (fun i j => raw21394 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw21394step0 raw21394; decide +kernel
      have hl : raw21394step0Labels = raw21394Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21394 raw21394Labels permutation520 hz
    mixedMoment B raw21394step0 raw21394step0Labels = mixedMoment B raw21394step1 raw21394step1Labels := by
      have hz : ∀ j, raw21394step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw21394step1 = (fun i j => raw21394step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw21394step1 raw21394step0; decide +kernel
      have hl : raw21394step1Labels = raw21394step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21394step0 raw21394step0Labels permutation104 hz
    mixedMoment B raw21394step1 raw21394step1Labels = mixedMoment B raw21394step2 raw21394step2Labels := by
      have hz : ∀ j, raw21394step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw21394step2 = (fun i j => raw21394step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw21394step2 raw21394step1; decide +kernel
      have hl : raw21394step2Labels = raw21394step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21394step1 raw21394step1Labels permutation20 hz
    _ = mixedMoment B node4468 node4468Labels := by rfl

theorem canonical21425 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21425 raw21425Labels = mixedMoment B node2261 node2261Labels := by
  calc
    mixedMoment B raw21425 raw21425Labels = mixedMoment B raw21425step0 raw21425step0Labels := by
      have hz : ∀ j, raw21425 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21425step0 = (fun i j => raw21425 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21425step0 raw21425; decide +kernel
      have hl : raw21425step0Labels = raw21425Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21425 raw21425Labels permutation434 hz
    mixedMoment B raw21425step0 raw21425step0Labels = mixedMoment B raw21425step1 raw21425step1Labels := by
      have hz : ∀ j, raw21425step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21425step1 = (fun i j => raw21425step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21425step1 raw21425step0; decide +kernel
      have hl : raw21425step1Labels = raw21425step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21425step0 raw21425step0Labels permutation80 hz
    mixedMoment B raw21425step1 raw21425step1Labels = mixedMoment B raw21425step2 raw21425step2Labels := by
      have ha : raw21425step2 = (fun i j => raw21425step1 (permutation10 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21425step2 raw21425step1; decide +kernel
      have hl : raw21425step2Labels = raw21425step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21425step1 raw21425step1Labels permutation10 permutation7
    mixedMoment B raw21425step2 raw21425step2Labels = mixedMoment B raw21425step3 raw21425step3Labels := by
      have ha : raw21425step3 = -raw21425step2 := by apply Matrix.ext; change ∀ i j, raw21425step3 i j = -(raw21425step2 i j); unfold raw21425step3 raw21425step2; decide +kernel
      have hl : raw21425step3Labels = raw21425step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21425step3 raw21425step3Labels = mixedMoment B raw21425step4 raw21425step4Labels := by
      have ha : raw21425step4 = raw21425step3 := by apply Matrix.ext; unfold raw21425step4 raw21425step3; decide +kernel
      have hl : raw21425step3Labels = labelEmbedding1 ∘ raw21425step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21425step3 raw21425step3Labels raw21425step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2261 node2261Labels := by rfl

theorem canonical21426 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21426 raw21426Labels = mixedMoment B node2203 node2203Labels := by
  calc
    mixedMoment B raw21426 raw21426Labels = mixedMoment B raw21426step0 raw21426step0Labels := by
      have hz : ∀ j, raw21426 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21426step0 = (fun i j => raw21426 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21426step0 raw21426; decide +kernel
      have hl : raw21426step0Labels = raw21426Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21426 raw21426Labels permutation434 hz
    mixedMoment B raw21426step0 raw21426step0Labels = mixedMoment B raw21426step1 raw21426step1Labels := by
      have ha : raw21426step1 = (fun i j => raw21426step0 (permutation40 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21426step1 raw21426step0; decide +kernel
      have hl : raw21426step1Labels = raw21426step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21426step0 raw21426step0Labels permutation40 permutation7
    mixedMoment B raw21426step1 raw21426step1Labels = mixedMoment B raw21426step2 raw21426step2Labels := by
      have ha : raw21426step2 = -raw21426step1 := by apply Matrix.ext; change ∀ i j, raw21426step2 i j = -(raw21426step1 i j); unfold raw21426step2 raw21426step1; decide +kernel
      have hl : raw21426step2Labels = raw21426step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21426step2 raw21426step2Labels = mixedMoment B raw21426step3 raw21426step3Labels := by
      have ha : raw21426step3 = raw21426step2 := by apply Matrix.ext; unfold raw21426step3 raw21426step2; decide +kernel
      have hl : raw21426step2Labels = labelEmbedding1 ∘ raw21426step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21426step2 raw21426step2Labels raw21426step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2203 node2203Labels := by rfl

theorem canonical21427 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21427 raw21427Labels = mixedMoment B node2203 node2203Labels := by
  calc
    mixedMoment B raw21427 raw21427Labels = mixedMoment B raw21427step0 raw21427step0Labels := by
      have hz : ∀ j, raw21427 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21427step0 = (fun i j => raw21427 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21427step0 raw21427; decide +kernel
      have hl : raw21427step0Labels = raw21427Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21427 raw21427Labels permutation346 hz
    mixedMoment B raw21427step0 raw21427step0Labels = mixedMoment B raw21427step1 raw21427step1Labels := by
      have ha : raw21427step1 = (fun i j => raw21427step0 (permutation40 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21427step1 raw21427step0; decide +kernel
      have hl : raw21427step1Labels = raw21427step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21427step0 raw21427step0Labels permutation40 permutation7
    mixedMoment B raw21427step1 raw21427step1Labels = mixedMoment B raw21427step2 raw21427step2Labels := by
      have ha : raw21427step2 = -raw21427step1 := by apply Matrix.ext; change ∀ i j, raw21427step2 i j = -(raw21427step1 i j); unfold raw21427step2 raw21427step1; decide +kernel
      have hl : raw21427step2Labels = raw21427step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21427step2 raw21427step2Labels = mixedMoment B raw21427step3 raw21427step3Labels := by
      have ha : raw21427step3 = raw21427step2 := by apply Matrix.ext; unfold raw21427step3 raw21427step2; decide +kernel
      have hl : raw21427step2Labels = labelEmbedding1 ∘ raw21427step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21427step2 raw21427step2Labels raw21427step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2203 node2203Labels := by rfl

theorem canonical21428 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21428 raw21428Labels = mixedMoment B node2292 node2292Labels := by
  calc
    mixedMoment B raw21428 raw21428Labels = mixedMoment B raw21428step0 raw21428step0Labels := by
      have hz : ∀ j, raw21428 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw21428step0 = (fun i j => raw21428 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw21428step0 raw21428; decide +kernel
      have hl : raw21428step0Labels = raw21428Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21428 raw21428Labels permutation520 hz
    mixedMoment B raw21428step0 raw21428step0Labels = mixedMoment B raw21428step1 raw21428step1Labels := by
      have hz : ∀ j, raw21428step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw21428step1 = (fun i j => raw21428step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw21428step1 raw21428step0; decide +kernel
      have hl : raw21428step1Labels = raw21428step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21428step0 raw21428step0Labels permutation104 hz
    mixedMoment B raw21428step1 raw21428step1Labels = mixedMoment B raw21428step2 raw21428step2Labels := by
      have hz : ∀ j, raw21428step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw21428step2 = (fun i j => raw21428step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw21428step2 raw21428step1; decide +kernel
      have hl : raw21428step2Labels = raw21428step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21428step1 raw21428step1Labels permutation20 hz
    mixedMoment B raw21428step2 raw21428step2Labels = mixedMoment B raw21428step3 raw21428step3Labels := by
      have ha : raw21428step3 = (fun i j => raw21428step2 (permutation2 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21428step3 raw21428step2; decide +kernel
      have hl : raw21428step3Labels = raw21428step2Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21428step2 raw21428step2Labels permutation2 permutation7
    mixedMoment B raw21428step3 raw21428step3Labels = mixedMoment B raw21428step4 raw21428step4Labels := by
      have ha : raw21428step4 = -raw21428step3 := by apply Matrix.ext; change ∀ i j, raw21428step4 i j = -(raw21428step3 i j); unfold raw21428step4 raw21428step3; decide +kernel
      have hl : raw21428step4Labels = raw21428step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21428step4 raw21428step4Labels = mixedMoment B raw21428step5 raw21428step5Labels := by
      have ha : raw21428step5 = raw21428step4 := by apply Matrix.ext; unfold raw21428step5 raw21428step4; decide +kernel
      have hl : raw21428step4Labels = labelEmbedding1 ∘ raw21428step5Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21428step4 raw21428step4Labels raw21428step5Labels labelEmbedding1 hl
    _ = mixedMoment B node2292 node2292Labels := by rfl

theorem canonical21429 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21429 raw21429Labels = mixedMoment B node2264 node2264Labels := by
  calc
    mixedMoment B raw21429 raw21429Labels = mixedMoment B raw21429step0 raw21429step0Labels := by
      have hz : ∀ j, raw21429 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21429step0 = (fun i j => raw21429 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21429step0 raw21429; decide +kernel
      have hl : raw21429step0Labels = raw21429Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21429 raw21429Labels permutation434 hz
    mixedMoment B raw21429step0 raw21429step0Labels = mixedMoment B raw21429step1 raw21429step1Labels := by
      have hz : ∀ j, raw21429step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21429step1 = (fun i j => raw21429step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21429step1 raw21429step0; decide +kernel
      have hl : raw21429step1Labels = raw21429step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21429step0 raw21429step0Labels permutation80 hz
    mixedMoment B raw21429step1 raw21429step1Labels = mixedMoment B raw21429step2 raw21429step2Labels := by
      have ha : raw21429step2 = (fun i j => raw21429step1 (permutation10 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21429step2 raw21429step1; decide +kernel
      have hl : raw21429step2Labels = raw21429step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21429step1 raw21429step1Labels permutation10 permutation7
    mixedMoment B raw21429step2 raw21429step2Labels = mixedMoment B raw21429step3 raw21429step3Labels := by
      have ha : raw21429step3 = -raw21429step2 := by apply Matrix.ext; change ∀ i j, raw21429step3 i j = -(raw21429step2 i j); unfold raw21429step3 raw21429step2; decide +kernel
      have hl : raw21429step3Labels = raw21429step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21429step3 raw21429step3Labels = mixedMoment B raw21429step4 raw21429step4Labels := by
      have ha : raw21429step4 = raw21429step3 := by apply Matrix.ext; unfold raw21429step4 raw21429step3; decide +kernel
      have hl : raw21429step3Labels = labelEmbedding1 ∘ raw21429step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21429step3 raw21429step3Labels raw21429step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2264 node2264Labels := by rfl

theorem canonical21430 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21430 raw21430Labels = mixedMoment B node1518 node1518Labels := by
  calc
    mixedMoment B raw21430 raw21430Labels = mixedMoment B raw21430step0 raw21430step0Labels := by
      have hz : ∀ j, raw21430 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21430step0 = (fun i j => raw21430 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21430step0 raw21430; decide +kernel
      have hl : raw21430step0Labels = raw21430Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21430 raw21430Labels permutation434 hz
    mixedMoment B raw21430step0 raw21430step0Labels = mixedMoment B raw21430step1 raw21430step1Labels := by
      have hz : ∀ j, raw21430step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21430step1 = (fun i j => raw21430step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21430step1 raw21430step0; decide +kernel
      have hl : raw21430step1Labels = raw21430step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21430step0 raw21430step0Labels permutation80 hz
    mixedMoment B raw21430step1 raw21430step1Labels = mixedMoment B raw21430step2 raw21430step2Labels := by
      have ha : raw21430step2 = (fun i j => raw21430step1 (permutation10 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21430step2 raw21430step1; decide +kernel
      have hl : raw21430step2Labels = raw21430step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21430step1 raw21430step1Labels permutation10 permutation7
    mixedMoment B raw21430step2 raw21430step2Labels = mixedMoment B raw21430step3 raw21430step3Labels := by
      have ha : raw21430step3 = -raw21430step2 := by apply Matrix.ext; change ∀ i j, raw21430step3 i j = -(raw21430step2 i j); unfold raw21430step3 raw21430step2; decide +kernel
      have hl : raw21430step3Labels = raw21430step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21430step3 raw21430step3Labels = mixedMoment B raw21430step4 raw21430step4Labels := by
      have ha : raw21430step4 = raw21430step3 := by apply Matrix.ext; unfold raw21430step4 raw21430step3; decide +kernel
      have hl : raw21430step3Labels = labelEmbedding1 ∘ raw21430step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21430step3 raw21430step3Labels raw21430step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1518 node1518Labels := by rfl

theorem canonical21431 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21431 raw21431Labels = mixedMoment B node1674 node1674Labels := by
  calc
    mixedMoment B raw21431 raw21431Labels = mixedMoment B raw21431step0 raw21431step0Labels := by
      have hz : ∀ j, raw21431 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21431step0 = (fun i j => raw21431 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21431step0 raw21431; decide +kernel
      have hl : raw21431step0Labels = raw21431Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21431 raw21431Labels permutation434 hz
    mixedMoment B raw21431step0 raw21431step0Labels = mixedMoment B raw21431step1 raw21431step1Labels := by
      have ha : raw21431step1 = (fun i j => raw21431step0 (permutation40 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21431step1 raw21431step0; decide +kernel
      have hl : raw21431step1Labels = raw21431step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21431step0 raw21431step0Labels permutation40 permutation7
    mixedMoment B raw21431step1 raw21431step1Labels = mixedMoment B raw21431step2 raw21431step2Labels := by
      have ha : raw21431step2 = -raw21431step1 := by apply Matrix.ext; change ∀ i j, raw21431step2 i j = -(raw21431step1 i j); unfold raw21431step2 raw21431step1; decide +kernel
      have hl : raw21431step2Labels = raw21431step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21431step2 raw21431step2Labels = mixedMoment B raw21431step3 raw21431step3Labels := by
      have ha : raw21431step3 = raw21431step2 := by apply Matrix.ext; unfold raw21431step3 raw21431step2; decide +kernel
      have hl : raw21431step2Labels = labelEmbedding1 ∘ raw21431step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21431step2 raw21431step2Labels raw21431step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1674 node1674Labels := by rfl

theorem canonical21432 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21432 raw21432Labels = mixedMoment B node1674 node1674Labels := by
  calc
    mixedMoment B raw21432 raw21432Labels = mixedMoment B raw21432step0 raw21432step0Labels := by
      have hz : ∀ j, raw21432 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21432step0 = (fun i j => raw21432 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21432step0 raw21432; decide +kernel
      have hl : raw21432step0Labels = raw21432Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21432 raw21432Labels permutation346 hz
    mixedMoment B raw21432step0 raw21432step0Labels = mixedMoment B raw21432step1 raw21432step1Labels := by
      have ha : raw21432step1 = (fun i j => raw21432step0 (permutation40 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21432step1 raw21432step0; decide +kernel
      have hl : raw21432step1Labels = raw21432step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21432step0 raw21432step0Labels permutation40 permutation7
    mixedMoment B raw21432step1 raw21432step1Labels = mixedMoment B raw21432step2 raw21432step2Labels := by
      have ha : raw21432step2 = -raw21432step1 := by apply Matrix.ext; change ∀ i j, raw21432step2 i j = -(raw21432step1 i j); unfold raw21432step2 raw21432step1; decide +kernel
      have hl : raw21432step2Labels = raw21432step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21432step2 raw21432step2Labels = mixedMoment B raw21432step3 raw21432step3Labels := by
      have ha : raw21432step3 = raw21432step2 := by apply Matrix.ext; unfold raw21432step3 raw21432step2; decide +kernel
      have hl : raw21432step2Labels = labelEmbedding1 ∘ raw21432step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21432step2 raw21432step2Labels raw21432step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1674 node1674Labels := by rfl

theorem canonical21433 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21433 raw21433Labels = mixedMoment B node1754 node1754Labels := by
  calc
    mixedMoment B raw21433 raw21433Labels = mixedMoment B raw21433step0 raw21433step0Labels := by
      have hz : ∀ j, raw21433 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw21433step0 = (fun i j => raw21433 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw21433step0 raw21433; decide +kernel
      have hl : raw21433step0Labels = raw21433Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21433 raw21433Labels permutation520 hz
    mixedMoment B raw21433step0 raw21433step0Labels = mixedMoment B raw21433step1 raw21433step1Labels := by
      have hz : ∀ j, raw21433step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw21433step1 = (fun i j => raw21433step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw21433step1 raw21433step0; decide +kernel
      have hl : raw21433step1Labels = raw21433step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21433step0 raw21433step0Labels permutation104 hz
    mixedMoment B raw21433step1 raw21433step1Labels = mixedMoment B raw21433step2 raw21433step2Labels := by
      have hz : ∀ j, raw21433step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw21433step2 = (fun i j => raw21433step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw21433step2 raw21433step1; decide +kernel
      have hl : raw21433step2Labels = raw21433step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21433step1 raw21433step1Labels permutation20 hz
    mixedMoment B raw21433step2 raw21433step2Labels = mixedMoment B raw21433step3 raw21433step3Labels := by
      have ha : raw21433step3 = (fun i j => raw21433step2 (permutation2 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21433step3 raw21433step2; decide +kernel
      have hl : raw21433step3Labels = raw21433step2Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21433step2 raw21433step2Labels permutation2 permutation7
    mixedMoment B raw21433step3 raw21433step3Labels = mixedMoment B raw21433step4 raw21433step4Labels := by
      have ha : raw21433step4 = -raw21433step3 := by apply Matrix.ext; change ∀ i j, raw21433step4 i j = -(raw21433step3 i j); unfold raw21433step4 raw21433step3; decide +kernel
      have hl : raw21433step4Labels = raw21433step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21433step4 raw21433step4Labels = mixedMoment B raw21433step5 raw21433step5Labels := by
      have ha : raw21433step5 = raw21433step4 := by apply Matrix.ext; unfold raw21433step5 raw21433step4; decide +kernel
      have hl : raw21433step4Labels = labelEmbedding1 ∘ raw21433step5Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21433step4 raw21433step4Labels raw21433step5Labels labelEmbedding1 hl
    _ = mixedMoment B node1754 node1754Labels := by rfl

theorem canonical21434 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21434 raw21434Labels = mixedMoment B node1727 node1727Labels := by
  calc
    mixedMoment B raw21434 raw21434Labels = mixedMoment B raw21434step0 raw21434step0Labels := by
      have hz : ∀ j, raw21434 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21434step0 = (fun i j => raw21434 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21434step0 raw21434; decide +kernel
      have hl : raw21434step0Labels = raw21434Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21434 raw21434Labels permutation434 hz
    mixedMoment B raw21434step0 raw21434step0Labels = mixedMoment B raw21434step1 raw21434step1Labels := by
      have hz : ∀ j, raw21434step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21434step1 = (fun i j => raw21434step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21434step1 raw21434step0; decide +kernel
      have hl : raw21434step1Labels = raw21434step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21434step0 raw21434step0Labels permutation80 hz
    mixedMoment B raw21434step1 raw21434step1Labels = mixedMoment B raw21434step2 raw21434step2Labels := by
      have ha : raw21434step2 = (fun i j => raw21434step1 (permutation10 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21434step2 raw21434step1; decide +kernel
      have hl : raw21434step2Labels = raw21434step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21434step1 raw21434step1Labels permutation10 permutation7
    mixedMoment B raw21434step2 raw21434step2Labels = mixedMoment B raw21434step3 raw21434step3Labels := by
      have ha : raw21434step3 = -raw21434step2 := by apply Matrix.ext; change ∀ i j, raw21434step3 i j = -(raw21434step2 i j); unfold raw21434step3 raw21434step2; decide +kernel
      have hl : raw21434step3Labels = raw21434step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21434step3 raw21434step3Labels = mixedMoment B raw21434step4 raw21434step4Labels := by
      have ha : raw21434step4 = raw21434step3 := by apply Matrix.ext; unfold raw21434step4 raw21434step3; decide +kernel
      have hl : raw21434step3Labels = labelEmbedding1 ∘ raw21434step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21434step3 raw21434step3Labels raw21434step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1727 node1727Labels := by rfl

theorem canonical21435 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21435 raw21435Labels = mixedMoment B node1505 node1505Labels := by
  calc
    mixedMoment B raw21435 raw21435Labels = mixedMoment B raw21435step0 raw21435step0Labels := by
      have hz : ∀ j, raw21435 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21435step0 = (fun i j => raw21435 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21435step0 raw21435; decide +kernel
      have hl : raw21435step0Labels = raw21435Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21435 raw21435Labels permutation434 hz
    mixedMoment B raw21435step0 raw21435step0Labels = mixedMoment B raw21435step1 raw21435step1Labels := by
      have ha : raw21435step1 = (fun i j => raw21435step0 (permutation40 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21435step1 raw21435step0; decide +kernel
      have hl : raw21435step1Labels = raw21435step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21435step0 raw21435step0Labels permutation40 permutation7
    mixedMoment B raw21435step1 raw21435step1Labels = mixedMoment B raw21435step2 raw21435step2Labels := by
      have ha : raw21435step2 = -raw21435step1 := by apply Matrix.ext; change ∀ i j, raw21435step2 i j = -(raw21435step1 i j); unfold raw21435step2 raw21435step1; decide +kernel
      have hl : raw21435step2Labels = raw21435step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21435step2 raw21435step2Labels = mixedMoment B raw21435step3 raw21435step3Labels := by
      have ha : raw21435step3 = raw21435step2 := by apply Matrix.ext; unfold raw21435step3 raw21435step2; decide +kernel
      have hl : raw21435step2Labels = labelEmbedding1 ∘ raw21435step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21435step2 raw21435step2Labels raw21435step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1505 node1505Labels := by rfl

theorem canonical21436 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21436 raw21436Labels = mixedMoment B node1704 node1704Labels := by
  calc
    mixedMoment B raw21436 raw21436Labels = mixedMoment B raw21436step0 raw21436step0Labels := by
      have hz : ∀ j, raw21436 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21436step0 = (fun i j => raw21436 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21436step0 raw21436; decide +kernel
      have hl : raw21436step0Labels = raw21436Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21436 raw21436Labels permutation434 hz
    mixedMoment B raw21436step0 raw21436step0Labels = mixedMoment B raw21436step1 raw21436step1Labels := by
      have ha : raw21436step1 = (fun i j => raw21436step0 (permutation40 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21436step1 raw21436step0; decide +kernel
      have hl : raw21436step1Labels = raw21436step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21436step0 raw21436step0Labels permutation40 permutation7
    mixedMoment B raw21436step1 raw21436step1Labels = mixedMoment B raw21436step2 raw21436step2Labels := by
      have ha : raw21436step2 = -raw21436step1 := by apply Matrix.ext; change ∀ i j, raw21436step2 i j = -(raw21436step1 i j); unfold raw21436step2 raw21436step1; decide +kernel
      have hl : raw21436step2Labels = raw21436step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21436step2 raw21436step2Labels = mixedMoment B raw21436step3 raw21436step3Labels := by
      have ha : raw21436step3 = raw21436step2 := by apply Matrix.ext; unfold raw21436step3 raw21436step2; decide +kernel
      have hl : raw21436step2Labels = labelEmbedding1 ∘ raw21436step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21436step2 raw21436step2Labels raw21436step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1704 node1704Labels := by rfl

theorem canonical21437 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21437 raw21437Labels = mixedMoment B node1663 node1663Labels := by
  calc
    mixedMoment B raw21437 raw21437Labels = mixedMoment B raw21437step0 raw21437step0Labels := by
      have ha : raw21437step0 = (fun i j => raw21437 (permutation208 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21437step0 raw21437; decide +kernel
      have hl : raw21437step0Labels = raw21437Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21437 raw21437Labels permutation208 permutation7
    mixedMoment B raw21437step0 raw21437step0Labels = mixedMoment B raw21437step1 raw21437step1Labels := by
      have ha : raw21437step1 = -raw21437step0 := by apply Matrix.ext; change ∀ i j, raw21437step1 i j = -(raw21437step0 i j); unfold raw21437step1 raw21437step0; decide +kernel
      have hl : raw21437step1Labels = raw21437step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21437step1 raw21437step1Labels = mixedMoment B raw21437step2 raw21437step2Labels := by
      have ha : raw21437step2 = raw21437step1 := by apply Matrix.ext; unfold raw21437step2 raw21437step1; decide +kernel
      have hl : raw21437step1Labels = labelEmbedding1 ∘ raw21437step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21437step1 raw21437step1Labels raw21437step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1663 node1663Labels := by rfl

theorem canonical21438 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21438 raw21438Labels = mixedMoment B node1725 node1725Labels := by
  calc
    mixedMoment B raw21438 raw21438Labels = mixedMoment B raw21438step0 raw21438step0Labels := by
      have hz : ∀ j, raw21438 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw21438step0 = (fun i j => raw21438 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw21438step0 raw21438; decide +kernel
      have hl : raw21438step0Labels = raw21438Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21438 raw21438Labels permutation520 hz
    mixedMoment B raw21438step0 raw21438step0Labels = mixedMoment B raw21438step1 raw21438step1Labels := by
      have hz : ∀ j, raw21438step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw21438step1 = (fun i j => raw21438step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw21438step1 raw21438step0; decide +kernel
      have hl : raw21438step1Labels = raw21438step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21438step0 raw21438step0Labels permutation104 hz
    mixedMoment B raw21438step1 raw21438step1Labels = mixedMoment B raw21438step2 raw21438step2Labels := by
      have ha : raw21438step2 = (fun i j => raw21438step1 (permutation10 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21438step2 raw21438step1; decide +kernel
      have hl : raw21438step2Labels = raw21438step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21438step1 raw21438step1Labels permutation10 permutation7
    mixedMoment B raw21438step2 raw21438step2Labels = mixedMoment B raw21438step3 raw21438step3Labels := by
      have ha : raw21438step3 = -raw21438step2 := by apply Matrix.ext; change ∀ i j, raw21438step3 i j = -(raw21438step2 i j); unfold raw21438step3 raw21438step2; decide +kernel
      have hl : raw21438step3Labels = raw21438step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21438step3 raw21438step3Labels = mixedMoment B raw21438step4 raw21438step4Labels := by
      have ha : raw21438step4 = raw21438step3 := by apply Matrix.ext; unfold raw21438step4 raw21438step3; decide +kernel
      have hl : raw21438step3Labels = labelEmbedding1 ∘ raw21438step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21438step3 raw21438step3Labels raw21438step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1725 node1725Labels := by rfl

theorem canonical21439 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21439 raw21439Labels = mixedMoment B node1707 node1707Labels := by
  calc
    mixedMoment B raw21439 raw21439Labels = mixedMoment B raw21439step0 raw21439step0Labels := by
      have hz : ∀ j, raw21439 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21439step0 = (fun i j => raw21439 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21439step0 raw21439; decide +kernel
      have hl : raw21439step0Labels = raw21439Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21439 raw21439Labels permutation434 hz
    mixedMoment B raw21439step0 raw21439step0Labels = mixedMoment B raw21439step1 raw21439step1Labels := by
      have ha : raw21439step1 = (fun i j => raw21439step0 (permutation40 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21439step1 raw21439step0; decide +kernel
      have hl : raw21439step1Labels = raw21439step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21439step0 raw21439step0Labels permutation40 permutation7
    mixedMoment B raw21439step1 raw21439step1Labels = mixedMoment B raw21439step2 raw21439step2Labels := by
      have ha : raw21439step2 = -raw21439step1 := by apply Matrix.ext; change ∀ i j, raw21439step2 i j = -(raw21439step1 i j); unfold raw21439step2 raw21439step1; decide +kernel
      have hl : raw21439step2Labels = raw21439step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21439step2 raw21439step2Labels = mixedMoment B raw21439step3 raw21439step3Labels := by
      have ha : raw21439step3 = raw21439step2 := by apply Matrix.ext; unfold raw21439step3 raw21439step2; decide +kernel
      have hl : raw21439step2Labels = labelEmbedding1 ∘ raw21439step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21439step2 raw21439step2Labels raw21439step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1707 node1707Labels := by rfl

theorem canonical21440 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21440 raw21440Labels = mixedMoment B node1505 node1505Labels := by
  calc
    mixedMoment B raw21440 raw21440Labels = mixedMoment B raw21440step0 raw21440step0Labels := by
      have hz : ∀ j, raw21440 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21440step0 = (fun i j => raw21440 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21440step0 raw21440; decide +kernel
      have hl : raw21440step0Labels = raw21440Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21440 raw21440Labels permutation346 hz
    mixedMoment B raw21440step0 raw21440step0Labels = mixedMoment B raw21440step1 raw21440step1Labels := by
      have ha : raw21440step1 = (fun i j => raw21440step0 (permutation40 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21440step1 raw21440step0; decide +kernel
      have hl : raw21440step1Labels = raw21440step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21440step0 raw21440step0Labels permutation40 permutation7
    mixedMoment B raw21440step1 raw21440step1Labels = mixedMoment B raw21440step2 raw21440step2Labels := by
      have ha : raw21440step2 = -raw21440step1 := by apply Matrix.ext; change ∀ i j, raw21440step2 i j = -(raw21440step1 i j); unfold raw21440step2 raw21440step1; decide +kernel
      have hl : raw21440step2Labels = raw21440step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21440step2 raw21440step2Labels = mixedMoment B raw21440step3 raw21440step3Labels := by
      have ha : raw21440step3 = raw21440step2 := by apply Matrix.ext; unfold raw21440step3 raw21440step2; decide +kernel
      have hl : raw21440step2Labels = labelEmbedding1 ∘ raw21440step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21440step2 raw21440step2Labels raw21440step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1505 node1505Labels := by rfl

theorem canonical21441 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21441 raw21441Labels = mixedMoment B node1704 node1704Labels := by
  calc
    mixedMoment B raw21441 raw21441Labels = mixedMoment B raw21441step0 raw21441step0Labels := by
      have hz : ∀ j, raw21441 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21441step0 = (fun i j => raw21441 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21441step0 raw21441; decide +kernel
      have hl : raw21441step0Labels = raw21441Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21441 raw21441Labels permutation346 hz
    mixedMoment B raw21441step0 raw21441step0Labels = mixedMoment B raw21441step1 raw21441step1Labels := by
      have ha : raw21441step1 = (fun i j => raw21441step0 (permutation40 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21441step1 raw21441step0; decide +kernel
      have hl : raw21441step1Labels = raw21441step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21441step0 raw21441step0Labels permutation40 permutation7
    mixedMoment B raw21441step1 raw21441step1Labels = mixedMoment B raw21441step2 raw21441step2Labels := by
      have ha : raw21441step2 = -raw21441step1 := by apply Matrix.ext; change ∀ i j, raw21441step2 i j = -(raw21441step1 i j); unfold raw21441step2 raw21441step1; decide +kernel
      have hl : raw21441step2Labels = raw21441step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21441step2 raw21441step2Labels = mixedMoment B raw21441step3 raw21441step3Labels := by
      have ha : raw21441step3 = raw21441step2 := by apply Matrix.ext; unfold raw21441step3 raw21441step2; decide +kernel
      have hl : raw21441step2Labels = labelEmbedding1 ∘ raw21441step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21441step2 raw21441step2Labels raw21441step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1704 node1704Labels := by rfl

theorem canonical21442 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21442 raw21442Labels = mixedMoment B node1663 node1663Labels := by
  calc
    mixedMoment B raw21442 raw21442Labels = mixedMoment B raw21442step0 raw21442step0Labels := by
      have ha : raw21442step0 = (fun i j => raw21442 (permutation184 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21442step0 raw21442; decide +kernel
      have hl : raw21442step0Labels = raw21442Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21442 raw21442Labels permutation184 permutation7
    mixedMoment B raw21442step0 raw21442step0Labels = mixedMoment B raw21442step1 raw21442step1Labels := by
      have ha : raw21442step1 = -raw21442step0 := by apply Matrix.ext; change ∀ i j, raw21442step1 i j = -(raw21442step0 i j); unfold raw21442step1 raw21442step0; decide +kernel
      have hl : raw21442step1Labels = raw21442step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21442step1 raw21442step1Labels = mixedMoment B raw21442step2 raw21442step2Labels := by
      have ha : raw21442step2 = raw21442step1 := by apply Matrix.ext; unfold raw21442step2 raw21442step1; decide +kernel
      have hl : raw21442step1Labels = labelEmbedding1 ∘ raw21442step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21442step1 raw21442step1Labels raw21442step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1663 node1663Labels := by rfl

theorem canonical21443 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21443 raw21443Labels = mixedMoment B node1725 node1725Labels := by
  calc
    mixedMoment B raw21443 raw21443Labels = mixedMoment B raw21443step0 raw21443step0Labels := by
      have hz : ∀ j, raw21443 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw21443step0 = (fun i j => raw21443 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw21443step0 raw21443; decide +kernel
      have hl : raw21443step0Labels = raw21443Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21443 raw21443Labels permutation520 hz
    mixedMoment B raw21443step0 raw21443step0Labels = mixedMoment B raw21443step1 raw21443step1Labels := by
      have hz : ∀ j, raw21443step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21443step1 = (fun i j => raw21443step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21443step1 raw21443step0; decide +kernel
      have hl : raw21443step1Labels = raw21443step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21443step0 raw21443step0Labels permutation80 hz
    mixedMoment B raw21443step1 raw21443step1Labels = mixedMoment B raw21443step2 raw21443step2Labels := by
      have ha : raw21443step2 = (fun i j => raw21443step1 (permutation10 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21443step2 raw21443step1; decide +kernel
      have hl : raw21443step2Labels = raw21443step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21443step1 raw21443step1Labels permutation10 permutation7
    mixedMoment B raw21443step2 raw21443step2Labels = mixedMoment B raw21443step3 raw21443step3Labels := by
      have ha : raw21443step3 = -raw21443step2 := by apply Matrix.ext; change ∀ i j, raw21443step3 i j = -(raw21443step2 i j); unfold raw21443step3 raw21443step2; decide +kernel
      have hl : raw21443step3Labels = raw21443step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21443step3 raw21443step3Labels = mixedMoment B raw21443step4 raw21443step4Labels := by
      have ha : raw21443step4 = raw21443step3 := by apply Matrix.ext; unfold raw21443step4 raw21443step3; decide +kernel
      have hl : raw21443step3Labels = labelEmbedding1 ∘ raw21443step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21443step3 raw21443step3Labels raw21443step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1725 node1725Labels := by rfl

theorem canonical21444 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21444 raw21444Labels = mixedMoment B node1707 node1707Labels := by
  calc
    mixedMoment B raw21444 raw21444Labels = mixedMoment B raw21444step0 raw21444step0Labels := by
      have hz : ∀ j, raw21444 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21444step0 = (fun i j => raw21444 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21444step0 raw21444; decide +kernel
      have hl : raw21444step0Labels = raw21444Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21444 raw21444Labels permutation346 hz
    mixedMoment B raw21444step0 raw21444step0Labels = mixedMoment B raw21444step1 raw21444step1Labels := by
      have ha : raw21444step1 = (fun i j => raw21444step0 (permutation40 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21444step1 raw21444step0; decide +kernel
      have hl : raw21444step1Labels = raw21444step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21444step0 raw21444step0Labels permutation40 permutation7
    mixedMoment B raw21444step1 raw21444step1Labels = mixedMoment B raw21444step2 raw21444step2Labels := by
      have ha : raw21444step2 = -raw21444step1 := by apply Matrix.ext; change ∀ i j, raw21444step2 i j = -(raw21444step1 i j); unfold raw21444step2 raw21444step1; decide +kernel
      have hl : raw21444step2Labels = raw21444step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21444step2 raw21444step2Labels = mixedMoment B raw21444step3 raw21444step3Labels := by
      have ha : raw21444step3 = raw21444step2 := by apply Matrix.ext; unfold raw21444step3 raw21444step2; decide +kernel
      have hl : raw21444step2Labels = labelEmbedding1 ∘ raw21444step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21444step2 raw21444step2Labels raw21444step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1707 node1707Labels := by rfl

theorem canonical21445 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21445 raw21445Labels = mixedMoment B node1523 node1523Labels := by
  calc
    mixedMoment B raw21445 raw21445Labels = mixedMoment B raw21445step0 raw21445step0Labels := by
      have hz : ∀ j, raw21445 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21445step0 = (fun i j => raw21445 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21445step0 raw21445; decide +kernel
      have hl : raw21445step0Labels = raw21445Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21445 raw21445Labels permutation434 hz
    mixedMoment B raw21445step0 raw21445step0Labels = mixedMoment B raw21445step1 raw21445step1Labels := by
      have hz : ∀ j, raw21445step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21445step1 = (fun i j => raw21445step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21445step1 raw21445step0; decide +kernel
      have hl : raw21445step1Labels = raw21445step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21445step0 raw21445step0Labels permutation80 hz
    mixedMoment B raw21445step1 raw21445step1Labels = mixedMoment B raw21445step2 raw21445step2Labels := by
      have ha : raw21445step2 = (fun i j => raw21445step1 (permutation10 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21445step2 raw21445step1; decide +kernel
      have hl : raw21445step2Labels = raw21445step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21445step1 raw21445step1Labels permutation10 permutation7
    mixedMoment B raw21445step2 raw21445step2Labels = mixedMoment B raw21445step3 raw21445step3Labels := by
      have ha : raw21445step3 = -raw21445step2 := by apply Matrix.ext; change ∀ i j, raw21445step3 i j = -(raw21445step2 i j); unfold raw21445step3 raw21445step2; decide +kernel
      have hl : raw21445step3Labels = raw21445step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21445step3 raw21445step3Labels = mixedMoment B raw21445step4 raw21445step4Labels := by
      have ha : raw21445step4 = raw21445step3 := by apply Matrix.ext; unfold raw21445step4 raw21445step3; decide +kernel
      have hl : raw21445step3Labels = labelEmbedding1 ∘ raw21445step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21445step3 raw21445step3Labels raw21445step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1523 node1523Labels := by rfl

theorem canonical21446 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21446 raw21446Labels = mixedMoment B node1735 node1735Labels := by
  calc
    mixedMoment B raw21446 raw21446Labels = mixedMoment B raw21446step0 raw21446step0Labels := by
      have hz : ∀ j, raw21446 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21446step0 = (fun i j => raw21446 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21446step0 raw21446; decide +kernel
      have hl : raw21446step0Labels = raw21446Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21446 raw21446Labels permutation434 hz
    mixedMoment B raw21446step0 raw21446step0Labels = mixedMoment B raw21446step1 raw21446step1Labels := by
      have hz : ∀ j, raw21446step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21446step1 = (fun i j => raw21446step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21446step1 raw21446step0; decide +kernel
      have hl : raw21446step1Labels = raw21446step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21446step0 raw21446step0Labels permutation80 hz
    mixedMoment B raw21446step1 raw21446step1Labels = mixedMoment B raw21446step2 raw21446step2Labels := by
      have ha : raw21446step2 = (fun i j => raw21446step1 (permutation10 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21446step2 raw21446step1; decide +kernel
      have hl : raw21446step2Labels = raw21446step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21446step1 raw21446step1Labels permutation10 permutation7
    mixedMoment B raw21446step2 raw21446step2Labels = mixedMoment B raw21446step3 raw21446step3Labels := by
      have ha : raw21446step3 = -raw21446step2 := by apply Matrix.ext; change ∀ i j, raw21446step3 i j = -(raw21446step2 i j); unfold raw21446step3 raw21446step2; decide +kernel
      have hl : raw21446step3Labels = raw21446step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21446step3 raw21446step3Labels = mixedMoment B raw21446step4 raw21446step4Labels := by
      have ha : raw21446step4 = raw21446step3 := by apply Matrix.ext; unfold raw21446step4 raw21446step3; decide +kernel
      have hl : raw21446step3Labels = labelEmbedding1 ∘ raw21446step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21446step3 raw21446step3Labels raw21446step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1735 node1735Labels := by rfl

theorem canonical21447 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21447 raw21447Labels = mixedMoment B node1679 node1679Labels := by
  calc
    mixedMoment B raw21447 raw21447Labels = mixedMoment B raw21447step0 raw21447step0Labels := by
      have hz : ∀ j, raw21447 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21447step0 = (fun i j => raw21447 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21447step0 raw21447; decide +kernel
      have hl : raw21447step0Labels = raw21447Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21447 raw21447Labels permutation434 hz
    mixedMoment B raw21447step0 raw21447step0Labels = mixedMoment B raw21447step1 raw21447step1Labels := by
      have ha : raw21447step1 = (fun i j => raw21447step0 (permutation40 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21447step1 raw21447step0; decide +kernel
      have hl : raw21447step1Labels = raw21447step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21447step0 raw21447step0Labels permutation40 permutation7
    mixedMoment B raw21447step1 raw21447step1Labels = mixedMoment B raw21447step2 raw21447step2Labels := by
      have ha : raw21447step2 = -raw21447step1 := by apply Matrix.ext; change ∀ i j, raw21447step2 i j = -(raw21447step1 i j); unfold raw21447step2 raw21447step1; decide +kernel
      have hl : raw21447step2Labels = raw21447step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21447step2 raw21447step2Labels = mixedMoment B raw21447step3 raw21447step3Labels := by
      have ha : raw21447step3 = raw21447step2 := by apply Matrix.ext; unfold raw21447step3 raw21447step2; decide +kernel
      have hl : raw21447step2Labels = labelEmbedding1 ∘ raw21447step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21447step2 raw21447step2Labels raw21447step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1679 node1679Labels := by rfl

theorem canonical21448 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21448 raw21448Labels = mixedMoment B node1679 node1679Labels := by
  calc
    mixedMoment B raw21448 raw21448Labels = mixedMoment B raw21448step0 raw21448step0Labels := by
      have hz : ∀ j, raw21448 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21448step0 = (fun i j => raw21448 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21448step0 raw21448; decide +kernel
      have hl : raw21448step0Labels = raw21448Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21448 raw21448Labels permutation346 hz
    mixedMoment B raw21448step0 raw21448step0Labels = mixedMoment B raw21448step1 raw21448step1Labels := by
      have ha : raw21448step1 = (fun i j => raw21448step0 (permutation40 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21448step1 raw21448step0; decide +kernel
      have hl : raw21448step1Labels = raw21448step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21448step0 raw21448step0Labels permutation40 permutation7
    mixedMoment B raw21448step1 raw21448step1Labels = mixedMoment B raw21448step2 raw21448step2Labels := by
      have ha : raw21448step2 = -raw21448step1 := by apply Matrix.ext; change ∀ i j, raw21448step2 i j = -(raw21448step1 i j); unfold raw21448step2 raw21448step1; decide +kernel
      have hl : raw21448step2Labels = raw21448step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21448step2 raw21448step2Labels = mixedMoment B raw21448step3 raw21448step3Labels := by
      have ha : raw21448step3 = raw21448step2 := by apply Matrix.ext; unfold raw21448step3 raw21448step2; decide +kernel
      have hl : raw21448step2Labels = labelEmbedding1 ∘ raw21448step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21448step2 raw21448step2Labels raw21448step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1679 node1679Labels := by rfl

theorem canonical21449 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21449 raw21449Labels = mixedMoment B node1738 node1738Labels := by
  calc
    mixedMoment B raw21449 raw21449Labels = mixedMoment B raw21449step0 raw21449step0Labels := by
      have hz : ∀ j, raw21449 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21449step0 = (fun i j => raw21449 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21449step0 raw21449; decide +kernel
      have hl : raw21449step0Labels = raw21449Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21449 raw21449Labels permutation434 hz
    mixedMoment B raw21449step0 raw21449step0Labels = mixedMoment B raw21449step1 raw21449step1Labels := by
      have hz : ∀ j, raw21449step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21449step1 = (fun i j => raw21449step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21449step1 raw21449step0; decide +kernel
      have hl : raw21449step1Labels = raw21449step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21449step0 raw21449step0Labels permutation80 hz
    mixedMoment B raw21449step1 raw21449step1Labels = mixedMoment B raw21449step2 raw21449step2Labels := by
      have ha : raw21449step2 = (fun i j => raw21449step1 (permutation10 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21449step2 raw21449step1; decide +kernel
      have hl : raw21449step2Labels = raw21449step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21449step1 raw21449step1Labels permutation10 permutation7
    mixedMoment B raw21449step2 raw21449step2Labels = mixedMoment B raw21449step3 raw21449step3Labels := by
      have ha : raw21449step3 = -raw21449step2 := by apply Matrix.ext; change ∀ i j, raw21449step3 i j = -(raw21449step2 i j); unfold raw21449step3 raw21449step2; decide +kernel
      have hl : raw21449step3Labels = raw21449step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21449step3 raw21449step3Labels = mixedMoment B raw21449step4 raw21449step4Labels := by
      have ha : raw21449step4 = raw21449step3 := by apply Matrix.ext; unfold raw21449step4 raw21449step3; decide +kernel
      have hl : raw21449step3Labels = labelEmbedding1 ∘ raw21449step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21449step3 raw21449step3Labels raw21449step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1738 node1738Labels := by rfl

theorem canonical21450 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21450 raw21450Labels = mixedMoment B node1516 node1516Labels := by
  calc
    mixedMoment B raw21450 raw21450Labels = mixedMoment B raw21450step0 raw21450step0Labels := by
      have hz : ∀ j, raw21450 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21450step0 = (fun i j => raw21450 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21450step0 raw21450; decide +kernel
      have hl : raw21450step0Labels = raw21450Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21450 raw21450Labels permutation434 hz
    mixedMoment B raw21450step0 raw21450step0Labels = mixedMoment B raw21450step1 raw21450step1Labels := by
      have hz : ∀ j, raw21450step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21450step1 = (fun i j => raw21450step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21450step1 raw21450step0; decide +kernel
      have hl : raw21450step1Labels = raw21450step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21450step0 raw21450step0Labels permutation80 hz
    mixedMoment B raw21450step1 raw21450step1Labels = mixedMoment B raw21450step2 raw21450step2Labels := by
      have ha : raw21450step2 = (fun i j => raw21450step1 (permutation10 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21450step2 raw21450step1; decide +kernel
      have hl : raw21450step2Labels = raw21450step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21450step1 raw21450step1Labels permutation10 permutation7
    mixedMoment B raw21450step2 raw21450step2Labels = mixedMoment B raw21450step3 raw21450step3Labels := by
      have ha : raw21450step3 = -raw21450step2 := by apply Matrix.ext; change ∀ i j, raw21450step3 i j = -(raw21450step2 i j); unfold raw21450step3 raw21450step2; decide +kernel
      have hl : raw21450step3Labels = raw21450step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21450step3 raw21450step3Labels = mixedMoment B raw21450step4 raw21450step4Labels := by
      have ha : raw21450step4 = raw21450step3 := by apply Matrix.ext; unfold raw21450step4 raw21450step3; decide +kernel
      have hl : raw21450step3Labels = labelEmbedding1 ∘ raw21450step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21450step3 raw21450step3Labels raw21450step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1516 node1516Labels := by rfl

theorem canonical21451 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21451 raw21451Labels = mixedMoment B node1722 node1722Labels := by
  calc
    mixedMoment B raw21451 raw21451Labels = mixedMoment B raw21451step0 raw21451step0Labels := by
      have hz : ∀ j, raw21451 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21451step0 = (fun i j => raw21451 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21451step0 raw21451; decide +kernel
      have hl : raw21451step0Labels = raw21451Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21451 raw21451Labels permutation434 hz
    mixedMoment B raw21451step0 raw21451step0Labels = mixedMoment B raw21451step1 raw21451step1Labels := by
      have hz : ∀ j, raw21451step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21451step1 = (fun i j => raw21451step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21451step1 raw21451step0; decide +kernel
      have hl : raw21451step1Labels = raw21451step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21451step0 raw21451step0Labels permutation80 hz
    mixedMoment B raw21451step1 raw21451step1Labels = mixedMoment B raw21451step2 raw21451step2Labels := by
      have ha : raw21451step2 = (fun i j => raw21451step1 (permutation10 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21451step2 raw21451step1; decide +kernel
      have hl : raw21451step2Labels = raw21451step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21451step1 raw21451step1Labels permutation10 permutation7
    mixedMoment B raw21451step2 raw21451step2Labels = mixedMoment B raw21451step3 raw21451step3Labels := by
      have ha : raw21451step3 = -raw21451step2 := by apply Matrix.ext; change ∀ i j, raw21451step3 i j = -(raw21451step2 i j); unfold raw21451step3 raw21451step2; decide +kernel
      have hl : raw21451step3Labels = raw21451step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21451step3 raw21451step3Labels = mixedMoment B raw21451step4 raw21451step4Labels := by
      have ha : raw21451step4 = raw21451step3 := by apply Matrix.ext; unfold raw21451step4 raw21451step3; decide +kernel
      have hl : raw21451step3Labels = labelEmbedding1 ∘ raw21451step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21451step3 raw21451step3Labels raw21451step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1722 node1722Labels := by rfl

theorem canonical21452 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21452 raw21452Labels = mixedMoment B node1672 node1672Labels := by
  calc
    mixedMoment B raw21452 raw21452Labels = mixedMoment B raw21452step0 raw21452step0Labels := by
      have hz : ∀ j, raw21452 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21452step0 = (fun i j => raw21452 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21452step0 raw21452; decide +kernel
      have hl : raw21452step0Labels = raw21452Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21452 raw21452Labels permutation434 hz
    mixedMoment B raw21452step0 raw21452step0Labels = mixedMoment B raw21452step1 raw21452step1Labels := by
      have ha : raw21452step1 = (fun i j => raw21452step0 (permutation40 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21452step1 raw21452step0; decide +kernel
      have hl : raw21452step1Labels = raw21452step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21452step0 raw21452step0Labels permutation40 permutation7
    mixedMoment B raw21452step1 raw21452step1Labels = mixedMoment B raw21452step2 raw21452step2Labels := by
      have ha : raw21452step2 = -raw21452step1 := by apply Matrix.ext; change ∀ i j, raw21452step2 i j = -(raw21452step1 i j); unfold raw21452step2 raw21452step1; decide +kernel
      have hl : raw21452step2Labels = raw21452step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21452step2 raw21452step2Labels = mixedMoment B raw21452step3 raw21452step3Labels := by
      have ha : raw21452step3 = raw21452step2 := by apply Matrix.ext; unfold raw21452step3 raw21452step2; decide +kernel
      have hl : raw21452step2Labels = labelEmbedding1 ∘ raw21452step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21452step2 raw21452step2Labels raw21452step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1672 node1672Labels := by rfl

theorem canonical21453 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21453 raw21453Labels = mixedMoment B node1672 node1672Labels := by
  calc
    mixedMoment B raw21453 raw21453Labels = mixedMoment B raw21453step0 raw21453step0Labels := by
      have hz : ∀ j, raw21453 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21453step0 = (fun i j => raw21453 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21453step0 raw21453; decide +kernel
      have hl : raw21453step0Labels = raw21453Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21453 raw21453Labels permutation346 hz
    mixedMoment B raw21453step0 raw21453step0Labels = mixedMoment B raw21453step1 raw21453step1Labels := by
      have ha : raw21453step1 = (fun i j => raw21453step0 (permutation40 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21453step1 raw21453step0; decide +kernel
      have hl : raw21453step1Labels = raw21453step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21453step0 raw21453step0Labels permutation40 permutation7
    mixedMoment B raw21453step1 raw21453step1Labels = mixedMoment B raw21453step2 raw21453step2Labels := by
      have ha : raw21453step2 = -raw21453step1 := by apply Matrix.ext; change ∀ i j, raw21453step2 i j = -(raw21453step1 i j); unfold raw21453step2 raw21453step1; decide +kernel
      have hl : raw21453step2Labels = raw21453step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21453step2 raw21453step2Labels = mixedMoment B raw21453step3 raw21453step3Labels := by
      have ha : raw21453step3 = raw21453step2 := by apply Matrix.ext; unfold raw21453step3 raw21453step2; decide +kernel
      have hl : raw21453step2Labels = labelEmbedding1 ∘ raw21453step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21453step2 raw21453step2Labels raw21453step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1672 node1672Labels := by rfl

theorem canonical21454 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21454 raw21454Labels = mixedMoment B node1752 node1752Labels := by
  calc
    mixedMoment B raw21454 raw21454Labels = mixedMoment B raw21454step0 raw21454step0Labels := by
      have hz : ∀ j, raw21454 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw21454step0 = (fun i j => raw21454 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw21454step0 raw21454; decide +kernel
      have hl : raw21454step0Labels = raw21454Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21454 raw21454Labels permutation520 hz
    mixedMoment B raw21454step0 raw21454step0Labels = mixedMoment B raw21454step1 raw21454step1Labels := by
      have hz : ∀ j, raw21454step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw21454step1 = (fun i j => raw21454step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw21454step1 raw21454step0; decide +kernel
      have hl : raw21454step1Labels = raw21454step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21454step0 raw21454step0Labels permutation104 hz
    mixedMoment B raw21454step1 raw21454step1Labels = mixedMoment B raw21454step2 raw21454step2Labels := by
      have hz : ∀ j, raw21454step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw21454step2 = (fun i j => raw21454step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw21454step2 raw21454step1; decide +kernel
      have hl : raw21454step2Labels = raw21454step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21454step1 raw21454step1Labels permutation20 hz
    mixedMoment B raw21454step2 raw21454step2Labels = mixedMoment B raw21454step3 raw21454step3Labels := by
      have ha : raw21454step3 = (fun i j => raw21454step2 (permutation2 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21454step3 raw21454step2; decide +kernel
      have hl : raw21454step3Labels = raw21454step2Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21454step2 raw21454step2Labels permutation2 permutation7
    mixedMoment B raw21454step3 raw21454step3Labels = mixedMoment B raw21454step4 raw21454step4Labels := by
      have ha : raw21454step4 = -raw21454step3 := by apply Matrix.ext; change ∀ i j, raw21454step4 i j = -(raw21454step3 i j); unfold raw21454step4 raw21454step3; decide +kernel
      have hl : raw21454step4Labels = raw21454step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21454step4 raw21454step4Labels = mixedMoment B raw21454step5 raw21454step5Labels := by
      have ha : raw21454step5 = raw21454step4 := by apply Matrix.ext; unfold raw21454step5 raw21454step4; decide +kernel
      have hl : raw21454step4Labels = labelEmbedding1 ∘ raw21454step5Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21454step4 raw21454step4Labels raw21454step5Labels labelEmbedding1 hl
    _ = mixedMoment B node1752 node1752Labels := by rfl

theorem canonical21455 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21455 raw21455Labels = mixedMoment B node1043 node1043Labels := by
  calc
    mixedMoment B raw21455 raw21455Labels = mixedMoment B raw21455step0 raw21455step0Labels := by
      have hz : ∀ j, raw21455 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21455step0 = (fun i j => raw21455 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21455step0 raw21455; decide +kernel
      have hl : raw21455step0Labels = raw21455Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21455 raw21455Labels permutation434 hz
    mixedMoment B raw21455step0 raw21455step0Labels = mixedMoment B raw21455step1 raw21455step1Labels := by
      have hz : ∀ j, raw21455step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21455step1 = (fun i j => raw21455step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21455step1 raw21455step0; decide +kernel
      have hl : raw21455step1Labels = raw21455step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21455step0 raw21455step0Labels permutation80 hz
    _ = mixedMoment B node1043 node1043Labels := by rfl

theorem canonical21456 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21456 raw21456Labels = mixedMoment B node605 node605Labels := by
  calc
    mixedMoment B raw21456 raw21456Labels = mixedMoment B raw21456step0 raw21456step0Labels := by
      have hz : ∀ j, raw21456 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21456step0 = (fun i j => raw21456 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21456step0 raw21456; decide +kernel
      have hl : raw21456step0Labels = raw21456Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21456 raw21456Labels permutation434 hz
    mixedMoment B raw21456step0 raw21456step0Labels = mixedMoment B raw21456step1 raw21456step1Labels := by
      have hz : ∀ j, raw21456step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21456step1 = (fun i j => raw21456step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21456step1 raw21456step0; decide +kernel
      have hl : raw21456step1Labels = raw21456step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21456step0 raw21456step0Labels permutation80 hz
    mixedMoment B raw21456step1 raw21456step1Labels = mixedMoment B raw21456step2 raw21456step2Labels := by
      have ha : raw21456step2 = (fun i j => raw21456step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21456step2 raw21456step1; decide +kernel
      have hl : raw21456step2Labels = raw21456step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21456step1 raw21456step1Labels permutation10 permutation2
    _ = mixedMoment B node605 node605Labels := by rfl

theorem canonical21457 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21457 raw21457Labels = mixedMoment B node579 node579Labels := by
  calc
    mixedMoment B raw21457 raw21457Labels = mixedMoment B raw21457step0 raw21457step0Labels := by
      have hz : ∀ j, raw21457 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21457step0 = (fun i j => raw21457 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21457step0 raw21457; decide +kernel
      have hl : raw21457step0Labels = raw21457Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21457 raw21457Labels permutation434 hz
    _ = mixedMoment B node579 node579Labels := by rfl

theorem canonical21458 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21458 raw21458Labels = mixedMoment B node579 node579Labels := by
  calc
    mixedMoment B raw21458 raw21458Labels = mixedMoment B raw21458step0 raw21458step0Labels := by
      have hz : ∀ j, raw21458 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21458step0 = (fun i j => raw21458 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21458step0 raw21458; decide +kernel
      have hl : raw21458step0Labels = raw21458Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21458 raw21458Labels permutation346 hz
    _ = mixedMoment B node579 node579Labels := by rfl

theorem canonical21459 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21459 raw21459Labels = mixedMoment B node588 node588Labels := by
  calc
    mixedMoment B raw21459 raw21459Labels = mixedMoment B raw21459step0 raw21459step0Labels := by
      have hz : ∀ j, raw21459 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21459step0 = (fun i j => raw21459 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21459step0 raw21459; decide +kernel
      have hl : raw21459step0Labels = raw21459Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21459 raw21459Labels permutation434 hz
    mixedMoment B raw21459step0 raw21459step0Labels = mixedMoment B raw21459step1 raw21459step1Labels := by
      have hz : ∀ j, raw21459step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21459step1 = (fun i j => raw21459step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21459step1 raw21459step0; decide +kernel
      have hl : raw21459step1Labels = raw21459step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21459step0 raw21459step0Labels permutation80 hz
    _ = mixedMoment B node588 node588Labels := by rfl

theorem canonical21460 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21460 raw21460Labels = mixedMoment B node584 node584Labels := by
  calc
    mixedMoment B raw21460 raw21460Labels = mixedMoment B raw21460step0 raw21460step0Labels := by
      have hz : ∀ j, raw21460 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21460step0 = (fun i j => raw21460 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21460step0 raw21460; decide +kernel
      have hl : raw21460step0Labels = raw21460Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21460 raw21460Labels permutation434 hz
    mixedMoment B raw21460step0 raw21460step0Labels = mixedMoment B raw21460step1 raw21460step1Labels := by
      have hz : ∀ j, raw21460step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21460step1 = (fun i j => raw21460step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21460step1 raw21460step0; decide +kernel
      have hl : raw21460step1Labels = raw21460step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21460step0 raw21460step0Labels permutation80 hz
    _ = mixedMoment B node584 node584Labels := by rfl

theorem canonical21461 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21461 raw21461Labels = mixedMoment B node4084 node4084Labels := by
  calc
    mixedMoment B raw21461 raw21461Labels = mixedMoment B raw21461step0 raw21461step0Labels := by
      have hz : ∀ j, raw21461 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw21461step0 = (fun i j => raw21461 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw21461step0 raw21461; decide +kernel
      have hl : raw21461step0Labels = raw21461Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21461 raw21461Labels permutation520 hz
    mixedMoment B raw21461step0 raw21461step0Labels = mixedMoment B raw21461step1 raw21461step1Labels := by
      have hz : ∀ j, raw21461step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw21461step1 = (fun i j => raw21461step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw21461step1 raw21461step0; decide +kernel
      have hl : raw21461step1Labels = raw21461step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21461step0 raw21461step0Labels permutation104 hz
    mixedMoment B raw21461step1 raw21461step1Labels = mixedMoment B raw21461step2 raw21461step2Labels := by
      have hz : ∀ j, raw21461step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw21461step2 = (fun i j => raw21461step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw21461step2 raw21461step1; decide +kernel
      have hl : raw21461step2Labels = raw21461step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21461step1 raw21461step1Labels permutation20 hz
    _ = mixedMoment B node4084 node4084Labels := by rfl

theorem canonical21462 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21462 raw21462Labels = mixedMoment B node924 node924Labels := by
  calc
    mixedMoment B raw21462 raw21462Labels = mixedMoment B raw21462step0 raw21462step0Labels := by
      have hz : ∀ j, raw21462 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21462step0 = (fun i j => raw21462 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21462step0 raw21462; decide +kernel
      have hl : raw21462step0Labels = raw21462Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21462 raw21462Labels permutation434 hz
    mixedMoment B raw21462step0 raw21462step0Labels = mixedMoment B raw21462step1 raw21462step1Labels := by
      have ha : raw21462step1 = (fun i j => raw21462step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21462step1 raw21462step0; decide +kernel
      have hl : raw21462step1Labels = raw21462step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21462step0 raw21462step0Labels permutation40 permutation2
    _ = mixedMoment B node924 node924Labels := by rfl

theorem canonical21463 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21463 raw21463Labels = mixedMoment B node924 node924Labels := by
  calc
    mixedMoment B raw21463 raw21463Labels = mixedMoment B raw21463step0 raw21463step0Labels := by
      have hz : ∀ j, raw21463 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21463step0 = (fun i j => raw21463 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21463step0 raw21463; decide +kernel
      have hl : raw21463step0Labels = raw21463Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21463 raw21463Labels permutation346 hz
    mixedMoment B raw21463step0 raw21463step0Labels = mixedMoment B raw21463step1 raw21463step1Labels := by
      have ha : raw21463step1 = (fun i j => raw21463step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21463step1 raw21463step0; decide +kernel
      have hl : raw21463step1Labels = raw21463step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21463step0 raw21463step0Labels permutation40 permutation2
    _ = mixedMoment B node924 node924Labels := by rfl

theorem canonical21464 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21464 raw21464Labels = mixedMoment B node1089 node1089Labels := by
  calc
    mixedMoment B raw21464 raw21464Labels = mixedMoment B raw21464step0 raw21464step0Labels := by
      have hz : ∀ j, raw21464 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw21464step0 = (fun i j => raw21464 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw21464step0 raw21464; decide +kernel
      have hl : raw21464step0Labels = raw21464Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21464 raw21464Labels permutation520 hz
    mixedMoment B raw21464step0 raw21464step0Labels = mixedMoment B raw21464step1 raw21464step1Labels := by
      have hz : ∀ j, raw21464step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw21464step1 = (fun i j => raw21464step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw21464step1 raw21464step0; decide +kernel
      have hl : raw21464step1Labels = raw21464step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21464step0 raw21464step0Labels permutation104 hz
    mixedMoment B raw21464step1 raw21464step1Labels = mixedMoment B raw21464step2 raw21464step2Labels := by
      have hz : ∀ j, raw21464step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw21464step2 = (fun i j => raw21464step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw21464step2 raw21464step1; decide +kernel
      have hl : raw21464step2Labels = raw21464step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21464step1 raw21464step1Labels permutation20 hz
    _ = mixedMoment B node1089 node1089Labels := by rfl

theorem canonical21465 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21465 raw21465Labels = mixedMoment B node1082 node1082Labels := by
  calc
    mixedMoment B raw21465 raw21465Labels = mixedMoment B raw21465step0 raw21465step0Labels := by
      have hz : ∀ j, raw21465 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21465step0 = (fun i j => raw21465 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21465step0 raw21465; decide +kernel
      have hl : raw21465step0Labels = raw21465Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21465 raw21465Labels permutation434 hz
    mixedMoment B raw21465step0 raw21465step0Labels = mixedMoment B raw21465step1 raw21465step1Labels := by
      have hz : ∀ j, raw21465step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21465step1 = (fun i j => raw21465step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21465step1 raw21465step0; decide +kernel
      have hl : raw21465step1Labels = raw21465step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21465step0 raw21465step0Labels permutation80 hz
    mixedMoment B raw21465step1 raw21465step1Labels = mixedMoment B raw21465step2 raw21465step2Labels := by
      have ha : raw21465step2 = (fun i j => raw21465step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21465step2 raw21465step1; decide +kernel
      have hl : raw21465step2Labels = raw21465step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21465step1 raw21465step1Labels permutation10 permutation2
    _ = mixedMoment B node1082 node1082Labels := by rfl

theorem canonical21466 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21466 raw21466Labels = mixedMoment B node2109 node2109Labels := by
  calc
    mixedMoment B raw21466 raw21466Labels = mixedMoment B raw21466step0 raw21466step0Labels := by
      have hz : ∀ j, raw21466 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21466step0 = (fun i j => raw21466 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21466step0 raw21466; decide +kernel
      have hl : raw21466step0Labels = raw21466Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21466 raw21466Labels permutation434 hz
    mixedMoment B raw21466step0 raw21466step0Labels = mixedMoment B raw21466step1 raw21466step1Labels := by
      have hz : ∀ j, raw21466step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21466step1 = (fun i j => raw21466step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21466step1 raw21466step0; decide +kernel
      have hl : raw21466step1Labels = raw21466step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21466step0 raw21466step0Labels permutation80 hz
    _ = mixedMoment B node2109 node2109Labels := by rfl

theorem canonical21467 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21467 raw21467Labels = mixedMoment B node943 node943Labels := by
  calc
    mixedMoment B raw21467 raw21467Labels = mixedMoment B raw21467step0 raw21467step0Labels := by
      have hz : ∀ j, raw21467 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21467step0 = (fun i j => raw21467 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21467step0 raw21467; decide +kernel
      have hl : raw21467step0Labels = raw21467Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21467 raw21467Labels permutation434 hz
    _ = mixedMoment B node943 node943Labels := by rfl

theorem canonical21468 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21468 raw21468Labels = mixedMoment B node943 node943Labels := by
  calc
    mixedMoment B raw21468 raw21468Labels = mixedMoment B raw21468step0 raw21468step0Labels := by
      have hz : ∀ j, raw21468 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21468step0 = (fun i j => raw21468 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21468step0 raw21468; decide +kernel
      have hl : raw21468step0Labels = raw21468Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21468 raw21468Labels permutation346 hz
    _ = mixedMoment B node943 node943Labels := by rfl

theorem canonical21469 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21469 raw21469Labels = mixedMoment B node952 node952Labels := by
  calc
    mixedMoment B raw21469 raw21469Labels = mixedMoment B raw21469step0 raw21469step0Labels := by
      have hz : ∀ j, raw21469 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21469step0 = (fun i j => raw21469 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21469step0 raw21469; decide +kernel
      have hl : raw21469step0Labels = raw21469Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21469 raw21469Labels permutation434 hz
    mixedMoment B raw21469step0 raw21469step0Labels = mixedMoment B raw21469step1 raw21469step1Labels := by
      have hz : ∀ j, raw21469step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21469step1 = (fun i j => raw21469step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21469step1 raw21469step0; decide +kernel
      have hl : raw21469step1Labels = raw21469step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21469step0 raw21469step0Labels permutation80 hz
    _ = mixedMoment B node952 node952Labels := by rfl

theorem canonical21470 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21470 raw21470Labels = mixedMoment B node948 node948Labels := by
  calc
    mixedMoment B raw21470 raw21470Labels = mixedMoment B raw21470step0 raw21470step0Labels := by
      have hz : ∀ j, raw21470 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21470step0 = (fun i j => raw21470 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21470step0 raw21470; decide +kernel
      have hl : raw21470step0Labels = raw21470Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21470 raw21470Labels permutation434 hz
    mixedMoment B raw21470step0 raw21470step0Labels = mixedMoment B raw21470step1 raw21470step1Labels := by
      have hz : ∀ j, raw21470step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21470step1 = (fun i j => raw21470step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21470step1 raw21470step0; decide +kernel
      have hl : raw21470step1Labels = raw21470step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21470step0 raw21470step0Labels permutation80 hz
    _ = mixedMoment B node948 node948Labels := by rfl

theorem canonical21471 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21471 raw21471Labels = mixedMoment B node904 node904Labels := by
  calc
    mixedMoment B raw21471 raw21471Labels = mixedMoment B raw21471step0 raw21471step0Labels := by
      have ha : raw21471step0 = (fun i j => raw21471 (permutation200 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21471step0 raw21471; decide +kernel
      have hl : raw21471step0Labels = raw21471Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21471 raw21471Labels permutation200 permutation2
    _ = mixedMoment B node904 node904Labels := by rfl

theorem canonical21472 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21472 raw21472Labels = mixedMoment B node1043 node1043Labels := by
  calc
    mixedMoment B raw21472 raw21472Labels = mixedMoment B raw21472step0 raw21472step0Labels := by
      have hz : ∀ j, raw21472 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw21472step0 = (fun i j => raw21472 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw21472step0 raw21472; decide +kernel
      have hl : raw21472step0Labels = raw21472Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21472 raw21472Labels permutation520 hz
    mixedMoment B raw21472step0 raw21472step0Labels = mixedMoment B raw21472step1 raw21472step1Labels := by
      have hz : ∀ j, raw21472step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw21472step1 = (fun i j => raw21472step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw21472step1 raw21472step0; decide +kernel
      have hl : raw21472step1Labels = raw21472step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21472step0 raw21472step0Labels permutation104 hz
    _ = mixedMoment B node1043 node1043Labels := by rfl

theorem canonical21473 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21473 raw21473Labels = mixedMoment B node1040 node1040Labels := by
  calc
    mixedMoment B raw21473 raw21473Labels = mixedMoment B raw21473step0 raw21473step0Labels := by
      have hz : ∀ j, raw21473 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21473step0 = (fun i j => raw21473 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21473step0 raw21473; decide +kernel
      have hl : raw21473step0Labels = raw21473Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21473 raw21473Labels permutation434 hz
    _ = mixedMoment B node1040 node1040Labels := by rfl

theorem canonical21474 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21474 raw21474Labels = mixedMoment B node2022 node2022Labels := by
  calc
    mixedMoment B raw21474 raw21474Labels = mixedMoment B raw21474step0 raw21474step0Labels := by
      have hz : ∀ j, raw21474 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21474step0 = (fun i j => raw21474 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21474step0 raw21474; decide +kernel
      have hl : raw21474step0Labels = raw21474Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21474 raw21474Labels permutation434 hz
    mixedMoment B raw21474step0 raw21474step0Labels = mixedMoment B raw21474step1 raw21474step1Labels := by
      have ha : raw21474step1 = (fun i j => raw21474step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21474step1 raw21474step0; decide +kernel
      have hl : raw21474step1Labels = raw21474step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21474step0 raw21474step0Labels permutation38 permutation2
    _ = mixedMoment B node2022 node2022Labels := by rfl

theorem canonical21475 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21475 raw21475Labels = mixedMoment B node904 node904Labels := by
  calc
    mixedMoment B raw21475 raw21475Labels = mixedMoment B raw21475step0 raw21475step0Labels := by
      have ha : raw21475step0 = (fun i j => raw21475 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21475step0 raw21475; decide +kernel
      have hl : raw21475step0Labels = raw21475Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21475 raw21475Labels permutation176 permutation2
    _ = mixedMoment B node904 node904Labels := by rfl

theorem canonical21476 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21476 raw21476Labels = mixedMoment B node912 node912Labels := by
  calc
    mixedMoment B raw21476 raw21476Labels = mixedMoment B raw21476step0 raw21476step0Labels := by
      have hz : ∀ j, raw21476 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21476step0 = (fun i j => raw21476 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21476step0 raw21476; decide +kernel
      have hl : raw21476step0Labels = raw21476Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21476 raw21476Labels permutation434 hz
    mixedMoment B raw21476step0 raw21476step0Labels = mixedMoment B raw21476step1 raw21476step1Labels := by
      have ha : raw21476step1 = (fun i j => raw21476step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21476step1 raw21476step0; decide +kernel
      have hl : raw21476step1Labels = raw21476step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21476step0 raw21476step0Labels permutation38 permutation2
    _ = mixedMoment B node912 node912Labels := by rfl

theorem canonical21477 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21477 raw21477Labels = mixedMoment B node908 node908Labels := by
  calc
    mixedMoment B raw21477 raw21477Labels = mixedMoment B raw21477step0 raw21477step0Labels := by
      have hz : ∀ j, raw21477 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21477step0 = (fun i j => raw21477 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21477step0 raw21477; decide +kernel
      have hl : raw21477step0Labels = raw21477Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21477 raw21477Labels permutation434 hz
    mixedMoment B raw21477step0 raw21477step0Labels = mixedMoment B raw21477step1 raw21477step1Labels := by
      have ha : raw21477step1 = (fun i j => raw21477step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21477step1 raw21477step0; decide +kernel
      have hl : raw21477step1Labels = raw21477step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21477step0 raw21477step0Labels permutation38 permutation2
    _ = mixedMoment B node908 node908Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical168
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical21563 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21563 raw21563Labels = mixedMoment B node1037 node1037Labels := by
  calc
    mixedMoment B raw21563 raw21563Labels = mixedMoment B raw21563step0 raw21563step0Labels := by
      have hz : ∀ j, raw21563 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21563step0 = (fun i j => raw21563 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21563step0 raw21563; decide +kernel
      have hl : raw21563step0Labels = raw21563Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21563 raw21563Labels permutation434 hz
    mixedMoment B raw21563step0 raw21563step0Labels = mixedMoment B raw21563step1 raw21563step1Labels := by
      have hz : ∀ j, raw21563step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21563step1 = (fun i j => raw21563step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21563step1 raw21563step0; decide +kernel
      have hl : raw21563step1Labels = raw21563step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21563step0 raw21563step0Labels permutation80 hz
    _ = mixedMoment B node1037 node1037Labels := by rfl

theorem canonical21564 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21564 raw21564Labels = mixedMoment B node2103 node2103Labels := by
  calc
    mixedMoment B raw21564 raw21564Labels = mixedMoment B raw21564step0 raw21564step0Labels := by
      have hz : ∀ j, raw21564 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21564step0 = (fun i j => raw21564 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21564step0 raw21564; decide +kernel
      have hl : raw21564step0Labels = raw21564Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21564 raw21564Labels permutation434 hz
    mixedMoment B raw21564step0 raw21564step0Labels = mixedMoment B raw21564step1 raw21564step1Labels := by
      have hz : ∀ j, raw21564step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21564step1 = (fun i j => raw21564step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21564step1 raw21564step0; decide +kernel
      have hl : raw21564step1Labels = raw21564step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21564step0 raw21564step0Labels permutation80 hz
    _ = mixedMoment B node2103 node2103Labels := by rfl

theorem canonical21565 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21565 raw21565Labels = mixedMoment B node2018 node2018Labels := by
  calc
    mixedMoment B raw21565 raw21565Labels = mixedMoment B raw21565step0 raw21565step0Labels := by
      have hz : ∀ j, raw21565 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21565step0 = (fun i j => raw21565 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21565step0 raw21565; decide +kernel
      have hl : raw21565step0Labels = raw21565Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21565 raw21565Labels permutation434 hz
    mixedMoment B raw21565step0 raw21565step0Labels = mixedMoment B raw21565step1 raw21565step1Labels := by
      have ha : raw21565step1 = (fun i j => raw21565step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21565step1 raw21565step0; decide +kernel
      have hl : raw21565step1Labels = raw21565step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21565step0 raw21565step0Labels permutation38 permutation2
    _ = mixedMoment B node2018 node2018Labels := by rfl

theorem canonical21566 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21566 raw21566Labels = mixedMoment B node2018 node2018Labels := by
  calc
    mixedMoment B raw21566 raw21566Labels = mixedMoment B raw21566step0 raw21566step0Labels := by
      have hz : ∀ j, raw21566 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21566step0 = (fun i j => raw21566 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21566step0 raw21566; decide +kernel
      have hl : raw21566step0Labels = raw21566Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21566 raw21566Labels permutation346 hz
    mixedMoment B raw21566step0 raw21566step0Labels = mixedMoment B raw21566step1 raw21566step1Labels := by
      have ha : raw21566step1 = (fun i j => raw21566step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21566step1 raw21566step0; decide +kernel
      have hl : raw21566step1Labels = raw21566step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21566step0 raw21566step0Labels permutation38 permutation2
    _ = mixedMoment B node2018 node2018Labels := by rfl

theorem canonical21567 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21567 raw21567Labels = mixedMoment B node2261 node2261Labels := by
  calc
    mixedMoment B raw21567 raw21567Labels = mixedMoment B raw21567step0 raw21567step0Labels := by
      have hz : ∀ j, raw21567 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21567step0 = (fun i j => raw21567 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21567step0 raw21567; decide +kernel
      have hl : raw21567step0Labels = raw21567Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21567 raw21567Labels permutation434 hz
    mixedMoment B raw21567step0 raw21567step0Labels = mixedMoment B raw21567step1 raw21567step1Labels := by
      have hz : ∀ j, raw21567step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21567step1 = (fun i j => raw21567step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21567step1 raw21567step0; decide +kernel
      have hl : raw21567step1Labels = raw21567step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21567step0 raw21567step0Labels permutation80 hz
    _ = mixedMoment B node2261 node2261Labels := by rfl

theorem canonical21568 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21568 raw21568Labels = mixedMoment B node594 node594Labels := by
  calc
    mixedMoment B raw21568 raw21568Labels = mixedMoment B raw21568step0 raw21568step0Labels := by
      have hz : ∀ j, raw21568 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21568step0 = (fun i j => raw21568 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21568step0 raw21568; decide +kernel
      have hl : raw21568step0Labels = raw21568Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21568 raw21568Labels permutation434 hz
    mixedMoment B raw21568step0 raw21568step0Labels = mixedMoment B raw21568step1 raw21568step1Labels := by
      have hz : ∀ j, raw21568step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21568step1 = (fun i j => raw21568step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21568step1 raw21568step0; decide +kernel
      have hl : raw21568step1Labels = raw21568step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21568step0 raw21568step0Labels permutation80 hz
    mixedMoment B raw21568step1 raw21568step1Labels = mixedMoment B raw21568step2 raw21568step2Labels := by
      have ha : raw21568step2 = (fun i j => raw21568step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21568step2 raw21568step1; decide +kernel
      have hl : raw21568step2Labels = raw21568step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21568step1 raw21568step1Labels permutation10 permutation2
    _ = mixedMoment B node594 node594Labels := by rfl

theorem canonical21569 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21569 raw21569Labels = mixedMoment B node916 node916Labels := by
  calc
    mixedMoment B raw21569 raw21569Labels = mixedMoment B raw21569step0 raw21569step0Labels := by
      have hz : ∀ j, raw21569 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21569step0 = (fun i j => raw21569 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21569step0 raw21569; decide +kernel
      have hl : raw21569step0Labels = raw21569Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21569 raw21569Labels permutation434 hz
    mixedMoment B raw21569step0 raw21569step0Labels = mixedMoment B raw21569step1 raw21569step1Labels := by
      have ha : raw21569step1 = (fun i j => raw21569step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21569step1 raw21569step0; decide +kernel
      have hl : raw21569step1Labels = raw21569step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21569step0 raw21569step0Labels permutation40 permutation2
    _ = mixedMoment B node916 node916Labels := by rfl

theorem canonical21570 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21570 raw21570Labels = mixedMoment B node916 node916Labels := by
  calc
    mixedMoment B raw21570 raw21570Labels = mixedMoment B raw21570step0 raw21570step0Labels := by
      have hz : ∀ j, raw21570 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21570step0 = (fun i j => raw21570 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21570step0 raw21570; decide +kernel
      have hl : raw21570step0Labels = raw21570Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21570 raw21570Labels permutation346 hz
    mixedMoment B raw21570step0 raw21570step0Labels = mixedMoment B raw21570step1 raw21570step1Labels := by
      have ha : raw21570step1 = (fun i j => raw21570step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21570step1 raw21570step0; decide +kernel
      have hl : raw21570step1Labels = raw21570step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21570step0 raw21570step0Labels permutation40 permutation2
    _ = mixedMoment B node916 node916Labels := by rfl

theorem canonical21571 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21571 raw21571Labels = mixedMoment B node1074 node1074Labels := by
  calc
    mixedMoment B raw21571 raw21571Labels = mixedMoment B raw21571step0 raw21571step0Labels := by
      have hz : ∀ j, raw21571 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21571step0 = (fun i j => raw21571 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21571step0 raw21571; decide +kernel
      have hl : raw21571step0Labels = raw21571Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21571 raw21571Labels permutation434 hz
    mixedMoment B raw21571step0 raw21571step0Labels = mixedMoment B raw21571step1 raw21571step1Labels := by
      have hz : ∀ j, raw21571step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21571step1 = (fun i j => raw21571step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21571step1 raw21571step0; decide +kernel
      have hl : raw21571step1Labels = raw21571step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21571step0 raw21571step0Labels permutation80 hz
    mixedMoment B raw21571step1 raw21571step1Labels = mixedMoment B raw21571step2 raw21571step2Labels := by
      have ha : raw21571step2 = (fun i j => raw21571step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21571step2 raw21571step1; decide +kernel
      have hl : raw21571step2Labels = raw21571step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21571step1 raw21571step1Labels permutation10 permutation2
    _ = mixedMoment B node1074 node1074Labels := by rfl

theorem canonical21572 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21572 raw21572Labels = mixedMoment B node1033 node1033Labels := by
  calc
    mixedMoment B raw21572 raw21572Labels = mixedMoment B raw21572step0 raw21572step0Labels := by
      have hz : ∀ j, raw21572 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21572step0 = (fun i j => raw21572 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21572step0 raw21572; decide +kernel
      have hl : raw21572step0Labels = raw21572Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21572 raw21572Labels permutation434 hz
    mixedMoment B raw21572step0 raw21572step0Labels = mixedMoment B raw21572step1 raw21572step1Labels := by
      have ha : raw21572step1 = (fun i j => raw21572step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21572step1 raw21572step0; decide +kernel
      have hl : raw21572step1Labels = raw21572step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21572step0 raw21572step0Labels permutation34 permutation2
    _ = mixedMoment B node1033 node1033Labels := by rfl

theorem canonical21573 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21573 raw21573Labels = mixedMoment B node1033 node1033Labels := by
  calc
    mixedMoment B raw21573 raw21573Labels = mixedMoment B raw21573step0 raw21573step0Labels := by
      have hz : ∀ j, raw21573 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21573step0 = (fun i j => raw21573 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21573step0 raw21573; decide +kernel
      have hl : raw21573step0Labels = raw21573Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21573 raw21573Labels permutation346 hz
    mixedMoment B raw21573step0 raw21573step0Labels = mixedMoment B raw21573step1 raw21573step1Labels := by
      have ha : raw21573step1 = (fun i j => raw21573step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21573step1 raw21573step0; decide +kernel
      have hl : raw21573step1Labels = raw21573step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21573step0 raw21573step0Labels permutation34 permutation2
    _ = mixedMoment B node1033 node1033Labels := by rfl

theorem canonical21574 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21574 raw21574Labels = mixedMoment B node1048 node1048Labels := by
  calc
    mixedMoment B raw21574 raw21574Labels = mixedMoment B raw21574step0 raw21574step0Labels := by
      have hz : ∀ j, raw21574 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21574step0 = (fun i j => raw21574 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21574step0 raw21574; decide +kernel
      have hl : raw21574step0Labels = raw21574Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21574 raw21574Labels permutation434 hz
    mixedMoment B raw21574step0 raw21574step0Labels = mixedMoment B raw21574step1 raw21574step1Labels := by
      have hz : ∀ j, raw21574step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21574step1 = (fun i j => raw21574step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21574step1 raw21574step0; decide +kernel
      have hl : raw21574step1Labels = raw21574step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21574step0 raw21574step0Labels permutation80 hz
    _ = mixedMoment B node1048 node1048Labels := by rfl

theorem canonical21575 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21575 raw21575Labels = mixedMoment B node741 node741Labels := by
  calc
    mixedMoment B raw21575 raw21575Labels = mixedMoment B raw21575step0 raw21575step0Labels := by
      have hz : ∀ j, raw21575 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21575step0 = (fun i j => raw21575 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21575step0 raw21575; decide +kernel
      have hl : raw21575step0Labels = raw21575Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21575 raw21575Labels permutation434 hz
    mixedMoment B raw21575step0 raw21575step0Labels = mixedMoment B raw21575step1 raw21575step1Labels := by
      have hz : ∀ j, raw21575step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21575step1 = (fun i j => raw21575step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21575step1 raw21575step0; decide +kernel
      have hl : raw21575step1Labels = raw21575step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21575step0 raw21575step0Labels permutation80 hz
    mixedMoment B raw21575step1 raw21575step1Labels = mixedMoment B raw21575step2 raw21575step2Labels := by
      have ha : raw21575step2 = (fun i j => raw21575step1 (permutation10 i) (permutation4 j)) := by apply Matrix.ext; unfold raw21575step2 raw21575step1; decide +kernel
      have hl : raw21575step2Labels = raw21575step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21575step1 raw21575step1Labels permutation10 permutation4
    mixedMoment B raw21575step2 raw21575step2Labels = mixedMoment B raw21575step3 raw21575step3Labels := by
      have ha : raw21575step3 = -raw21575step2 := by apply Matrix.ext; change ∀ i j, raw21575step3 i j = -(raw21575step2 i j); unfold raw21575step3 raw21575step2; decide +kernel
      have hl : raw21575step3Labels = raw21575step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node741 node741Labels := by rfl

theorem canonical21576 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21576 raw21576Labels = mixedMoment B node731 node731Labels := by
  calc
    mixedMoment B raw21576 raw21576Labels = mixedMoment B raw21576step0 raw21576step0Labels := by
      have hz : ∀ j, raw21576 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21576step0 = (fun i j => raw21576 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21576step0 raw21576; decide +kernel
      have hl : raw21576step0Labels = raw21576Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21576 raw21576Labels permutation434 hz
    mixedMoment B raw21576step0 raw21576step0Labels = mixedMoment B raw21576step1 raw21576step1Labels := by
      have ha : raw21576step1 = (fun i j => raw21576step0 (permutation44 i) (permutation4 j)) := by apply Matrix.ext; unfold raw21576step1 raw21576step0; decide +kernel
      have hl : raw21576step1Labels = raw21576step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21576step0 raw21576step0Labels permutation44 permutation4
    mixedMoment B raw21576step1 raw21576step1Labels = mixedMoment B raw21576step2 raw21576step2Labels := by
      have ha : raw21576step2 = -raw21576step1 := by apply Matrix.ext; change ∀ i j, raw21576step2 i j = -(raw21576step1 i j); unfold raw21576step2 raw21576step1; decide +kernel
      have hl : raw21576step2Labels = raw21576step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node731 node731Labels := by rfl

theorem canonical21577 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21577 raw21577Labels = mixedMoment B node731 node731Labels := by
  calc
    mixedMoment B raw21577 raw21577Labels = mixedMoment B raw21577step0 raw21577step0Labels := by
      have hz : ∀ j, raw21577 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21577step0 = (fun i j => raw21577 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21577step0 raw21577; decide +kernel
      have hl : raw21577step0Labels = raw21577Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21577 raw21577Labels permutation346 hz
    mixedMoment B raw21577step0 raw21577step0Labels = mixedMoment B raw21577step1 raw21577step1Labels := by
      have ha : raw21577step1 = (fun i j => raw21577step0 (permutation44 i) (permutation4 j)) := by apply Matrix.ext; unfold raw21577step1 raw21577step0; decide +kernel
      have hl : raw21577step1Labels = raw21577step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21577step0 raw21577step0Labels permutation44 permutation4
    mixedMoment B raw21577step1 raw21577step1Labels = mixedMoment B raw21577step2 raw21577step2Labels := by
      have ha : raw21577step2 = -raw21577step1 := by apply Matrix.ext; change ∀ i j, raw21577step2 i j = -(raw21577step1 i j); unfold raw21577step2 raw21577step1; decide +kernel
      have hl : raw21577step2Labels = raw21577step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node731 node731Labels := by rfl

theorem canonical21578 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21578 raw21578Labels = mixedMoment B node809 node809Labels := by
  calc
    mixedMoment B raw21578 raw21578Labels = mixedMoment B raw21578step0 raw21578step0Labels := by
      have hz : ∀ j, raw21578 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21578step0 = (fun i j => raw21578 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21578step0 raw21578; decide +kernel
      have hl : raw21578step0Labels = raw21578Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21578 raw21578Labels permutation434 hz
    mixedMoment B raw21578step0 raw21578step0Labels = mixedMoment B raw21578step1 raw21578step1Labels := by
      have hz : ∀ j, raw21578step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21578step1 = (fun i j => raw21578step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21578step1 raw21578step0; decide +kernel
      have hl : raw21578step1Labels = raw21578step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21578step0 raw21578step0Labels permutation80 hz
    mixedMoment B raw21578step1 raw21578step1Labels = mixedMoment B raw21578step2 raw21578step2Labels := by
      have ha : raw21578step2 = (fun i j => raw21578step1 (permutation10 i) (permutation4 j)) := by apply Matrix.ext; unfold raw21578step2 raw21578step1; decide +kernel
      have hl : raw21578step2Labels = raw21578step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21578step1 raw21578step1Labels permutation10 permutation4
    mixedMoment B raw21578step2 raw21578step2Labels = mixedMoment B raw21578step3 raw21578step3Labels := by
      have ha : raw21578step3 = -raw21578step2 := by apply Matrix.ext; change ∀ i j, raw21578step3 i j = -(raw21578step2 i j); unfold raw21578step3 raw21578step2; decide +kernel
      have hl : raw21578step3Labels = raw21578step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node809 node809Labels := by rfl

theorem canonical21579 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21579 raw21579Labels = mixedMoment B node735 node735Labels := by
  calc
    mixedMoment B raw21579 raw21579Labels = mixedMoment B raw21579step0 raw21579step0Labels := by
      have hz : ∀ j, raw21579 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21579step0 = (fun i j => raw21579 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21579step0 raw21579; decide +kernel
      have hl : raw21579step0Labels = raw21579Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21579 raw21579Labels permutation434 hz
    mixedMoment B raw21579step0 raw21579step0Labels = mixedMoment B raw21579step1 raw21579step1Labels := by
      have hz : ∀ j, raw21579step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21579step1 = (fun i j => raw21579step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21579step1 raw21579step0; decide +kernel
      have hl : raw21579step1Labels = raw21579step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21579step0 raw21579step0Labels permutation80 hz
    mixedMoment B raw21579step1 raw21579step1Labels = mixedMoment B raw21579step2 raw21579step2Labels := by
      have ha : raw21579step2 = (fun i j => raw21579step1 (permutation10 i) (permutation4 j)) := by apply Matrix.ext; unfold raw21579step2 raw21579step1; decide +kernel
      have hl : raw21579step2Labels = raw21579step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21579step1 raw21579step1Labels permutation10 permutation4
    mixedMoment B raw21579step2 raw21579step2Labels = mixedMoment B raw21579step3 raw21579step3Labels := by
      have ha : raw21579step3 = -raw21579step2 := by apply Matrix.ext; change ∀ i j, raw21579step3 i j = -(raw21579step2 i j); unfold raw21579step3 raw21579step2; decide +kernel
      have hl : raw21579step3Labels = raw21579step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node735 node735Labels := by rfl

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

theorem canonical813 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw813 raw813Labels = mixedMoment B node4177 node4177Labels := by
  calc
    mixedMoment B raw813 raw813Labels = mixedMoment B raw813step0 raw813step0Labels := by
      have ha : raw813step0 = (fun i j => raw813 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw813step0 raw813; decide +kernel
      have hl : raw813step0Labels = raw813Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw813 raw813Labels permutation8 permutation4
    mixedMoment B raw813step0 raw813step0Labels = mixedMoment B raw813step1 raw813step1Labels := by
      have ha : raw813step1 = raw813step0 := by apply Matrix.ext; unfold raw813step1 raw813step0; decide +kernel
      have hl : raw813step0Labels = labelEmbedding7 ∘ raw813step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw813step0 raw813step0Labels raw813step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4177 node4177Labels := by rfl

theorem canonical814 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw814 raw814Labels = mixedMoment B node605 node605Labels := by
  calc
    mixedMoment B raw814 raw814Labels = mixedMoment B raw814step0 raw814step0Labels := by
      have ha : raw814step0 = (fun i j => raw814 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw814step0 raw814; decide +kernel
      have hl : raw814step0Labels = raw814Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw814 raw814Labels permutation8 permutation4
    _ = mixedMoment B node605 node605Labels := by rfl

theorem canonical815 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw815 raw815Labels = mixedMoment B node1518 node1518Labels := by
  calc
    mixedMoment B raw815 raw815Labels = mixedMoment B raw815step0 raw815step0Labels := by
      have ha : raw815step0 = (fun i j => raw815 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw815step0 raw815; decide +kernel
      have hl : raw815step0Labels = raw815Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw815 raw815Labels permutation8 permutation6
    mixedMoment B raw815step0 raw815step0Labels = mixedMoment B raw815step1 raw815step1Labels := by
      have ha : raw815step1 = -raw815step0 := by apply Matrix.ext; change ∀ i j, raw815step1 i j = -(raw815step0 i j); unfold raw815step1 raw815step0; decide +kernel
      have hl : raw815step1Labels = raw815step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw815step1 raw815step1Labels = mixedMoment B raw815step2 raw815step2Labels := by
      have ha : raw815step2 = raw815step1 := by apply Matrix.ext; unfold raw815step2 raw815step1; decide +kernel
      have hl : raw815step1Labels = labelEmbedding1 ∘ raw815step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw815step1 raw815step1Labels raw815step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1518 node1518Labels := by rfl

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

theorem canonical1131 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1131 raw1131Labels = mixedMoment B node4346 node4346Labels := by
  calc
    mixedMoment B raw1131 raw1131Labels = mixedMoment B raw1131step0 raw1131step0Labels := by
      have ha : raw1131step0 = (fun i j => raw1131 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1131step0 raw1131; decide +kernel
      have hl : raw1131step0Labels = raw1131Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1131 raw1131Labels permutation32 permutation4
    mixedMoment B raw1131step0 raw1131step0Labels = mixedMoment B raw1131step1 raw1131step1Labels := by
      have ha : raw1131step1 = raw1131step0 := by apply Matrix.ext; unfold raw1131step1 raw1131step0; decide +kernel
      have hl : raw1131step0Labels = labelEmbedding7 ∘ raw1131step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1131step0 raw1131step0Labels raw1131step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4346 node4346Labels := by rfl

theorem canonical1132 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1132 raw1132Labels = mixedMoment B node924 node924Labels := by
  calc
    mixedMoment B raw1132 raw1132Labels = mixedMoment B raw1132step0 raw1132step0Labels := by
      have ha : raw1132step0 = (fun i j => raw1132 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1132step0 raw1132; decide +kernel
      have hl : raw1132step0Labels = raw1132Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1132 raw1132Labels permutation32 permutation4
    _ = mixedMoment B node924 node924Labels := by rfl

theorem canonical1133 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1133 raw1133Labels = mixedMoment B node1674 node1674Labels := by
  calc
    mixedMoment B raw1133 raw1133Labels = mixedMoment B raw1133step0 raw1133step0Labels := by
      have ha : raw1133step0 = (fun i j => raw1133 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1133step0 raw1133; decide +kernel
      have hl : raw1133step0Labels = raw1133Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1133 raw1133Labels permutation32 permutation6
    mixedMoment B raw1133step0 raw1133step0Labels = mixedMoment B raw1133step1 raw1133step1Labels := by
      have ha : raw1133step1 = -raw1133step0 := by apply Matrix.ext; change ∀ i j, raw1133step1 i j = -(raw1133step0 i j); unfold raw1133step1 raw1133step0; decide +kernel
      have hl : raw1133step1Labels = raw1133step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1133step1 raw1133step1Labels = mixedMoment B raw1133step2 raw1133step2Labels := by
      have ha : raw1133step2 = raw1133step1 := by apply Matrix.ext; unfold raw1133step2 raw1133step1; decide +kernel
      have hl : raw1133step1Labels = labelEmbedding1 ∘ raw1133step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1133step1 raw1133step1Labels raw1133step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1674 node1674Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical89
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical11476 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11476 raw11476Labels = mixedMoment B node4498 node4498Labels := by
  calc
    mixedMoment B raw11476 raw11476Labels = mixedMoment B raw11476step0 raw11476step0Labels := by
      have hz : ∀ j, raw11476 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11476step0 = (fun i j => raw11476 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11476step0 raw11476; decide +kernel
      have hl : raw11476step0Labels = raw11476Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11476 raw11476Labels permutation434 hz
    mixedMoment B raw11476step0 raw11476step0Labels = mixedMoment B raw11476step1 raw11476step1Labels := by
      have hz : ∀ j, raw11476step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw11476step1 = (fun i j => raw11476step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw11476step1 raw11476step0; decide +kernel
      have hl : raw11476step1Labels = raw11476step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11476step0 raw11476step0Labels permutation80 hz
    mixedMoment B raw11476step1 raw11476step1Labels = mixedMoment B raw11476step2 raw11476step2Labels := by
      have ha : raw11476step2 = (fun i j => raw11476step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw11476step2 raw11476step1; decide +kernel
      have hl : raw11476step2Labels = raw11476step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11476step1 raw11476step1Labels permutation10 permutation2
    _ = mixedMoment B node4498 node4498Labels := by rfl

theorem canonical11481 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11481 raw11481Labels = mixedMoment B node4457 node4457Labels := by
  calc
    mixedMoment B raw11481 raw11481Labels = mixedMoment B raw11481step0 raw11481step0Labels := by
      have hz : ∀ j, raw11481 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11481step0 = (fun i j => raw11481 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11481step0 raw11481; decide +kernel
      have hl : raw11481step0Labels = raw11481Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11481 raw11481Labels permutation434 hz
    _ = mixedMoment B node4457 node4457Labels := by rfl

theorem canonical11486 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11486 raw11486Labels = mixedMoment B node4457 node4457Labels := by
  calc
    mixedMoment B raw11486 raw11486Labels = mixedMoment B raw11486step0 raw11486step0Labels := by
      have hz : ∀ j, raw11486 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw11486step0 = (fun i j => raw11486 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw11486step0 raw11486; decide +kernel
      have hl : raw11486step0Labels = raw11486Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11486 raw11486Labels permutation346 hz
    _ = mixedMoment B node4457 node4457Labels := by rfl

theorem canonical11491 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11491 raw11491Labels = mixedMoment B node4466 node4466Labels := by
  calc
    mixedMoment B raw11491 raw11491Labels = mixedMoment B raw11491step0 raw11491step0Labels := by
      have hz : ∀ j, raw11491 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11491step0 = (fun i j => raw11491 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11491step0 raw11491; decide +kernel
      have hl : raw11491step0Labels = raw11491Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11491 raw11491Labels permutation434 hz
    mixedMoment B raw11491step0 raw11491step0Labels = mixedMoment B raw11491step1 raw11491step1Labels := by
      have hz : ∀ j, raw11491step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw11491step1 = (fun i j => raw11491step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw11491step1 raw11491step0; decide +kernel
      have hl : raw11491step1Labels = raw11491step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11491step0 raw11491step0Labels permutation80 hz
    _ = mixedMoment B node4466 node4466Labels := by rfl

theorem canonical11497 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11497 raw11497Labels = mixedMoment B node4868 node4868Labels := by
  calc
    mixedMoment B raw11497 raw11497Labels = mixedMoment B raw11497step0 raw11497step0Labels := by
      have hz : ∀ j, raw11497 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11497step0 = (fun i j => raw11497 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11497step0 raw11497; decide +kernel
      have hl : raw11497step0Labels = raw11497Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11497 raw11497Labels permutation434 hz
    mixedMoment B raw11497step0 raw11497step0Labels = mixedMoment B raw11497step1 raw11497step1Labels := by
      have hz : ∀ j, raw11497step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw11497step1 = (fun i j => raw11497step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw11497step1 raw11497step0; decide +kernel
      have hl : raw11497step1Labels = raw11497step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11497step0 raw11497step0Labels permutation80 hz
    _ = mixedMoment B node4868 node4868Labels := by rfl

theorem canonical11498 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11498 raw11498Labels = mixedMoment B node4804 node4804Labels := by
  calc
    mixedMoment B raw11498 raw11498Labels = mixedMoment B raw11498step0 raw11498step0Labels := by
      have hz : ∀ j, raw11498 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11498step0 = (fun i j => raw11498 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11498step0 raw11498; decide +kernel
      have hl : raw11498step0Labels = raw11498Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11498 raw11498Labels permutation434 hz
    mixedMoment B raw11498step0 raw11498step0Labels = mixedMoment B raw11498step1 raw11498step1Labels := by
      have ha : raw11498step1 = (fun i j => raw11498step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw11498step1 raw11498step0; decide +kernel
      have hl : raw11498step1Labels = raw11498step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11498step0 raw11498step0Labels permutation38 permutation2
    _ = mixedMoment B node4804 node4804Labels := by rfl

theorem canonical11499 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11499 raw11499Labels = mixedMoment B node4804 node4804Labels := by
  calc
    mixedMoment B raw11499 raw11499Labels = mixedMoment B raw11499step0 raw11499step0Labels := by
      have hz : ∀ j, raw11499 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw11499step0 = (fun i j => raw11499 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw11499step0 raw11499; decide +kernel
      have hl : raw11499step0Labels = raw11499Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11499 raw11499Labels permutation346 hz
    mixedMoment B raw11499step0 raw11499step0Labels = mixedMoment B raw11499step1 raw11499step1Labels := by
      have ha : raw11499step1 = (fun i j => raw11499step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw11499step1 raw11499step0; decide +kernel
      have hl : raw11499step1Labels = raw11499step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11499step0 raw11499step0Labels permutation38 permutation2
    _ = mixedMoment B node4804 node4804Labels := by rfl

theorem canonical11500 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11500 raw11500Labels = mixedMoment B node4897 node4897Labels := by
  calc
    mixedMoment B raw11500 raw11500Labels = mixedMoment B raw11500step0 raw11500step0Labels := by
      have hz : ∀ j, raw11500 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw11500step0 = (fun i j => raw11500 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw11500step0 raw11500; decide +kernel
      have hl : raw11500step0Labels = raw11500Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11500 raw11500Labels permutation520 hz
    mixedMoment B raw11500step0 raw11500step0Labels = mixedMoment B raw11500step1 raw11500step1Labels := by
      have hz : ∀ j, raw11500step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw11500step1 = (fun i j => raw11500step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw11500step1 raw11500step0; decide +kernel
      have hl : raw11500step1Labels = raw11500step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11500step0 raw11500step0Labels permutation104 hz
    mixedMoment B raw11500step1 raw11500step1Labels = mixedMoment B raw11500step2 raw11500step2Labels := by
      have hz : ∀ j, raw11500step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw11500step2 = (fun i j => raw11500step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw11500step2 raw11500step1; decide +kernel
      have hl : raw11500step2Labels = raw11500step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11500step1 raw11500step1Labels permutation20 hz
    _ = mixedMoment B node4897 node4897Labels := by rfl

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

theorem canonical1257 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1257 raw1257Labels = mixedMoment B node4457 node4457Labels := by
  calc
    mixedMoment B raw1257 raw1257Labels = mixedMoment B raw1257step0 raw1257step0Labels := by
      have ha : raw1257step0 = (fun i j => raw1257 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1257step0 raw1257; decide +kernel
      have hl : raw1257step0Labels = raw1257Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1257 raw1257Labels permutation32 permutation4
    mixedMoment B raw1257step0 raw1257step0Labels = mixedMoment B raw1257step1 raw1257step1Labels := by
      have ha : raw1257step1 = raw1257step0 := by apply Matrix.ext; unfold raw1257step1 raw1257step0; decide +kernel
      have hl : raw1257step0Labels = labelEmbedding7 ∘ raw1257step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1257step0 raw1257step0Labels raw1257step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4457 node4457Labels := by rfl

theorem canonical1258 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1258 raw1258Labels = mixedMoment B node1040 node1040Labels := by
  calc
    mixedMoment B raw1258 raw1258Labels = mixedMoment B raw1258step0 raw1258step0Labels := by
      have ha : raw1258step0 = (fun i j => raw1258 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1258step0 raw1258; decide +kernel
      have hl : raw1258step0Labels = raw1258Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1258 raw1258Labels permutation32 permutation4
    _ = mixedMoment B node1040 node1040Labels := by rfl

theorem canonical1259 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1259 raw1259Labels = mixedMoment B node1707 node1707Labels := by
  calc
    mixedMoment B raw1259 raw1259Labels = mixedMoment B raw1259step0 raw1259step0Labels := by
      have ha : raw1259step0 = (fun i j => raw1259 (permutation40 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1259step0 raw1259; decide +kernel
      have hl : raw1259step0Labels = raw1259Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1259 raw1259Labels permutation40 permutation6
    mixedMoment B raw1259step0 raw1259step0Labels = mixedMoment B raw1259step1 raw1259step1Labels := by
      have ha : raw1259step1 = -raw1259step0 := by apply Matrix.ext; change ∀ i j, raw1259step1 i j = -(raw1259step0 i j); unfold raw1259step1 raw1259step0; decide +kernel
      have hl : raw1259step1Labels = raw1259step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1259step1 raw1259step1Labels = mixedMoment B raw1259step2 raw1259step2Labels := by
      have ha : raw1259step2 = raw1259step1 := by apply Matrix.ext; unfold raw1259step2 raw1259step1; decide +kernel
      have hl : raw1259step1Labels = labelEmbedding1 ∘ raw1259step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1259step1 raw1259step1Labels raw1259step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1707 node1707Labels := by rfl

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

theorem canonical1272 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1272 raw1272Labels = mixedMoment B node4466 node4466Labels := by
  calc
    mixedMoment B raw1272 raw1272Labels = mixedMoment B raw1272step0 raw1272step0Labels := by
      have ha : raw1272step0 = (fun i j => raw1272 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1272step0 raw1272; decide +kernel
      have hl : raw1272step0Labels = raw1272Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1272 raw1272Labels permutation8 permutation4
    mixedMoment B raw1272step0 raw1272step0Labels = mixedMoment B raw1272step1 raw1272step1Labels := by
      have ha : raw1272step1 = raw1272step0 := by apply Matrix.ext; unfold raw1272step1 raw1272step0; decide +kernel
      have hl : raw1272step0Labels = labelEmbedding7 ∘ raw1272step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1272step0 raw1272step0Labels raw1272step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4466 node4466Labels := by rfl

theorem canonical1273 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1273 raw1273Labels = mixedMoment B node1049 node1049Labels := by
  calc
    mixedMoment B raw1273 raw1273Labels = mixedMoment B raw1273step0 raw1273step0Labels := by
      have ha : raw1273step0 = (fun i j => raw1273 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1273step0 raw1273; decide +kernel
      have hl : raw1273step0Labels = raw1273Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1273 raw1273Labels permutation8 permutation4
    _ = mixedMoment B node1049 node1049Labels := by rfl

theorem canonical1274 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1274 raw1274Labels = mixedMoment B node1738 node1738Labels := by
  calc
    mixedMoment B raw1274 raw1274Labels = mixedMoment B raw1274step0 raw1274step0Labels := by
      have ha : raw1274step0 = (fun i j => raw1274 (permutation10 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1274step0 raw1274; decide +kernel
      have hl : raw1274step0Labels = raw1274Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1274 raw1274Labels permutation10 permutation6
    mixedMoment B raw1274step0 raw1274step0Labels = mixedMoment B raw1274step1 raw1274step1Labels := by
      have ha : raw1274step1 = -raw1274step0 := by apply Matrix.ext; change ∀ i j, raw1274step1 i j = -(raw1274step0 i j); unfold raw1274step1 raw1274step0; decide +kernel
      have hl : raw1274step1Labels = raw1274step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1274step1 raw1274step1Labels = mixedMoment B raw1274step2 raw1274step2Labels := by
      have ha : raw1274step2 = raw1274step1 := by apply Matrix.ext; unfold raw1274step2 raw1274step1; decide +kernel
      have hl : raw1274step1Labels = labelEmbedding1 ∘ raw1274step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1274step1 raw1274step1Labels raw1274step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1738 node1738Labels := by rfl

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

theorem singleton4177 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4177 node4177Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node605 node605Labels + mixedMoment B node1518 node1518Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw813 singletonSmall4177
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4177) = raw813Labels := by decide +kernel
  rw [hl, canonical813 B hB] at h
  have hc0 : mixedMoment B raw813 (Fin.cases (0 : Fin 2) singletonSmall4177) =
      mixedMoment B node605 node605Labels := by
    have ha : raw813 = raw814 := by apply Matrix.ext; unfold raw813 raw814; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4177 = raw814Labels := by decide +kernel
    rw [ha, hj, canonical814 B hB]
  have hc1 : mixedMoment B raw813 (Fin.cases (1 : Fin 2) singletonSmall4177) =
      mixedMoment B node1518 node1518Labels := by
    have ha : raw813 = raw815 := by apply Matrix.ext; unfold raw813 raw815; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4177 = raw815Labels := by decide +kernel
    rw [ha, hj, canonical815 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
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

theorem singleton4346 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4346 node4346Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node924 node924Labels + mixedMoment B node1674 node1674Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1131 singletonSmall4346
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4346) = raw1131Labels := by decide +kernel
  rw [hl, canonical1131 B hB] at h
  have hc0 : mixedMoment B raw1131 (Fin.cases (0 : Fin 2) singletonSmall4346) =
      mixedMoment B node924 node924Labels := by
    have ha : raw1131 = raw1132 := by apply Matrix.ext; unfold raw1131 raw1132; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4346 = raw1132Labels := by decide +kernel
    rw [ha, hj, canonical1132 B hB]
  have hc1 : mixedMoment B raw1131 (Fin.cases (1 : Fin 2) singletonSmall4346) =
      mixedMoment B node1674 node1674Labels := by
    have ha : raw1131 = raw1133 := by apply Matrix.ext; unfold raw1131 raw1133; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4346 = raw1133Labels := by decide +kernel
    rw [ha, hj, canonical1133 B hB]
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

theorem singleton4457 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4457 node4457Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1040 node1040Labels + mixedMoment B node1707 node1707Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1257 singletonSmall4457
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4457) = raw1257Labels := by decide +kernel
  rw [hl, canonical1257 B hB] at h
  have hc0 : mixedMoment B raw1257 (Fin.cases (0 : Fin 2) singletonSmall4457) =
      mixedMoment B node1040 node1040Labels := by
    have ha : raw1257 = raw1258 := by apply Matrix.ext; unfold raw1257 raw1258; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4457 = raw1258Labels := by decide +kernel
    rw [ha, hj, canonical1258 B hB]
  have hc1 : mixedMoment B raw1257 (Fin.cases (1 : Fin 2) singletonSmall4457) =
      mixedMoment B node1707 node1707Labels := by
    have ha : raw1257 = raw1259 := by apply Matrix.ext; unfold raw1257 raw1259; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4457 = raw1259Labels := by decide +kernel
    rw [ha, hj, canonical1259 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

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

theorem singleton4466 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4466 node4466Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1049 node1049Labels + mixedMoment B node1738 node1738Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1272 singletonSmall4466
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4466) = raw1272Labels := by decide +kernel
  rw [hl, canonical1272 B hB] at h
  have hc0 : mixedMoment B raw1272 (Fin.cases (0 : Fin 2) singletonSmall4466) =
      mixedMoment B node1049 node1049Labels := by
    have ha : raw1272 = raw1273 := by apply Matrix.ext; unfold raw1272 raw1273; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4466 = raw1273Labels := by decide +kernel
    rw [ha, hj, canonical1273 B hB]
  have hc1 : mixedMoment B raw1272 (Fin.cases (1 : Fin 2) singletonSmall4466) =
      mixedMoment B node1738 node1738Labels := by
    have ha : raw1272 = raw1274 := by apply Matrix.ext; unfold raw1272 raw1274; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4466 = raw1274Labels := by decide +kernel
    rw [ha, hj, canonical1274 B hB]
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons75
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

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

theorem singleton4868 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4868 node4868Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2109 node2109Labels + mixedMoment B node2261 node2261Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1797 singletonSmall4868
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4868) = raw1797Labels := by decide +kernel
  rw [hl, canonical1797 B hB] at h
  have hc0 : mixedMoment B raw1797 (Fin.cases (0 : Fin 2) singletonSmall4868) =
      mixedMoment B node2109 node2109Labels := by
    have ha : raw1797 = raw1798 := by apply Matrix.ext; unfold raw1797 raw1798; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4868 = raw1798Labels := by decide +kernel
    rw [ha, hj, canonical1798 B hB]
  have hc1 : mixedMoment B raw1797 (Fin.cases (1 : Fin 2) singletonSmall4868) =
      mixedMoment B node2261 node2261Labels := by
    have ha : raw1797 = raw1799 := by apply Matrix.ext; unfold raw1797 raw1799; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4868 = raw1799Labels := by decide +kernel
    rw [ha, hj, canonical1799 B hB]
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

theorem sound731 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node731 node731Labels = Sparse.eval nodeValue731 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 731) = mixedMoment B node731 node731Labels := rfl
  simpa [nodeValue731, Sparse.eval] using hc.symm

theorem sound735 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node735 node735Labels = Sparse.eval nodeValue735 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 735) = mixedMoment B node735 node735Labels := rfl
  simpa [nodeValue735, Sparse.eval] using hc.symm

theorem sound741 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node741 node741Labels = Sparse.eval nodeValue741 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 741) = mixedMoment B node741 node741Labels := rfl
  simpa [nodeValue741, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros12
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero809 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node809 node809Labels = 0 := by
  exact mixedMoment_order_one B hB node809 node809Labels 1
    (by decide +kernel) (by decide +kernel)

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

theorem sound809 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node809 node809Labels = Sparse.eval nodeValue809 (mixedVector B) := by
  simpa only [nodeValue809, Sparse.eval_nil] using zero809 B _hB _hF

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

theorem zero851 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node851 node851Labels = 0 := by
  exact mixedMoment_order_one B hB node851 node851Labels 1
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

theorem sound847 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node847 node847Labels = Sparse.eval nodeValue847 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 847) = mixedMoment B node847 node847Labels := rfl
  simpa [nodeValue847, Sparse.eval] using hc.symm

theorem sound851 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node851 node851Labels = Sparse.eval nodeValue851 (mixedVector B) := by
  simpa only [nodeValue851, Sparse.eval_nil] using zero851 B _hB _hF

theorem sound853 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node853 node853Labels = Sparse.eval nodeValue853 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 853) = mixedMoment B node853 node853Labels := rfl
  simpa [nodeValue853, Sparse.eval] using hc.symm

theorem sound857 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node857 node857Labels = Sparse.eval nodeValue857 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 857) = mixedMoment B node857 node857Labels := rfl
  simpa [nodeValue857, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros14
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero904 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node904 node904Labels = 0 := by
  exact mixedMoment_alpha B hF node904 node904Labels 1 permutation152
    (by decide +kernel)

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

theorem sound904 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node904 node904Labels = Sparse.eval nodeValue904 (mixedVector B) := by
  simpa only [nodeValue904, Sparse.eval_nil] using zero904 B _hB _hF

theorem sound908 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node908 node908Labels = Sparse.eval nodeValue908 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 908) = mixedMoment B node908 node908Labels := rfl
  simpa [nodeValue908, Sparse.eval] using hc.symm

theorem sound912 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node912 node912Labels = Sparse.eval nodeValue912 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 912) = mixedMoment B node912 node912Labels := rfl
  simpa [nodeValue912, Sparse.eval] using hc.symm

theorem sound916 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node916 node916Labels = Sparse.eval nodeValue916 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 916) = mixedMoment B node916 node916Labels := rfl
  simpa [nodeValue916, Sparse.eval] using hc.symm

theorem sound924 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node924 node924Labels = Sparse.eval nodeValue924 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 924) = mixedMoment B node924 node924Labels := rfl
  simpa [nodeValue924, Sparse.eval] using hc.symm

theorem sound943 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node943 node943Labels = Sparse.eval nodeValue943 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 943) = mixedMoment B node943 node943Labels := rfl
  simpa [nodeValue943, Sparse.eval] using hc.symm

theorem sound948 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node948 node948Labels = Sparse.eval nodeValue948 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 948) = mixedMoment B node948 node948Labels := rfl
  simpa [nodeValue948, Sparse.eval] using hc.symm

theorem sound952 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node952 node952Labels = Sparse.eval nodeValue952 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 952) = mixedMoment B node952 node952Labels := rfl
  simpa [nodeValue952, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros15
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero1007 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1007 node1007Labels = 0 := by
  exact mixedMoment_order_one B hB node1007 node1007Labels 1
    (by decide +kernel) (by decide +kernel)

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound15
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound1007 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1007 node1007Labels = Sparse.eval nodeValue1007 (mixedVector B) := by
  simpa only [nodeValue1007, Sparse.eval_nil] using zero1007 B _hB _hF

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros16
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero1082 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1082 node1082Labels = 0 := by
  exact mixedMoment_order_one B hB node1082 node1082Labels 1
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

theorem sound1033 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1033 node1033Labels = Sparse.eval nodeValue1033 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1033) = mixedMoment B node1033 node1033Labels := rfl
  simpa [nodeValue1033, Sparse.eval] using hc.symm

theorem sound1037 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1037 node1037Labels = Sparse.eval nodeValue1037 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1037) = mixedMoment B node1037 node1037Labels := rfl
  simpa [nodeValue1037, Sparse.eval] using hc.symm

theorem sound1040 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1040 node1040Labels = Sparse.eval nodeValue1040 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1040) = mixedMoment B node1040 node1040Labels := rfl
  simpa [nodeValue1040, Sparse.eval] using hc.symm

theorem sound1043 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1043 node1043Labels = Sparse.eval nodeValue1043 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1043) = mixedMoment B node1043 node1043Labels := rfl
  simpa [nodeValue1043, Sparse.eval] using hc.symm

theorem sound1048 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1048 node1048Labels = Sparse.eval nodeValue1048 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1048) = mixedMoment B node1048 node1048Labels := rfl
  simpa [nodeValue1048, Sparse.eval] using hc.symm

theorem sound1049 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1049 node1049Labels = Sparse.eval nodeValue1049 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1049) = mixedMoment B node1049 node1049Labels := rfl
  simpa [nodeValue1049, Sparse.eval] using hc.symm

theorem sound1051 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1051 node1051Labels = Sparse.eval nodeValue1051 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1051) = mixedMoment B node1051 node1051Labels := rfl
  simpa [nodeValue1051, Sparse.eval] using hc.symm

theorem sound1074 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1074 node1074Labels = Sparse.eval nodeValue1074 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1074) = mixedMoment B node1074 node1074Labels := rfl
  simpa [nodeValue1074, Sparse.eval] using hc.symm

theorem sound1082 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1082 node1082Labels = Sparse.eval nodeValue1082 (mixedVector B) := by
  simpa only [nodeValue1082, Sparse.eval_nil] using zero1082 B _hB _hF

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound23
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound1505 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1505 node1505Labels = Sparse.eval nodeValue1505 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1505) = mixedMoment B node1505 node1505Labels := rfl
  simpa [nodeValue1505, Sparse.eval] using hc.symm

theorem sound1516 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1516 node1516Labels = Sparse.eval nodeValue1516 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1516) = mixedMoment B node1516 node1516Labels := rfl
  simpa [nodeValue1516, Sparse.eval] using hc.symm

theorem sound1518 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1518 node1518Labels = Sparse.eval nodeValue1518 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1518) = mixedMoment B node1518 node1518Labels := rfl
  simpa [nodeValue1518, Sparse.eval] using hc.symm

theorem sound1523 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1523 node1523Labels = Sparse.eval nodeValue1523 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1523) = mixedMoment B node1523 node1523Labels := rfl
  simpa [nodeValue1523, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros25
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero1663 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node1663 node1663Labels = 0 := by
  exact mixedMoment_alpha B hF node1663 node1663Labels 1 permutation485
    (by decide +kernel)

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

theorem sound1647 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1647 node1647Labels = Sparse.eval nodeValue1647 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1647) = mixedMoment B node1647 node1647Labels := rfl
  simpa [nodeValue1647, Sparse.eval] using hc.symm

theorem sound1663 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1663 node1663Labels = Sparse.eval nodeValue1663 (mixedVector B) := by
  simpa only [nodeValue1663, Sparse.eval_nil] using zero1663 B _hB _hF

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros26
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero1727 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1727 node1727Labels = 0 := by
  exact mixedMoment_order_one B hB node1727 node1727Labels 1
    (by decide +kernel) (by decide +kernel)

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

theorem sound1674 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1674 node1674Labels = Sparse.eval nodeValue1674 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1674) = mixedMoment B node1674 node1674Labels := rfl
  simpa [nodeValue1674, Sparse.eval] using hc.symm

theorem sound1679 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1679 node1679Labels = Sparse.eval nodeValue1679 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1679) = mixedMoment B node1679 node1679Labels := rfl
  simpa [nodeValue1679, Sparse.eval] using hc.symm

theorem sound1704 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1704 node1704Labels = Sparse.eval nodeValue1704 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1704) = mixedMoment B node1704 node1704Labels := rfl
  simpa [nodeValue1704, Sparse.eval] using hc.symm

theorem sound1707 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1707 node1707Labels = Sparse.eval nodeValue1707 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1707) = mixedMoment B node1707 node1707Labels := rfl
  simpa [nodeValue1707, Sparse.eval] using hc.symm

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

theorem sound1727 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1727 node1727Labels = Sparse.eval nodeValue1727 (mixedVector B) := by
  simpa only [nodeValue1727, Sparse.eval_nil] using zero1727 B _hB _hF

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

theorem sound1735 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1735 node1735Labels = Sparse.eval nodeValue1735 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1735) = mixedMoment B node1735 node1735Labels := rfl
  simpa [nodeValue1735, Sparse.eval] using hc.symm

theorem sound1738 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1738 node1738Labels = Sparse.eval nodeValue1738 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1738) = mixedMoment B node1738 node1738Labels := rfl
  simpa [nodeValue1738, Sparse.eval] using hc.symm

theorem sound1750 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1750 node1750Labels = Sparse.eval nodeValue1750 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1750) = mixedMoment B node1750 node1750Labels := rfl
  simpa [nodeValue1750, Sparse.eval] using hc.symm

theorem sound1752 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1752 node1752Labels = Sparse.eval nodeValue1752 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1752) = mixedMoment B node1752 node1752Labels := rfl
  simpa [nodeValue1752, Sparse.eval] using hc.symm

theorem sound1754 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1754 node1754Labels = Sparse.eval nodeValue1754 (mixedVector B) := by
  simpa only [nodeValue1754, Sparse.eval_nil] using zero1754 B _hB _hF

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

theorem sound2018 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2018 node2018Labels = Sparse.eval nodeValue2018 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2018) = mixedMoment B node2018 node2018Labels := rfl
  simpa [nodeValue2018, Sparse.eval] using hc.symm

theorem sound2022 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2022 node2022Labels = Sparse.eval nodeValue2022 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2022) = mixedMoment B node2022 node2022Labels := rfl
  simpa [nodeValue2022, Sparse.eval] using hc.symm

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

theorem sound2103 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2103 node2103Labels = Sparse.eval nodeValue2103 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2103) = mixedMoment B node2103 node2103Labels := rfl
  simpa [nodeValue2103, Sparse.eval] using hc.symm

theorem sound2109 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2109 node2109Labels = Sparse.eval nodeValue2109 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2109) = mixedMoment B node2109 node2109Labels := rfl
  simpa [nodeValue2109, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros34
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero2208 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2208 node2208Labels = 0 := by
  exact mixedMoment_order_one B hB node2208 node2208Labels 1
    (by decide +kernel) (by decide +kernel)

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

theorem sound2203 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2203 node2203Labels = Sparse.eval nodeValue2203 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2203) = mixedMoment B node2203 node2203Labels := rfl
  simpa [nodeValue2203, Sparse.eval] using hc.symm

theorem sound2208 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2208 node2208Labels = Sparse.eval nodeValue2208 (mixedVector B) := by
  simpa only [nodeValue2208, Sparse.eval_nil] using zero2208 B _hB _hF

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

theorem sound2261 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2261 node2261Labels = Sparse.eval nodeValue2261 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2261) = mixedMoment B node2261 node2261Labels := rfl
  simpa [nodeValue2261, Sparse.eval] using hc.symm

theorem sound2264 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2264 node2264Labels = Sparse.eval nodeValue2264 (mixedVector B) := by
  simpa only [nodeValue2264, Sparse.eval_nil] using zero2264 B _hB _hF

theorem sound2292 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2292 node2292Labels = Sparse.eval nodeValue2292 (mixedVector B) := by
  simpa only [nodeValue2292, Sparse.eval_nil] using zero2292 B _hB _hF

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

theorem sound4070 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4070 node4070Labels = Sparse.eval nodeValue4070 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4070) = mixedMoment B node4070 node4070Labels := rfl
  simpa [nodeValue4070, Sparse.eval] using hc.symm

theorem sound4081 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4081 node4081Labels = Sparse.eval nodeValue4081 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4081) = mixedMoment B node4081 node4081Labels := rfl
  simpa [nodeValue4081, Sparse.eval] using hc.symm

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

theorem sound579 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node579 node579Labels = Sparse.eval nodeValue579 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 579) = mixedMoment B node579 node579Labels := rfl
  simpa [nodeValue579, Sparse.eval] using hc.symm

theorem sound584 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node584 node584Labels = Sparse.eval nodeValue584 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 584) = mixedMoment B node584 node584Labels := rfl
  simpa [nodeValue584, Sparse.eval] using hc.symm

theorem sound588 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node588 node588Labels = Sparse.eval nodeValue588 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 588) = mixedMoment B node588 node588Labels := rfl
  simpa [nodeValue588, Sparse.eval] using hc.symm

theorem sound594 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node594 node594Labels = Sparse.eval nodeValue594 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 594) = mixedMoment B node594 node594Labels := rfl
  simpa [nodeValue594, Sparse.eval] using hc.symm

theorem sound605 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node605 node605Labels = Sparse.eval nodeValue605 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 605) = mixedMoment B node605 node605Labels := rfl
  simpa [nodeValue605, Sparse.eval] using hc.symm

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

theorem sound4151 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4151 node4151Labels = Sparse.eval nodeValue4151 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4151) = mixedMoment B node4151 node4151Labels := rfl
  simpa [nodeValue4151, Sparse.eval] using hc.symm

theorem sound4156 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4156 node4156Labels = Sparse.eval nodeValue4156 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4156) = mixedMoment B node4156 node4156Labels := rfl
  simpa [nodeValue4156, Sparse.eval] using hc.symm

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

theorem sound4160 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4160 node4160Labels = Sparse.eval nodeValue4160 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4160) = mixedMoment B node4160 node4160Labels := rfl
  simpa [nodeValue4160, Sparse.eval] using hc.symm

theorem sound4177 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4177 node4177Labels = Sparse.eval nodeValue4177 (mixedVector B) := by
  have h := singleton4177 B _hB
  rw [sound605 B _hB _hF, sound1518 B _hB _hF] at h
  norm_num [nodeValue4177, nodeValue605, nodeValue1518, Sparse.eval] at h ⊢
  linarith only [h]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros67
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero4326 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node4326 node4326Labels = 0 := by
  exact mixedMoment_alpha B hF node4326 node4326Labels 1 permutation152
    (by decide +kernel)

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

theorem sound4326 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4326 node4326Labels = Sparse.eval nodeValue4326 (mixedVector B) := by
  simpa only [nodeValue4326, Sparse.eval_nil] using zero4326 B _hB _hF

theorem sound4330 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4330 node4330Labels = Sparse.eval nodeValue4330 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4330) = mixedMoment B node4330 node4330Labels := rfl
  simpa [nodeValue4330, Sparse.eval] using hc.symm

theorem sound4334 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4334 node4334Labels = Sparse.eval nodeValue4334 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4334) = mixedMoment B node4334 node4334Labels := rfl
  simpa [nodeValue4334, Sparse.eval] using hc.symm

theorem sound4346 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4346 node4346Labels = Sparse.eval nodeValue4346 (mixedVector B) := by
  have h := singleton4346 B _hB
  rw [sound924 B _hB _hF, sound1674 B _hB _hF] at h
  norm_num [nodeValue4346, nodeValue924, nodeValue1674, Sparse.eval] at h ⊢
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

theorem sound4365 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4365 node4365Labels = Sparse.eval nodeValue4365 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4365) = mixedMoment B node4365 node4365Labels := rfl
  simpa [nodeValue4365, Sparse.eval] using hc.symm

theorem sound4370 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4370 node4370Labels = Sparse.eval nodeValue4370 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4370) = mixedMoment B node4370 node4370Labels := rfl
  simpa [nodeValue4370, Sparse.eval] using hc.symm

theorem sound4373 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4373 node4373Labels = Sparse.eval nodeValue4373 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4373) = mixedMoment B node4373 node4373Labels := rfl
  simpa [nodeValue4373, Sparse.eval] using hc.symm

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

theorem sound4457 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4457 node4457Labels = Sparse.eval nodeValue4457 (mixedVector B) := by
  have h := singleton4457 B _hB
  rw [sound1040 B _hB _hF, sound1707 B _hB _hF] at h
  norm_num [nodeValue4457, nodeValue1040, nodeValue1707, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4460 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4460 node4460Labels = Sparse.eval nodeValue4460 (mixedVector B) := by
  have h := singleton4460 B _hB
  rw [sound1043 B _hB _hF, sound1725 B _hB _hF] at h
  norm_num [nodeValue4460, nodeValue1043, nodeValue1725, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4466 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4466 node4466Labels = Sparse.eval nodeValue4466 (mixedVector B) := by
  have h := singleton4466 B _hB
  rw [sound1049 B _hB _hF, sound1738 B _hB _hF] at h
  norm_num [nodeValue4466, nodeValue1049, nodeValue1738, Sparse.eval] at h ⊢
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

theorem zero4498 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4498 node4498Labels = 0 := by
  exact mixedMoment_order_one B hB node4498 node4498Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero4505 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4505 node4505Labels = 0 := by
  exact mixedMoment_order_one B hB node4505 node4505Labels 1
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

theorem sound4498 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4498 node4498Labels = Sparse.eval nodeValue4498 (mixedVector B) := by
  simpa only [nodeValue4498, Sparse.eval_nil] using zero4498 B _hB _hF

theorem sound4505 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4505 node4505Labels = Sparse.eval nodeValue4505 (mixedVector B) := by
  simpa only [nodeValue4505, Sparse.eval_nil] using zero4505 B _hB _hF

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

theorem sound4804 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4804 node4804Labels = Sparse.eval nodeValue4804 (mixedVector B) := by
  have h := singleton4804 B _hB
  rw [sound2022 B _hB _hF, sound2203 B _hB _hF] at h
  norm_num [nodeValue4804, nodeValue2022, nodeValue2203, Sparse.eval] at h ⊢
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

theorem zero4894 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4894 node4894Labels = 0 := by
  exact mixedMoment_order_one B hB node4894 node4894Labels 1
    (by decide +kernel) (by decide +kernel)

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

theorem sound4868 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4868 node4868Labels = Sparse.eval nodeValue4868 (mixedVector B) := by
  have h := singleton4868 B _hB
  rw [sound2109 B _hB _hF, sound2261 B _hB _hF] at h
  norm_num [nodeValue4868, nodeValue2109, nodeValue2261, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4894 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4894 node4894Labels = Sparse.eval nodeValue4894 (mixedVector B) := by
  simpa only [nodeValue4894, Sparse.eval_nil] using zero4894 B _hB _hF

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources42
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sourceEq1347 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1347 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1347 + difference 0 0) (sourceB1347 + difference 0 0) sourceC1347) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1750) := by
    have ha : (tripleCharges (sourceA1347 + difference 0 0) (sourceB1347 + difference 0 0) sourceC1347) = raw21367 := by
      apply Matrix.ext; unfold tripleCharges sourceA1347 sourceB1347 sourceC1347 difference raw21367; decide +kernel
    rw [ha]
    exact (canonical21367 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1347 + difference 1 0) (sourceB1347 + difference 0 1) sourceC1347) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 857) := by
    have ha : (tripleCharges (sourceA1347 + difference 1 0) (sourceB1347 + difference 0 1) sourceC1347) = raw21368 := by
      apply Matrix.ext; unfold tripleCharges sourceA1347 sourceB1347 sourceC1347 difference raw21368; decide +kernel
    rw [ha]
    exact (canonical21368 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1347 + difference 2 0) (sourceB1347 + difference 0 2) sourceC1347) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 847) := by
    have ha : (tripleCharges (sourceA1347 + difference 2 0) (sourceB1347 + difference 0 2) sourceC1347) = raw21369 := by
      apply Matrix.ext; unfold tripleCharges sourceA1347 sourceB1347 sourceC1347 difference raw21369; decide +kernel
    rw [ha]
    exact (canonical21369 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1347 + difference 3 0) (sourceB1347 + difference 0 3) sourceC1347) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 847) := by
    have ha : (tripleCharges (sourceA1347 + difference 3 0) (sourceB1347 + difference 0 3) sourceC1347) = raw21370 := by
      apply Matrix.ext; unfold tripleCharges sourceA1347 sourceB1347 sourceC1347 difference raw21370; decide +kernel
    rw [ha]
    exact (canonical21370 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1347 + difference 4 0) (sourceB1347 + difference 0 4) sourceC1347) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 853) := by
    have ha : (tripleCharges (sourceA1347 + difference 4 0) (sourceB1347 + difference 0 4) sourceC1347) = raw21371 := by
      apply Matrix.ext; unfold tripleCharges sourceA1347 sourceB1347 sourceC1347 difference raw21371; decide +kernel
    rw [ha]
    exact (canonical21371 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1347 + difference 5 0) (sourceB1347 + difference 0 5) sourceC1347) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 851) := by
    have ha : (tripleCharges (sourceA1347 + difference 5 0) (sourceB1347 + difference 0 5) sourceC1347) = raw21372 := by
      apply Matrix.ext; unfold tripleCharges sourceA1347 sourceB1347 sourceC1347 difference raw21372; decide +kernel
    rw [ha]
    exact (canonical21372 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1347 + sourceB1347) sourceC1347) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4070) := by
    have ha : (doubleCharges (sourceA1347 + sourceB1347) sourceC1347) = raw20099 := by
      apply Matrix.ext; unfold doubleCharges sourceA1347 sourceB1347 sourceC1347 raw20099; decide +kernel
    rw [ha]
    exact (canonical20099 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1347 sourceB1347 sourceC1347
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1347, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1348 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1348 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1348 + difference 0 1) (sourceB1348 + difference 1 0) sourceC1348) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4868) := by
    have ha : (tripleCharges (sourceA1348 + difference 0 1) (sourceB1348 + difference 1 0) sourceC1348) = raw11497 := by
      apply Matrix.ext; unfold tripleCharges sourceA1348 sourceB1348 sourceC1348 difference raw11497; decide +kernel
    rw [ha]
    exact (canonical11497 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1348 + difference 0 2) (sourceB1348 + difference 2 0) sourceC1348) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4804) := by
    have ha : (tripleCharges (sourceA1348 + difference 0 2) (sourceB1348 + difference 2 0) sourceC1348) = raw11498 := by
      apply Matrix.ext; unfold tripleCharges sourceA1348 sourceB1348 sourceC1348 difference raw11498; decide +kernel
    rw [ha]
    exact (canonical11498 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1348 + difference 0 3) (sourceB1348 + difference 3 0) sourceC1348) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4804) := by
    have ha : (tripleCharges (sourceA1348 + difference 0 3) (sourceB1348 + difference 3 0) sourceC1348) = raw11499 := by
      apply Matrix.ext; unfold tripleCharges sourceA1348 sourceB1348 sourceC1348 difference raw11499; decide +kernel
    rw [ha]
    exact (canonical11499 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1348 + difference 0 4) (sourceB1348 + difference 4 0) sourceC1348) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4897) := by
    have ha : (tripleCharges (sourceA1348 + difference 0 4) (sourceB1348 + difference 4 0) sourceC1348) = raw11500 := by
      apply Matrix.ext; unfold tripleCharges sourceA1348 sourceB1348 sourceC1348 difference raw11500; decide +kernel
    rw [ha]
    exact (canonical11500 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1348 + difference 0 5) (sourceB1348 + difference 5 0) sourceC1348) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4894) := by
    have ha : (tripleCharges (sourceA1348 + difference 0 5) (sourceB1348 + difference 5 0) sourceC1348) = raw21373 := by
      apply Matrix.ext; unfold tripleCharges sourceA1348 sourceB1348 sourceC1348 difference raw21373; decide +kernel
    rw [ha]
    exact (canonical21373 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1348 + difference 1 0) (sourceB1348 + difference 0 1) sourceC1348) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4177) := by
    have ha : (tripleCharges (sourceA1348 + difference 1 0) (sourceB1348 + difference 0 1) sourceC1348) = raw21374 := by
      apply Matrix.ext; unfold tripleCharges sourceA1348 sourceB1348 sourceC1348 difference raw21374; decide +kernel
    rw [ha]
    exact (canonical21374 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1348 + difference 1 2) (sourceB1348 + difference 2 1) sourceC1348) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4346) := by
    have ha : (tripleCharges (sourceA1348 + difference 1 2) (sourceB1348 + difference 2 1) sourceC1348) = raw21375 := by
      apply Matrix.ext; unfold tripleCharges sourceA1348 sourceB1348 sourceC1348 difference raw21375; decide +kernel
    rw [ha]
    exact (canonical21375 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1348 + difference 1 3) (sourceB1348 + difference 3 1) sourceC1348) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4346) := by
    have ha : (tripleCharges (sourceA1348 + difference 1 3) (sourceB1348 + difference 3 1) sourceC1348) = raw21376 := by
      apply Matrix.ext; unfold tripleCharges sourceA1348 sourceB1348 sourceC1348 difference raw21376; decide +kernel
    rw [ha]
    exact (canonical21376 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1348 + difference 1 4) (sourceB1348 + difference 4 1) sourceC1348) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4505) := by
    have ha : (tripleCharges (sourceA1348 + difference 1 4) (sourceB1348 + difference 4 1) sourceC1348) = raw21377 := by
      apply Matrix.ext; unfold tripleCharges sourceA1348 sourceB1348 sourceC1348 difference raw21377; decide +kernel
    rw [ha]
    exact (canonical21377 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1348 + difference 1 5) (sourceB1348 + difference 5 1) sourceC1348) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4498) := by
    have ha : (tripleCharges (sourceA1348 + difference 1 5) (sourceB1348 + difference 5 1) sourceC1348) = raw11476 := by
      apply Matrix.ext; unfold tripleCharges sourceA1348 sourceB1348 sourceC1348 difference raw11476; decide +kernel
    rw [ha]
    exact (canonical11476 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1348 + difference 2 0) (sourceB1348 + difference 0 2) sourceC1348) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4151) := by
    have ha : (tripleCharges (sourceA1348 + difference 2 0) (sourceB1348 + difference 0 2) sourceC1348) = raw21378 := by
      apply Matrix.ext; unfold tripleCharges sourceA1348 sourceB1348 sourceC1348 difference raw21378; decide +kernel
    rw [ha]
    exact (canonical21378 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1348 + difference 2 1) (sourceB1348 + difference 1 2) sourceC1348) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4365) := by
    have ha : (tripleCharges (sourceA1348 + difference 2 1) (sourceB1348 + difference 1 2) sourceC1348) = raw21379 := by
      apply Matrix.ext; unfold tripleCharges sourceA1348 sourceB1348 sourceC1348 difference raw21379; decide +kernel
    rw [ha]
    exact (canonical21379 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1348 + difference 2 3) (sourceB1348 + difference 3 2) sourceC1348) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4326) := by
    have ha : (tripleCharges (sourceA1348 + difference 2 3) (sourceB1348 + difference 3 2) sourceC1348) = raw21380 := by
      apply Matrix.ext; unfold tripleCharges sourceA1348 sourceB1348 sourceC1348 difference raw21380; decide +kernel
    rw [ha]
    exact (canonical21380 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1348 + difference 2 4) (sourceB1348 + difference 4 2) sourceC1348) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4460) := by
    have ha : (tripleCharges (sourceA1348 + difference 2 4) (sourceB1348 + difference 4 2) sourceC1348) = raw21381 := by
      apply Matrix.ext; unfold tripleCharges sourceA1348 sourceB1348 sourceC1348 difference raw21381; decide +kernel
    rw [ha]
    exact (canonical21381 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1348 + difference 2 5) (sourceB1348 + difference 5 2) sourceC1348) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4457) := by
    have ha : (tripleCharges (sourceA1348 + difference 2 5) (sourceB1348 + difference 5 2) sourceC1348) = raw11481 := by
      apply Matrix.ext; unfold tripleCharges sourceA1348 sourceB1348 sourceC1348 difference raw11481; decide +kernel
    rw [ha]
    exact (canonical11481 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1348 + difference 3 0) (sourceB1348 + difference 0 3) sourceC1348) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4151) := by
    have ha : (tripleCharges (sourceA1348 + difference 3 0) (sourceB1348 + difference 0 3) sourceC1348) = raw21382 := by
      apply Matrix.ext; unfold tripleCharges sourceA1348 sourceB1348 sourceC1348 difference raw21382; decide +kernel
    rw [ha]
    exact (canonical21382 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1348 + difference 3 1) (sourceB1348 + difference 1 3) sourceC1348) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4365) := by
    have ha : (tripleCharges (sourceA1348 + difference 3 1) (sourceB1348 + difference 1 3) sourceC1348) = raw21383 := by
      apply Matrix.ext; unfold tripleCharges sourceA1348 sourceB1348 sourceC1348 difference raw21383; decide +kernel
    rw [ha]
    exact (canonical21383 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1348 + difference 3 2) (sourceB1348 + difference 2 3) sourceC1348) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4326) := by
    have ha : (tripleCharges (sourceA1348 + difference 3 2) (sourceB1348 + difference 2 3) sourceC1348) = raw21384 := by
      apply Matrix.ext; unfold tripleCharges sourceA1348 sourceB1348 sourceC1348 difference raw21384; decide +kernel
    rw [ha]
    exact (canonical21384 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1348 + difference 3 4) (sourceB1348 + difference 4 3) sourceC1348) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4460) := by
    have ha : (tripleCharges (sourceA1348 + difference 3 4) (sourceB1348 + difference 4 3) sourceC1348) = raw21385 := by
      apply Matrix.ext; unfold tripleCharges sourceA1348 sourceB1348 sourceC1348 difference raw21385; decide +kernel
    rw [ha]
    exact (canonical21385 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1348 + difference 3 5) (sourceB1348 + difference 5 3) sourceC1348) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4457) := by
    have ha : (tripleCharges (sourceA1348 + difference 3 5) (sourceB1348 + difference 5 3) sourceC1348) = raw11486 := by
      apply Matrix.ext; unfold tripleCharges sourceA1348 sourceB1348 sourceC1348 difference raw11486; decide +kernel
    rw [ha]
    exact (canonical11486 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1348 + difference 4 0) (sourceB1348 + difference 0 4) sourceC1348) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4160) := by
    have ha : (tripleCharges (sourceA1348 + difference 4 0) (sourceB1348 + difference 0 4) sourceC1348) = raw21386 := by
      apply Matrix.ext; unfold tripleCharges sourceA1348 sourceB1348 sourceC1348 difference raw21386; decide +kernel
    rw [ha]
    exact (canonical21386 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1348 + difference 4 1) (sourceB1348 + difference 1 4) sourceC1348) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4373) := by
    have ha : (tripleCharges (sourceA1348 + difference 4 1) (sourceB1348 + difference 1 4) sourceC1348) = raw21387 := by
      apply Matrix.ext; unfold tripleCharges sourceA1348 sourceB1348 sourceC1348 difference raw21387; decide +kernel
    rw [ha]
    exact (canonical21387 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1348 + difference 4 2) (sourceB1348 + difference 2 4) sourceC1348) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4334) := by
    have ha : (tripleCharges (sourceA1348 + difference 4 2) (sourceB1348 + difference 2 4) sourceC1348) = raw21388 := by
      apply Matrix.ext; unfold tripleCharges sourceA1348 sourceB1348 sourceC1348 difference raw21388; decide +kernel
    rw [ha]
    exact (canonical21388 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1348 + difference 4 3) (sourceB1348 + difference 3 4) sourceC1348) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4334) := by
    have ha : (tripleCharges (sourceA1348 + difference 4 3) (sourceB1348 + difference 3 4) sourceC1348) = raw21389 := by
      apply Matrix.ext; unfold tripleCharges sourceA1348 sourceB1348 sourceC1348 difference raw21389; decide +kernel
    rw [ha]
    exact (canonical21389 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1348 + difference 4 5) (sourceB1348 + difference 5 4) sourceC1348) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4466) := by
    have ha : (tripleCharges (sourceA1348 + difference 4 5) (sourceB1348 + difference 5 4) sourceC1348) = raw11491 := by
      apply Matrix.ext; unfold tripleCharges sourceA1348 sourceB1348 sourceC1348 difference raw11491; decide +kernel
    rw [ha]
    exact (canonical11491 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1348 + difference 5 0) (sourceB1348 + difference 0 5) sourceC1348) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4156) := by
    have ha : (tripleCharges (sourceA1348 + difference 5 0) (sourceB1348 + difference 0 5) sourceC1348) = raw21390 := by
      apply Matrix.ext; unfold tripleCharges sourceA1348 sourceB1348 sourceC1348 difference raw21390; decide +kernel
    rw [ha]
    exact (canonical21390 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1348 + difference 5 1) (sourceB1348 + difference 1 5) sourceC1348) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4370) := by
    have ha : (tripleCharges (sourceA1348 + difference 5 1) (sourceB1348 + difference 1 5) sourceC1348) = raw21391 := by
      apply Matrix.ext; unfold tripleCharges sourceA1348 sourceB1348 sourceC1348 difference raw21391; decide +kernel
    rw [ha]
    exact (canonical21391 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1348 + difference 5 2) (sourceB1348 + difference 2 5) sourceC1348) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4330) := by
    have ha : (tripleCharges (sourceA1348 + difference 5 2) (sourceB1348 + difference 2 5) sourceC1348) = raw21392 := by
      apply Matrix.ext; unfold tripleCharges sourceA1348 sourceB1348 sourceC1348 difference raw21392; decide +kernel
    rw [ha]
    exact (canonical21392 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1348 + difference 5 3) (sourceB1348 + difference 3 5) sourceC1348) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4330) := by
    have ha : (tripleCharges (sourceA1348 + difference 5 3) (sourceB1348 + difference 3 5) sourceC1348) = raw21393 := by
      apply Matrix.ext; unfold tripleCharges sourceA1348 sourceB1348 sourceC1348 difference raw21393; decide +kernel
    rw [ha]
    exact (canonical21393 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1348 + difference 5 4) (sourceB1348 + difference 4 5) sourceC1348) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4468) := by
    have ha : (tripleCharges (sourceA1348 + difference 5 4) (sourceB1348 + difference 4 5) sourceC1348) = raw21394 := by
      apply Matrix.ext; unfold tripleCharges sourceA1348 sourceB1348 sourceC1348 difference raw21394; decide +kernel
    rw [ha]
    exact (canonical21394 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1348 sourceB1348 sourceC1348
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1348, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1350 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1350 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1350 + difference 0 1) (sourceB1350 + difference 1 0) sourceC1350) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2261) := by
    have ha : (tripleCharges (sourceA1350 + difference 0 1) (sourceB1350 + difference 1 0) sourceC1350) = raw21425 := by
      apply Matrix.ext; unfold tripleCharges sourceA1350 sourceB1350 sourceC1350 difference raw21425; decide +kernel
    rw [ha]
    exact (canonical21425 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1350 + difference 0 2) (sourceB1350 + difference 2 0) sourceC1350) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2203) := by
    have ha : (tripleCharges (sourceA1350 + difference 0 2) (sourceB1350 + difference 2 0) sourceC1350) = raw21426 := by
      apply Matrix.ext; unfold tripleCharges sourceA1350 sourceB1350 sourceC1350 difference raw21426; decide +kernel
    rw [ha]
    exact (canonical21426 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1350 + difference 0 3) (sourceB1350 + difference 3 0) sourceC1350) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2203) := by
    have ha : (tripleCharges (sourceA1350 + difference 0 3) (sourceB1350 + difference 3 0) sourceC1350) = raw21427 := by
      apply Matrix.ext; unfold tripleCharges sourceA1350 sourceB1350 sourceC1350 difference raw21427; decide +kernel
    rw [ha]
    exact (canonical21427 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1350 + difference 0 4) (sourceB1350 + difference 4 0) sourceC1350) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2292) := by
    have ha : (tripleCharges (sourceA1350 + difference 0 4) (sourceB1350 + difference 4 0) sourceC1350) = raw21428 := by
      apply Matrix.ext; unfold tripleCharges sourceA1350 sourceB1350 sourceC1350 difference raw21428; decide +kernel
    rw [ha]
    exact (canonical21428 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1350 + difference 0 5) (sourceB1350 + difference 5 0) sourceC1350) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2264) := by
    have ha : (tripleCharges (sourceA1350 + difference 0 5) (sourceB1350 + difference 5 0) sourceC1350) = raw21429 := by
      apply Matrix.ext; unfold tripleCharges sourceA1350 sourceB1350 sourceC1350 difference raw21429; decide +kernel
    rw [ha]
    exact (canonical21429 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1350 + difference 1 0) (sourceB1350 + difference 0 1) sourceC1350) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1518) := by
    have ha : (tripleCharges (sourceA1350 + difference 1 0) (sourceB1350 + difference 0 1) sourceC1350) = raw21430 := by
      apply Matrix.ext; unfold tripleCharges sourceA1350 sourceB1350 sourceC1350 difference raw21430; decide +kernel
    rw [ha]
    exact (canonical21430 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1350 + difference 1 2) (sourceB1350 + difference 2 1) sourceC1350) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1674) := by
    have ha : (tripleCharges (sourceA1350 + difference 1 2) (sourceB1350 + difference 2 1) sourceC1350) = raw21431 := by
      apply Matrix.ext; unfold tripleCharges sourceA1350 sourceB1350 sourceC1350 difference raw21431; decide +kernel
    rw [ha]
    exact (canonical21431 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1350 + difference 1 3) (sourceB1350 + difference 3 1) sourceC1350) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1674) := by
    have ha : (tripleCharges (sourceA1350 + difference 1 3) (sourceB1350 + difference 3 1) sourceC1350) = raw21432 := by
      apply Matrix.ext; unfold tripleCharges sourceA1350 sourceB1350 sourceC1350 difference raw21432; decide +kernel
    rw [ha]
    exact (canonical21432 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1350 + difference 1 4) (sourceB1350 + difference 4 1) sourceC1350) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1754) := by
    have ha : (tripleCharges (sourceA1350 + difference 1 4) (sourceB1350 + difference 4 1) sourceC1350) = raw21433 := by
      apply Matrix.ext; unfold tripleCharges sourceA1350 sourceB1350 sourceC1350 difference raw21433; decide +kernel
    rw [ha]
    exact (canonical21433 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1350 + difference 1 5) (sourceB1350 + difference 5 1) sourceC1350) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1727) := by
    have ha : (tripleCharges (sourceA1350 + difference 1 5) (sourceB1350 + difference 5 1) sourceC1350) = raw21434 := by
      apply Matrix.ext; unfold tripleCharges sourceA1350 sourceB1350 sourceC1350 difference raw21434; decide +kernel
    rw [ha]
    exact (canonical21434 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1350 + difference 2 0) (sourceB1350 + difference 0 2) sourceC1350) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1505) := by
    have ha : (tripleCharges (sourceA1350 + difference 2 0) (sourceB1350 + difference 0 2) sourceC1350) = raw21435 := by
      apply Matrix.ext; unfold tripleCharges sourceA1350 sourceB1350 sourceC1350 difference raw21435; decide +kernel
    rw [ha]
    exact (canonical21435 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1350 + difference 2 1) (sourceB1350 + difference 1 2) sourceC1350) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1704) := by
    have ha : (tripleCharges (sourceA1350 + difference 2 1) (sourceB1350 + difference 1 2) sourceC1350) = raw21436 := by
      apply Matrix.ext; unfold tripleCharges sourceA1350 sourceB1350 sourceC1350 difference raw21436; decide +kernel
    rw [ha]
    exact (canonical21436 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1350 + difference 2 3) (sourceB1350 + difference 3 2) sourceC1350) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1663) := by
    have ha : (tripleCharges (sourceA1350 + difference 2 3) (sourceB1350 + difference 3 2) sourceC1350) = raw21437 := by
      apply Matrix.ext; unfold tripleCharges sourceA1350 sourceB1350 sourceC1350 difference raw21437; decide +kernel
    rw [ha]
    exact (canonical21437 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1350 + difference 2 4) (sourceB1350 + difference 4 2) sourceC1350) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1725) := by
    have ha : (tripleCharges (sourceA1350 + difference 2 4) (sourceB1350 + difference 4 2) sourceC1350) = raw21438 := by
      apply Matrix.ext; unfold tripleCharges sourceA1350 sourceB1350 sourceC1350 difference raw21438; decide +kernel
    rw [ha]
    exact (canonical21438 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1350 + difference 2 5) (sourceB1350 + difference 5 2) sourceC1350) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1707) := by
    have ha : (tripleCharges (sourceA1350 + difference 2 5) (sourceB1350 + difference 5 2) sourceC1350) = raw21439 := by
      apply Matrix.ext; unfold tripleCharges sourceA1350 sourceB1350 sourceC1350 difference raw21439; decide +kernel
    rw [ha]
    exact (canonical21439 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1350 + difference 3 0) (sourceB1350 + difference 0 3) sourceC1350) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1505) := by
    have ha : (tripleCharges (sourceA1350 + difference 3 0) (sourceB1350 + difference 0 3) sourceC1350) = raw21440 := by
      apply Matrix.ext; unfold tripleCharges sourceA1350 sourceB1350 sourceC1350 difference raw21440; decide +kernel
    rw [ha]
    exact (canonical21440 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1350 + difference 3 1) (sourceB1350 + difference 1 3) sourceC1350) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1704) := by
    have ha : (tripleCharges (sourceA1350 + difference 3 1) (sourceB1350 + difference 1 3) sourceC1350) = raw21441 := by
      apply Matrix.ext; unfold tripleCharges sourceA1350 sourceB1350 sourceC1350 difference raw21441; decide +kernel
    rw [ha]
    exact (canonical21441 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1350 + difference 3 2) (sourceB1350 + difference 2 3) sourceC1350) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1663) := by
    have ha : (tripleCharges (sourceA1350 + difference 3 2) (sourceB1350 + difference 2 3) sourceC1350) = raw21442 := by
      apply Matrix.ext; unfold tripleCharges sourceA1350 sourceB1350 sourceC1350 difference raw21442; decide +kernel
    rw [ha]
    exact (canonical21442 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1350 + difference 3 4) (sourceB1350 + difference 4 3) sourceC1350) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1725) := by
    have ha : (tripleCharges (sourceA1350 + difference 3 4) (sourceB1350 + difference 4 3) sourceC1350) = raw21443 := by
      apply Matrix.ext; unfold tripleCharges sourceA1350 sourceB1350 sourceC1350 difference raw21443; decide +kernel
    rw [ha]
    exact (canonical21443 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1350 + difference 3 5) (sourceB1350 + difference 5 3) sourceC1350) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1707) := by
    have ha : (tripleCharges (sourceA1350 + difference 3 5) (sourceB1350 + difference 5 3) sourceC1350) = raw21444 := by
      apply Matrix.ext; unfold tripleCharges sourceA1350 sourceB1350 sourceC1350 difference raw21444; decide +kernel
    rw [ha]
    exact (canonical21444 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1350 + difference 4 0) (sourceB1350 + difference 0 4) sourceC1350) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1523) := by
    have ha : (tripleCharges (sourceA1350 + difference 4 0) (sourceB1350 + difference 0 4) sourceC1350) = raw21445 := by
      apply Matrix.ext; unfold tripleCharges sourceA1350 sourceB1350 sourceC1350 difference raw21445; decide +kernel
    rw [ha]
    exact (canonical21445 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1350 + difference 4 1) (sourceB1350 + difference 1 4) sourceC1350) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1735) := by
    have ha : (tripleCharges (sourceA1350 + difference 4 1) (sourceB1350 + difference 1 4) sourceC1350) = raw21446 := by
      apply Matrix.ext; unfold tripleCharges sourceA1350 sourceB1350 sourceC1350 difference raw21446; decide +kernel
    rw [ha]
    exact (canonical21446 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1350 + difference 4 2) (sourceB1350 + difference 2 4) sourceC1350) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1679) := by
    have ha : (tripleCharges (sourceA1350 + difference 4 2) (sourceB1350 + difference 2 4) sourceC1350) = raw21447 := by
      apply Matrix.ext; unfold tripleCharges sourceA1350 sourceB1350 sourceC1350 difference raw21447; decide +kernel
    rw [ha]
    exact (canonical21447 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1350 + difference 4 3) (sourceB1350 + difference 3 4) sourceC1350) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1679) := by
    have ha : (tripleCharges (sourceA1350 + difference 4 3) (sourceB1350 + difference 3 4) sourceC1350) = raw21448 := by
      apply Matrix.ext; unfold tripleCharges sourceA1350 sourceB1350 sourceC1350 difference raw21448; decide +kernel
    rw [ha]
    exact (canonical21448 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1350 + difference 4 5) (sourceB1350 + difference 5 4) sourceC1350) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1738) := by
    have ha : (tripleCharges (sourceA1350 + difference 4 5) (sourceB1350 + difference 5 4) sourceC1350) = raw21449 := by
      apply Matrix.ext; unfold tripleCharges sourceA1350 sourceB1350 sourceC1350 difference raw21449; decide +kernel
    rw [ha]
    exact (canonical21449 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1350 + difference 5 0) (sourceB1350 + difference 0 5) sourceC1350) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1516) := by
    have ha : (tripleCharges (sourceA1350 + difference 5 0) (sourceB1350 + difference 0 5) sourceC1350) = raw21450 := by
      apply Matrix.ext; unfold tripleCharges sourceA1350 sourceB1350 sourceC1350 difference raw21450; decide +kernel
    rw [ha]
    exact (canonical21450 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1350 + difference 5 1) (sourceB1350 + difference 1 5) sourceC1350) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1722) := by
    have ha : (tripleCharges (sourceA1350 + difference 5 1) (sourceB1350 + difference 1 5) sourceC1350) = raw21451 := by
      apply Matrix.ext; unfold tripleCharges sourceA1350 sourceB1350 sourceC1350 difference raw21451; decide +kernel
    rw [ha]
    exact (canonical21451 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1350 + difference 5 2) (sourceB1350 + difference 2 5) sourceC1350) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1672) := by
    have ha : (tripleCharges (sourceA1350 + difference 5 2) (sourceB1350 + difference 2 5) sourceC1350) = raw21452 := by
      apply Matrix.ext; unfold tripleCharges sourceA1350 sourceB1350 sourceC1350 difference raw21452; decide +kernel
    rw [ha]
    exact (canonical21452 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1350 + difference 5 3) (sourceB1350 + difference 3 5) sourceC1350) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1672) := by
    have ha : (tripleCharges (sourceA1350 + difference 5 3) (sourceB1350 + difference 3 5) sourceC1350) = raw21453 := by
      apply Matrix.ext; unfold tripleCharges sourceA1350 sourceB1350 sourceC1350 difference raw21453; decide +kernel
    rw [ha]
    exact (canonical21453 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1350 + difference 5 4) (sourceB1350 + difference 4 5) sourceC1350) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1752) := by
    have ha : (tripleCharges (sourceA1350 + difference 5 4) (sourceB1350 + difference 4 5) sourceC1350) = raw21454 := by
      apply Matrix.ext; unfold tripleCharges sourceA1350 sourceB1350 sourceC1350 difference raw21454; decide +kernel
    rw [ha]
    exact (canonical21454 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1350 sourceB1350 sourceC1350
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1350, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1351 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1351 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1351 + difference 0 0) (sourceB1351 + difference 0 0) sourceC1351) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1043) := by
    have ha : (tripleCharges (sourceA1351 + difference 0 0) (sourceB1351 + difference 0 0) sourceC1351) = raw21455 := by
      apply Matrix.ext; unfold tripleCharges sourceA1351 sourceB1351 sourceC1351 difference raw21455; decide +kernel
    rw [ha]
    exact (canonical21455 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1351 + difference 1 0) (sourceB1351 + difference 0 1) sourceC1351) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 605) := by
    have ha : (tripleCharges (sourceA1351 + difference 1 0) (sourceB1351 + difference 0 1) sourceC1351) = raw21456 := by
      apply Matrix.ext; unfold tripleCharges sourceA1351 sourceB1351 sourceC1351 difference raw21456; decide +kernel
    rw [ha]
    exact (canonical21456 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1351 + difference 2 0) (sourceB1351 + difference 0 2) sourceC1351) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 579) := by
    have ha : (tripleCharges (sourceA1351 + difference 2 0) (sourceB1351 + difference 0 2) sourceC1351) = raw21457 := by
      apply Matrix.ext; unfold tripleCharges sourceA1351 sourceB1351 sourceC1351 difference raw21457; decide +kernel
    rw [ha]
    exact (canonical21457 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1351 + difference 3 0) (sourceB1351 + difference 0 3) sourceC1351) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 579) := by
    have ha : (tripleCharges (sourceA1351 + difference 3 0) (sourceB1351 + difference 0 3) sourceC1351) = raw21458 := by
      apply Matrix.ext; unfold tripleCharges sourceA1351 sourceB1351 sourceC1351 difference raw21458; decide +kernel
    rw [ha]
    exact (canonical21458 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1351 + difference 4 0) (sourceB1351 + difference 0 4) sourceC1351) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 588) := by
    have ha : (tripleCharges (sourceA1351 + difference 4 0) (sourceB1351 + difference 0 4) sourceC1351) = raw21459 := by
      apply Matrix.ext; unfold tripleCharges sourceA1351 sourceB1351 sourceC1351 difference raw21459; decide +kernel
    rw [ha]
    exact (canonical21459 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1351 + difference 5 0) (sourceB1351 + difference 0 5) sourceC1351) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 584) := by
    have ha : (tripleCharges (sourceA1351 + difference 5 0) (sourceB1351 + difference 0 5) sourceC1351) = raw21460 := by
      apply Matrix.ext; unfold tripleCharges sourceA1351 sourceB1351 sourceC1351 difference raw21460; decide +kernel
    rw [ha]
    exact (canonical21460 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1351 + sourceB1351) sourceC1351) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA1351 + sourceB1351) sourceC1351) = raw21461 := by
      apply Matrix.ext; unfold doubleCharges sourceA1351 sourceB1351 sourceC1351 raw21461; decide +kernel
    rw [ha]
    exact (canonical21461 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1351 sourceB1351 sourceC1351
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1351, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1352 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1352 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1352 + difference 1 0) (sourceB1352 + difference 0 1) sourceC1352) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 605) := by
    have ha : (tripleCharges (sourceA1352 + difference 1 0) (sourceB1352 + difference 0 1) sourceC1352) = raw21456 := by
      apply Matrix.ext; unfold tripleCharges sourceA1352 sourceB1352 sourceC1352 difference raw21456; decide +kernel
    rw [ha]
    exact (canonical21456 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1352 + difference 1 1) (sourceB1352 + difference 1 1) sourceC1352) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1043) := by
    have ha : (tripleCharges (sourceA1352 + difference 1 1) (sourceB1352 + difference 1 1) sourceC1352) = raw21455 := by
      apply Matrix.ext; unfold tripleCharges sourceA1352 sourceB1352 sourceC1352 difference raw21455; decide +kernel
    rw [ha]
    exact (canonical21455 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1352 + difference 1 2) (sourceB1352 + difference 2 1) sourceC1352) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 924) := by
    have ha : (tripleCharges (sourceA1352 + difference 1 2) (sourceB1352 + difference 2 1) sourceC1352) = raw21462 := by
      apply Matrix.ext; unfold tripleCharges sourceA1352 sourceB1352 sourceC1352 difference raw21462; decide +kernel
    rw [ha]
    exact (canonical21462 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1352 + difference 1 3) (sourceB1352 + difference 3 1) sourceC1352) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 924) := by
    have ha : (tripleCharges (sourceA1352 + difference 1 3) (sourceB1352 + difference 3 1) sourceC1352) = raw21463 := by
      apply Matrix.ext; unfold tripleCharges sourceA1352 sourceB1352 sourceC1352 difference raw21463; decide +kernel
    rw [ha]
    exact (canonical21463 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1352 + difference 1 4) (sourceB1352 + difference 4 1) sourceC1352) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1089) := by
    have ha : (tripleCharges (sourceA1352 + difference 1 4) (sourceB1352 + difference 4 1) sourceC1352) = raw21464 := by
      apply Matrix.ext; unfold tripleCharges sourceA1352 sourceB1352 sourceC1352 difference raw21464; decide +kernel
    rw [ha]
    exact (canonical21464 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1352 + difference 1 5) (sourceB1352 + difference 5 1) sourceC1352) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1082) := by
    have ha : (tripleCharges (sourceA1352 + difference 1 5) (sourceB1352 + difference 5 1) sourceC1352) = raw21465 := by
      apply Matrix.ext; unfold tripleCharges sourceA1352 sourceB1352 sourceC1352 difference raw21465; decide +kernel
    rw [ha]
    exact (canonical21465 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1352 + sourceB1352) sourceC1352) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA1352 + sourceB1352) sourceC1352) = raw21461 := by
      apply Matrix.ext; unfold doubleCharges sourceA1352 sourceB1352 sourceC1352 raw21461; decide +kernel
    rw [ha]
    exact (canonical21461 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1352 sourceB1352 sourceC1352
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1352, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1353 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1353 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1353 + difference 0 1) (sourceB1353 + difference 1 0) sourceC1353) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2109) := by
    have ha : (tripleCharges (sourceA1353 + difference 0 1) (sourceB1353 + difference 1 0) sourceC1353) = raw21466 := by
      apply Matrix.ext; unfold tripleCharges sourceA1353 sourceB1353 sourceC1353 difference raw21466; decide +kernel
    rw [ha]
    exact (canonical21466 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1353 + difference 1 1) (sourceB1353 + difference 1 1) sourceC1353) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1043) := by
    have ha : (tripleCharges (sourceA1353 + difference 1 1) (sourceB1353 + difference 1 1) sourceC1353) = raw21455 := by
      apply Matrix.ext; unfold tripleCharges sourceA1353 sourceB1353 sourceC1353 difference raw21455; decide +kernel
    rw [ha]
    exact (canonical21455 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1353 + difference 2 1) (sourceB1353 + difference 1 2) sourceC1353) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 943) := by
    have ha : (tripleCharges (sourceA1353 + difference 2 1) (sourceB1353 + difference 1 2) sourceC1353) = raw21467 := by
      apply Matrix.ext; unfold tripleCharges sourceA1353 sourceB1353 sourceC1353 difference raw21467; decide +kernel
    rw [ha]
    exact (canonical21467 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1353 + difference 3 1) (sourceB1353 + difference 1 3) sourceC1353) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 943) := by
    have ha : (tripleCharges (sourceA1353 + difference 3 1) (sourceB1353 + difference 1 3) sourceC1353) = raw21468 := by
      apply Matrix.ext; unfold tripleCharges sourceA1353 sourceB1353 sourceC1353 difference raw21468; decide +kernel
    rw [ha]
    exact (canonical21468 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1353 + difference 4 1) (sourceB1353 + difference 1 4) sourceC1353) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 952) := by
    have ha : (tripleCharges (sourceA1353 + difference 4 1) (sourceB1353 + difference 1 4) sourceC1353) = raw21469 := by
      apply Matrix.ext; unfold tripleCharges sourceA1353 sourceB1353 sourceC1353 difference raw21469; decide +kernel
    rw [ha]
    exact (canonical21469 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1353 + difference 5 1) (sourceB1353 + difference 1 5) sourceC1353) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 948) := by
    have ha : (tripleCharges (sourceA1353 + difference 5 1) (sourceB1353 + difference 1 5) sourceC1353) = raw21470 := by
      apply Matrix.ext; unfold tripleCharges sourceA1353 sourceB1353 sourceC1353 difference raw21470; decide +kernel
    rw [ha]
    exact (canonical21470 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1353 + sourceB1353) sourceC1353) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA1353 + sourceB1353) sourceC1353) = raw21461 := by
      apply Matrix.ext; unfold doubleCharges sourceA1353 sourceB1353 sourceC1353 raw21461; decide +kernel
    rw [ha]
    exact (canonical21461 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1353 sourceB1353 sourceC1353
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1353, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1354 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1354 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1354 + difference 2 0) (sourceB1354 + difference 0 2) sourceC1354) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 579) := by
    have ha : (tripleCharges (sourceA1354 + difference 2 0) (sourceB1354 + difference 0 2) sourceC1354) = raw21457 := by
      apply Matrix.ext; unfold tripleCharges sourceA1354 sourceB1354 sourceC1354 difference raw21457; decide +kernel
    rw [ha]
    exact (canonical21457 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1354 + difference 2 1) (sourceB1354 + difference 1 2) sourceC1354) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 943) := by
    have ha : (tripleCharges (sourceA1354 + difference 2 1) (sourceB1354 + difference 1 2) sourceC1354) = raw21467 := by
      apply Matrix.ext; unfold tripleCharges sourceA1354 sourceB1354 sourceC1354 difference raw21467; decide +kernel
    rw [ha]
    exact (canonical21467 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1354 + difference 2 2) (sourceB1354 + difference 2 2) sourceC1354) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1043) := by
    have ha : (tripleCharges (sourceA1354 + difference 2 2) (sourceB1354 + difference 2 2) sourceC1354) = raw21455 := by
      apply Matrix.ext; unfold tripleCharges sourceA1354 sourceB1354 sourceC1354 difference raw21455; decide +kernel
    rw [ha]
    exact (canonical21455 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1354 + difference 2 3) (sourceB1354 + difference 3 2) sourceC1354) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 904) := by
    have ha : (tripleCharges (sourceA1354 + difference 2 3) (sourceB1354 + difference 3 2) sourceC1354) = raw21471 := by
      apply Matrix.ext; unfold tripleCharges sourceA1354 sourceB1354 sourceC1354 difference raw21471; decide +kernel
    rw [ha]
    exact (canonical21471 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1354 + difference 2 4) (sourceB1354 + difference 4 2) sourceC1354) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1043) := by
    have ha : (tripleCharges (sourceA1354 + difference 2 4) (sourceB1354 + difference 4 2) sourceC1354) = raw21472 := by
      apply Matrix.ext; unfold tripleCharges sourceA1354 sourceB1354 sourceC1354 difference raw21472; decide +kernel
    rw [ha]
    exact (canonical21472 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1354 + difference 2 5) (sourceB1354 + difference 5 2) sourceC1354) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1040) := by
    have ha : (tripleCharges (sourceA1354 + difference 2 5) (sourceB1354 + difference 5 2) sourceC1354) = raw21473 := by
      apply Matrix.ext; unfold tripleCharges sourceA1354 sourceB1354 sourceC1354 difference raw21473; decide +kernel
    rw [ha]
    exact (canonical21473 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1354 + sourceB1354) sourceC1354) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA1354 + sourceB1354) sourceC1354) = raw21461 := by
      apply Matrix.ext; unfold doubleCharges sourceA1354 sourceB1354 sourceC1354 raw21461; decide +kernel
    rw [ha]
    exact (canonical21461 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1354 sourceB1354 sourceC1354
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1354, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1355 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1355 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1355 + difference 0 2) (sourceB1355 + difference 2 0) sourceC1355) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2022) := by
    have ha : (tripleCharges (sourceA1355 + difference 0 2) (sourceB1355 + difference 2 0) sourceC1355) = raw21474 := by
      apply Matrix.ext; unfold tripleCharges sourceA1355 sourceB1355 sourceC1355 difference raw21474; decide +kernel
    rw [ha]
    exact (canonical21474 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1355 + difference 1 2) (sourceB1355 + difference 2 1) sourceC1355) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 924) := by
    have ha : (tripleCharges (sourceA1355 + difference 1 2) (sourceB1355 + difference 2 1) sourceC1355) = raw21462 := by
      apply Matrix.ext; unfold tripleCharges sourceA1355 sourceB1355 sourceC1355 difference raw21462; decide +kernel
    rw [ha]
    exact (canonical21462 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1355 + difference 2 2) (sourceB1355 + difference 2 2) sourceC1355) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1043) := by
    have ha : (tripleCharges (sourceA1355 + difference 2 2) (sourceB1355 + difference 2 2) sourceC1355) = raw21455 := by
      apply Matrix.ext; unfold tripleCharges sourceA1355 sourceB1355 sourceC1355 difference raw21455; decide +kernel
    rw [ha]
    exact (canonical21455 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1355 + difference 3 2) (sourceB1355 + difference 2 3) sourceC1355) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 904) := by
    have ha : (tripleCharges (sourceA1355 + difference 3 2) (sourceB1355 + difference 2 3) sourceC1355) = raw21475 := by
      apply Matrix.ext; unfold tripleCharges sourceA1355 sourceB1355 sourceC1355 difference raw21475; decide +kernel
    rw [ha]
    exact (canonical21475 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1355 + difference 4 2) (sourceB1355 + difference 2 4) sourceC1355) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 912) := by
    have ha : (tripleCharges (sourceA1355 + difference 4 2) (sourceB1355 + difference 2 4) sourceC1355) = raw21476 := by
      apply Matrix.ext; unfold tripleCharges sourceA1355 sourceB1355 sourceC1355 difference raw21476; decide +kernel
    rw [ha]
    exact (canonical21476 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1355 + difference 5 2) (sourceB1355 + difference 2 5) sourceC1355) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 908) := by
    have ha : (tripleCharges (sourceA1355 + difference 5 2) (sourceB1355 + difference 2 5) sourceC1355) = raw21477 := by
      apply Matrix.ext; unfold tripleCharges sourceA1355 sourceB1355 sourceC1355 difference raw21477; decide +kernel
    rw [ha]
    exact (canonical21477 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1355 + sourceB1355) sourceC1355) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA1355 + sourceB1355) sourceC1355) = raw21461 := by
      apply Matrix.ext; unfold doubleCharges sourceA1355 sourceB1355 sourceC1355 raw21461; decide +kernel
    rw [ha]
    exact (canonical21461 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1355 sourceB1355 sourceC1355
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1355, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1361 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1361 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1361 + difference 0 0) (sourceB1361 + difference 0 0) sourceC1361) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1037) := by
    have ha : (tripleCharges (sourceA1361 + difference 0 0) (sourceB1361 + difference 0 0) sourceC1361) = raw21563 := by
      apply Matrix.ext; unfold tripleCharges sourceA1361 sourceB1361 sourceC1361 difference raw21563; decide +kernel
    rw [ha]
    exact (canonical21563 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1361 + difference 0 1) (sourceB1361 + difference 1 0) sourceC1361) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2103) := by
    have ha : (tripleCharges (sourceA1361 + difference 0 1) (sourceB1361 + difference 1 0) sourceC1361) = raw21564 := by
      apply Matrix.ext; unfold tripleCharges sourceA1361 sourceB1361 sourceC1361 difference raw21564; decide +kernel
    rw [ha]
    exact (canonical21564 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1361 + difference 0 2) (sourceB1361 + difference 2 0) sourceC1361) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2018) := by
    have ha : (tripleCharges (sourceA1361 + difference 0 2) (sourceB1361 + difference 2 0) sourceC1361) = raw21565 := by
      apply Matrix.ext; unfold tripleCharges sourceA1361 sourceB1361 sourceC1361 difference raw21565; decide +kernel
    rw [ha]
    exact (canonical21565 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1361 + difference 0 3) (sourceB1361 + difference 3 0) sourceC1361) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2018) := by
    have ha : (tripleCharges (sourceA1361 + difference 0 3) (sourceB1361 + difference 3 0) sourceC1361) = raw21566 := by
      apply Matrix.ext; unfold tripleCharges sourceA1361 sourceB1361 sourceC1361 difference raw21566; decide +kernel
    rw [ha]
    exact (canonical21566 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1361 + difference 0 4) (sourceB1361 + difference 4 0) sourceC1361) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2208) := by
    have ha : (tripleCharges (sourceA1361 + difference 0 4) (sourceB1361 + difference 4 0) sourceC1361) = raw19875 := by
      apply Matrix.ext; unfold tripleCharges sourceA1361 sourceB1361 sourceC1361 difference raw19875; decide +kernel
    rw [ha]
    exact (canonical19875 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1361 + difference 0 5) (sourceB1361 + difference 5 0) sourceC1361) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2261) := by
    have ha : (tripleCharges (sourceA1361 + difference 0 5) (sourceB1361 + difference 5 0) sourceC1361) = raw21567 := by
      apply Matrix.ext; unfold tripleCharges sourceA1361 sourceB1361 sourceC1361 difference raw21567; decide +kernel
    rw [ha]
    exact (canonical21567 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1361 + sourceB1361) sourceC1361) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4081) := by
    have ha : (doubleCharges (sourceA1361 + sourceB1361) sourceC1361) = raw19876 := by
      apply Matrix.ext; unfold doubleCharges sourceA1361 sourceB1361 sourceC1361 raw19876; decide +kernel
    rw [ha]
    exact (canonical19876 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1361 sourceB1361 sourceC1361
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1361, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1362 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1362 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1362 + difference 1 0) (sourceB1362 + difference 0 1) sourceC1362) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 594) := by
    have ha : (tripleCharges (sourceA1362 + difference 1 0) (sourceB1362 + difference 0 1) sourceC1362) = raw21568 := by
      apply Matrix.ext; unfold tripleCharges sourceA1362 sourceB1362 sourceC1362 difference raw21568; decide +kernel
    rw [ha]
    exact (canonical21568 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1362 + difference 1 1) (sourceB1362 + difference 1 1) sourceC1362) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1037) := by
    have ha : (tripleCharges (sourceA1362 + difference 1 1) (sourceB1362 + difference 1 1) sourceC1362) = raw21563 := by
      apply Matrix.ext; unfold tripleCharges sourceA1362 sourceB1362 sourceC1362 difference raw21563; decide +kernel
    rw [ha]
    exact (canonical21563 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1362 + difference 1 2) (sourceB1362 + difference 2 1) sourceC1362) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 916) := by
    have ha : (tripleCharges (sourceA1362 + difference 1 2) (sourceB1362 + difference 2 1) sourceC1362) = raw21569 := by
      apply Matrix.ext; unfold tripleCharges sourceA1362 sourceB1362 sourceC1362 difference raw21569; decide +kernel
    rw [ha]
    exact (canonical21569 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1362 + difference 1 3) (sourceB1362 + difference 3 1) sourceC1362) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 916) := by
    have ha : (tripleCharges (sourceA1362 + difference 1 3) (sourceB1362 + difference 3 1) sourceC1362) = raw21570 := by
      apply Matrix.ext; unfold tripleCharges sourceA1362 sourceB1362 sourceC1362 difference raw21570; decide +kernel
    rw [ha]
    exact (canonical21570 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1362 + difference 1 4) (sourceB1362 + difference 4 1) sourceC1362) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1007) := by
    have ha : (tripleCharges (sourceA1362 + difference 1 4) (sourceB1362 + difference 4 1) sourceC1362) = raw19881 := by
      apply Matrix.ext; unfold tripleCharges sourceA1362 sourceB1362 sourceC1362 difference raw19881; decide +kernel
    rw [ha]
    exact (canonical19881 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1362 + difference 1 5) (sourceB1362 + difference 5 1) sourceC1362) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1074) := by
    have ha : (tripleCharges (sourceA1362 + difference 1 5) (sourceB1362 + difference 5 1) sourceC1362) = raw21571 := by
      apply Matrix.ext; unfold tripleCharges sourceA1362 sourceB1362 sourceC1362 difference raw21571; decide +kernel
    rw [ha]
    exact (canonical21571 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1362 + sourceB1362) sourceC1362) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4081) := by
    have ha : (doubleCharges (sourceA1362 + sourceB1362) sourceC1362) = raw19876 := by
      apply Matrix.ext; unfold doubleCharges sourceA1362 sourceB1362 sourceC1362 raw19876; decide +kernel
    rw [ha]
    exact (canonical19876 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1362 sourceB1362 sourceC1362
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1362, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1363 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1363 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1363 + difference 0 5) (sourceB1363 + difference 5 0) sourceC1363) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2261) := by
    have ha : (tripleCharges (sourceA1363 + difference 0 5) (sourceB1363 + difference 5 0) sourceC1363) = raw21567 := by
      apply Matrix.ext; unfold tripleCharges sourceA1363 sourceB1363 sourceC1363 difference raw21567; decide +kernel
    rw [ha]
    exact (canonical21567 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1363 + difference 1 5) (sourceB1363 + difference 5 1) sourceC1363) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1074) := by
    have ha : (tripleCharges (sourceA1363 + difference 1 5) (sourceB1363 + difference 5 1) sourceC1363) = raw21571 := by
      apply Matrix.ext; unfold tripleCharges sourceA1363 sourceB1363 sourceC1363 difference raw21571; decide +kernel
    rw [ha]
    exact (canonical21571 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1363 + difference 2 5) (sourceB1363 + difference 5 2) sourceC1363) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1033) := by
    have ha : (tripleCharges (sourceA1363 + difference 2 5) (sourceB1363 + difference 5 2) sourceC1363) = raw21572 := by
      apply Matrix.ext; unfold tripleCharges sourceA1363 sourceB1363 sourceC1363 difference raw21572; decide +kernel
    rw [ha]
    exact (canonical21572 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1363 + difference 3 5) (sourceB1363 + difference 5 3) sourceC1363) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1033) := by
    have ha : (tripleCharges (sourceA1363 + difference 3 5) (sourceB1363 + difference 5 3) sourceC1363) = raw21573 := by
      apply Matrix.ext; unfold tripleCharges sourceA1363 sourceB1363 sourceC1363 difference raw21573; decide +kernel
    rw [ha]
    exact (canonical21573 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1363 + difference 4 5) (sourceB1363 + difference 5 4) sourceC1363) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1048) := by
    have ha : (tripleCharges (sourceA1363 + difference 4 5) (sourceB1363 + difference 5 4) sourceC1363) = raw21574 := by
      apply Matrix.ext; unfold tripleCharges sourceA1363 sourceB1363 sourceC1363 difference raw21574; decide +kernel
    rw [ha]
    exact (canonical21574 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1363 + difference 5 5) (sourceB1363 + difference 5 5) sourceC1363) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1037) := by
    have ha : (tripleCharges (sourceA1363 + difference 5 5) (sourceB1363 + difference 5 5) sourceC1363) = raw21563 := by
      apply Matrix.ext; unfold tripleCharges sourceA1363 sourceB1363 sourceC1363 difference raw21563; decide +kernel
    rw [ha]
    exact (canonical21563 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1363 + sourceB1363) sourceC1363) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4081) := by
    have ha : (doubleCharges (sourceA1363 + sourceB1363) sourceC1363) = raw19876 := by
      apply Matrix.ext; unfold doubleCharges sourceA1363 sourceB1363 sourceC1363 raw19876; decide +kernel
    rw [ha]
    exact (canonical19876 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1363 sourceB1363 sourceC1363
    (0 : Fin 2) 1 (5 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1363, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1364 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1364 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1364 + difference 0 0) (sourceB1364 + difference 0 0) sourceC1364) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1647) := by
    have ha : (tripleCharges (sourceA1364 + difference 0 0) (sourceB1364 + difference 0 0) sourceC1364) = raw20643 := by
      apply Matrix.ext; unfold tripleCharges sourceA1364 sourceB1364 sourceC1364 difference raw20643; decide +kernel
    rw [ha]
    exact (canonical20643 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1364 + difference 1 0) (sourceB1364 + difference 0 1) sourceC1364) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 741) := by
    have ha : (tripleCharges (sourceA1364 + difference 1 0) (sourceB1364 + difference 0 1) sourceC1364) = raw21575 := by
      apply Matrix.ext; unfold tripleCharges sourceA1364 sourceB1364 sourceC1364 difference raw21575; decide +kernel
    rw [ha]
    exact (canonical21575 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1364 + difference 2 0) (sourceB1364 + difference 0 2) sourceC1364) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 731) := by
    have ha : (tripleCharges (sourceA1364 + difference 2 0) (sourceB1364 + difference 0 2) sourceC1364) = raw21576 := by
      apply Matrix.ext; unfold tripleCharges sourceA1364 sourceB1364 sourceC1364 difference raw21576; decide +kernel
    rw [ha]
    exact (canonical21576 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1364 + difference 3 0) (sourceB1364 + difference 0 3) sourceC1364) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 731) := by
    have ha : (tripleCharges (sourceA1364 + difference 3 0) (sourceB1364 + difference 0 3) sourceC1364) = raw21577 := by
      apply Matrix.ext; unfold tripleCharges sourceA1364 sourceB1364 sourceC1364 difference raw21577; decide +kernel
    rw [ha]
    exact (canonical21577 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1364 + difference 4 0) (sourceB1364 + difference 0 4) sourceC1364) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 809) := by
    have ha : (tripleCharges (sourceA1364 + difference 4 0) (sourceB1364 + difference 0 4) sourceC1364) = raw21578 := by
      apply Matrix.ext; unfold tripleCharges sourceA1364 sourceB1364 sourceC1364 difference raw21578; decide +kernel
    rw [ha]
    exact (canonical21578 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1364 + difference 5 0) (sourceB1364 + difference 0 5) sourceC1364) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 735) := by
    have ha : (tripleCharges (sourceA1364 + difference 5 0) (sourceB1364 + difference 0 5) sourceC1364) = raw21579 := by
      apply Matrix.ext; unfold tripleCharges sourceA1364 sourceB1364 sourceC1364 difference raw21579; decide +kernel
    rw [ha]
    exact (canonical21579 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1364 + sourceB1364) sourceC1364) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4070) := by
    have ha : (doubleCharges (sourceA1364 + sourceB1364) sourceC1364) = raw20099 := by
      apply Matrix.ext; unfold doubleCharges sourceA1364 sourceB1364 sourceC1364 raw20099; decide +kernel
    rw [ha]
    exact (canonical20099 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1364 sourceB1364 sourceC1364
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1364, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic73
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reindexCheck1168 : Integer.Sparse.reindex keyMap MixedData.row1168 = numericRow1168 := by decide +kernel

theorem numericCheck1168 (x : Master → ℝ) : Integer.Sparse.eval numericRow1168 x =
    (1 : ℝ) * reducedSource1168 x := by
  norm_num [numericRow1168, reducedSource1168, Integer.Sparse.eval, Sparse.eval, nodeValue847, nodeValue851, nodeValue853, nodeValue857, nodeValue1750, nodeValue4070]

theorem reindexCheck1169 : Integer.Sparse.reindex keyMap MixedData.row1169 = numericRow1169 := by decide +kernel

theorem numericCheck1169 (x : Master → ℝ) : Integer.Sparse.eval numericRow1169 x =
    (4 : ℝ) * reducedSource1169 x := by
  norm_num [numericRow1169, reducedSource1169, Integer.Sparse.eval, Sparse.eval, nodeValue4151, nodeValue4156, nodeValue4160, nodeValue4177, nodeValue4326, nodeValue4330, nodeValue4334, nodeValue4346, nodeValue4365, nodeValue4370, nodeValue4373, nodeValue4457, nodeValue4460, nodeValue4466, nodeValue4468, nodeValue4498, nodeValue4505, nodeValue4804, nodeValue4868, nodeValue4894, nodeValue4897]
  ring

theorem reindexCheck1171 : Integer.Sparse.reindex keyMap MixedData.row1171 = numericRow1171 := by decide +kernel

theorem numericCheck1171 (x : Master → ℝ) : Integer.Sparse.eval numericRow1171 x =
    (1 : ℝ) * reducedSource1171 x := by
  norm_num [numericRow1171, reducedSource1171, Integer.Sparse.eval, Sparse.eval, nodeValue1505, nodeValue1516, nodeValue1518, nodeValue1523, nodeValue1663, nodeValue1672, nodeValue1674, nodeValue1679, nodeValue1704, nodeValue1707, nodeValue1722, nodeValue1725, nodeValue1727, nodeValue1735, nodeValue1738, nodeValue1752, nodeValue1754, nodeValue2203, nodeValue2261, nodeValue2264, nodeValue2292]

theorem reindexCheck1172 : Integer.Sparse.reindex keyMap MixedData.row1172 = numericRow1172 := by decide +kernel

theorem numericCheck1172 (x : Master → ℝ) : Integer.Sparse.eval numericRow1172 x =
    (1 : ℝ) * reducedSource1172 x := by
  norm_num [numericRow1172, reducedSource1172, Integer.Sparse.eval, Sparse.eval, nodeValue579, nodeValue584, nodeValue588, nodeValue605, nodeValue1043, nodeValue4084]

theorem reindexCheck1173 : Integer.Sparse.reindex keyMap MixedData.row1173 = numericRow1173 := by decide +kernel

theorem numericCheck1173 (x : Master → ℝ) : Integer.Sparse.eval numericRow1173 x =
    (1 : ℝ) * reducedSource1173 x := by
  norm_num [numericRow1173, reducedSource1173, Integer.Sparse.eval, Sparse.eval, nodeValue605, nodeValue924, nodeValue1043, nodeValue1082, nodeValue1089, nodeValue4084]

theorem reindexCheck1174 : Integer.Sparse.reindex keyMap MixedData.row1174 = numericRow1174 := by decide +kernel

theorem numericCheck1174 (x : Master → ℝ) : Integer.Sparse.eval numericRow1174 x =
    (1 : ℝ) * reducedSource1174 x := by
  norm_num [numericRow1174, reducedSource1174, Integer.Sparse.eval, Sparse.eval, nodeValue943, nodeValue948, nodeValue952, nodeValue1043, nodeValue2109, nodeValue4084]

theorem reindexCheck1175 : Integer.Sparse.reindex keyMap MixedData.row1175 = numericRow1175 := by decide +kernel

theorem numericCheck1175 (x : Master → ℝ) : Integer.Sparse.eval numericRow1175 x =
    (1 : ℝ) * reducedSource1175 x := by
  norm_num [numericRow1175, reducedSource1175, Integer.Sparse.eval, Sparse.eval, nodeValue579, nodeValue904, nodeValue943, nodeValue1040, nodeValue1043, nodeValue4084]

theorem reindexCheck1176 : Integer.Sparse.reindex keyMap MixedData.row1176 = numericRow1176 := by decide +kernel

theorem numericCheck1176 (x : Master → ℝ) : Integer.Sparse.eval numericRow1176 x =
    (1 : ℝ) * reducedSource1176 x := by
  norm_num [numericRow1176, reducedSource1176, Integer.Sparse.eval, Sparse.eval, nodeValue904, nodeValue908, nodeValue912, nodeValue924, nodeValue1043, nodeValue2022, nodeValue4084]

theorem reindexCheck1180 : Integer.Sparse.reindex keyMap MixedData.row1180 = numericRow1180 := by decide +kernel

theorem numericCheck1180 (x : Master → ℝ) : Integer.Sparse.eval numericRow1180 x =
    (1 : ℝ) * reducedSource1180 x := by
  norm_num [numericRow1180, reducedSource1180, Integer.Sparse.eval, Sparse.eval, nodeValue1037, nodeValue2018, nodeValue2103, nodeValue2208, nodeValue2261, nodeValue4081]

theorem reindexCheck1181 : Integer.Sparse.reindex keyMap MixedData.row1181 = numericRow1181 := by decide +kernel

theorem numericCheck1181 (x : Master → ℝ) : Integer.Sparse.eval numericRow1181 x =
    (1 : ℝ) * reducedSource1181 x := by
  norm_num [numericRow1181, reducedSource1181, Integer.Sparse.eval, Sparse.eval, nodeValue594, nodeValue916, nodeValue1007, nodeValue1037, nodeValue1074, nodeValue4081]

theorem reindexCheck1182 : Integer.Sparse.reindex keyMap MixedData.row1182 = numericRow1182 := by decide +kernel

theorem numericCheck1182 (x : Master → ℝ) : Integer.Sparse.eval numericRow1182 x =
    (1 : ℝ) * reducedSource1182 x := by
  norm_num [numericRow1182, reducedSource1182, Integer.Sparse.eval, Sparse.eval, nodeValue1033, nodeValue1037, nodeValue1048, nodeValue1074, nodeValue2261, nodeValue4081]

theorem reindexCheck1183 : Integer.Sparse.reindex keyMap MixedData.row1183 = numericRow1183 := by decide +kernel

theorem numericCheck1183 (x : Master → ℝ) : Integer.Sparse.eval numericRow1183 x =
    (1 : ℝ) * reducedSource1183 x := by
  norm_num [numericRow1183, reducedSource1183, Integer.Sparse.eval, Sparse.eval, nodeValue731, nodeValue735, nodeValue741, nodeValue809, nodeValue1647, nodeValue4070]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Rows73
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero1168 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1168 (mixedVector B) = 0 := by
  have h847 : mixedVector B (Sum.inr 847) = Sparse.eval nodeValue847 (mixedVector B) := by
    change mixedMoment B node847 node847Labels = _
    exact sound847 B hB hF
  have h851 : mixedVector B (Sum.inr 851) = Sparse.eval nodeValue851 (mixedVector B) := by
    change mixedMoment B node851 node851Labels = _
    exact sound851 B hB hF
  have h853 : mixedVector B (Sum.inr 853) = Sparse.eval nodeValue853 (mixedVector B) := by
    change mixedMoment B node853 node853Labels = _
    exact sound853 B hB hF
  have h857 : mixedVector B (Sum.inr 857) = Sparse.eval nodeValue857 (mixedVector B) := by
    change mixedMoment B node857 node857Labels = _
    exact sound857 B hB hF
  have h1750 : mixedVector B (Sum.inr 1750) = Sparse.eval nodeValue1750 (mixedVector B) := by
    change mixedMoment B node1750 node1750Labels = _
    exact sound1750 B hB hF
  have h4070 : mixedVector B (Sum.inr 4070) = Sparse.eval nodeValue4070 (mixedVector B) := by
    change mixedMoment B node4070 node4070Labels = _
    exact sound4070 B hB hF
  simpa only [sourceForm1347, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h847, h851, h853, h857, h1750, h4070, reducedSource1168] using sourceEq1347 B hB

theorem rowSound1168 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1168 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1168, numericCheck1168, reducedZero1168 B hB hF, mul_zero]

theorem reducedZero1169 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1169 (mixedVector B) = 0 := by
  have h4151 : mixedVector B (Sum.inr 4151) = Sparse.eval nodeValue4151 (mixedVector B) := by
    change mixedMoment B node4151 node4151Labels = _
    exact sound4151 B hB hF
  have h4156 : mixedVector B (Sum.inr 4156) = Sparse.eval nodeValue4156 (mixedVector B) := by
    change mixedMoment B node4156 node4156Labels = _
    exact sound4156 B hB hF
  have h4160 : mixedVector B (Sum.inr 4160) = Sparse.eval nodeValue4160 (mixedVector B) := by
    change mixedMoment B node4160 node4160Labels = _
    exact sound4160 B hB hF
  have h4177 : mixedVector B (Sum.inr 4177) = Sparse.eval nodeValue4177 (mixedVector B) := by
    change mixedMoment B node4177 node4177Labels = _
    exact sound4177 B hB hF
  have h4326 : mixedVector B (Sum.inr 4326) = Sparse.eval nodeValue4326 (mixedVector B) := by
    change mixedMoment B node4326 node4326Labels = _
    exact sound4326 B hB hF
  have h4330 : mixedVector B (Sum.inr 4330) = Sparse.eval nodeValue4330 (mixedVector B) := by
    change mixedMoment B node4330 node4330Labels = _
    exact sound4330 B hB hF
  have h4334 : mixedVector B (Sum.inr 4334) = Sparse.eval nodeValue4334 (mixedVector B) := by
    change mixedMoment B node4334 node4334Labels = _
    exact sound4334 B hB hF
  have h4346 : mixedVector B (Sum.inr 4346) = Sparse.eval nodeValue4346 (mixedVector B) := by
    change mixedMoment B node4346 node4346Labels = _
    exact sound4346 B hB hF
  have h4365 : mixedVector B (Sum.inr 4365) = Sparse.eval nodeValue4365 (mixedVector B) := by
    change mixedMoment B node4365 node4365Labels = _
    exact sound4365 B hB hF
  have h4370 : mixedVector B (Sum.inr 4370) = Sparse.eval nodeValue4370 (mixedVector B) := by
    change mixedMoment B node4370 node4370Labels = _
    exact sound4370 B hB hF
  have h4373 : mixedVector B (Sum.inr 4373) = Sparse.eval nodeValue4373 (mixedVector B) := by
    change mixedMoment B node4373 node4373Labels = _
    exact sound4373 B hB hF
  have h4457 : mixedVector B (Sum.inr 4457) = Sparse.eval nodeValue4457 (mixedVector B) := by
    change mixedMoment B node4457 node4457Labels = _
    exact sound4457 B hB hF
  have h4460 : mixedVector B (Sum.inr 4460) = Sparse.eval nodeValue4460 (mixedVector B) := by
    change mixedMoment B node4460 node4460Labels = _
    exact sound4460 B hB hF
  have h4466 : mixedVector B (Sum.inr 4466) = Sparse.eval nodeValue4466 (mixedVector B) := by
    change mixedMoment B node4466 node4466Labels = _
    exact sound4466 B hB hF
  have h4468 : mixedVector B (Sum.inr 4468) = Sparse.eval nodeValue4468 (mixedVector B) := by
    change mixedMoment B node4468 node4468Labels = _
    exact sound4468 B hB hF
  have h4498 : mixedVector B (Sum.inr 4498) = Sparse.eval nodeValue4498 (mixedVector B) := by
    change mixedMoment B node4498 node4498Labels = _
    exact sound4498 B hB hF
  have h4505 : mixedVector B (Sum.inr 4505) = Sparse.eval nodeValue4505 (mixedVector B) := by
    change mixedMoment B node4505 node4505Labels = _
    exact sound4505 B hB hF
  have h4804 : mixedVector B (Sum.inr 4804) = Sparse.eval nodeValue4804 (mixedVector B) := by
    change mixedMoment B node4804 node4804Labels = _
    exact sound4804 B hB hF
  have h4868 : mixedVector B (Sum.inr 4868) = Sparse.eval nodeValue4868 (mixedVector B) := by
    change mixedMoment B node4868 node4868Labels = _
    exact sound4868 B hB hF
  have h4894 : mixedVector B (Sum.inr 4894) = Sparse.eval nodeValue4894 (mixedVector B) := by
    change mixedMoment B node4894 node4894Labels = _
    exact sound4894 B hB hF
  have h4897 : mixedVector B (Sum.inr 4897) = Sparse.eval nodeValue4897 (mixedVector B) := by
    change mixedMoment B node4897 node4897Labels = _
    exact sound4897 B hB hF
  simpa only [sourceForm1348, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4151, h4156, h4160, h4177, h4326, h4330, h4334, h4346, h4365, h4370, h4373, h4457, h4460, h4466, h4468, h4498, h4505, h4804, h4868, h4894, h4897, reducedSource1169] using sourceEq1348 B hB

theorem rowSound1169 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1169 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1169, numericCheck1169, reducedZero1169 B hB hF, mul_zero]

theorem reducedZero1171 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1171 (mixedVector B) = 0 := by
  have h1505 : mixedVector B (Sum.inr 1505) = Sparse.eval nodeValue1505 (mixedVector B) := by
    change mixedMoment B node1505 node1505Labels = _
    exact sound1505 B hB hF
  have h1516 : mixedVector B (Sum.inr 1516) = Sparse.eval nodeValue1516 (mixedVector B) := by
    change mixedMoment B node1516 node1516Labels = _
    exact sound1516 B hB hF
  have h1518 : mixedVector B (Sum.inr 1518) = Sparse.eval nodeValue1518 (mixedVector B) := by
    change mixedMoment B node1518 node1518Labels = _
    exact sound1518 B hB hF
  have h1523 : mixedVector B (Sum.inr 1523) = Sparse.eval nodeValue1523 (mixedVector B) := by
    change mixedMoment B node1523 node1523Labels = _
    exact sound1523 B hB hF
  have h1663 : mixedVector B (Sum.inr 1663) = Sparse.eval nodeValue1663 (mixedVector B) := by
    change mixedMoment B node1663 node1663Labels = _
    exact sound1663 B hB hF
  have h1672 : mixedVector B (Sum.inr 1672) = Sparse.eval nodeValue1672 (mixedVector B) := by
    change mixedMoment B node1672 node1672Labels = _
    exact sound1672 B hB hF
  have h1674 : mixedVector B (Sum.inr 1674) = Sparse.eval nodeValue1674 (mixedVector B) := by
    change mixedMoment B node1674 node1674Labels = _
    exact sound1674 B hB hF
  have h1679 : mixedVector B (Sum.inr 1679) = Sparse.eval nodeValue1679 (mixedVector B) := by
    change mixedMoment B node1679 node1679Labels = _
    exact sound1679 B hB hF
  have h1704 : mixedVector B (Sum.inr 1704) = Sparse.eval nodeValue1704 (mixedVector B) := by
    change mixedMoment B node1704 node1704Labels = _
    exact sound1704 B hB hF
  have h1707 : mixedVector B (Sum.inr 1707) = Sparse.eval nodeValue1707 (mixedVector B) := by
    change mixedMoment B node1707 node1707Labels = _
    exact sound1707 B hB hF
  have h1722 : mixedVector B (Sum.inr 1722) = Sparse.eval nodeValue1722 (mixedVector B) := by
    change mixedMoment B node1722 node1722Labels = _
    exact sound1722 B hB hF
  have h1725 : mixedVector B (Sum.inr 1725) = Sparse.eval nodeValue1725 (mixedVector B) := by
    change mixedMoment B node1725 node1725Labels = _
    exact sound1725 B hB hF
  have h1727 : mixedVector B (Sum.inr 1727) = Sparse.eval nodeValue1727 (mixedVector B) := by
    change mixedMoment B node1727 node1727Labels = _
    exact sound1727 B hB hF
  have h1735 : mixedVector B (Sum.inr 1735) = Sparse.eval nodeValue1735 (mixedVector B) := by
    change mixedMoment B node1735 node1735Labels = _
    exact sound1735 B hB hF
  have h1738 : mixedVector B (Sum.inr 1738) = Sparse.eval nodeValue1738 (mixedVector B) := by
    change mixedMoment B node1738 node1738Labels = _
    exact sound1738 B hB hF
  have h1752 : mixedVector B (Sum.inr 1752) = Sparse.eval nodeValue1752 (mixedVector B) := by
    change mixedMoment B node1752 node1752Labels = _
    exact sound1752 B hB hF
  have h1754 : mixedVector B (Sum.inr 1754) = Sparse.eval nodeValue1754 (mixedVector B) := by
    change mixedMoment B node1754 node1754Labels = _
    exact sound1754 B hB hF
  have h2203 : mixedVector B (Sum.inr 2203) = Sparse.eval nodeValue2203 (mixedVector B) := by
    change mixedMoment B node2203 node2203Labels = _
    exact sound2203 B hB hF
  have h2261 : mixedVector B (Sum.inr 2261) = Sparse.eval nodeValue2261 (mixedVector B) := by
    change mixedMoment B node2261 node2261Labels = _
    exact sound2261 B hB hF
  have h2264 : mixedVector B (Sum.inr 2264) = Sparse.eval nodeValue2264 (mixedVector B) := by
    change mixedMoment B node2264 node2264Labels = _
    exact sound2264 B hB hF
  have h2292 : mixedVector B (Sum.inr 2292) = Sparse.eval nodeValue2292 (mixedVector B) := by
    change mixedMoment B node2292 node2292Labels = _
    exact sound2292 B hB hF
  simpa only [sourceForm1350, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1505, h1516, h1518, h1523, h1663, h1672, h1674, h1679, h1704, h1707, h1722, h1725, h1727, h1735, h1738, h1752, h1754, h2203, h2261, h2264, h2292, reducedSource1171] using sourceEq1350 B hB

theorem rowSound1171 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1171 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1171, numericCheck1171, reducedZero1171 B hB hF, mul_zero]

theorem reducedZero1172 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1172 (mixedVector B) = 0 := by
  have h579 : mixedVector B (Sum.inr 579) = Sparse.eval nodeValue579 (mixedVector B) := by
    change mixedMoment B node579 node579Labels = _
    exact sound579 B hB hF
  have h584 : mixedVector B (Sum.inr 584) = Sparse.eval nodeValue584 (mixedVector B) := by
    change mixedMoment B node584 node584Labels = _
    exact sound584 B hB hF
  have h588 : mixedVector B (Sum.inr 588) = Sparse.eval nodeValue588 (mixedVector B) := by
    change mixedMoment B node588 node588Labels = _
    exact sound588 B hB hF
  have h605 : mixedVector B (Sum.inr 605) = Sparse.eval nodeValue605 (mixedVector B) := by
    change mixedMoment B node605 node605Labels = _
    exact sound605 B hB hF
  have h1043 : mixedVector B (Sum.inr 1043) = Sparse.eval nodeValue1043 (mixedVector B) := by
    change mixedMoment B node1043 node1043Labels = _
    exact sound1043 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm1351, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h579, h584, h588, h605, h1043, h4084, reducedSource1172] using sourceEq1351 B hB

theorem rowSound1172 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1172 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1172, numericCheck1172, reducedZero1172 B hB hF, mul_zero]

theorem reducedZero1173 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1173 (mixedVector B) = 0 := by
  have h605 : mixedVector B (Sum.inr 605) = Sparse.eval nodeValue605 (mixedVector B) := by
    change mixedMoment B node605 node605Labels = _
    exact sound605 B hB hF
  have h924 : mixedVector B (Sum.inr 924) = Sparse.eval nodeValue924 (mixedVector B) := by
    change mixedMoment B node924 node924Labels = _
    exact sound924 B hB hF
  have h1043 : mixedVector B (Sum.inr 1043) = Sparse.eval nodeValue1043 (mixedVector B) := by
    change mixedMoment B node1043 node1043Labels = _
    exact sound1043 B hB hF
  have h1082 : mixedVector B (Sum.inr 1082) = Sparse.eval nodeValue1082 (mixedVector B) := by
    change mixedMoment B node1082 node1082Labels = _
    exact sound1082 B hB hF
  have h1089 : mixedVector B (Sum.inr 1089) = Sparse.eval nodeValue1089 (mixedVector B) := by
    change mixedMoment B node1089 node1089Labels = _
    exact sound1089 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm1352, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h605, h924, h1043, h1082, h1089, h4084, reducedSource1173] using sourceEq1352 B hB

theorem rowSound1173 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1173 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1173, numericCheck1173, reducedZero1173 B hB hF, mul_zero]

theorem reducedZero1174 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1174 (mixedVector B) = 0 := by
  have h943 : mixedVector B (Sum.inr 943) = Sparse.eval nodeValue943 (mixedVector B) := by
    change mixedMoment B node943 node943Labels = _
    exact sound943 B hB hF
  have h948 : mixedVector B (Sum.inr 948) = Sparse.eval nodeValue948 (mixedVector B) := by
    change mixedMoment B node948 node948Labels = _
    exact sound948 B hB hF
  have h952 : mixedVector B (Sum.inr 952) = Sparse.eval nodeValue952 (mixedVector B) := by
    change mixedMoment B node952 node952Labels = _
    exact sound952 B hB hF
  have h1043 : mixedVector B (Sum.inr 1043) = Sparse.eval nodeValue1043 (mixedVector B) := by
    change mixedMoment B node1043 node1043Labels = _
    exact sound1043 B hB hF
  have h2109 : mixedVector B (Sum.inr 2109) = Sparse.eval nodeValue2109 (mixedVector B) := by
    change mixedMoment B node2109 node2109Labels = _
    exact sound2109 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm1353, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h943, h948, h952, h1043, h2109, h4084, reducedSource1174] using sourceEq1353 B hB

theorem rowSound1174 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1174 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1174, numericCheck1174, reducedZero1174 B hB hF, mul_zero]

theorem reducedZero1175 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1175 (mixedVector B) = 0 := by
  have h579 : mixedVector B (Sum.inr 579) = Sparse.eval nodeValue579 (mixedVector B) := by
    change mixedMoment B node579 node579Labels = _
    exact sound579 B hB hF
  have h904 : mixedVector B (Sum.inr 904) = Sparse.eval nodeValue904 (mixedVector B) := by
    change mixedMoment B node904 node904Labels = _
    exact sound904 B hB hF
  have h943 : mixedVector B (Sum.inr 943) = Sparse.eval nodeValue943 (mixedVector B) := by
    change mixedMoment B node943 node943Labels = _
    exact sound943 B hB hF
  have h1040 : mixedVector B (Sum.inr 1040) = Sparse.eval nodeValue1040 (mixedVector B) := by
    change mixedMoment B node1040 node1040Labels = _
    exact sound1040 B hB hF
  have h1043 : mixedVector B (Sum.inr 1043) = Sparse.eval nodeValue1043 (mixedVector B) := by
    change mixedMoment B node1043 node1043Labels = _
    exact sound1043 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm1354, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h579, h904, h943, h1040, h1043, h4084, reducedSource1175] using sourceEq1354 B hB

theorem rowSound1175 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1175 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1175, numericCheck1175, reducedZero1175 B hB hF, mul_zero]

theorem reducedZero1176 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1176 (mixedVector B) = 0 := by
  have h904 : mixedVector B (Sum.inr 904) = Sparse.eval nodeValue904 (mixedVector B) := by
    change mixedMoment B node904 node904Labels = _
    exact sound904 B hB hF
  have h908 : mixedVector B (Sum.inr 908) = Sparse.eval nodeValue908 (mixedVector B) := by
    change mixedMoment B node908 node908Labels = _
    exact sound908 B hB hF
  have h912 : mixedVector B (Sum.inr 912) = Sparse.eval nodeValue912 (mixedVector B) := by
    change mixedMoment B node912 node912Labels = _
    exact sound912 B hB hF
  have h924 : mixedVector B (Sum.inr 924) = Sparse.eval nodeValue924 (mixedVector B) := by
    change mixedMoment B node924 node924Labels = _
    exact sound924 B hB hF
  have h1043 : mixedVector B (Sum.inr 1043) = Sparse.eval nodeValue1043 (mixedVector B) := by
    change mixedMoment B node1043 node1043Labels = _
    exact sound1043 B hB hF
  have h2022 : mixedVector B (Sum.inr 2022) = Sparse.eval nodeValue2022 (mixedVector B) := by
    change mixedMoment B node2022 node2022Labels = _
    exact sound2022 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm1355, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h904, h908, h912, h924, h1043, h2022, h4084, reducedSource1176] using sourceEq1355 B hB

theorem rowSound1176 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1176 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1176, numericCheck1176, reducedZero1176 B hB hF, mul_zero]

theorem reducedZero1180 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1180 (mixedVector B) = 0 := by
  have h1037 : mixedVector B (Sum.inr 1037) = Sparse.eval nodeValue1037 (mixedVector B) := by
    change mixedMoment B node1037 node1037Labels = _
    exact sound1037 B hB hF
  have h2018 : mixedVector B (Sum.inr 2018) = Sparse.eval nodeValue2018 (mixedVector B) := by
    change mixedMoment B node2018 node2018Labels = _
    exact sound2018 B hB hF
  have h2103 : mixedVector B (Sum.inr 2103) = Sparse.eval nodeValue2103 (mixedVector B) := by
    change mixedMoment B node2103 node2103Labels = _
    exact sound2103 B hB hF
  have h2208 : mixedVector B (Sum.inr 2208) = Sparse.eval nodeValue2208 (mixedVector B) := by
    change mixedMoment B node2208 node2208Labels = _
    exact sound2208 B hB hF
  have h2261 : mixedVector B (Sum.inr 2261) = Sparse.eval nodeValue2261 (mixedVector B) := by
    change mixedMoment B node2261 node2261Labels = _
    exact sound2261 B hB hF
  have h4081 : mixedVector B (Sum.inr 4081) = Sparse.eval nodeValue4081 (mixedVector B) := by
    change mixedMoment B node4081 node4081Labels = _
    exact sound4081 B hB hF
  simpa only [sourceForm1361, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1037, h2018, h2103, h2208, h2261, h4081, reducedSource1180] using sourceEq1361 B hB

theorem rowSound1180 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1180 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1180, numericCheck1180, reducedZero1180 B hB hF, mul_zero]

theorem reducedZero1181 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1181 (mixedVector B) = 0 := by
  have h594 : mixedVector B (Sum.inr 594) = Sparse.eval nodeValue594 (mixedVector B) := by
    change mixedMoment B node594 node594Labels = _
    exact sound594 B hB hF
  have h916 : mixedVector B (Sum.inr 916) = Sparse.eval nodeValue916 (mixedVector B) := by
    change mixedMoment B node916 node916Labels = _
    exact sound916 B hB hF
  have h1007 : mixedVector B (Sum.inr 1007) = Sparse.eval nodeValue1007 (mixedVector B) := by
    change mixedMoment B node1007 node1007Labels = _
    exact sound1007 B hB hF
  have h1037 : mixedVector B (Sum.inr 1037) = Sparse.eval nodeValue1037 (mixedVector B) := by
    change mixedMoment B node1037 node1037Labels = _
    exact sound1037 B hB hF
  have h1074 : mixedVector B (Sum.inr 1074) = Sparse.eval nodeValue1074 (mixedVector B) := by
    change mixedMoment B node1074 node1074Labels = _
    exact sound1074 B hB hF
  have h4081 : mixedVector B (Sum.inr 4081) = Sparse.eval nodeValue4081 (mixedVector B) := by
    change mixedMoment B node4081 node4081Labels = _
    exact sound4081 B hB hF
  simpa only [sourceForm1362, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h594, h916, h1007, h1037, h1074, h4081, reducedSource1181] using sourceEq1362 B hB

theorem rowSound1181 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1181 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1181, numericCheck1181, reducedZero1181 B hB hF, mul_zero]

theorem reducedZero1182 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1182 (mixedVector B) = 0 := by
  have h1033 : mixedVector B (Sum.inr 1033) = Sparse.eval nodeValue1033 (mixedVector B) := by
    change mixedMoment B node1033 node1033Labels = _
    exact sound1033 B hB hF
  have h1037 : mixedVector B (Sum.inr 1037) = Sparse.eval nodeValue1037 (mixedVector B) := by
    change mixedMoment B node1037 node1037Labels = _
    exact sound1037 B hB hF
  have h1048 : mixedVector B (Sum.inr 1048) = Sparse.eval nodeValue1048 (mixedVector B) := by
    change mixedMoment B node1048 node1048Labels = _
    exact sound1048 B hB hF
  have h1074 : mixedVector B (Sum.inr 1074) = Sparse.eval nodeValue1074 (mixedVector B) := by
    change mixedMoment B node1074 node1074Labels = _
    exact sound1074 B hB hF
  have h2261 : mixedVector B (Sum.inr 2261) = Sparse.eval nodeValue2261 (mixedVector B) := by
    change mixedMoment B node2261 node2261Labels = _
    exact sound2261 B hB hF
  have h4081 : mixedVector B (Sum.inr 4081) = Sparse.eval nodeValue4081 (mixedVector B) := by
    change mixedMoment B node4081 node4081Labels = _
    exact sound4081 B hB hF
  simpa only [sourceForm1363, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1033, h1037, h1048, h1074, h2261, h4081, reducedSource1182] using sourceEq1363 B hB

theorem rowSound1182 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1182 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1182, numericCheck1182, reducedZero1182 B hB hF, mul_zero]

theorem reducedZero1183 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1183 (mixedVector B) = 0 := by
  have h731 : mixedVector B (Sum.inr 731) = Sparse.eval nodeValue731 (mixedVector B) := by
    change mixedMoment B node731 node731Labels = _
    exact sound731 B hB hF
  have h735 : mixedVector B (Sum.inr 735) = Sparse.eval nodeValue735 (mixedVector B) := by
    change mixedMoment B node735 node735Labels = _
    exact sound735 B hB hF
  have h741 : mixedVector B (Sum.inr 741) = Sparse.eval nodeValue741 (mixedVector B) := by
    change mixedMoment B node741 node741Labels = _
    exact sound741 B hB hF
  have h809 : mixedVector B (Sum.inr 809) = Sparse.eval nodeValue809 (mixedVector B) := by
    change mixedMoment B node809 node809Labels = _
    exact sound809 B hB hF
  have h1647 : mixedVector B (Sum.inr 1647) = Sparse.eval nodeValue1647 (mixedVector B) := by
    change mixedMoment B node1647 node1647Labels = _
    exact sound1647 B hB hF
  have h4070 : mixedVector B (Sum.inr 4070) = Sparse.eval nodeValue4070 (mixedVector B) := by
    change mixedMoment B node4070 node4070Labels = _
    exact sound4070 B hB hF
  simpa only [sourceForm1364, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h731, h735, h741, h809, h1647, h4070, reducedSource1183] using sourceEq1364 B hB

theorem rowSound1183 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1183 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1183, numericCheck1183, reducedZero1183 B hB hF, mul_zero]

theorem sourceRowsAt1168 : MixedData.sourceRows (1168 : Fin 2425) =
    MixedData.row1168 := by decide +kernel

theorem sourceRowsAt1169 : MixedData.sourceRows (1169 : Fin 2425) =
    MixedData.row1169 := by decide +kernel

theorem sourceRowsAt1170 : MixedData.sourceRows (1170 : Fin 2425) =
    MixedData.row1170 := by decide +kernel

theorem sourceRowsAt1171 : MixedData.sourceRows (1171 : Fin 2425) =
    MixedData.row1171 := by decide +kernel

theorem sourceRowsAt1172 : MixedData.sourceRows (1172 : Fin 2425) =
    MixedData.row1172 := by decide +kernel

theorem sourceRowsAt1173 : MixedData.sourceRows (1173 : Fin 2425) =
    MixedData.row1173 := by decide +kernel

theorem sourceRowsAt1174 : MixedData.sourceRows (1174 : Fin 2425) =
    MixedData.row1174 := by decide +kernel

theorem sourceRowsAt1175 : MixedData.sourceRows (1175 : Fin 2425) =
    MixedData.row1175 := by decide +kernel

theorem sourceRowsAt1176 : MixedData.sourceRows (1176 : Fin 2425) =
    MixedData.row1176 := by decide +kernel

theorem sourceRowsAt1177 : MixedData.sourceRows (1177 : Fin 2425) =
    MixedData.row1177 := by decide +kernel

theorem sourceRowsAt1178 : MixedData.sourceRows (1178 : Fin 2425) =
    MixedData.row1178 := by decide +kernel

theorem sourceRowsAt1179 : MixedData.sourceRows (1179 : Fin 2425) =
    MixedData.row1179 := by decide +kernel

theorem sourceRowsAt1180 : MixedData.sourceRows (1180 : Fin 2425) =
    MixedData.row1180 := by decide +kernel

theorem sourceRowsAt1181 : MixedData.sourceRows (1181 : Fin 2425) =
    MixedData.row1181 := by decide +kernel

theorem sourceRowsAt1182 : MixedData.sourceRows (1182 : Fin 2425) =
    MixedData.row1182 := by decide +kernel

theorem sourceRowsAt1183 : MixedData.sourceRows (1183 : Fin 2425) =
    MixedData.row1183 := by decide +kernel

theorem chunkSound73_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) (k : Fin 2425)
    (hk : k.val / 16 = 73) :
    Integer.Sparse.eval (MixedData.sourceRows k) (numericVector B) = 0 := by
  have heq : k.val = 1168 ∨ k.val = 1169 ∨ k.val = 1170 ∨ k.val = 1171 ∨ k.val = 1172 ∨ k.val = 1173 ∨ k.val = 1174 ∨ k.val = 1175 ∨ k.val = 1176 ∨ k.val = 1177 ∨ k.val = 1178 ∨ k.val = 1179 ∨ k.val = 1180 ∨ k.val = 1181 ∨ k.val = 1182 ∨ k.val = 1183 := by omega
  rcases heq with h1168 | h1169 | h1170 | h1171 | h1172 | h1173 | h1174 | h1175 | h1176 | h1177 | h1178 | h1179 | h1180 | h1181 | h1182 | h1183
  · have he : k = (1168 : Fin 2425) := Fin.ext h1168
    subst k
    rw [sourceRowsAt1168]
    exact rowSound1168 B hB hF
  · have he : k = (1169 : Fin 2425) := Fin.ext h1169
    subst k
    rw [sourceRowsAt1169]
    exact rowSound1169 B hB hF
  · have he : k = (1170 : Fin 2425) := Fin.ext h1170
    subst k
    rw [sourceRowsAt1170]
    exact rowSound1170_e B hB hF
  · have he : k = (1171 : Fin 2425) := Fin.ext h1171
    subst k
    rw [sourceRowsAt1171]
    exact rowSound1171 B hB hF
  · have he : k = (1172 : Fin 2425) := Fin.ext h1172
    subst k
    rw [sourceRowsAt1172]
    exact rowSound1172 B hB hF
  · have he : k = (1173 : Fin 2425) := Fin.ext h1173
    subst k
    rw [sourceRowsAt1173]
    exact rowSound1173 B hB hF
  · have he : k = (1174 : Fin 2425) := Fin.ext h1174
    subst k
    rw [sourceRowsAt1174]
    exact rowSound1174 B hB hF
  · have he : k = (1175 : Fin 2425) := Fin.ext h1175
    subst k
    rw [sourceRowsAt1175]
    exact rowSound1175 B hB hF
  · have he : k = (1176 : Fin 2425) := Fin.ext h1176
    subst k
    rw [sourceRowsAt1176]
    exact rowSound1176 B hB hF
  · have he : k = (1177 : Fin 2425) := Fin.ext h1177
    subst k
    rw [sourceRowsAt1177]
    exact rowSound1177_e B hB hF
  · have he : k = (1178 : Fin 2425) := Fin.ext h1178
    subst k
    rw [sourceRowsAt1178]
    exact rowSound1178_e B hB hF
  · have he : k = (1179 : Fin 2425) := Fin.ext h1179
    subst k
    rw [sourceRowsAt1179]
    exact rowSound1179_e B hB hF
  · have he : k = (1180 : Fin 2425) := Fin.ext h1180
    subst k
    rw [sourceRowsAt1180]
    exact rowSound1180 B hB hF
  · have he : k = (1181 : Fin 2425) := Fin.ext h1181
    subst k
    rw [sourceRowsAt1181]
    exact rowSound1181 B hB hF
  · have he : k = (1182 : Fin 2425) := Fin.ext h1182
    subst k
    rw [sourceRowsAt1182]
    exact rowSound1182 B hB hF
  · have he : k = (1183 : Fin 2425) := Fin.ext h1183
    subst k
    rw [sourceRowsAt1183]
    exact rowSound1183 B hB hF

end MUB6.Certificate.MixedSourceBridge

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedSourceBridge.chunkSound73_e_oai := @OAI.MUB6.Certificate.MixedSourceBridge.chunkSound73_e_oai
