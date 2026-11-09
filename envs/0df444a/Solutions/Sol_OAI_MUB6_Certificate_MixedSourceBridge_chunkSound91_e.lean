-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedSourceBridge.chunkSound91_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T04:41:13.368405+00:00
-- url     : https://prove2.me/submissions/4f0eb417-75b7-4a7b-be81-16a2b6d25294

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E077
import Definitions.Def_OAIQ106E086
import Definitions.Def_OAIQ106E087
import Definitions.Def_OAIQ106E088
import Definitions.Def_OAIQ106E089
import Definitions.Def_OAIQ106E090
import Definitions.Def_OAIQ106E093
import Definitions.Def_OAIQ106E094
import Definitions.Def_OAIQ106E097
import Definitions.Def_OAIQ106E194
import Definitions.Def_OAIQ106E117
import Definitions.Def_OAIQ106E119
import Definitions.Def_OAIQ106E120
import Definitions.Def_OAIQ106E124
import Definitions.Def_OAIQ106E140
import Definitions.Def_OAIQ106E147
import Definitions.Def_OAIQ106E170
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound1469_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound1470_e

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical111
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical14335 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14335 raw14335Labels = mixedMoment B node4497 node4497Labels := by
  calc
    mixedMoment B raw14335 raw14335Labels = mixedMoment B raw14335step0 raw14335step0Labels := by
      have hz : ∀ j, raw14335 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw14335step0 = (fun i j => raw14335 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw14335step0 raw14335; decide +kernel
      have hl : raw14335step0Labels = raw14335Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14335 raw14335Labels permutation346 hz
    mixedMoment B raw14335step0 raw14335step0Labels = mixedMoment B raw14335step1 raw14335step1Labels := by
      have ha : raw14335step1 = (fun i j => raw14335step0 (permutation50 i) (permutation2 j)) := by apply Matrix.ext; unfold raw14335step1 raw14335step0; decide +kernel
      have hl : raw14335step1Labels = raw14335step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14335step0 raw14335step0Labels permutation50 permutation2
    _ = mixedMoment B node4497 node4497Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical112
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical14340 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14340 raw14340Labels = mixedMoment B node4456 node4456Labels := by
  calc
    mixedMoment B raw14340 raw14340Labels = mixedMoment B raw14340step0 raw14340step0Labels := by
      have ha : raw14340step0 = (fun i j => raw14340 (permutation156 i) (permutation2 j)) := by apply Matrix.ext; unfold raw14340step0 raw14340; decide +kernel
      have hl : raw14340step0Labels = raw14340Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14340 raw14340Labels permutation156 permutation2
    _ = mixedMoment B node4456 node4456Labels := by rfl

theorem canonical14345 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14345 raw14345Labels = mixedMoment B node4458 node4458Labels := by
  calc
    mixedMoment B raw14345 raw14345Labels = mixedMoment B raw14345step0 raw14345step0Labels := by
      have hz : ∀ j, raw14345 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw14345step0 = (fun i j => raw14345 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw14345step0 raw14345; decide +kernel
      have hl : raw14345step0Labels = raw14345Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14345 raw14345Labels permutation346 hz
    mixedMoment B raw14345step0 raw14345step0Labels = mixedMoment B raw14345step1 raw14345step1Labels := by
      have ha : raw14345step1 = (fun i j => raw14345step0 (permutation37 i) (permutation2 j)) := by apply Matrix.ext; unfold raw14345step1 raw14345step0; decide +kernel
      have hl : raw14345step1Labels = raw14345step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14345step0 raw14345step0Labels permutation37 permutation2
    _ = mixedMoment B node4458 node4458Labels := by rfl

theorem canonical14350 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14350 raw14350Labels = mixedMoment B node4458 node4458Labels := by
  calc
    mixedMoment B raw14350 raw14350Labels = mixedMoment B raw14350step0 raw14350step0Labels := by
      have hz : ∀ j, raw14350 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw14350step0 = (fun i j => raw14350 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw14350step0 raw14350; decide +kernel
      have hl : raw14350step0Labels = raw14350Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14350 raw14350Labels permutation346 hz
    mixedMoment B raw14350step0 raw14350step0Labels = mixedMoment B raw14350step1 raw14350step1Labels := by
      have ha : raw14350step1 = (fun i j => raw14350step0 (permutation36 i) (permutation2 j)) := by apply Matrix.ext; unfold raw14350step1 raw14350step0; decide +kernel
      have hl : raw14350step1Labels = raw14350step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14350step0 raw14350step0Labels permutation36 permutation2
    _ = mixedMoment B node4458 node4458Labels := by rfl

theorem canonical14356 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14356 raw14356Labels = mixedMoment B node4869 node4869Labels := by
  calc
    mixedMoment B raw14356 raw14356Labels = mixedMoment B raw14356step0 raw14356step0Labels := by
      have hz : ∀ j, raw14356 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw14356step0 = (fun i j => raw14356 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw14356step0 raw14356; decide +kernel
      have hl : raw14356step0Labels = raw14356Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14356 raw14356Labels permutation346 hz
    _ = mixedMoment B node4869 node4869Labels := by rfl

theorem canonical14357 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14357 raw14357Labels = mixedMoment B node4805 node4805Labels := by
  calc
    mixedMoment B raw14357 raw14357Labels = mixedMoment B raw14357step0 raw14357step0Labels := by
      have ha : raw14357step0 = (fun i j => raw14357 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw14357step0 raw14357; decide +kernel
      have hl : raw14357step0Labels = raw14357Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14357 raw14357Labels permutation176 permutation2
    _ = mixedMoment B node4805 node4805Labels := by rfl

theorem canonical14358 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14358 raw14358Labels = mixedMoment B node4889 node4889Labels := by
  calc
    mixedMoment B raw14358 raw14358Labels = mixedMoment B raw14358step0 raw14358step0Labels := by
      have hz : ∀ j, raw14358 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw14358step0 = (fun i j => raw14358 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw14358step0 raw14358; decide +kernel
      have hl : raw14358step0Labels = raw14358Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14358 raw14358Labels permutation346 hz
    _ = mixedMoment B node4889 node4889Labels := by rfl

theorem canonical14359 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14359 raw14359Labels = mixedMoment B node4889 node4889Labels := by
  calc
    mixedMoment B raw14359 raw14359Labels = mixedMoment B raw14359step0 raw14359step0Labels := by
      have hz : ∀ j, raw14359 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw14359step0 = (fun i j => raw14359 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw14359step0 raw14359; decide +kernel
      have hl : raw14359step0Labels = raw14359Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14359 raw14359Labels permutation346 hz
    mixedMoment B raw14359step0 raw14359step0Labels = mixedMoment B raw14359step1 raw14359step1Labels := by
      have ha : raw14359step1 = (fun i j => raw14359step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw14359step1 raw14359step0; decide +kernel
      have hl : raw14359step1Labels = raw14359step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14359step0 raw14359step0Labels permutation34 permutation2
    _ = mixedMoment B node4889 node4889Labels := by rfl

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

theorem canonical1740 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1740 raw1740Labels = mixedMoment B node4805 node4805Labels := by
  calc
    mixedMoment B raw1740 raw1740Labels = mixedMoment B raw1740step0 raw1740step0Labels := by
      have ha : raw1740step0 = (fun i j => raw1740 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1740step0 raw1740; decide +kernel
      have hl : raw1740step0Labels = raw1740Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1740 raw1740Labels permutation152 permutation4
    mixedMoment B raw1740step0 raw1740step0Labels = mixedMoment B raw1740step1 raw1740step1Labels := by
      have ha : raw1740step1 = raw1740step0 := by apply Matrix.ext; unfold raw1740step1 raw1740step0; decide +kernel
      have hl : raw1740step0Labels = labelEmbedding7 ∘ raw1740step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1740step0 raw1740step0Labels raw1740step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4805 node4805Labels := by rfl

theorem canonical1741 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1741 raw1741Labels = mixedMoment B node2023 node2023Labels := by
  calc
    mixedMoment B raw1741 raw1741Labels = mixedMoment B raw1741step0 raw1741step0Labels := by
      have ha : raw1741step0 = (fun i j => raw1741 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1741step0 raw1741; decide +kernel
      have hl : raw1741step0Labels = raw1741Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1741 raw1741Labels permutation152 permutation4
    _ = mixedMoment B node2023 node2023Labels := by rfl

theorem canonical1742 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1742 raw1742Labels = mixedMoment B node2214 node2214Labels := by
  calc
    mixedMoment B raw1742 raw1742Labels = mixedMoment B raw1742step0 raw1742step0Labels := by
      have ha : raw1742step0 = (fun i j => raw1742 (permutation170 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1742step0 raw1742; decide +kernel
      have hl : raw1742step0Labels = raw1742Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1742 raw1742Labels permutation170 permutation6
    mixedMoment B raw1742step0 raw1742step0Labels = mixedMoment B raw1742step1 raw1742step1Labels := by
      have ha : raw1742step1 = -raw1742step0 := by apply Matrix.ext; change ∀ i j, raw1742step1 i j = -(raw1742step0 i j); unfold raw1742step1 raw1742step0; decide +kernel
      have hl : raw1742step1Labels = raw1742step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1742step1 raw1742step1Labels = mixedMoment B raw1742step2 raw1742step2Labels := by
      have ha : raw1742step2 = raw1742step1 := by apply Matrix.ext; unfold raw1742step2 raw1742step1; decide +kernel
      have hl : raw1742step1Labels = labelEmbedding1 ∘ raw1742step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1742step1 raw1742step1Labels raw1742step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2214 node2214Labels := by rfl

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

theorem canonical1794 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1794 raw1794Labels = mixedMoment B node4866 node4866Labels := by
  calc
    mixedMoment B raw1794 raw1794Labels = mixedMoment B raw1794step0 raw1794step0Labels := by
      have ha : raw1794step0 = (fun i j => raw1794 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1794step0 raw1794; decide +kernel
      have hl : raw1794step0Labels = raw1794Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1794 raw1794Labels permutation32 permutation4
    mixedMoment B raw1794step0 raw1794step0Labels = mixedMoment B raw1794step1 raw1794step1Labels := by
      have ha : raw1794step1 = raw1794step0 := by apply Matrix.ext; unfold raw1794step1 raw1794step0; decide +kernel
      have hl : raw1794step0Labels = labelEmbedding7 ∘ raw1794step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1794step0 raw1794step0Labels raw1794step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4866 node4866Labels := by rfl

theorem canonical1795 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1795 raw1795Labels = mixedMoment B node2107 node2107Labels := by
  calc
    mixedMoment B raw1795 raw1795Labels = mixedMoment B raw1795step0 raw1795step0Labels := by
      have ha : raw1795step0 = (fun i j => raw1795 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1795step0 raw1795; decide +kernel
      have hl : raw1795step0Labels = raw1795Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1795 raw1795Labels permutation32 permutation4
    _ = mixedMoment B node2107 node2107Labels := by rfl

theorem canonical1796 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1796 raw1796Labels = mixedMoment B node2260 node2260Labels := by
  calc
    mixedMoment B raw1796 raw1796Labels = mixedMoment B raw1796step0 raw1796step0Labels := by
      have ha : raw1796step0 = (fun i j => raw1796 (permutation38 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1796step0 raw1796; decide +kernel
      have hl : raw1796step0Labels = raw1796Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1796 raw1796Labels permutation38 permutation6
    mixedMoment B raw1796step0 raw1796step0Labels = mixedMoment B raw1796step1 raw1796step1Labels := by
      have ha : raw1796step1 = -raw1796step0 := by apply Matrix.ext; change ∀ i j, raw1796step1 i j = -(raw1796step0 i j); unfold raw1796step1 raw1796step0; decide +kernel
      have hl : raw1796step1Labels = raw1796step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1796step1 raw1796step1Labels = mixedMoment B raw1796step2 raw1796step2Labels := by
      have ha : raw1796step2 = raw1796step1 := by apply Matrix.ext; unfold raw1796step2 raw1796step1; decide +kernel
      have hl : raw1796step1Labels = labelEmbedding1 ∘ raw1796step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1796step1 raw1796step1Labels raw1796step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2260 node2260Labels := by rfl

theorem canonical1800 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1800 raw1800Labels = mixedMoment B node4869 node4869Labels := by
  calc
    mixedMoment B raw1800 raw1800Labels = mixedMoment B raw1800step0 raw1800step0Labels := by
      have ha : raw1800step0 = (fun i j => raw1800 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1800step0 raw1800; decide +kernel
      have hl : raw1800step0Labels = raw1800Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1800 raw1800Labels permutation32 permutation4
    mixedMoment B raw1800step0 raw1800step0Labels = mixedMoment B raw1800step1 raw1800step1Labels := by
      have ha : raw1800step1 = raw1800step0 := by apply Matrix.ext; unfold raw1800step1 raw1800step0; decide +kernel
      have hl : raw1800step0Labels = labelEmbedding7 ∘ raw1800step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1800step0 raw1800step0Labels raw1800step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4869 node4869Labels := by rfl

theorem canonical1801 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1801 raw1801Labels = mixedMoment B node2110 node2110Labels := by
  calc
    mixedMoment B raw1801 raw1801Labels = mixedMoment B raw1801step0 raw1801step0Labels := by
      have ha : raw1801step0 = (fun i j => raw1801 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1801step0 raw1801; decide +kernel
      have hl : raw1801step0Labels = raw1801Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1801 raw1801Labels permutation32 permutation4
    _ = mixedMoment B node2110 node2110Labels := by rfl

theorem canonical1802 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1802 raw1802Labels = mixedMoment B node2275 node2275Labels := by
  calc
    mixedMoment B raw1802 raw1802Labels = mixedMoment B raw1802step0 raw1802step0Labels := by
      have ha : raw1802step0 = (fun i j => raw1802 (permutation50 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1802step0 raw1802; decide +kernel
      have hl : raw1802step0Labels = raw1802Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1802 raw1802Labels permutation50 permutation6
    mixedMoment B raw1802step0 raw1802step0Labels = mixedMoment B raw1802step1 raw1802step1Labels := by
      have ha : raw1802step1 = -raw1802step0 := by apply Matrix.ext; change ∀ i j, raw1802step1 i j = -(raw1802step0 i j); unfold raw1802step1 raw1802step0; decide +kernel
      have hl : raw1802step1Labels = raw1802step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1802step1 raw1802step1Labels = mixedMoment B raw1802step2 raw1802step2Labels := by
      have ha : raw1802step2 = raw1802step1 := by apply Matrix.ext; unfold raw1802step2 raw1802step1; decide +kernel
      have hl : raw1802step1Labels = labelEmbedding1 ∘ raw1802step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1802step1 raw1802step1Labels raw1802step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2275 node2275Labels := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical164
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical21116 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21116 raw21116Labels = mixedMoment B node2242 node2242Labels := by
  calc
    mixedMoment B raw21116 raw21116Labels = mixedMoment B raw21116step0 raw21116step0Labels := by
      have hz : ∀ j, raw21116 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21116step0 = (fun i j => raw21116 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21116step0 raw21116; decide +kernel
      have hl : raw21116step0Labels = raw21116Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21116 raw21116Labels permutation434 hz
    _ = mixedMoment B node2242 node2242Labels := by rfl

theorem canonical21117 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21117 raw21117Labels = mixedMoment B node4080 node4080Labels := by
  calc
    mixedMoment B raw21117 raw21117Labels = mixedMoment B raw21117step0 raw21117step0Labels := by
      have hz : ∀ j, raw21117 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21117step0 = (fun i j => raw21117 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21117step0 raw21117; decide +kernel
      have hl : raw21117step0Labels = raw21117Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21117 raw21117Labels permutation434 hz
    mixedMoment B raw21117step0 raw21117step0Labels = mixedMoment B raw21117step1 raw21117step1Labels := by
      have ha : raw21117step1 = (fun i j => raw21117step0 (permutation44 i) (permutation0 j)) := by apply Matrix.ext; unfold raw21117step1 raw21117step0; decide +kernel
      have hl : raw21117step1Labels = raw21117step0Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21117step0 raw21117step0Labels permutation44 permutation0
    _ = mixedMoment B node4080 node4080Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical165
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical21120 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21120 raw21120Labels = mixedMoment B node1017 node1017Labels := by
  calc
    mixedMoment B raw21120 raw21120Labels = mixedMoment B raw21120step0 raw21120step0Labels := by
      have ha : raw21120step0 = (fun i j => raw21120 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21120step0 raw21120; decide +kernel
      have hl : raw21120step0Labels = raw21120Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21120 raw21120Labels permutation154 permutation2
    _ = mixedMoment B node1017 node1017Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical194
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical24949 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24949 raw24949Labels = mixedMoment B node988 node988Labels := by
  calc
    mixedMoment B raw24949 raw24949Labels = mixedMoment B raw24949step0 raw24949step0Labels := by
      have ha : raw24949step0 = (fun i j => raw24949 (permutation178 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24949step0 raw24949; decide +kernel
      have hl : raw24949step0Labels = raw24949Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24949 raw24949Labels permutation178 permutation2
    _ = mixedMoment B node988 node988Labels := by rfl

theorem canonical24950 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24950 raw24950Labels = mixedMoment B node2118 node2118Labels := by
  calc
    mixedMoment B raw24950 raw24950Labels = mixedMoment B raw24950step0 raw24950step0Labels := by
      have ha : raw24950step0 = (fun i j => raw24950 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24950step0 raw24950; decide +kernel
      have hl : raw24950step0Labels = raw24950Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24950 raw24950Labels permutation154 permutation2
    _ = mixedMoment B node2118 node2118Labels := by rfl

theorem canonical24951 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24951 raw24951Labels = mixedMoment B node1922 node1922Labels := by
  calc
    mixedMoment B raw24951 raw24951Labels = mixedMoment B raw24951step0 raw24951step0Labels := by
      have ha : raw24951step0 = (fun i j => raw24951 (permutation178 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24951step0 raw24951; decide +kernel
      have hl : raw24951step0Labels = raw24951Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24951 raw24951Labels permutation178 permutation2
    _ = mixedMoment B node1922 node1922Labels := by rfl

theorem canonical24952 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24952 raw24952Labels = mixedMoment B node2195 node2195Labels := by
  calc
    mixedMoment B raw24952 raw24952Labels = mixedMoment B raw24952step0 raw24952step0Labels := by
      have ha : raw24952step0 = (fun i j => raw24952 (permutation182 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24952step0 raw24952; decide +kernel
      have hl : raw24952step0Labels = raw24952Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24952 raw24952Labels permutation182 permutation2
    _ = mixedMoment B node2195 node2195Labels := by rfl

theorem canonical24953 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24953 raw24953Labels = mixedMoment B node2216 node2216Labels := by
  calc
    mixedMoment B raw24953 raw24953Labels = mixedMoment B raw24953step0 raw24953step0Labels := by
      have hz : ∀ j, raw24953 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw24953step0 = (fun i j => raw24953 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw24953step0 raw24953; decide +kernel
      have hl : raw24953step0Labels = raw24953Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24953 raw24953Labels permutation520 hz
    mixedMoment B raw24953step0 raw24953step0Labels = mixedMoment B raw24953step1 raw24953step1Labels := by
      have ha : raw24953step1 = (fun i j => raw24953step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24953step1 raw24953step0; decide +kernel
      have hl : raw24953step1Labels = raw24953step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24953step0 raw24953step0Labels permutation38 permutation2
    _ = mixedMoment B node2216 node2216Labels := by rfl

theorem canonical24954 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24954 raw24954Labels = mixedMoment B node2214 node2214Labels := by
  calc
    mixedMoment B raw24954 raw24954Labels = mixedMoment B raw24954step0 raw24954step0Labels := by
      have ha : raw24954step0 = (fun i j => raw24954 (permutation178 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24954step0 raw24954; decide +kernel
      have hl : raw24954step0Labels = raw24954Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24954 raw24954Labels permutation178 permutation2
    _ = mixedMoment B node2214 node2214Labels := by rfl

theorem canonical24955 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24955 raw24955Labels = mixedMoment B node4080 node4080Labels := by
  calc
    mixedMoment B raw24955 raw24955Labels = mixedMoment B raw24955step0 raw24955step0Labels := by
      have hz : ∀ j, raw24955 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw24955step0 = (fun i j => raw24955 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw24955step0 raw24955; decide +kernel
      have hl : raw24955step0Labels = raw24955Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24955 raw24955Labels permutation520 hz
    mixedMoment B raw24955step0 raw24955step0Labels = mixedMoment B raw24955step1 raw24955step1Labels := by
      have ha : raw24955step1 = (fun i j => raw24955step0 (permutation41 i) (permutation0 j)) := by apply Matrix.ext; unfold raw24955step1 raw24955step0; decide +kernel
      have hl : raw24955step1Labels = raw24955step0Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24955step0 raw24955step0Labels permutation41 permutation0
    _ = mixedMoment B node4080 node4080Labels := by rfl

theorem canonical24956 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24956 raw24956Labels = mixedMoment B node987 node987Labels := by
  calc
    mixedMoment B raw24956 raw24956Labels = mixedMoment B raw24956step0 raw24956step0Labels := by
      have ha : raw24956step0 = (fun i j => raw24956 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24956step0 raw24956; decide +kernel
      have hl : raw24956step0Labels = raw24956Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24956 raw24956Labels permutation176 permutation2
    _ = mixedMoment B node987 node987Labels := by rfl

theorem canonical24957 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24957 raw24957Labels = mixedMoment B node2117 node2117Labels := by
  calc
    _ = mixedMoment B node2117 node2117Labels := by rfl

theorem canonical24958 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24958 raw24958Labels = mixedMoment B node1921 node1921Labels := by
  calc
    mixedMoment B raw24958 raw24958Labels = mixedMoment B raw24958step0 raw24958step0Labels := by
      have ha : raw24958step0 = (fun i j => raw24958 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24958step0 raw24958; decide +kernel
      have hl : raw24958step0Labels = raw24958Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24958 raw24958Labels permutation176 permutation2
    _ = mixedMoment B node1921 node1921Labels := by rfl

theorem canonical24959 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24959 raw24959Labels = mixedMoment B node2215 node2215Labels := by
  calc
    mixedMoment B raw24959 raw24959Labels = mixedMoment B raw24959step0 raw24959step0Labels := by
      have hz : ∀ j, raw24959 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw24959step0 = (fun i j => raw24959 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw24959step0 raw24959; decide +kernel
      have hl : raw24959step0Labels = raw24959Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24959 raw24959Labels permutation434 hz
    mixedMoment B raw24959step0 raw24959step0Labels = mixedMoment B raw24959step1 raw24959step1Labels := by
      have ha : raw24959step1 = (fun i j => raw24959step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24959step1 raw24959step0; decide +kernel
      have hl : raw24959step1Labels = raw24959step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24959step0 raw24959step0Labels permutation38 permutation2
    _ = mixedMoment B node2215 node2215Labels := by rfl

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

theorem canonical24960 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24960 raw24960Labels = mixedMoment B node2215 node2215Labels := by
  calc
    mixedMoment B raw24960 raw24960Labels = mixedMoment B raw24960step0 raw24960step0Labels := by
      have hz : ∀ j, raw24960 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw24960step0 = (fun i j => raw24960 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw24960step0 raw24960; decide +kernel
      have hl : raw24960step0Labels = raw24960Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24960 raw24960Labels permutation520 hz
    mixedMoment B raw24960step0 raw24960step0Labels = mixedMoment B raw24960step1 raw24960step1Labels := by
      have ha : raw24960step1 = (fun i j => raw24960step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24960step1 raw24960step0; decide +kernel
      have hl : raw24960step1Labels = raw24960step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24960step0 raw24960step0Labels permutation38 permutation2
    _ = mixedMoment B node2215 node2215Labels := by rfl

theorem canonical24961 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24961 raw24961Labels = mixedMoment B node2213 node2213Labels := by
  calc
    mixedMoment B raw24961 raw24961Labels = mixedMoment B raw24961step0 raw24961step0Labels := by
      have ha : raw24961step0 = (fun i j => raw24961 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24961step0 raw24961; decide +kernel
      have hl : raw24961step0Labels = raw24961Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24961 raw24961Labels permutation176 permutation2
    _ = mixedMoment B node2213 node2213Labels := by rfl

theorem canonical24962 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24962 raw24962Labels = mixedMoment B node4082 node4082Labels := by
  calc
    mixedMoment B raw24962 raw24962Labels = mixedMoment B raw24962step0 raw24962step0Labels := by
      have hz : ∀ j, raw24962 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw24962step0 = (fun i j => raw24962 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw24962step0 raw24962; decide +kernel
      have hl : raw24962step0Labels = raw24962Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24962 raw24962Labels permutation520 hz
    mixedMoment B raw24962step0 raw24962step0Labels = mixedMoment B raw24962step1 raw24962step1Labels := by
      have hz : ∀ j, raw24962step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw24962step1 = (fun i j => raw24962step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw24962step1 raw24962step0; decide +kernel
      have hl : raw24962step1Labels = raw24962step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24962step0 raw24962step0Labels permutation104 hz
    mixedMoment B raw24962step1 raw24962step1Labels = mixedMoment B raw24962step2 raw24962step2Labels := by
      have ha : raw24962step2 = (fun i j => raw24962step1 (permutation10 i) (permutation0 j)) := by apply Matrix.ext; unfold raw24962step2 raw24962step1; decide +kernel
      have hl : raw24962step2Labels = raw24962step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24962step1 raw24962step1Labels permutation10 permutation0
    _ = mixedMoment B node4082 node4082Labels := by rfl

theorem canonical24963 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24963 raw24963Labels = mixedMoment B node1023 node1023Labels := by
  calc
    _ = mixedMoment B node1023 node1023Labels := by rfl

theorem canonical24964 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24964 raw24964Labels = mixedMoment B node2091 node2091Labels := by
  calc
    _ = mixedMoment B node2091 node2091Labels := by rfl

theorem canonical24965 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24965 raw24965Labels = mixedMoment B node2091 node2091Labels := by
  calc
    mixedMoment B raw24965 raw24965Labels = mixedMoment B raw24965step0 raw24965step0Labels := by
      have ha : raw24965step0 = (fun i j => raw24965 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24965step0 raw24965; decide +kernel
      have hl : raw24965step0Labels = raw24965Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24965 raw24965Labels permutation176 permutation2
    _ = mixedMoment B node2091 node2091Labels := by rfl

theorem canonical24966 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24966 raw24966Labels = mixedMoment B node2234 node2234Labels := by
  calc
    _ = mixedMoment B node2234 node2234Labels := by rfl

theorem canonical24967 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24967 raw24967Labels = mixedMoment B node2234 node2234Labels := by
  calc
    mixedMoment B raw24967 raw24967Labels = mixedMoment B raw24967step0 raw24967step0Labels := by
      have ha : raw24967step0 = (fun i j => raw24967 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24967step0 raw24967; decide +kernel
      have hl : raw24967step0Labels = raw24967Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24967 raw24967Labels permutation154 permutation2
    _ = mixedMoment B node2234 node2234Labels := by rfl

theorem canonical24968 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24968 raw24968Labels = mixedMoment B node2241 node2241Labels := by
  calc
    mixedMoment B raw24968 raw24968Labels = mixedMoment B raw24968step0 raw24968step0Labels := by
      have ha : raw24968step0 = (fun i j => raw24968 (permutation156 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24968step0 raw24968; decide +kernel
      have hl : raw24968step0Labels = raw24968Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24968 raw24968Labels permutation156 permutation2
    _ = mixedMoment B node2241 node2241Labels := by rfl

theorem canonical24969 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24969 raw24969Labels = mixedMoment B node4079 node4079Labels := by
  calc
    mixedMoment B raw24969 raw24969Labels = mixedMoment B raw24969step0 raw24969step0Labels := by
      have ha : raw24969step0 = (fun i j => raw24969 (permutation246 i) (permutation0 j)) := by apply Matrix.ext; unfold raw24969step0 raw24969; decide +kernel
      have hl : raw24969step0Labels = raw24969Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24969 raw24969Labels permutation246 permutation0
    _ = mixedMoment B node4079 node4079Labels := by rfl

theorem canonical24970 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24970 raw24970Labels = mixedMoment B node1034 node1034Labels := by
  calc
    mixedMoment B raw24970 raw24970Labels = mixedMoment B raw24970step0 raw24970step0Labels := by
      have ha : raw24970step0 = (fun i j => raw24970 (permutation194 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24970step0 raw24970; decide +kernel
      have hl : raw24970step0Labels = raw24970Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24970 raw24970Labels permutation194 permutation2
    _ = mixedMoment B node1034 node1034Labels := by rfl

theorem canonical24971 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24971 raw24971Labels = mixedMoment B node1034 node1034Labels := by
  calc
    mixedMoment B raw24971 raw24971Labels = mixedMoment B raw24971step0 raw24971step0Labels := by
      have ha : raw24971step0 = (fun i j => raw24971 (permutation170 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24971step0 raw24971; decide +kernel
      have hl : raw24971step0Labels = raw24971Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24971 raw24971Labels permutation170 permutation2
    _ = mixedMoment B node1034 node1034Labels := by rfl

theorem canonical24972 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24972 raw24972Labels = mixedMoment B node1018 node1018Labels := by
  calc
    mixedMoment B raw24972 raw24972Labels = mixedMoment B raw24972step0 raw24972step0Labels := by
      have ha : raw24972step0 = (fun i j => raw24972 (permutation157 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24972step0 raw24972; decide +kernel
      have hl : raw24972step0Labels = raw24972Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24972 raw24972Labels permutation157 permutation2
    _ = mixedMoment B node1018 node1018Labels := by rfl

theorem canonical24973 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24973 raw24973Labels = mixedMoment B node1018 node1018Labels := by
  calc
    mixedMoment B raw24973 raw24973Labels = mixedMoment B raw24973step0 raw24973step0Labels := by
      have ha : raw24973step0 = (fun i j => raw24973 (permutation156 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24973step0 raw24973; decide +kernel
      have hl : raw24973step0Labels = raw24973Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24973 raw24973Labels permutation156 permutation2
    _ = mixedMoment B node1018 node1018Labels := by rfl

theorem canonical24974 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24974 raw24974Labels = mixedMoment B node1018 node1018Labels := by
  calc
    mixedMoment B raw24974 raw24974Labels = mixedMoment B raw24974step0 raw24974step0Labels := by
      have ha : raw24974step0 = (fun i j => raw24974 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24974step0 raw24974; decide +kernel
      have hl : raw24974step0Labels = raw24974Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24974 raw24974Labels permutation154 permutation2
    _ = mixedMoment B node1018 node1018Labels := by rfl

theorem canonical24975 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24975 raw24975Labels = mixedMoment B node2086 node2086Labels := by
  calc
    mixedMoment B raw24975 raw24975Labels = mixedMoment B raw24975step0 raw24975step0Labels := by
      have ha : raw24975step0 = (fun i j => raw24975 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24975step0 raw24975; decide +kernel
      have hl : raw24975step0Labels = raw24975Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24975 raw24975Labels permutation154 permutation2
    _ = mixedMoment B node2086 node2086Labels := by rfl

theorem canonical24976 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24976 raw24976Labels = mixedMoment B node2086 node2086Labels := by
  calc
    mixedMoment B raw24976 raw24976Labels = mixedMoment B raw24976step0 raw24976step0Labels := by
      have ha : raw24976step0 = (fun i j => raw24976 (permutation178 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24976step0 raw24976; decide +kernel
      have hl : raw24976step0Labels = raw24976Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24976 raw24976Labels permutation178 permutation2
    _ = mixedMoment B node2086 node2086Labels := by rfl

theorem canonical24977 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24977 raw24977Labels = mixedMoment B node2232 node2232Labels := by
  calc
    _ = mixedMoment B node2232 node2232Labels := by rfl

theorem canonical24978 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24978 raw24978Labels = mixedMoment B node2191 node2191Labels := by
  calc
    mixedMoment B raw24978 raw24978Labels = mixedMoment B raw24978step0 raw24978step0Labels := by
      have ha : raw24978step0 = (fun i j => raw24978 (permutation224 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24978step0 raw24978; decide +kernel
      have hl : raw24978step0Labels = raw24978Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24978 raw24978Labels permutation224 permutation2
    _ = mixedMoment B node2191 node2191Labels := by rfl

theorem canonical24979 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24979 raw24979Labels = mixedMoment B node2241 node2241Labels := by
  calc
    mixedMoment B raw24979 raw24979Labels = mixedMoment B raw24979step0 raw24979step0Labels := by
      have ha : raw24979step0 = (fun i j => raw24979 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24979step0 raw24979; decide +kernel
      have hl : raw24979step0Labels = raw24979Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24979 raw24979Labels permutation154 permutation2
    _ = mixedMoment B node2241 node2241Labels := by rfl

theorem canonical24980 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24980 raw24980Labels = mixedMoment B node4079 node4079Labels := by
  calc
    mixedMoment B raw24980 raw24980Labels = mixedMoment B raw24980step0 raw24980step0Labels := by
      have ha : raw24980step0 = (fun i j => raw24980 (permutation224 i) (permutation0 j)) := by apply Matrix.ext; unfold raw24980step0 raw24980; decide +kernel
      have hl : raw24980step0Labels = raw24980Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24980 raw24980Labels permutation224 permutation0
    _ = mixedMoment B node4079 node4079Labels := by rfl

theorem canonical24981 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24981 raw24981Labels = mixedMoment B node2085 node2085Labels := by
  calc
    mixedMoment B raw24981 raw24981Labels = mixedMoment B raw24981step0 raw24981step0Labels := by
      have ha : raw24981step0 = (fun i j => raw24981 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24981step0 raw24981; decide +kernel
      have hl : raw24981step0Labels = raw24981Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24981 raw24981Labels permutation154 permutation2
    _ = mixedMoment B node2085 node2085Labels := by rfl

theorem canonical24982 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24982 raw24982Labels = mixedMoment B node2085 node2085Labels := by
  calc
    mixedMoment B raw24982 raw24982Labels = mixedMoment B raw24982step0 raw24982step0Labels := by
      have ha : raw24982step0 = (fun i j => raw24982 (permutation178 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24982step0 raw24982; decide +kernel
      have hl : raw24982step0Labels = raw24982Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24982 raw24982Labels permutation178 permutation2
    _ = mixedMoment B node2085 node2085Labels := by rfl

theorem canonical24983 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24983 raw24983Labels = mixedMoment B node2190 node2190Labels := by
  calc
    mixedMoment B raw24983 raw24983Labels = mixedMoment B raw24983step0 raw24983step0Labels := by
      have ha : raw24983step0 = (fun i j => raw24983 (permutation224 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24983step0 raw24983; decide +kernel
      have hl : raw24983step0Labels = raw24983Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24983 raw24983Labels permutation224 permutation2
    _ = mixedMoment B node2190 node2190Labels := by rfl

theorem canonical24984 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24984 raw24984Labels = mixedMoment B node2240 node2240Labels := by
  calc
    mixedMoment B raw24984 raw24984Labels = mixedMoment B raw24984step0 raw24984step0Labels := by
      have ha : raw24984step0 = (fun i j => raw24984 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24984step0 raw24984; decide +kernel
      have hl : raw24984step0Labels = raw24984Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24984 raw24984Labels permutation154 permutation2
    _ = mixedMoment B node2240 node2240Labels := by rfl

theorem canonical24985 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24985 raw24985Labels = mixedMoment B node1045 node1045Labels := by
  calc
    mixedMoment B raw24985 raw24985Labels = mixedMoment B raw24985step0 raw24985step0Labels := by
      have hz : ∀ j, raw24985 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24985step0 = (fun i j => raw24985 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24985step0 raw24985; decide +kernel
      have hl : raw24985step0Labels = raw24985Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24985 raw24985Labels permutation346 hz
    mixedMoment B raw24985step0 raw24985step0Labels = mixedMoment B raw24985step1 raw24985step1Labels := by
      have ha : raw24985step1 = (fun i j => raw24985step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24985step1 raw24985step0; decide +kernel
      have hl : raw24985step1Labels = raw24985step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24985step0 raw24985step0Labels permutation34 permutation2
    _ = mixedMoment B node1045 node1045Labels := by rfl

theorem canonical24986 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24986 raw24986Labels = mixedMoment B node2111 node2111Labels := by
  calc
    mixedMoment B raw24986 raw24986Labels = mixedMoment B raw24986step0 raw24986step0Labels := by
      have hz : ∀ j, raw24986 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24986step0 = (fun i j => raw24986 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24986step0 raw24986; decide +kernel
      have hl : raw24986step0Labels = raw24986Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24986 raw24986Labels permutation346 hz
    mixedMoment B raw24986step0 raw24986step0Labels = mixedMoment B raw24986step1 raw24986step1Labels := by
      have ha : raw24986step1 = (fun i j => raw24986step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24986step1 raw24986step0; decide +kernel
      have hl : raw24986step1Labels = raw24986step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24986step0 raw24986step0Labels permutation34 permutation2
    _ = mixedMoment B node2111 node2111Labels := by rfl

theorem canonical24987 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24987 raw24987Labels = mixedMoment B node2024 node2024Labels := by
  calc
    mixedMoment B raw24987 raw24987Labels = mixedMoment B raw24987step0 raw24987step0Labels := by
      have ha : raw24987step0 = (fun i j => raw24987 (permutation178 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24987step0 raw24987; decide +kernel
      have hl : raw24987step0Labels = raw24987Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24987 raw24987Labels permutation178 permutation2
    _ = mixedMoment B node2024 node2024Labels := by rfl

theorem canonical24988 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24988 raw24988Labels = mixedMoment B node2254 node2254Labels := by
  calc
    mixedMoment B raw24988 raw24988Labels = mixedMoment B raw24988step0 raw24988step0Labels := by
      have hz : ∀ j, raw24988 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24988step0 = (fun i j => raw24988 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24988step0 raw24988; decide +kernel
      have hl : raw24988step0Labels = raw24988Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24988 raw24988Labels permutation346 hz
    _ = mixedMoment B node2254 node2254Labels := by rfl

theorem canonical24989 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24989 raw24989Labels = mixedMoment B node2246 node2246Labels := by
  calc
    mixedMoment B raw24989 raw24989Labels = mixedMoment B raw24989step0 raw24989step0Labels := by
      have hz : ∀ j, raw24989 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24989step0 = (fun i j => raw24989 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24989step0 raw24989; decide +kernel
      have hl : raw24989step0Labels = raw24989Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24989 raw24989Labels permutation346 hz
    mixedMoment B raw24989step0 raw24989step0Labels = mixedMoment B raw24989step1 raw24989step1Labels := by
      have ha : raw24989step1 = (fun i j => raw24989step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24989step1 raw24989step0; decide +kernel
      have hl : raw24989step1Labels = raw24989step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24989step0 raw24989step0Labels permutation34 permutation2
    _ = mixedMoment B node2246 node2246Labels := by rfl

theorem canonical24990 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24990 raw24990Labels = mixedMoment B node2260 node2260Labels := by
  calc
    mixedMoment B raw24990 raw24990Labels = mixedMoment B raw24990step0 raw24990step0Labels := by
      have hz : ∀ j, raw24990 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24990step0 = (fun i j => raw24990 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24990step0 raw24990; decide +kernel
      have hl : raw24990step0Labels = raw24990Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24990 raw24990Labels permutation346 hz
    mixedMoment B raw24990step0 raw24990step0Labels = mixedMoment B raw24990step1 raw24990step1Labels := by
      have ha : raw24990step1 = (fun i j => raw24990step0 (permutation37 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24990step1 raw24990step0; decide +kernel
      have hl : raw24990step1Labels = raw24990step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24990step0 raw24990step0Labels permutation37 permutation2
    _ = mixedMoment B node2260 node2260Labels := by rfl

theorem canonical24991 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24991 raw24991Labels = mixedMoment B node4080 node4080Labels := by
  calc
    mixedMoment B raw24991 raw24991Labels = mixedMoment B raw24991step0 raw24991step0Labels := by
      have hz : ∀ j, raw24991 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24991step0 = (fun i j => raw24991 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24991step0 raw24991; decide +kernel
      have hl : raw24991step0Labels = raw24991Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24991 raw24991Labels permutation346 hz
    mixedMoment B raw24991step0 raw24991step0Labels = mixedMoment B raw24991step1 raw24991step1Labels := by
      have ha : raw24991step1 = (fun i j => raw24991step0 (permutation51 i) (permutation0 j)) := by apply Matrix.ext; unfold raw24991step1 raw24991step0; decide +kernel
      have hl : raw24991step1Labels = raw24991step0Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24991step0 raw24991step0Labels permutation51 permutation0
    _ = mixedMoment B node4080 node4080Labels := by rfl

theorem canonical24992 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24992 raw24992Labels = mixedMoment B node1073 node1073Labels := by
  calc
    mixedMoment B raw24992 raw24992Labels = mixedMoment B raw24992step0 raw24992step0Labels := by
      have hz : ∀ j, raw24992 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24992step0 = (fun i j => raw24992 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24992step0 raw24992; decide +kernel
      have hl : raw24992step0Labels = raw24992Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24992 raw24992Labels permutation346 hz
    mixedMoment B raw24992step0 raw24992step0Labels = mixedMoment B raw24992step1 raw24992step1Labels := by
      have ha : raw24992step1 = (fun i j => raw24992step0 (permutation51 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24992step1 raw24992step0; decide +kernel
      have hl : raw24992step1Labels = raw24992step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24992step0 raw24992step0Labels permutation51 permutation2
    _ = mixedMoment B node1073 node1073Labels := by rfl

theorem canonical24993 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24993 raw24993Labels = mixedMoment B node1032 node1032Labels := by
  calc
    mixedMoment B raw24993 raw24993Labels = mixedMoment B raw24993step0 raw24993step0Labels := by
      have ha : raw24993step0 = (fun i j => raw24993 (permutation171 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24993step0 raw24993; decide +kernel
      have hl : raw24993step0Labels = raw24993Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24993 raw24993Labels permutation171 permutation2
    _ = mixedMoment B node1032 node1032Labels := by rfl

theorem canonical24994 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24994 raw24994Labels = mixedMoment B node1035 node1035Labels := by
  calc
    mixedMoment B raw24994 raw24994Labels = mixedMoment B raw24994step0 raw24994step0Labels := by
      have hz : ∀ j, raw24994 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24994step0 = (fun i j => raw24994 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24994step0 raw24994; decide +kernel
      have hl : raw24994step0Labels = raw24994Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24994 raw24994Labels permutation346 hz
    mixedMoment B raw24994step0 raw24994step0Labels = mixedMoment B raw24994step1 raw24994step1Labels := by
      have ha : raw24994step1 = (fun i j => raw24994step0 (permutation37 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24994step1 raw24994step0; decide +kernel
      have hl : raw24994step1Labels = raw24994step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24994step0 raw24994step0Labels permutation37 permutation2
    _ = mixedMoment B node1035 node1035Labels := by rfl

theorem canonical24995 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24995 raw24995Labels = mixedMoment B node1036 node1036Labels := by
  calc
    mixedMoment B raw24995 raw24995Labels = mixedMoment B raw24995step0 raw24995step0Labels := by
      have hz : ∀ j, raw24995 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24995step0 = (fun i j => raw24995 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24995step0 raw24995; decide +kernel
      have hl : raw24995step0Labels = raw24995Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24995 raw24995Labels permutation346 hz
    mixedMoment B raw24995step0 raw24995step0Labels = mixedMoment B raw24995step1 raw24995step1Labels := by
      have ha : raw24995step1 = (fun i j => raw24995step0 (permutation36 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24995step1 raw24995step0; decide +kernel
      have hl : raw24995step1Labels = raw24995step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24995step0 raw24995step0Labels permutation36 permutation2
    _ = mixedMoment B node1036 node1036Labels := by rfl

theorem canonical24996 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24996 raw24996Labels = mixedMoment B node1036 node1036Labels := by
  calc
    mixedMoment B raw24996 raw24996Labels = mixedMoment B raw24996step0 raw24996step0Labels := by
      have hz : ∀ j, raw24996 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24996step0 = (fun i j => raw24996 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24996step0 raw24996; decide +kernel
      have hl : raw24996step0Labels = raw24996Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24996 raw24996Labels permutation346 hz
    mixedMoment B raw24996step0 raw24996step0Labels = mixedMoment B raw24996step1 raw24996step1Labels := by
      have ha : raw24996step1 = (fun i j => raw24996step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24996step1 raw24996step0; decide +kernel
      have hl : raw24996step1Labels = raw24996step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24996step0 raw24996step0Labels permutation34 permutation2
    _ = mixedMoment B node1036 node1036Labels := by rfl

theorem canonical24997 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24997 raw24997Labels = mixedMoment B node2102 node2102Labels := by
  calc
    mixedMoment B raw24997 raw24997Labels = mixedMoment B raw24997step0 raw24997step0Labels := by
      have hz : ∀ j, raw24997 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24997step0 = (fun i j => raw24997 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24997step0 raw24997; decide +kernel
      have hl : raw24997step0Labels = raw24997Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24997 raw24997Labels permutation346 hz
    mixedMoment B raw24997step0 raw24997step0Labels = mixedMoment B raw24997step1 raw24997step1Labels := by
      have ha : raw24997step1 = (fun i j => raw24997step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24997step1 raw24997step0; decide +kernel
      have hl : raw24997step1Labels = raw24997step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24997step0 raw24997step0Labels permutation34 permutation2
    _ = mixedMoment B node2102 node2102Labels := by rfl

theorem canonical24998 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24998 raw24998Labels = mixedMoment B node2017 node2017Labels := by
  calc
    mixedMoment B raw24998 raw24998Labels = mixedMoment B raw24998step0 raw24998step0Labels := by
      have ha : raw24998step0 = (fun i j => raw24998 (permutation178 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24998step0 raw24998; decide +kernel
      have hl : raw24998step0Labels = raw24998Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24998 raw24998Labels permutation178 permutation2
    _ = mixedMoment B node2017 node2017Labels := by rfl

theorem canonical24999 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24999 raw24999Labels = mixedMoment B node2251 node2251Labels := by
  calc
    mixedMoment B raw24999 raw24999Labels = mixedMoment B raw24999step0 raw24999step0Labels := by
      have hz : ∀ j, raw24999 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24999step0 = (fun i j => raw24999 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24999step0 raw24999; decide +kernel
      have hl : raw24999step0Labels = raw24999Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24999 raw24999Labels permutation346 hz
    _ = mixedMoment B node2251 node2251Labels := by rfl

theorem canonical25000 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25000 raw25000Labels = mixedMoment B node2206 node2206Labels := by
  calc
    mixedMoment B raw25000 raw25000Labels = mixedMoment B raw25000step0 raw25000step0Labels := by
      have hz : ∀ j, raw25000 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25000step0 = (fun i j => raw25000 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25000step0 raw25000; decide +kernel
      have hl : raw25000step0Labels = raw25000Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25000 raw25000Labels permutation346 hz
    mixedMoment B raw25000step0 raw25000step0Labels = mixedMoment B raw25000step1 raw25000step1Labels := by
      have ha : raw25000step1 = (fun i j => raw25000step0 (permutation44 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25000step1 raw25000step0; decide +kernel
      have hl : raw25000step1Labels = raw25000step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25000step0 raw25000step0Labels permutation44 permutation2
    _ = mixedMoment B node2206 node2206Labels := by rfl

theorem canonical25001 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25001 raw25001Labels = mixedMoment B node2260 node2260Labels := by
  calc
    mixedMoment B raw25001 raw25001Labels = mixedMoment B raw25001step0 raw25001step0Labels := by
      have hz : ∀ j, raw25001 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25001step0 = (fun i j => raw25001 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25001step0 raw25001; decide +kernel
      have hl : raw25001step0Labels = raw25001Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25001 raw25001Labels permutation346 hz
    mixedMoment B raw25001step0 raw25001step0Labels = mixedMoment B raw25001step1 raw25001step1Labels := by
      have ha : raw25001step1 = (fun i j => raw25001step0 (permutation35 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25001step1 raw25001step0; decide +kernel
      have hl : raw25001step1Labels = raw25001step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25001step0 raw25001step0Labels permutation35 permutation2
    _ = mixedMoment B node2260 node2260Labels := by rfl

theorem canonical25002 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25002 raw25002Labels = mixedMoment B node4080 node4080Labels := by
  calc
    mixedMoment B raw25002 raw25002Labels = mixedMoment B raw25002step0 raw25002step0Labels := by
      have hz : ∀ j, raw25002 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25002step0 = (fun i j => raw25002 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25002step0 raw25002; decide +kernel
      have hl : raw25002step0Labels = raw25002Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25002 raw25002Labels permutation346 hz
    mixedMoment B raw25002step0 raw25002step0Labels = mixedMoment B raw25002step1 raw25002step1Labels := by
      have ha : raw25002step1 = (fun i j => raw25002step0 (permutation45 i) (permutation0 j)) := by apply Matrix.ext; unfold raw25002step1 raw25002step0; decide +kernel
      have hl : raw25002step1Labels = raw25002step0Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25002step0 raw25002step0Labels permutation45 permutation0
    _ = mixedMoment B node4080 node4080Labels := by rfl

theorem canonical25003 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25003 raw25003Labels = mixedMoment B node4893 node4893Labels := by
  calc
    mixedMoment B raw25003 raw25003Labels = mixedMoment B raw25003step0 raw25003step0Labels := by
      have hz : ∀ j, raw25003 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25003step0 = (fun i j => raw25003 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25003step0 raw25003; decide +kernel
      have hl : raw25003step0Labels = raw25003Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25003 raw25003Labels permutation346 hz
    mixedMoment B raw25003step0 raw25003step0Labels = mixedMoment B raw25003step1 raw25003step1Labels := by
      have ha : raw25003step1 = (fun i j => raw25003step0 (permutation36 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25003step1 raw25003step0; decide +kernel
      have hl : raw25003step1Labels = raw25003step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25003step0 raw25003step0Labels permutation36 permutation2
    _ = mixedMoment B node4893 node4893Labels := by rfl

theorem canonical25004 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25004 raw25004Labels = mixedMoment B node4182 node4182Labels := by
  calc
    mixedMoment B raw25004 raw25004Labels = mixedMoment B raw25004step0 raw25004step0Labels := by
      have hz : ∀ j, raw25004 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25004step0 = (fun i j => raw25004 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25004step0 raw25004; decide +kernel
      have hl : raw25004step0Labels = raw25004Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25004 raw25004Labels permutation346 hz
    _ = mixedMoment B node4182 node4182Labels := by rfl

theorem canonical25005 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25005 raw25005Labels = mixedMoment B node4351 node4351Labels := by
  calc
    mixedMoment B raw25005 raw25005Labels = mixedMoment B raw25005step0 raw25005step0Labels := by
      have ha : raw25005step0 = (fun i j => raw25005 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25005step0 raw25005; decide +kernel
      have hl : raw25005step0Labels = raw25005Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25005 raw25005Labels permutation176 permutation2
    _ = mixedMoment B node4351 node4351Labels := by rfl

theorem canonical25006 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25006 raw25006Labels = mixedMoment B node4461 node4461Labels := by
  calc
    mixedMoment B raw25006 raw25006Labels = mixedMoment B raw25006step0 raw25006step0Labels := by
      have hz : ∀ j, raw25006 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25006step0 = (fun i j => raw25006 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25006step0 raw25006; decide +kernel
      have hl : raw25006step0Labels = raw25006Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25006 raw25006Labels permutation346 hz
    mixedMoment B raw25006step0 raw25006step0Labels = mixedMoment B raw25006step1 raw25006step1Labels := by
      have ha : raw25006step1 = (fun i j => raw25006step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25006step1 raw25006step0; decide +kernel
      have hl : raw25006step1Labels = raw25006step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25006step0 raw25006step0Labels permutation38 permutation2
    _ = mixedMoment B node4461 node4461Labels := by rfl

theorem canonical25007 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25007 raw25007Labels = mixedMoment B node4461 node4461Labels := by
  calc
    mixedMoment B raw25007 raw25007Labels = mixedMoment B raw25007step0 raw25007step0Labels := by
      have hz : ∀ j, raw25007 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25007step0 = (fun i j => raw25007 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25007step0 raw25007; decide +kernel
      have hl : raw25007step0Labels = raw25007Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25007 raw25007Labels permutation346 hz
    mixedMoment B raw25007step0 raw25007step0Labels = mixedMoment B raw25007step1 raw25007step1Labels := by
      have ha : raw25007step1 = (fun i j => raw25007step0 (permutation44 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25007step1 raw25007step0; decide +kernel
      have hl : raw25007step1Labels = raw25007step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25007step0 raw25007step0Labels permutation44 permutation2
    _ = mixedMoment B node4461 node4461Labels := by rfl

theorem canonical25008 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25008 raw25008Labels = mixedMoment B node4152 node4152Labels := by
  calc
    _ = mixedMoment B node4152 node4152Labels := by rfl

theorem canonical25009 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25009 raw25009Labels = mixedMoment B node4366 node4366Labels := by
  calc
    _ = mixedMoment B node4366 node4366Labels := by rfl

theorem canonical25010 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25010 raw25010Labels = mixedMoment B node4439 node4439Labels := by
  calc
    mixedMoment B raw25010 raw25010Labels = mixedMoment B raw25010step0 raw25010step0Labels := by
      have ha : raw25010step0 = (fun i j => raw25010 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25010step0 raw25010; decide +kernel
      have hl : raw25010step0Labels = raw25010Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25010 raw25010Labels permutation158 permutation2
    _ = mixedMoment B node4439 node4439Labels := by rfl

theorem canonical25011 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25011 raw25011Labels = mixedMoment B node4439 node4439Labels := by
  calc
    mixedMoment B raw25011 raw25011Labels = mixedMoment B raw25011step0 raw25011step0Labels := by
      have ha : raw25011step0 = (fun i j => raw25011 (permutation164 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25011step0 raw25011; decide +kernel
      have hl : raw25011step0Labels = raw25011Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25011 raw25011Labels permutation164 permutation2
    _ = mixedMoment B node4439 node4439Labels := by rfl

theorem canonical25012 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25012 raw25012Labels = mixedMoment B node4158 node4158Labels := by
  calc
    mixedMoment B raw25012 raw25012Labels = mixedMoment B raw25012step0 raw25012step0Labels := by
      have hz : ∀ j, raw25012 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25012step0 = (fun i j => raw25012 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25012step0 raw25012; decide +kernel
      have hl : raw25012step0Labels = raw25012Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25012 raw25012Labels permutation346 hz
    mixedMoment B raw25012step0 raw25012step0Labels = mixedMoment B raw25012step1 raw25012step1Labels := by
      have ha : raw25012step1 = (fun i j => raw25012step0 (permutation35 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25012step1 raw25012step0; decide +kernel
      have hl : raw25012step1Labels = raw25012step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25012step0 raw25012step0Labels permutation35 permutation2
    _ = mixedMoment B node4158 node4158Labels := by rfl

theorem canonical25013 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25013 raw25013Labels = mixedMoment B node4372 node4372Labels := by
  calc
    mixedMoment B raw25013 raw25013Labels = mixedMoment B raw25013step0 raw25013step0Labels := by
      have hz : ∀ j, raw25013 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25013step0 = (fun i j => raw25013 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25013step0 raw25013; decide +kernel
      have hl : raw25013step0Labels = raw25013Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25013 raw25013Labels permutation346 hz
    mixedMoment B raw25013step0 raw25013step0Labels = mixedMoment B raw25013step1 raw25013step1Labels := by
      have ha : raw25013step1 = (fun i j => raw25013step0 (permutation35 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25013step1 raw25013step0; decide +kernel
      have hl : raw25013step1Labels = raw25013step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25013step0 raw25013step0Labels permutation35 permutation2
    _ = mixedMoment B node4372 node4372Labels := by rfl

theorem canonical25014 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25014 raw25014Labels = mixedMoment B node4332 node4332Labels := by
  calc
    mixedMoment B raw25014 raw25014Labels = mixedMoment B raw25014step0 raw25014step0Labels := by
      have ha : raw25014step0 = (fun i j => raw25014 (permutation179 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25014step0 raw25014; decide +kernel
      have hl : raw25014step0Labels = raw25014Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25014 raw25014Labels permutation179 permutation2
    _ = mixedMoment B node4332 node4332Labels := by rfl

theorem canonical25015 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25015 raw25015Labels = mixedMoment B node4444 node4444Labels := by
  calc
    mixedMoment B raw25015 raw25015Labels = mixedMoment B raw25015step0 raw25015step0Labels := by
      have hz : ∀ j, raw25015 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25015step0 = (fun i j => raw25015 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25015step0 raw25015; decide +kernel
      have hl : raw25015step0Labels = raw25015Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25015 raw25015Labels permutation346 hz
    mixedMoment B raw25015step0 raw25015step0Labels = mixedMoment B raw25015step1 raw25015step1Labels := by
      have ha : raw25015step1 = (fun i j => raw25015step0 (permutation35 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25015step1 raw25015step0; decide +kernel
      have hl : raw25015step1Labels = raw25015step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25015step0 raw25015step0Labels permutation35 permutation2
    _ = mixedMoment B node4444 node4444Labels := by rfl

theorem canonical25016 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25016 raw25016Labels = mixedMoment B node4158 node4158Labels := by
  calc
    mixedMoment B raw25016 raw25016Labels = mixedMoment B raw25016step0 raw25016step0Labels := by
      have hz : ∀ j, raw25016 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25016step0 = (fun i j => raw25016 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25016step0 raw25016; decide +kernel
      have hl : raw25016step0Labels = raw25016Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25016 raw25016Labels permutation346 hz
    mixedMoment B raw25016step0 raw25016step0Labels = mixedMoment B raw25016step1 raw25016step1Labels := by
      have ha : raw25016step1 = (fun i j => raw25016step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25016step1 raw25016step0; decide +kernel
      have hl : raw25016step1Labels = raw25016step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25016step0 raw25016step0Labels permutation33 permutation2
    _ = mixedMoment B node4158 node4158Labels := by rfl

theorem canonical25017 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25017 raw25017Labels = mixedMoment B node4372 node4372Labels := by
  calc
    mixedMoment B raw25017 raw25017Labels = mixedMoment B raw25017step0 raw25017step0Labels := by
      have hz : ∀ j, raw25017 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25017step0 = (fun i j => raw25017 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25017step0 raw25017; decide +kernel
      have hl : raw25017step0Labels = raw25017Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25017 raw25017Labels permutation346 hz
    mixedMoment B raw25017step0 raw25017step0Labels = mixedMoment B raw25017step1 raw25017step1Labels := by
      have ha : raw25017step1 = (fun i j => raw25017step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25017step1 raw25017step0; decide +kernel
      have hl : raw25017step1Labels = raw25017step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25017step0 raw25017step0Labels permutation33 permutation2
    _ = mixedMoment B node4372 node4372Labels := by rfl

theorem canonical25018 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25018 raw25018Labels = mixedMoment B node4332 node4332Labels := by
  calc
    mixedMoment B raw25018 raw25018Labels = mixedMoment B raw25018step0 raw25018step0Labels := by
      have ha : raw25018step0 = (fun i j => raw25018 (permutation177 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25018step0 raw25018; decide +kernel
      have hl : raw25018step0Labels = raw25018Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25018 raw25018Labels permutation177 permutation2
    _ = mixedMoment B node4332 node4332Labels := by rfl

theorem canonical25019 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25019 raw25019Labels = mixedMoment B node4444 node4444Labels := by
  calc
    mixedMoment B raw25019 raw25019Labels = mixedMoment B raw25019step0 raw25019step0Labels := by
      have hz : ∀ j, raw25019 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25019step0 = (fun i j => raw25019 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25019step0 raw25019; decide +kernel
      have hl : raw25019step0Labels = raw25019Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25019 raw25019Labels permutation346 hz
    mixedMoment B raw25019step0 raw25019step0Labels = mixedMoment B raw25019step1 raw25019step1Labels := by
      have ha : raw25019step1 = (fun i j => raw25019step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25019step1 raw25019step0; decide +kernel
      have hl : raw25019step1Labels = raw25019step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25019step0 raw25019step0Labels permutation33 permutation2
    _ = mixedMoment B node4444 node4444Labels := by rfl

theorem canonical25020 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25020 raw25020Labels = mixedMoment B node4157 node4157Labels := by
  calc
    mixedMoment B raw25020 raw25020Labels = mixedMoment B raw25020step0 raw25020step0Labels := by
      have hz : ∀ j, raw25020 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25020step0 = (fun i j => raw25020 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25020step0 raw25020; decide +kernel
      have hl : raw25020step0Labels = raw25020Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25020 raw25020Labels permutation346 hz
    _ = mixedMoment B node4157 node4157Labels := by rfl

theorem canonical25021 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25021 raw25021Labels = mixedMoment B node4371 node4371Labels := by
  calc
    mixedMoment B raw25021 raw25021Labels = mixedMoment B raw25021step0 raw25021step0Labels := by
      have hz : ∀ j, raw25021 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25021step0 = (fun i j => raw25021 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25021step0 raw25021; decide +kernel
      have hl : raw25021step0Labels = raw25021Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25021 raw25021Labels permutation346 hz
    _ = mixedMoment B node4371 node4371Labels := by rfl

theorem canonical25022 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25022 raw25022Labels = mixedMoment B node4331 node4331Labels := by
  calc
    mixedMoment B raw25022 raw25022Labels = mixedMoment B raw25022step0 raw25022step0Labels := by
      have ha : raw25022step0 = (fun i j => raw25022 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25022step0 raw25022; decide +kernel
      have hl : raw25022step0Labels = raw25022Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25022 raw25022Labels permutation176 permutation2
    _ = mixedMoment B node4331 node4331Labels := by rfl

theorem canonical25023 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25023 raw25023Labels = mixedMoment B node4442 node4442Labels := by
  calc
    mixedMoment B raw25023 raw25023Labels = mixedMoment B raw25023step0 raw25023step0Labels := by
      have hz : ∀ j, raw25023 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25023step0 = (fun i j => raw25023 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25023step0 raw25023; decide +kernel
      have hl : raw25023step0Labels = raw25023Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25023 raw25023Labels permutation346 hz
    _ = mixedMoment B node4442 node4442Labels := by rfl

theorem canonical25024 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25024 raw25024Labels = mixedMoment B node4442 node4442Labels := by
  calc
    mixedMoment B raw25024 raw25024Labels = mixedMoment B raw25024step0 raw25024step0Labels := by
      have hz : ∀ j, raw25024 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25024step0 = (fun i j => raw25024 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25024step0 raw25024; decide +kernel
      have hl : raw25024step0Labels = raw25024Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25024 raw25024Labels permutation346 hz
    mixedMoment B raw25024step0 raw25024step0Labels = mixedMoment B raw25024step1 raw25024step1Labels := by
      have ha : raw25024step1 = (fun i j => raw25024step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25024step1 raw25024step0; decide +kernel
      have hl : raw25024step1Labels = raw25024step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25024step0 raw25024step0Labels permutation34 permutation2
    _ = mixedMoment B node4442 node4442Labels := by rfl

theorem canonical25025 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25025 raw25025Labels = mixedMoment B node2275 node2275Labels := by
  calc
    mixedMoment B raw25025 raw25025Labels = mixedMoment B raw25025step0 raw25025step0Labels := by
      have hz : ∀ j, raw25025 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25025step0 = (fun i j => raw25025 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25025step0 raw25025; decide +kernel
      have hl : raw25025step0Labels = raw25025Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25025 raw25025Labels permutation346 hz
    mixedMoment B raw25025step0 raw25025step0Labels = mixedMoment B raw25025step1 raw25025step1Labels := by
      have ha : raw25025step1 = (fun i j => raw25025step0 (permutation50 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25025step1 raw25025step0; decide +kernel
      have hl : raw25025step1Labels = raw25025step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25025step0 raw25025step0Labels permutation50 permutation7
    mixedMoment B raw25025step1 raw25025step1Labels = mixedMoment B raw25025step2 raw25025step2Labels := by
      have ha : raw25025step2 = -raw25025step1 := by apply Matrix.ext; change ∀ i j, raw25025step2 i j = -(raw25025step1 i j); unfold raw25025step2 raw25025step1; decide +kernel
      have hl : raw25025step2Labels = raw25025step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25025step2 raw25025step2Labels = mixedMoment B raw25025step3 raw25025step3Labels := by
      have ha : raw25025step3 = raw25025step2 := by apply Matrix.ext; unfold raw25025step3 raw25025step2; decide +kernel
      have hl : raw25025step2Labels = labelEmbedding1 ∘ raw25025step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25025step2 raw25025step2Labels raw25025step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2275 node2275Labels := by rfl

theorem canonical25026 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25026 raw25026Labels = mixedMoment B node2214 node2214Labels := by
  calc
    mixedMoment B raw25026 raw25026Labels = mixedMoment B raw25026step0 raw25026step0Labels := by
      have ha : raw25026step0 = (fun i j => raw25026 (permutation194 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25026step0 raw25026; decide +kernel
      have hl : raw25026step0Labels = raw25026Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25026 raw25026Labels permutation194 permutation7
    mixedMoment B raw25026step0 raw25026step0Labels = mixedMoment B raw25026step1 raw25026step1Labels := by
      have ha : raw25026step1 = -raw25026step0 := by apply Matrix.ext; change ∀ i j, raw25026step1 i j = -(raw25026step0 i j); unfold raw25026step1 raw25026step0; decide +kernel
      have hl : raw25026step1Labels = raw25026step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25026step1 raw25026step1Labels = mixedMoment B raw25026step2 raw25026step2Labels := by
      have ha : raw25026step2 = raw25026step1 := by apply Matrix.ext; unfold raw25026step2 raw25026step1; decide +kernel
      have hl : raw25026step1Labels = labelEmbedding1 ∘ raw25026step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25026step1 raw25026step1Labels raw25026step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2214 node2214Labels := by rfl

theorem canonical25027 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25027 raw25027Labels = mixedMoment B node2277 node2277Labels := by
  calc
    mixedMoment B raw25027 raw25027Labels = mixedMoment B raw25027step0 raw25027step0Labels := by
      have hz : ∀ j, raw25027 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25027step0 = (fun i j => raw25027 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25027step0 raw25027; decide +kernel
      have hl : raw25027step0Labels = raw25027Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25027 raw25027Labels permutation346 hz
    mixedMoment B raw25027step0 raw25027step0Labels = mixedMoment B raw25027step1 raw25027step1Labels := by
      have ha : raw25027step1 = (fun i j => raw25027step0 (permutation50 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25027step1 raw25027step0; decide +kernel
      have hl : raw25027step1Labels = raw25027step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25027step0 raw25027step0Labels permutation50 permutation7
    mixedMoment B raw25027step1 raw25027step1Labels = mixedMoment B raw25027step2 raw25027step2Labels := by
      have ha : raw25027step2 = -raw25027step1 := by apply Matrix.ext; change ∀ i j, raw25027step2 i j = -(raw25027step1 i j); unfold raw25027step2 raw25027step1; decide +kernel
      have hl : raw25027step2Labels = raw25027step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25027step2 raw25027step2Labels = mixedMoment B raw25027step3 raw25027step3Labels := by
      have ha : raw25027step3 = raw25027step2 := by apply Matrix.ext; unfold raw25027step3 raw25027step2; decide +kernel
      have hl : raw25027step2Labels = labelEmbedding1 ∘ raw25027step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25027step2 raw25027step2Labels raw25027step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2277 node2277Labels := by rfl

theorem canonical25028 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25028 raw25028Labels = mixedMoment B node2277 node2277Labels := by
  calc
    mixedMoment B raw25028 raw25028Labels = mixedMoment B raw25028step0 raw25028step0Labels := by
      have hz : ∀ j, raw25028 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25028step0 = (fun i j => raw25028 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25028step0 raw25028; decide +kernel
      have hl : raw25028step0Labels = raw25028Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25028 raw25028Labels permutation346 hz
    mixedMoment B raw25028step0 raw25028step0Labels = mixedMoment B raw25028step1 raw25028step1Labels := by
      have ha : raw25028step1 = (fun i j => raw25028step0 (permutation51 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25028step1 raw25028step0; decide +kernel
      have hl : raw25028step1Labels = raw25028step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25028step0 raw25028step0Labels permutation51 permutation7
    mixedMoment B raw25028step1 raw25028step1Labels = mixedMoment B raw25028step2 raw25028step2Labels := by
      have ha : raw25028step2 = -raw25028step1 := by apply Matrix.ext; change ∀ i j, raw25028step2 i j = -(raw25028step1 i j); unfold raw25028step2 raw25028step1; decide +kernel
      have hl : raw25028step2Labels = raw25028step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25028step2 raw25028step2Labels = mixedMoment B raw25028step3 raw25028step3Labels := by
      have ha : raw25028step3 = raw25028step2 := by apply Matrix.ext; unfold raw25028step3 raw25028step2; decide +kernel
      have hl : raw25028step2Labels = labelEmbedding1 ∘ raw25028step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25028step2 raw25028step2Labels raw25028step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2277 node2277Labels := by rfl

theorem canonical25029 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25029 raw25029Labels = mixedMoment B node2263 node2263Labels := by
  calc
    mixedMoment B raw25029 raw25029Labels = mixedMoment B raw25029step0 raw25029step0Labels := by
      have hz : ∀ j, raw25029 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25029step0 = (fun i j => raw25029 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25029step0 raw25029; decide +kernel
      have hl : raw25029step0Labels = raw25029Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25029 raw25029Labels permutation346 hz
    mixedMoment B raw25029step0 raw25029step0Labels = mixedMoment B raw25029step1 raw25029step1Labels := by
      have ha : raw25029step1 = (fun i j => raw25029step0 (permutation50 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25029step1 raw25029step0; decide +kernel
      have hl : raw25029step1Labels = raw25029step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25029step0 raw25029step0Labels permutation50 permutation7
    mixedMoment B raw25029step1 raw25029step1Labels = mixedMoment B raw25029step2 raw25029step2Labels := by
      have ha : raw25029step2 = -raw25029step1 := by apply Matrix.ext; change ∀ i j, raw25029step2 i j = -(raw25029step1 i j); unfold raw25029step2 raw25029step1; decide +kernel
      have hl : raw25029step2Labels = raw25029step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25029step2 raw25029step2Labels = mixedMoment B raw25029step3 raw25029step3Labels := by
      have ha : raw25029step3 = raw25029step2 := by apply Matrix.ext; unfold raw25029step3 raw25029step2; decide +kernel
      have hl : raw25029step2Labels = labelEmbedding1 ∘ raw25029step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25029step2 raw25029step2Labels raw25029step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2263 node2263Labels := by rfl

theorem canonical25030 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25030 raw25030Labels = mixedMoment B node1524 node1524Labels := by
  calc
    mixedMoment B raw25030 raw25030Labels = mixedMoment B raw25030step0 raw25030step0Labels := by
      have hz : ∀ j, raw25030 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25030step0 = (fun i j => raw25030 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25030step0 raw25030; decide +kernel
      have hl : raw25030step0Labels = raw25030Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25030 raw25030Labels permutation346 hz
    mixedMoment B raw25030step0 raw25030step0Labels = mixedMoment B raw25030step1 raw25030step1Labels := by
      have ha : raw25030step1 = (fun i j => raw25030step0 (permutation50 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25030step1 raw25030step0; decide +kernel
      have hl : raw25030step1Labels = raw25030step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25030step0 raw25030step0Labels permutation50 permutation7
    mixedMoment B raw25030step1 raw25030step1Labels = mixedMoment B raw25030step2 raw25030step2Labels := by
      have ha : raw25030step2 = -raw25030step1 := by apply Matrix.ext; change ∀ i j, raw25030step2 i j = -(raw25030step1 i j); unfold raw25030step2 raw25030step1; decide +kernel
      have hl : raw25030step2Labels = raw25030step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25030step2 raw25030step2Labels = mixedMoment B raw25030step3 raw25030step3Labels := by
      have ha : raw25030step3 = raw25030step2 := by apply Matrix.ext; unfold raw25030step3 raw25030step2; decide +kernel
      have hl : raw25030step2Labels = labelEmbedding1 ∘ raw25030step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25030step2 raw25030step2Labels raw25030step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1524 node1524Labels := by rfl

theorem canonical25031 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25031 raw25031Labels = mixedMoment B node1680 node1680Labels := by
  calc
    mixedMoment B raw25031 raw25031Labels = mixedMoment B raw25031step0 raw25031step0Labels := by
      have ha : raw25031step0 = (fun i j => raw25031 (permutation194 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25031step0 raw25031; decide +kernel
      have hl : raw25031step0Labels = raw25031Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25031 raw25031Labels permutation194 permutation7
    mixedMoment B raw25031step0 raw25031step0Labels = mixedMoment B raw25031step1 raw25031step1Labels := by
      have ha : raw25031step1 = -raw25031step0 := by apply Matrix.ext; change ∀ i j, raw25031step1 i j = -(raw25031step0 i j); unfold raw25031step1 raw25031step0; decide +kernel
      have hl : raw25031step1Labels = raw25031step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25031step1 raw25031step1Labels = mixedMoment B raw25031step2 raw25031step2Labels := by
      have ha : raw25031step2 = raw25031step1 := by apply Matrix.ext; unfold raw25031step2 raw25031step1; decide +kernel
      have hl : raw25031step1Labels = labelEmbedding1 ∘ raw25031step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25031step1 raw25031step1Labels raw25031step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1680 node1680Labels := by rfl

theorem canonical25032 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25032 raw25032Labels = mixedMoment B node1737 node1737Labels := by
  calc
    mixedMoment B raw25032 raw25032Labels = mixedMoment B raw25032step0 raw25032step0Labels := by
      have hz : ∀ j, raw25032 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25032step0 = (fun i j => raw25032 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25032step0 raw25032; decide +kernel
      have hl : raw25032step0Labels = raw25032Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25032 raw25032Labels permutation346 hz
    mixedMoment B raw25032step0 raw25032step0Labels = mixedMoment B raw25032step1 raw25032step1Labels := by
      have ha : raw25032step1 = (fun i j => raw25032step0 (permutation52 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25032step1 raw25032step0; decide +kernel
      have hl : raw25032step1Labels = raw25032step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25032step0 raw25032step0Labels permutation52 permutation7
    mixedMoment B raw25032step1 raw25032step1Labels = mixedMoment B raw25032step2 raw25032step2Labels := by
      have ha : raw25032step2 = -raw25032step1 := by apply Matrix.ext; change ∀ i j, raw25032step2 i j = -(raw25032step1 i j); unfold raw25032step2 raw25032step1; decide +kernel
      have hl : raw25032step2Labels = raw25032step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25032step2 raw25032step2Labels = mixedMoment B raw25032step3 raw25032step3Labels := by
      have ha : raw25032step3 = raw25032step2 := by apply Matrix.ext; unfold raw25032step3 raw25032step2; decide +kernel
      have hl : raw25032step2Labels = labelEmbedding1 ∘ raw25032step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25032step2 raw25032step2Labels raw25032step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1737 node1737Labels := by rfl

theorem canonical25033 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25033 raw25033Labels = mixedMoment B node1737 node1737Labels := by
  calc
    mixedMoment B raw25033 raw25033Labels = mixedMoment B raw25033step0 raw25033step0Labels := by
      have hz : ∀ j, raw25033 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25033step0 = (fun i j => raw25033 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25033step0 raw25033; decide +kernel
      have hl : raw25033step0Labels = raw25033Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25033 raw25033Labels permutation346 hz
    mixedMoment B raw25033step0 raw25033step0Labels = mixedMoment B raw25033step1 raw25033step1Labels := by
      have ha : raw25033step1 = (fun i j => raw25033step0 (permutation54 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25033step1 raw25033step0; decide +kernel
      have hl : raw25033step1Labels = raw25033step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25033step0 raw25033step0Labels permutation54 permutation7
    mixedMoment B raw25033step1 raw25033step1Labels = mixedMoment B raw25033step2 raw25033step2Labels := by
      have ha : raw25033step2 = -raw25033step1 := by apply Matrix.ext; change ∀ i j, raw25033step2 i j = -(raw25033step1 i j); unfold raw25033step2 raw25033step1; decide +kernel
      have hl : raw25033step2Labels = raw25033step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25033step2 raw25033step2Labels = mixedMoment B raw25033step3 raw25033step3Labels := by
      have ha : raw25033step3 = raw25033step2 := by apply Matrix.ext; unfold raw25033step3 raw25033step2; decide +kernel
      have hl : raw25033step2Labels = labelEmbedding1 ∘ raw25033step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25033step2 raw25033step2Labels raw25033step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1737 node1737Labels := by rfl

theorem canonical25034 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25034 raw25034Labels = mixedMoment B node1726 node1726Labels := by
  calc
    mixedMoment B raw25034 raw25034Labels = mixedMoment B raw25034step0 raw25034step0Labels := by
      have hz : ∀ j, raw25034 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25034step0 = (fun i j => raw25034 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25034step0 raw25034; decide +kernel
      have hl : raw25034step0Labels = raw25034Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25034 raw25034Labels permutation346 hz
    mixedMoment B raw25034step0 raw25034step0Labels = mixedMoment B raw25034step1 raw25034step1Labels := by
      have ha : raw25034step1 = (fun i j => raw25034step0 (permutation50 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25034step1 raw25034step0; decide +kernel
      have hl : raw25034step1Labels = raw25034step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25034step0 raw25034step0Labels permutation50 permutation7
    mixedMoment B raw25034step1 raw25034step1Labels = mixedMoment B raw25034step2 raw25034step2Labels := by
      have ha : raw25034step2 = -raw25034step1 := by apply Matrix.ext; change ∀ i j, raw25034step2 i j = -(raw25034step1 i j); unfold raw25034step2 raw25034step1; decide +kernel
      have hl : raw25034step2Labels = raw25034step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25034step2 raw25034step2Labels = mixedMoment B raw25034step3 raw25034step3Labels := by
      have ha : raw25034step3 = raw25034step2 := by apply Matrix.ext; unfold raw25034step3 raw25034step2; decide +kernel
      have hl : raw25034step2Labels = labelEmbedding1 ∘ raw25034step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25034step2 raw25034step2Labels raw25034step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1726 node1726Labels := by rfl

theorem canonical25035 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25035 raw25035Labels = mixedMoment B node1510 node1510Labels := by
  calc
    mixedMoment B raw25035 raw25035Labels = mixedMoment B raw25035step0 raw25035step0Labels := by
      have ha : raw25035step0 = (fun i j => raw25035 (permutation194 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25035step0 raw25035; decide +kernel
      have hl : raw25035step0Labels = raw25035Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25035 raw25035Labels permutation194 permutation7
    mixedMoment B raw25035step0 raw25035step0Labels = mixedMoment B raw25035step1 raw25035step1Labels := by
      have ha : raw25035step1 = -raw25035step0 := by apply Matrix.ext; change ∀ i j, raw25035step1 i j = -(raw25035step0 i j); unfold raw25035step1 raw25035step0; decide +kernel
      have hl : raw25035step1Labels = raw25035step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25035step1 raw25035step1Labels = mixedMoment B raw25035step2 raw25035step2Labels := by
      have ha : raw25035step2 = raw25035step1 := by apply Matrix.ext; unfold raw25035step2 raw25035step1; decide +kernel
      have hl : raw25035step1Labels = labelEmbedding1 ∘ raw25035step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25035step1 raw25035step1Labels raw25035step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1510 node1510Labels := by rfl

theorem canonical25036 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25036 raw25036Labels = mixedMoment B node1711 node1711Labels := by
  calc
    mixedMoment B raw25036 raw25036Labels = mixedMoment B raw25036step0 raw25036step0Labels := by
      have ha : raw25036step0 = (fun i j => raw25036 (permutation194 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25036step0 raw25036; decide +kernel
      have hl : raw25036step0Labels = raw25036Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25036 raw25036Labels permutation194 permutation7
    mixedMoment B raw25036step0 raw25036step0Labels = mixedMoment B raw25036step1 raw25036step1Labels := by
      have ha : raw25036step1 = -raw25036step0 := by apply Matrix.ext; change ∀ i j, raw25036step1 i j = -(raw25036step0 i j); unfold raw25036step1 raw25036step0; decide +kernel
      have hl : raw25036step1Labels = raw25036step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25036step1 raw25036step1Labels = mixedMoment B raw25036step2 raw25036step2Labels := by
      have ha : raw25036step2 = raw25036step1 := by apply Matrix.ext; unfold raw25036step2 raw25036step1; decide +kernel
      have hl : raw25036step1Labels = labelEmbedding1 ∘ raw25036step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25036step1 raw25036step1Labels raw25036step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1711 node1711Labels := by rfl

theorem canonical25037 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25037 raw25037Labels = mixedMoment B node1713 node1713Labels := by
  calc
    mixedMoment B raw25037 raw25037Labels = mixedMoment B raw25037step0 raw25037step0Labels := by
      have ha : raw25037step0 = (fun i j => raw25037 (permutation194 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25037step0 raw25037; decide +kernel
      have hl : raw25037step0Labels = raw25037Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25037 raw25037Labels permutation194 permutation7
    mixedMoment B raw25037step0 raw25037step0Labels = mixedMoment B raw25037step1 raw25037step1Labels := by
      have ha : raw25037step1 = -raw25037step0 := by apply Matrix.ext; change ∀ i j, raw25037step1 i j = -(raw25037step0 i j); unfold raw25037step1 raw25037step0; decide +kernel
      have hl : raw25037step1Labels = raw25037step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25037step1 raw25037step1Labels = mixedMoment B raw25037step2 raw25037step2Labels := by
      have ha : raw25037step2 = raw25037step1 := by apply Matrix.ext; unfold raw25037step2 raw25037step1; decide +kernel
      have hl : raw25037step1Labels = labelEmbedding1 ∘ raw25037step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25037step1 raw25037step1Labels raw25037step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1713 node1713Labels := by rfl

theorem canonical25038 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25038 raw25038Labels = mixedMoment B node1713 node1713Labels := by
  calc
    mixedMoment B raw25038 raw25038Labels = mixedMoment B raw25038step0 raw25038step0Labels := by
      have ha : raw25038step0 = (fun i j => raw25038 (permutation195 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25038step0 raw25038; decide +kernel
      have hl : raw25038step0Labels = raw25038Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25038 raw25038Labels permutation195 permutation7
    mixedMoment B raw25038step0 raw25038step0Labels = mixedMoment B raw25038step1 raw25038step1Labels := by
      have ha : raw25038step1 = -raw25038step0 := by apply Matrix.ext; change ∀ i j, raw25038step1 i j = -(raw25038step0 i j); unfold raw25038step1 raw25038step0; decide +kernel
      have hl : raw25038step1Labels = raw25038step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25038step1 raw25038step1Labels = mixedMoment B raw25038step2 raw25038step2Labels := by
      have ha : raw25038step2 = raw25038step1 := by apply Matrix.ext; unfold raw25038step2 raw25038step1; decide +kernel
      have hl : raw25038step1Labels = labelEmbedding1 ∘ raw25038step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25038step1 raw25038step1Labels raw25038step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1713 node1713Labels := by rfl

theorem canonical25039 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25039 raw25039Labels = mixedMoment B node1706 node1706Labels := by
  calc
    mixedMoment B raw25039 raw25039Labels = mixedMoment B raw25039step0 raw25039step0Labels := by
      have ha : raw25039step0 = (fun i j => raw25039 (permutation194 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25039step0 raw25039; decide +kernel
      have hl : raw25039step0Labels = raw25039Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25039 raw25039Labels permutation194 permutation7
    mixedMoment B raw25039step0 raw25039step0Labels = mixedMoment B raw25039step1 raw25039step1Labels := by
      have ha : raw25039step1 = -raw25039step0 := by apply Matrix.ext; change ∀ i j, raw25039step1 i j = -(raw25039step0 i j); unfold raw25039step1 raw25039step0; decide +kernel
      have hl : raw25039step1Labels = raw25039step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25039step1 raw25039step1Labels = mixedMoment B raw25039step2 raw25039step2Labels := by
      have ha : raw25039step2 = raw25039step1 := by apply Matrix.ext; unfold raw25039step2 raw25039step1; decide +kernel
      have hl : raw25039step1Labels = labelEmbedding1 ∘ raw25039step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25039step1 raw25039step1Labels raw25039step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1706 node1706Labels := by rfl

theorem canonical25040 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25040 raw25040Labels = mixedMoment B node1522 node1522Labels := by
  calc
    mixedMoment B raw25040 raw25040Labels = mixedMoment B raw25040step0 raw25040step0Labels := by
      have hz : ∀ j, raw25040 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25040step0 = (fun i j => raw25040 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25040step0 raw25040; decide +kernel
      have hl : raw25040step0Labels = raw25040Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25040 raw25040Labels permutation346 hz
    mixedMoment B raw25040step0 raw25040step0Labels = mixedMoment B raw25040step1 raw25040step1Labels := by
      have ha : raw25040step1 = (fun i j => raw25040step0 (permutation51 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25040step1 raw25040step0; decide +kernel
      have hl : raw25040step1Labels = raw25040step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25040step0 raw25040step0Labels permutation51 permutation7
    mixedMoment B raw25040step1 raw25040step1Labels = mixedMoment B raw25040step2 raw25040step2Labels := by
      have ha : raw25040step2 = -raw25040step1 := by apply Matrix.ext; change ∀ i j, raw25040step2 i j = -(raw25040step1 i j); unfold raw25040step2 raw25040step1; decide +kernel
      have hl : raw25040step2Labels = raw25040step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25040step2 raw25040step2Labels = mixedMoment B raw25040step3 raw25040step3Labels := by
      have ha : raw25040step3 = raw25040step2 := by apply Matrix.ext; unfold raw25040step3 raw25040step2; decide +kernel
      have hl : raw25040step2Labels = labelEmbedding1 ∘ raw25040step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25040step2 raw25040step2Labels raw25040step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1522 node1522Labels := by rfl

theorem canonical25041 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25041 raw25041Labels = mixedMoment B node1734 node1734Labels := by
  calc
    mixedMoment B raw25041 raw25041Labels = mixedMoment B raw25041step0 raw25041step0Labels := by
      have hz : ∀ j, raw25041 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25041step0 = (fun i j => raw25041 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25041step0 raw25041; decide +kernel
      have hl : raw25041step0Labels = raw25041Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25041 raw25041Labels permutation346 hz
    mixedMoment B raw25041step0 raw25041step0Labels = mixedMoment B raw25041step1 raw25041step1Labels := by
      have ha : raw25041step1 = (fun i j => raw25041step0 (permutation51 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25041step1 raw25041step0; decide +kernel
      have hl : raw25041step1Labels = raw25041step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25041step0 raw25041step0Labels permutation51 permutation7
    mixedMoment B raw25041step1 raw25041step1Labels = mixedMoment B raw25041step2 raw25041step2Labels := by
      have ha : raw25041step2 = -raw25041step1 := by apply Matrix.ext; change ∀ i j, raw25041step2 i j = -(raw25041step1 i j); unfold raw25041step2 raw25041step1; decide +kernel
      have hl : raw25041step2Labels = raw25041step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25041step2 raw25041step2Labels = mixedMoment B raw25041step3 raw25041step3Labels := by
      have ha : raw25041step3 = raw25041step2 := by apply Matrix.ext; unfold raw25041step3 raw25041step2; decide +kernel
      have hl : raw25041step2Labels = labelEmbedding1 ∘ raw25041step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25041step2 raw25041step2Labels raw25041step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1734 node1734Labels := by rfl

theorem canonical25042 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25042 raw25042Labels = mixedMoment B node1678 node1678Labels := by
  calc
    mixedMoment B raw25042 raw25042Labels = mixedMoment B raw25042step0 raw25042step0Labels := by
      have ha : raw25042step0 = (fun i j => raw25042 (permutation195 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25042step0 raw25042; decide +kernel
      have hl : raw25042step0Labels = raw25042Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25042 raw25042Labels permutation195 permutation7
    mixedMoment B raw25042step0 raw25042step0Labels = mixedMoment B raw25042step1 raw25042step1Labels := by
      have ha : raw25042step1 = -raw25042step0 := by apply Matrix.ext; change ∀ i j, raw25042step1 i j = -(raw25042step0 i j); unfold raw25042step1 raw25042step0; decide +kernel
      have hl : raw25042step1Labels = raw25042step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25042step1 raw25042step1Labels = mixedMoment B raw25042step2 raw25042step2Labels := by
      have ha : raw25042step2 = raw25042step1 := by apply Matrix.ext; unfold raw25042step2 raw25042step1; decide +kernel
      have hl : raw25042step1Labels = labelEmbedding1 ∘ raw25042step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25042step1 raw25042step1Labels raw25042step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1678 node1678Labels := by rfl

theorem canonical25043 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25043 raw25043Labels = mixedMoment B node1736 node1736Labels := by
  calc
    mixedMoment B raw25043 raw25043Labels = mixedMoment B raw25043step0 raw25043step0Labels := by
      have hz : ∀ j, raw25043 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25043step0 = (fun i j => raw25043 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25043step0 raw25043; decide +kernel
      have hl : raw25043step0Labels = raw25043Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25043 raw25043Labels permutation346 hz
    mixedMoment B raw25043step0 raw25043step0Labels = mixedMoment B raw25043step1 raw25043step1Labels := by
      have ha : raw25043step1 = (fun i j => raw25043step0 (permutation51 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25043step1 raw25043step0; decide +kernel
      have hl : raw25043step1Labels = raw25043step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25043step0 raw25043step0Labels permutation51 permutation7
    mixedMoment B raw25043step1 raw25043step1Labels = mixedMoment B raw25043step2 raw25043step2Labels := by
      have ha : raw25043step2 = -raw25043step1 := by apply Matrix.ext; change ∀ i j, raw25043step2 i j = -(raw25043step1 i j); unfold raw25043step2 raw25043step1; decide +kernel
      have hl : raw25043step2Labels = raw25043step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25043step2 raw25043step2Labels = mixedMoment B raw25043step3 raw25043step3Labels := by
      have ha : raw25043step3 = raw25043step2 := by apply Matrix.ext; unfold raw25043step3 raw25043step2; decide +kernel
      have hl : raw25043step2Labels = labelEmbedding1 ∘ raw25043step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25043step2 raw25043step2Labels raw25043step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1736 node1736Labels := by rfl

theorem canonical25044 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25044 raw25044Labels = mixedMoment B node1724 node1724Labels := by
  calc
    mixedMoment B raw25044 raw25044Labels = mixedMoment B raw25044step0 raw25044step0Labels := by
      have hz : ∀ j, raw25044 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25044step0 = (fun i j => raw25044 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25044step0 raw25044; decide +kernel
      have hl : raw25044step0Labels = raw25044Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25044 raw25044Labels permutation346 hz
    mixedMoment B raw25044step0 raw25044step0Labels = mixedMoment B raw25044step1 raw25044step1Labels := by
      have ha : raw25044step1 = (fun i j => raw25044step0 (permutation51 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25044step1 raw25044step0; decide +kernel
      have hl : raw25044step1Labels = raw25044step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25044step0 raw25044step0Labels permutation51 permutation7
    mixedMoment B raw25044step1 raw25044step1Labels = mixedMoment B raw25044step2 raw25044step2Labels := by
      have ha : raw25044step2 = -raw25044step1 := by apply Matrix.ext; change ∀ i j, raw25044step2 i j = -(raw25044step1 i j); unfold raw25044step2 raw25044step1; decide +kernel
      have hl : raw25044step2Labels = raw25044step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25044step2 raw25044step2Labels = mixedMoment B raw25044step3 raw25044step3Labels := by
      have ha : raw25044step3 = raw25044step2 := by apply Matrix.ext; unfold raw25044step3 raw25044step2; decide +kernel
      have hl : raw25044step2Labels = labelEmbedding1 ∘ raw25044step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25044step2 raw25044step2Labels raw25044step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1724 node1724Labels := by rfl

theorem canonical25045 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25045 raw25045Labels = mixedMoment B node1522 node1522Labels := by
  calc
    mixedMoment B raw25045 raw25045Labels = mixedMoment B raw25045step0 raw25045step0Labels := by
      have hz : ∀ j, raw25045 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25045step0 = (fun i j => raw25045 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25045step0 raw25045; decide +kernel
      have hl : raw25045step0Labels = raw25045Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25045 raw25045Labels permutation346 hz
    mixedMoment B raw25045step0 raw25045step0Labels = mixedMoment B raw25045step1 raw25045step1Labels := by
      have ha : raw25045step1 = (fun i j => raw25045step0 (permutation50 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25045step1 raw25045step0; decide +kernel
      have hl : raw25045step1Labels = raw25045step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25045step0 raw25045step0Labels permutation50 permutation7
    mixedMoment B raw25045step1 raw25045step1Labels = mixedMoment B raw25045step2 raw25045step2Labels := by
      have ha : raw25045step2 = -raw25045step1 := by apply Matrix.ext; change ∀ i j, raw25045step2 i j = -(raw25045step1 i j); unfold raw25045step2 raw25045step1; decide +kernel
      have hl : raw25045step2Labels = raw25045step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25045step2 raw25045step2Labels = mixedMoment B raw25045step3 raw25045step3Labels := by
      have ha : raw25045step3 = raw25045step2 := by apply Matrix.ext; unfold raw25045step3 raw25045step2; decide +kernel
      have hl : raw25045step2Labels = labelEmbedding1 ∘ raw25045step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25045step2 raw25045step2Labels raw25045step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1522 node1522Labels := by rfl

theorem canonical25046 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25046 raw25046Labels = mixedMoment B node1734 node1734Labels := by
  calc
    mixedMoment B raw25046 raw25046Labels = mixedMoment B raw25046step0 raw25046step0Labels := by
      have hz : ∀ j, raw25046 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25046step0 = (fun i j => raw25046 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25046step0 raw25046; decide +kernel
      have hl : raw25046step0Labels = raw25046Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25046 raw25046Labels permutation346 hz
    mixedMoment B raw25046step0 raw25046step0Labels = mixedMoment B raw25046step1 raw25046step1Labels := by
      have ha : raw25046step1 = (fun i j => raw25046step0 (permutation50 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25046step1 raw25046step0; decide +kernel
      have hl : raw25046step1Labels = raw25046step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25046step0 raw25046step0Labels permutation50 permutation7
    mixedMoment B raw25046step1 raw25046step1Labels = mixedMoment B raw25046step2 raw25046step2Labels := by
      have ha : raw25046step2 = -raw25046step1 := by apply Matrix.ext; change ∀ i j, raw25046step2 i j = -(raw25046step1 i j); unfold raw25046step2 raw25046step1; decide +kernel
      have hl : raw25046step2Labels = raw25046step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25046step2 raw25046step2Labels = mixedMoment B raw25046step3 raw25046step3Labels := by
      have ha : raw25046step3 = raw25046step2 := by apply Matrix.ext; unfold raw25046step3 raw25046step2; decide +kernel
      have hl : raw25046step2Labels = labelEmbedding1 ∘ raw25046step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25046step2 raw25046step2Labels raw25046step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1734 node1734Labels := by rfl

theorem canonical25047 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25047 raw25047Labels = mixedMoment B node1678 node1678Labels := by
  calc
    mixedMoment B raw25047 raw25047Labels = mixedMoment B raw25047step0 raw25047step0Labels := by
      have ha : raw25047step0 = (fun i j => raw25047 (permutation194 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25047step0 raw25047; decide +kernel
      have hl : raw25047step0Labels = raw25047Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25047 raw25047Labels permutation194 permutation7
    mixedMoment B raw25047step0 raw25047step0Labels = mixedMoment B raw25047step1 raw25047step1Labels := by
      have ha : raw25047step1 = -raw25047step0 := by apply Matrix.ext; change ∀ i j, raw25047step1 i j = -(raw25047step0 i j); unfold raw25047step1 raw25047step0; decide +kernel
      have hl : raw25047step1Labels = raw25047step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25047step1 raw25047step1Labels = mixedMoment B raw25047step2 raw25047step2Labels := by
      have ha : raw25047step2 = raw25047step1 := by apply Matrix.ext; unfold raw25047step2 raw25047step1; decide +kernel
      have hl : raw25047step1Labels = labelEmbedding1 ∘ raw25047step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25047step1 raw25047step1Labels raw25047step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1678 node1678Labels := by rfl

theorem canonical25048 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25048 raw25048Labels = mixedMoment B node1736 node1736Labels := by
  calc
    mixedMoment B raw25048 raw25048Labels = mixedMoment B raw25048step0 raw25048step0Labels := by
      have hz : ∀ j, raw25048 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25048step0 = (fun i j => raw25048 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25048step0 raw25048; decide +kernel
      have hl : raw25048step0Labels = raw25048Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25048 raw25048Labels permutation346 hz
    mixedMoment B raw25048step0 raw25048step0Labels = mixedMoment B raw25048step1 raw25048step1Labels := by
      have ha : raw25048step1 = (fun i j => raw25048step0 (permutation50 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25048step1 raw25048step0; decide +kernel
      have hl : raw25048step1Labels = raw25048step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25048step0 raw25048step0Labels permutation50 permutation7
    mixedMoment B raw25048step1 raw25048step1Labels = mixedMoment B raw25048step2 raw25048step2Labels := by
      have ha : raw25048step2 = -raw25048step1 := by apply Matrix.ext; change ∀ i j, raw25048step2 i j = -(raw25048step1 i j); unfold raw25048step2 raw25048step1; decide +kernel
      have hl : raw25048step2Labels = raw25048step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25048step2 raw25048step2Labels = mixedMoment B raw25048step3 raw25048step3Labels := by
      have ha : raw25048step3 = raw25048step2 := by apply Matrix.ext; unfold raw25048step3 raw25048step2; decide +kernel
      have hl : raw25048step2Labels = labelEmbedding1 ∘ raw25048step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25048step2 raw25048step2Labels raw25048step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1736 node1736Labels := by rfl

theorem canonical25049 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25049 raw25049Labels = mixedMoment B node1724 node1724Labels := by
  calc
    mixedMoment B raw25049 raw25049Labels = mixedMoment B raw25049step0 raw25049step0Labels := by
      have hz : ∀ j, raw25049 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25049step0 = (fun i j => raw25049 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25049step0 raw25049; decide +kernel
      have hl : raw25049step0Labels = raw25049Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25049 raw25049Labels permutation346 hz
    mixedMoment B raw25049step0 raw25049step0Labels = mixedMoment B raw25049step1 raw25049step1Labels := by
      have ha : raw25049step1 = (fun i j => raw25049step0 (permutation50 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25049step1 raw25049step0; decide +kernel
      have hl : raw25049step1Labels = raw25049step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25049step0 raw25049step0Labels permutation50 permutation7
    mixedMoment B raw25049step1 raw25049step1Labels = mixedMoment B raw25049step2 raw25049step2Labels := by
      have ha : raw25049step2 = -raw25049step1 := by apply Matrix.ext; change ∀ i j, raw25049step2 i j = -(raw25049step1 i j); unfold raw25049step2 raw25049step1; decide +kernel
      have hl : raw25049step2Labels = raw25049step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25049step2 raw25049step2Labels = mixedMoment B raw25049step3 raw25049step3Labels := by
      have ha : raw25049step3 = raw25049step2 := by apply Matrix.ext; unfold raw25049step3 raw25049step2; decide +kernel
      have hl : raw25049step2Labels = labelEmbedding1 ∘ raw25049step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25049step2 raw25049step2Labels raw25049step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1724 node1724Labels := by rfl

theorem canonical25050 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25050 raw25050Labels = mixedMoment B node1528 node1528Labels := by
  calc
    mixedMoment B raw25050 raw25050Labels = mixedMoment B raw25050step0 raw25050step0Labels := by
      have hz : ∀ j, raw25050 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25050step0 = (fun i j => raw25050 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25050step0 raw25050; decide +kernel
      have hl : raw25050step0Labels = raw25050Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25050 raw25050Labels permutation346 hz
    mixedMoment B raw25050step0 raw25050step0Labels = mixedMoment B raw25050step1 raw25050step1Labels := by
      have ha : raw25050step1 = (fun i j => raw25050step0 (permutation50 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25050step1 raw25050step0; decide +kernel
      have hl : raw25050step1Labels = raw25050step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25050step0 raw25050step0Labels permutation50 permutation7
    mixedMoment B raw25050step1 raw25050step1Labels = mixedMoment B raw25050step2 raw25050step2Labels := by
      have ha : raw25050step2 = -raw25050step1 := by apply Matrix.ext; change ∀ i j, raw25050step2 i j = -(raw25050step1 i j); unfold raw25050step2 raw25050step1; decide +kernel
      have hl : raw25050step2Labels = raw25050step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25050step2 raw25050step2Labels = mixedMoment B raw25050step3 raw25050step3Labels := by
      have ha : raw25050step3 = raw25050step2 := by apply Matrix.ext; unfold raw25050step3 raw25050step2; decide +kernel
      have hl : raw25050step2Labels = labelEmbedding1 ∘ raw25050step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25050step2 raw25050step2Labels raw25050step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1528 node1528Labels := by rfl

theorem canonical25051 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25051 raw25051Labels = mixedMoment B node1742 node1742Labels := by
  calc
    mixedMoment B raw25051 raw25051Labels = mixedMoment B raw25051step0 raw25051step0Labels := by
      have hz : ∀ j, raw25051 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25051step0 = (fun i j => raw25051 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25051step0 raw25051; decide +kernel
      have hl : raw25051step0Labels = raw25051Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25051 raw25051Labels permutation346 hz
    mixedMoment B raw25051step0 raw25051step0Labels = mixedMoment B raw25051step1 raw25051step1Labels := by
      have ha : raw25051step1 = (fun i j => raw25051step0 (permutation50 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25051step1 raw25051step0; decide +kernel
      have hl : raw25051step1Labels = raw25051step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25051step0 raw25051step0Labels permutation50 permutation7
    mixedMoment B raw25051step1 raw25051step1Labels = mixedMoment B raw25051step2 raw25051step2Labels := by
      have ha : raw25051step2 = -raw25051step1 := by apply Matrix.ext; change ∀ i j, raw25051step2 i j = -(raw25051step1 i j); unfold raw25051step2 raw25051step1; decide +kernel
      have hl : raw25051step2Labels = raw25051step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25051step2 raw25051step2Labels = mixedMoment B raw25051step3 raw25051step3Labels := by
      have ha : raw25051step3 = raw25051step2 := by apply Matrix.ext; unfold raw25051step3 raw25051step2; decide +kernel
      have hl : raw25051step2Labels = labelEmbedding1 ∘ raw25051step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25051step2 raw25051step2Labels raw25051step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1742 node1742Labels := by rfl

theorem canonical25052 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25052 raw25052Labels = mixedMoment B node1684 node1684Labels := by
  calc
    mixedMoment B raw25052 raw25052Labels = mixedMoment B raw25052step0 raw25052step0Labels := by
      have ha : raw25052step0 = (fun i j => raw25052 (permutation194 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25052step0 raw25052; decide +kernel
      have hl : raw25052step0Labels = raw25052Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25052 raw25052Labels permutation194 permutation7
    mixedMoment B raw25052step0 raw25052step0Labels = mixedMoment B raw25052step1 raw25052step1Labels := by
      have ha : raw25052step1 = -raw25052step0 := by apply Matrix.ext; change ∀ i j, raw25052step1 i j = -(raw25052step0 i j); unfold raw25052step1 raw25052step0; decide +kernel
      have hl : raw25052step1Labels = raw25052step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25052step1 raw25052step1Labels = mixedMoment B raw25052step2 raw25052step2Labels := by
      have ha : raw25052step2 = raw25052step1 := by apply Matrix.ext; unfold raw25052step2 raw25052step1; decide +kernel
      have hl : raw25052step1Labels = labelEmbedding1 ∘ raw25052step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25052step1 raw25052step1Labels raw25052step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1684 node1684Labels := by rfl

theorem canonical25053 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25053 raw25053Labels = mixedMoment B node1744 node1744Labels := by
  calc
    mixedMoment B raw25053 raw25053Labels = mixedMoment B raw25053step0 raw25053step0Labels := by
      have hz : ∀ j, raw25053 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25053step0 = (fun i j => raw25053 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25053step0 raw25053; decide +kernel
      have hl : raw25053step0Labels = raw25053Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25053 raw25053Labels permutation346 hz
    mixedMoment B raw25053step0 raw25053step0Labels = mixedMoment B raw25053step1 raw25053step1Labels := by
      have ha : raw25053step1 = (fun i j => raw25053step0 (permutation50 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25053step1 raw25053step0; decide +kernel
      have hl : raw25053step1Labels = raw25053step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25053step0 raw25053step0Labels permutation50 permutation7
    mixedMoment B raw25053step1 raw25053step1Labels = mixedMoment B raw25053step2 raw25053step2Labels := by
      have ha : raw25053step2 = -raw25053step1 := by apply Matrix.ext; change ∀ i j, raw25053step2 i j = -(raw25053step1 i j); unfold raw25053step2 raw25053step1; decide +kernel
      have hl : raw25053step2Labels = raw25053step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25053step2 raw25053step2Labels = mixedMoment B raw25053step3 raw25053step3Labels := by
      have ha : raw25053step3 = raw25053step2 := by apply Matrix.ext; unfold raw25053step3 raw25053step2; decide +kernel
      have hl : raw25053step2Labels = labelEmbedding1 ∘ raw25053step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25053step2 raw25053step2Labels raw25053step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1744 node1744Labels := by rfl

theorem canonical25054 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25054 raw25054Labels = mixedMoment B node1744 node1744Labels := by
  calc
    mixedMoment B raw25054 raw25054Labels = mixedMoment B raw25054step0 raw25054step0Labels := by
      have hz : ∀ j, raw25054 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25054step0 = (fun i j => raw25054 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25054step0 raw25054; decide +kernel
      have hl : raw25054step0Labels = raw25054Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25054 raw25054Labels permutation346 hz
    mixedMoment B raw25054step0 raw25054step0Labels = mixedMoment B raw25054step1 raw25054step1Labels := by
      have ha : raw25054step1 = (fun i j => raw25054step0 (permutation51 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25054step1 raw25054step0; decide +kernel
      have hl : raw25054step1Labels = raw25054step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25054step0 raw25054step0Labels permutation51 permutation7
    mixedMoment B raw25054step1 raw25054step1Labels = mixedMoment B raw25054step2 raw25054step2Labels := by
      have ha : raw25054step2 = -raw25054step1 := by apply Matrix.ext; change ∀ i j, raw25054step2 i j = -(raw25054step1 i j); unfold raw25054step2 raw25054step1; decide +kernel
      have hl : raw25054step2Labels = raw25054step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25054step2 raw25054step2Labels = mixedMoment B raw25054step3 raw25054step3Labels := by
      have ha : raw25054step3 = raw25054step2 := by apply Matrix.ext; unfold raw25054step3 raw25054step2; decide +kernel
      have hl : raw25054step2Labels = labelEmbedding1 ∘ raw25054step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25054step2 raw25054step2Labels raw25054step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1744 node1744Labels := by rfl

theorem canonical25055 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25055 raw25055Labels = mixedMoment B node610 node610Labels := by
  calc
    mixedMoment B raw25055 raw25055Labels = mixedMoment B raw25055step0 raw25055step0Labels := by
      have hz : ∀ j, raw25055 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25055step0 = (fun i j => raw25055 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25055step0 raw25055; decide +kernel
      have hl : raw25055step0Labels = raw25055Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25055 raw25055Labels permutation346 hz
    _ = mixedMoment B node610 node610Labels := by rfl

theorem canonical25056 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25056 raw25056Labels = mixedMoment B node1044 node1044Labels := by
  calc
    mixedMoment B raw25056 raw25056Labels = mixedMoment B raw25056step0 raw25056step0Labels := by
      have hz : ∀ j, raw25056 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25056step0 = (fun i j => raw25056 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25056step0 raw25056; decide +kernel
      have hl : raw25056step0Labels = raw25056Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25056 raw25056Labels permutation346 hz
    _ = mixedMoment B node1044 node1044Labels := by rfl

theorem canonical25057 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25057 raw25057Labels = mixedMoment B node929 node929Labels := by
  calc
    mixedMoment B raw25057 raw25057Labels = mixedMoment B raw25057step0 raw25057step0Labels := by
      have ha : raw25057step0 = (fun i j => raw25057 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25057step0 raw25057; decide +kernel
      have hl : raw25057step0Labels = raw25057Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25057 raw25057Labels permutation176 permutation2
    _ = mixedMoment B node929 node929Labels := by rfl

theorem canonical25058 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25058 raw25058Labels = mixedMoment B node1044 node1044Labels := by
  calc
    mixedMoment B raw25058 raw25058Labels = mixedMoment B raw25058step0 raw25058step0Labels := by
      have hz : ∀ j, raw25058 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25058step0 = (fun i j => raw25058 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25058step0 raw25058; decide +kernel
      have hl : raw25058step0Labels = raw25058Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25058 raw25058Labels permutation346 hz
    mixedMoment B raw25058step0 raw25058step0Labels = mixedMoment B raw25058step1 raw25058step1Labels := by
      have ha : raw25058step1 = (fun i j => raw25058step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25058step1 raw25058step0; decide +kernel
      have hl : raw25058step1Labels = raw25058step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25058step0 raw25058step0Labels permutation38 permutation2
    _ = mixedMoment B node1044 node1044Labels := by rfl

theorem canonical25059 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25059 raw25059Labels = mixedMoment B node1044 node1044Labels := by
  calc
    mixedMoment B raw25059 raw25059Labels = mixedMoment B raw25059step0 raw25059step0Labels := by
      have hz : ∀ j, raw25059 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25059step0 = (fun i j => raw25059 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25059step0 raw25059; decide +kernel
      have hl : raw25059step0Labels = raw25059Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25059 raw25059Labels permutation346 hz
    mixedMoment B raw25059step0 raw25059step0Labels = mixedMoment B raw25059step1 raw25059step1Labels := by
      have ha : raw25059step1 = (fun i j => raw25059step0 (permutation44 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25059step1 raw25059step0; decide +kernel
      have hl : raw25059step1Labels = raw25059step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25059step0 raw25059step0Labels permutation44 permutation2
    _ = mixedMoment B node1044 node1044Labels := by rfl

theorem canonical25060 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25060 raw25060Labels = mixedMoment B node1081 node1081Labels := by
  calc
    mixedMoment B raw25060 raw25060Labels = mixedMoment B raw25060step0 raw25060step0Labels := by
      have hz : ∀ j, raw25060 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25060step0 = (fun i j => raw25060 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25060step0 raw25060; decide +kernel
      have hl : raw25060step0Labels = raw25060Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25060 raw25060Labels permutation346 hz
    mixedMoment B raw25060step0 raw25060step0Labels = mixedMoment B raw25060step1 raw25060step1Labels := by
      have ha : raw25060step1 = (fun i j => raw25060step0 (permutation50 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25060step1 raw25060step0; decide +kernel
      have hl : raw25060step1Labels = raw25060step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25060step0 raw25060step0Labels permutation50 permutation2
    _ = mixedMoment B node1081 node1081Labels := by rfl

theorem canonical25061 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25061 raw25061Labels = mixedMoment B node4083 node4083Labels := by
  calc
    mixedMoment B raw25061 raw25061Labels = mixedMoment B raw25061step0 raw25061step0Labels := by
      have hz : ∀ j, raw25061 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw25061step0 = (fun i j => raw25061 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw25061step0 raw25061; decide +kernel
      have hl : raw25061step0Labels = raw25061Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25061 raw25061Labels permutation590 hz
    mixedMoment B raw25061step0 raw25061step0Labels = mixedMoment B raw25061step1 raw25061step1Labels := by
      have hz : ∀ j, raw25061step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw25061step1 = (fun i j => raw25061step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw25061step1 raw25061step0; decide +kernel
      have hl : raw25061step1Labels = raw25061step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25061step0 raw25061step0Labels permutation80 hz
    _ = mixedMoment B node4083 node4083Labels := by rfl

theorem canonical25062 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25062 raw25062Labels = mixedMoment B node2110 node2110Labels := by
  calc
    mixedMoment B raw25062 raw25062Labels = mixedMoment B raw25062step0 raw25062step0Labels := by
      have hz : ∀ j, raw25062 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25062step0 = (fun i j => raw25062 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25062step0 raw25062; decide +kernel
      have hl : raw25062step0Labels = raw25062Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25062 raw25062Labels permutation346 hz
    _ = mixedMoment B node2110 node2110Labels := by rfl

theorem canonical25063 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25063 raw25063Labels = mixedMoment B node944 node944Labels := by
  calc
    _ = mixedMoment B node944 node944Labels := by rfl

theorem canonical25064 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25064 raw25064Labels = mixedMoment B node950 node950Labels := by
  calc
    mixedMoment B raw25064 raw25064Labels = mixedMoment B raw25064step0 raw25064step0Labels := by
      have hz : ∀ j, raw25064 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25064step0 = (fun i j => raw25064 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25064step0 raw25064; decide +kernel
      have hl : raw25064step0Labels = raw25064Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25064 raw25064Labels permutation346 hz
    mixedMoment B raw25064step0 raw25064step0Labels = mixedMoment B raw25064step1 raw25064step1Labels := by
      have ha : raw25064step1 = (fun i j => raw25064step0 (permutation35 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25064step1 raw25064step0; decide +kernel
      have hl : raw25064step1Labels = raw25064step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25064step0 raw25064step0Labels permutation35 permutation2
    _ = mixedMoment B node950 node950Labels := by rfl

theorem canonical25065 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25065 raw25065Labels = mixedMoment B node950 node950Labels := by
  calc
    mixedMoment B raw25065 raw25065Labels = mixedMoment B raw25065step0 raw25065step0Labels := by
      have hz : ∀ j, raw25065 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25065step0 = (fun i j => raw25065 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25065step0 raw25065; decide +kernel
      have hl : raw25065step0Labels = raw25065Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25065 raw25065Labels permutation346 hz
    mixedMoment B raw25065step0 raw25065step0Labels = mixedMoment B raw25065step1 raw25065step1Labels := by
      have ha : raw25065step1 = (fun i j => raw25065step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25065step1 raw25065step0; decide +kernel
      have hl : raw25065step1Labels = raw25065step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25065step0 raw25065step0Labels permutation33 permutation2
    _ = mixedMoment B node950 node950Labels := by rfl

theorem canonical25066 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25066 raw25066Labels = mixedMoment B node949 node949Labels := by
  calc
    mixedMoment B raw25066 raw25066Labels = mixedMoment B raw25066step0 raw25066step0Labels := by
      have hz : ∀ j, raw25066 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25066step0 = (fun i j => raw25066 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25066step0 raw25066; decide +kernel
      have hl : raw25066step0Labels = raw25066Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25066 raw25066Labels permutation346 hz
    _ = mixedMoment B node949 node949Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical196
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical25135 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25135 raw25135Labels = mixedMoment B node4866 node4866Labels := by
  calc
    mixedMoment B raw25135 raw25135Labels = mixedMoment B raw25135step0 raw25135step0Labels := by
      have hz : ∀ j, raw25135 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25135step0 = (fun i j => raw25135 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25135step0 raw25135; decide +kernel
      have hl : raw25135step0Labels = raw25135Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25135 raw25135Labels permutation346 hz
    mixedMoment B raw25135step0 raw25135step0Labels = mixedMoment B raw25135step1 raw25135step1Labels := by
      have ha : raw25135step1 = (fun i j => raw25135step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25135step1 raw25135step0; decide +kernel
      have hl : raw25135step1Labels = raw25135step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25135step0 raw25135step0Labels permutation34 permutation2
    _ = mixedMoment B node4866 node4866Labels := by rfl

theorem canonical25136 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25136 raw25136Labels = mixedMoment B node4802 node4802Labels := by
  calc
    mixedMoment B raw25136 raw25136Labels = mixedMoment B raw25136step0 raw25136step0Labels := by
      have ha : raw25136step0 = (fun i j => raw25136 (permutation178 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25136step0 raw25136; decide +kernel
      have hl : raw25136step0Labels = raw25136Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25136 raw25136Labels permutation178 permutation2
    _ = mixedMoment B node4802 node4802Labels := by rfl

theorem canonical25137 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25137 raw25137Labels = mixedMoment B node4888 node4888Labels := by
  calc
    mixedMoment B raw25137 raw25137Labels = mixedMoment B raw25137step0 raw25137step0Labels := by
      have hz : ∀ j, raw25137 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25137step0 = (fun i j => raw25137 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25137step0 raw25137; decide +kernel
      have hl : raw25137step0Labels = raw25137Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25137 raw25137Labels permutation346 hz
    _ = mixedMoment B node4888 node4888Labels := by rfl

theorem canonical25138 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25138 raw25138Labels = mixedMoment B node4895 node4895Labels := by
  calc
    mixedMoment B raw25138 raw25138Labels = mixedMoment B raw25138step0 raw25138step0Labels := by
      have hz : ∀ j, raw25138 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw25138step0 = (fun i j => raw25138 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw25138step0 raw25138; decide +kernel
      have hl : raw25138step0Labels = raw25138Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25138 raw25138Labels permutation520 hz
    mixedMoment B raw25138step0 raw25138step0Labels = mixedMoment B raw25138step1 raw25138step1Labels := by
      have hz : ∀ j, raw25138step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw25138step1 = (fun i j => raw25138step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw25138step1 raw25138step0; decide +kernel
      have hl : raw25138step1Labels = raw25138step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25138step0 raw25138step0Labels permutation80 hz
    _ = mixedMoment B node4895 node4895Labels := by rfl

theorem canonical25139 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25139 raw25139Labels = mixedMoment B node4893 node4893Labels := by
  calc
    mixedMoment B raw25139 raw25139Labels = mixedMoment B raw25139step0 raw25139step0Labels := by
      have hz : ∀ j, raw25139 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25139step0 = (fun i j => raw25139 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25139step0 raw25139; decide +kernel
      have hl : raw25139step0Labels = raw25139Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25139 raw25139Labels permutation346 hz
    mixedMoment B raw25139step0 raw25139step0Labels = mixedMoment B raw25139step1 raw25139step1Labels := by
      have ha : raw25139step1 = (fun i j => raw25139step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25139step1 raw25139step0; decide +kernel
      have hl : raw25139step1Labels = raw25139step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25139step0 raw25139step0Labels permutation34 permutation2
    _ = mixedMoment B node4893 node4893Labels := by rfl

theorem canonical25140 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25140 raw25140Labels = mixedMoment B node4175 node4175Labels := by
  calc
    mixedMoment B raw25140 raw25140Labels = mixedMoment B raw25140step0 raw25140step0Labels := by
      have hz : ∀ j, raw25140 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25140step0 = (fun i j => raw25140 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25140step0 raw25140; decide +kernel
      have hl : raw25140step0Labels = raw25140Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25140 raw25140Labels permutation346 hz
    mixedMoment B raw25140step0 raw25140step0Labels = mixedMoment B raw25140step1 raw25140step1Labels := by
      have ha : raw25140step1 = (fun i j => raw25140step0 (permutation44 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25140step1 raw25140step0; decide +kernel
      have hl : raw25140step1Labels = raw25140step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25140step0 raw25140step0Labels permutation44 permutation2
    _ = mixedMoment B node4175 node4175Labels := by rfl

theorem canonical25141 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25141 raw25141Labels = mixedMoment B node4344 node4344Labels := by
  calc
    mixedMoment B raw25141 raw25141Labels = mixedMoment B raw25141step0 raw25141step0Labels := by
      have ha : raw25141step0 = (fun i j => raw25141 (permutation188 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25141step0 raw25141; decide +kernel
      have hl : raw25141step0Labels = raw25141Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25141 raw25141Labels permutation188 permutation2
    _ = mixedMoment B node4344 node4344Labels := by rfl

theorem canonical25142 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25142 raw25142Labels = mixedMoment B node4458 node4458Labels := by
  calc
    mixedMoment B raw25142 raw25142Labels = mixedMoment B raw25142step0 raw25142step0Labels := by
      have hz : ∀ j, raw25142 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25142step0 = (fun i j => raw25142 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25142step0 raw25142; decide +kernel
      have hl : raw25142step0Labels = raw25142Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25142 raw25142Labels permutation346 hz
    mixedMoment B raw25142step0 raw25142step0Labels = mixedMoment B raw25142step1 raw25142step1Labels := by
      have ha : raw25142step1 = (fun i j => raw25142step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25142step1 raw25142step0; decide +kernel
      have hl : raw25142step1Labels = raw25142step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25142step0 raw25142step0Labels permutation40 permutation2
    _ = mixedMoment B node4458 node4458Labels := by rfl

theorem canonical25143 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25143 raw25143Labels = mixedMoment B node4502 node4502Labels := by
  calc
    mixedMoment B raw25143 raw25143Labels = mixedMoment B raw25143step0 raw25143step0Labels := by
      have hz : ∀ j, raw25143 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw25143step0 = (fun i j => raw25143 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw25143step0 raw25143; decide +kernel
      have hl : raw25143step0Labels = raw25143Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25143 raw25143Labels permutation520 hz
    mixedMoment B raw25143step0 raw25143step0Labels = mixedMoment B raw25143step1 raw25143step1Labels := by
      have hz : ∀ j, raw25143step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw25143step1 = (fun i j => raw25143step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw25143step1 raw25143step0; decide +kernel
      have hl : raw25143step1Labels = raw25143step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25143step0 raw25143step0Labels permutation80 hz
    _ = mixedMoment B node4502 node4502Labels := by rfl

theorem canonical25144 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25144 raw25144Labels = mixedMoment B node4497 node4497Labels := by
  calc
    mixedMoment B raw25144 raw25144Labels = mixedMoment B raw25144step0 raw25144step0Labels := by
      have hz : ∀ j, raw25144 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25144step0 = (fun i j => raw25144 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25144step0 raw25144; decide +kernel
      have hl : raw25144step0Labels = raw25144Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25144 raw25144Labels permutation346 hz
    mixedMoment B raw25144step0 raw25144step0Labels = mixedMoment B raw25144step1 raw25144step1Labels := by
      have ha : raw25144step1 = (fun i j => raw25144step0 (permutation44 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25144step1 raw25144step0; decide +kernel
      have hl : raw25144step1Labels = raw25144step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25144step0 raw25144step0Labels permutation44 permutation2
    _ = mixedMoment B node4497 node4497Labels := by rfl

theorem canonical25145 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25145 raw25145Labels = mixedMoment B node4150 node4150Labels := by
  calc
    mixedMoment B raw25145 raw25145Labels = mixedMoment B raw25145step0 raw25145step0Labels := by
      have ha : raw25145step0 = (fun i j => raw25145 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25145step0 raw25145; decide +kernel
      have hl : raw25145step0Labels = raw25145Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25145 raw25145Labels permutation154 permutation2
    _ = mixedMoment B node4150 node4150Labels := by rfl

theorem canonical25146 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25146 raw25146Labels = mixedMoment B node4364 node4364Labels := by
  calc
    mixedMoment B raw25146 raw25146Labels = mixedMoment B raw25146step0 raw25146step0Labels := by
      have ha : raw25146step0 = (fun i j => raw25146 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25146step0 raw25146; decide +kernel
      have hl : raw25146step0Labels = raw25146Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25146 raw25146Labels permutation154 permutation2
    _ = mixedMoment B node4364 node4364Labels := by rfl

theorem canonical25147 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25147 raw25147Labels = mixedMoment B node4438 node4438Labels := by
  calc
    mixedMoment B raw25147 raw25147Labels = mixedMoment B raw25147step0 raw25147step0Labels := by
      have ha : raw25147step0 = (fun i j => raw25147 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25147step0 raw25147; decide +kernel
      have hl : raw25147step0Labels = raw25147Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25147 raw25147Labels permutation158 permutation2
    _ = mixedMoment B node4438 node4438Labels := by rfl

theorem canonical25148 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25148 raw25148Labels = mixedMoment B node4458 node4458Labels := by
  calc
    mixedMoment B raw25148 raw25148Labels = mixedMoment B raw25148step0 raw25148step0Labels := by
      have hz : ∀ j, raw25148 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw25148step0 = (fun i j => raw25148 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw25148step0 raw25148; decide +kernel
      have hl : raw25148step0Labels = raw25148Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25148 raw25148Labels permutation520 hz
    _ = mixedMoment B node4458 node4458Labels := by rfl

theorem canonical25149 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25149 raw25149Labels = mixedMoment B node4456 node4456Labels := by
  calc
    mixedMoment B raw25149 raw25149Labels = mixedMoment B raw25149step0 raw25149step0Labels := by
      have ha : raw25149step0 = (fun i j => raw25149 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25149step0 raw25149; decide +kernel
      have hl : raw25149step0Labels = raw25149Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25149 raw25149Labels permutation154 permutation2
    _ = mixedMoment B node4456 node4456Labels := by rfl

theorem canonical25150 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25150 raw25150Labels = mixedMoment B node4155 node4155Labels := by
  calc
    mixedMoment B raw25150 raw25150Labels = mixedMoment B raw25150step0 raw25150step0Labels := by
      have hz : ∀ j, raw25150 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25150step0 = (fun i j => raw25150 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25150step0 raw25150; decide +kernel
      have hl : raw25150step0Labels = raw25150Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25150 raw25150Labels permutation346 hz
    mixedMoment B raw25150step0 raw25150step0Labels = mixedMoment B raw25150step1 raw25150step1Labels := by
      have ha : raw25150step1 = (fun i j => raw25150step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25150step1 raw25150step0; decide +kernel
      have hl : raw25150step1Labels = raw25150step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25150step0 raw25150step0Labels permutation34 permutation2
    _ = mixedMoment B node4155 node4155Labels := by rfl

theorem canonical25151 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25151 raw25151Labels = mixedMoment B node4369 node4369Labels := by
  calc
    mixedMoment B raw25151 raw25151Labels = mixedMoment B raw25151step0 raw25151step0Labels := by
      have hz : ∀ j, raw25151 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25151step0 = (fun i j => raw25151 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25151step0 raw25151; decide +kernel
      have hl : raw25151step0Labels = raw25151Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25151 raw25151Labels permutation346 hz
    mixedMoment B raw25151step0 raw25151step0Labels = mixedMoment B raw25151step1 raw25151step1Labels := by
      have ha : raw25151step1 = (fun i j => raw25151step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25151step1 raw25151step0; decide +kernel
      have hl : raw25151step1Labels = raw25151step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25151step0 raw25151step0Labels permutation34 permutation2
    _ = mixedMoment B node4369 node4369Labels := by rfl

theorem canonical25152 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25152 raw25152Labels = mixedMoment B node4329 node4329Labels := by
  calc
    mixedMoment B raw25152 raw25152Labels = mixedMoment B raw25152step0 raw25152step0Labels := by
      have ha : raw25152step0 = (fun i j => raw25152 (permutation178 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25152step0 raw25152; decide +kernel
      have hl : raw25152step0Labels = raw25152Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25152 raw25152Labels permutation178 permutation2
    _ = mixedMoment B node4329 node4329Labels := by rfl

theorem canonical25153 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25153 raw25153Labels = mixedMoment B node4467 node4467Labels := by
  calc
    mixedMoment B raw25153 raw25153Labels = mixedMoment B raw25153step0 raw25153step0Labels := by
      have hz : ∀ j, raw25153 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw25153step0 = (fun i j => raw25153 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw25153step0 raw25153; decide +kernel
      have hl : raw25153step0Labels = raw25153Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25153 raw25153Labels permutation520 hz
    mixedMoment B raw25153step0 raw25153step0Labels = mixedMoment B raw25153step1 raw25153step1Labels := by
      have hz : ∀ j, raw25153step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw25153step1 = (fun i j => raw25153step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw25153step1 raw25153step0; decide +kernel
      have hl : raw25153step1Labels = raw25153step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25153step0 raw25153step0Labels permutation80 hz
    _ = mixedMoment B node4467 node4467Labels := by rfl

theorem canonical25154 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25154 raw25154Labels = mixedMoment B node4458 node4458Labels := by
  calc
    mixedMoment B raw25154 raw25154Labels = mixedMoment B raw25154step0 raw25154step0Labels := by
      have hz : ∀ j, raw25154 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25154step0 = (fun i j => raw25154 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25154step0 raw25154; decide +kernel
      have hl : raw25154step0Labels = raw25154Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25154 raw25154Labels permutation346 hz
    mixedMoment B raw25154step0 raw25154step0Labels = mixedMoment B raw25154step1 raw25154step1Labels := by
      have ha : raw25154step1 = (fun i j => raw25154step0 (permutation35 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25154step1 raw25154step0; decide +kernel
      have hl : raw25154step1Labels = raw25154step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25154step0 raw25154step0Labels permutation35 permutation2
    _ = mixedMoment B node4458 node4458Labels := by rfl

theorem canonical25155 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25155 raw25155Labels = mixedMoment B node4158 node4158Labels := by
  calc
    mixedMoment B raw25155 raw25155Labels = mixedMoment B raw25155step0 raw25155step0Labels := by
      have hz : ∀ j, raw25155 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25155step0 = (fun i j => raw25155 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25155step0 raw25155; decide +kernel
      have hl : raw25155step0Labels = raw25155Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25155 raw25155Labels permutation346 hz
    _ = mixedMoment B node4158 node4158Labels := by rfl

theorem canonical25156 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25156 raw25156Labels = mixedMoment B node4372 node4372Labels := by
  calc
    mixedMoment B raw25156 raw25156Labels = mixedMoment B raw25156step0 raw25156step0Labels := by
      have hz : ∀ j, raw25156 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25156step0 = (fun i j => raw25156 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25156step0 raw25156; decide +kernel
      have hl : raw25156step0Labels = raw25156Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25156 raw25156Labels permutation346 hz
    _ = mixedMoment B node4372 node4372Labels := by rfl

theorem canonical25157 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25157 raw25157Labels = mixedMoment B node4332 node4332Labels := by
  calc
    mixedMoment B raw25157 raw25157Labels = mixedMoment B raw25157step0 raw25157step0Labels := by
      have ha : raw25157step0 = (fun i j => raw25157 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25157step0 raw25157; decide +kernel
      have hl : raw25157step0Labels = raw25157Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25157 raw25157Labels permutation176 permutation2
    _ = mixedMoment B node4332 node4332Labels := by rfl

theorem canonical25158 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25158 raw25158Labels = mixedMoment B node4444 node4444Labels := by
  calc
    mixedMoment B raw25158 raw25158Labels = mixedMoment B raw25158step0 raw25158step0Labels := by
      have hz : ∀ j, raw25158 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25158step0 = (fun i j => raw25158 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25158step0 raw25158; decide +kernel
      have hl : raw25158step0Labels = raw25158Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25158 raw25158Labels permutation346 hz
    _ = mixedMoment B node4444 node4444Labels := by rfl

theorem canonical25159 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25159 raw25159Labels = mixedMoment B node4461 node4461Labels := by
  calc
    mixedMoment B raw25159 raw25159Labels = mixedMoment B raw25159step0 raw25159step0Labels := by
      have hz : ∀ j, raw25159 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25159step0 = (fun i j => raw25159 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25159step0 raw25159; decide +kernel
      have hl : raw25159step0Labels = raw25159Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25159 raw25159Labels permutation346 hz
    mixedMoment B raw25159step0 raw25159step0Labels = mixedMoment B raw25159step1 raw25159step1Labels := by
      have ha : raw25159step1 = (fun i j => raw25159step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25159step1 raw25159step0; decide +kernel
      have hl : raw25159step1Labels = raw25159step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25159step0 raw25159step0Labels permutation33 permutation2
    _ = mixedMoment B node4461 node4461Labels := by rfl

theorem canonical25160 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25160 raw25160Labels = mixedMoment B node4153 node4153Labels := by
  calc
    mixedMoment B raw25160 raw25160Labels = mixedMoment B raw25160step0 raw25160step0Labels := by
      have hz : ∀ j, raw25160 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25160step0 = (fun i j => raw25160 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25160step0 raw25160; decide +kernel
      have hl : raw25160step0Labels = raw25160Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25160 raw25160Labels permutation346 hz
    mixedMoment B raw25160step0 raw25160step0Labels = mixedMoment B raw25160step1 raw25160step1Labels := by
      have ha : raw25160step1 = (fun i j => raw25160step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25160step1 raw25160step0; decide +kernel
      have hl : raw25160step1Labels = raw25160step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25160step0 raw25160step0Labels permutation34 permutation2
    _ = mixedMoment B node4153 node4153Labels := by rfl

theorem canonical25161 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25161 raw25161Labels = mixedMoment B node4367 node4367Labels := by
  calc
    mixedMoment B raw25161 raw25161Labels = mixedMoment B raw25161step0 raw25161step0Labels := by
      have hz : ∀ j, raw25161 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25161step0 = (fun i j => raw25161 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25161step0 raw25161; decide +kernel
      have hl : raw25161step0Labels = raw25161Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25161 raw25161Labels permutation346 hz
    mixedMoment B raw25161step0 raw25161step0Labels = mixedMoment B raw25161step1 raw25161step1Labels := by
      have ha : raw25161step1 = (fun i j => raw25161step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25161step1 raw25161step0; decide +kernel
      have hl : raw25161step1Labels = raw25161step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25161step0 raw25161step0Labels permutation34 permutation2
    _ = mixedMoment B node4367 node4367Labels := by rfl

theorem canonical25162 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25162 raw25162Labels = mixedMoment B node4327 node4327Labels := by
  calc
    mixedMoment B raw25162 raw25162Labels = mixedMoment B raw25162step0 raw25162step0Labels := by
      have ha : raw25162step0 = (fun i j => raw25162 (permutation178 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25162step0 raw25162; decide +kernel
      have hl : raw25162step0Labels = raw25162Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25162 raw25162Labels permutation178 permutation2
    _ = mixedMoment B node4327 node4327Labels := by rfl

theorem canonical25163 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25163 raw25163Labels = mixedMoment B node4440 node4440Labels := by
  calc
    mixedMoment B raw25163 raw25163Labels = mixedMoment B raw25163step0 raw25163step0Labels := by
      have hz : ∀ j, raw25163 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25163step0 = (fun i j => raw25163 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25163step0 raw25163; decide +kernel
      have hl : raw25163step0Labels = raw25163Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25163 raw25163Labels permutation346 hz
    _ = mixedMoment B node4440 node4440Labels := by rfl

theorem canonical25164 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25164 raw25164Labels = mixedMoment B node4463 node4463Labels := by
  calc
    mixedMoment B raw25164 raw25164Labels = mixedMoment B raw25164step0 raw25164step0Labels := by
      have hz : ∀ j, raw25164 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw25164step0 = (fun i j => raw25164 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw25164step0 raw25164; decide +kernel
      have hl : raw25164step0Labels = raw25164Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25164 raw25164Labels permutation520 hz
    mixedMoment B raw25164step0 raw25164step0Labels = mixedMoment B raw25164step1 raw25164step1Labels := by
      have hz : ∀ j, raw25164step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw25164step1 = (fun i j => raw25164step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw25164step1 raw25164step0; decide +kernel
      have hl : raw25164step1Labels = raw25164step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25164step0 raw25164step0Labels permutation80 hz
    _ = mixedMoment B node4463 node4463Labels := by rfl

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

theorem canonical810 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw810 raw810Labels = mixedMoment B node4175 node4175Labels := by
  calc
    mixedMoment B raw810 raw810Labels = mixedMoment B raw810step0 raw810step0Labels := by
      have ha : raw810step0 = (fun i j => raw810 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw810step0 raw810; decide +kernel
      have hl : raw810step0Labels = raw810Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw810 raw810Labels permutation32 permutation4
    mixedMoment B raw810step0 raw810step0Labels = mixedMoment B raw810step1 raw810step1Labels := by
      have ha : raw810step1 = raw810step0 := by apply Matrix.ext; unfold raw810step1 raw810step0; decide +kernel
      have hl : raw810step0Labels = labelEmbedding7 ∘ raw810step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw810step0 raw810step0Labels raw810step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4175 node4175Labels := by rfl

theorem canonical811 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw811 raw811Labels = mixedMoment B node603 node603Labels := by
  calc
    mixedMoment B raw811 raw811Labels = mixedMoment B raw811step0 raw811step0Labels := by
      have ha : raw811step0 = (fun i j => raw811 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw811step0 raw811; decide +kernel
      have hl : raw811step0Labels = raw811Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw811 raw811Labels permutation32 permutation4
    _ = mixedMoment B node603 node603Labels := by rfl

theorem canonical812 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw812 raw812Labels = mixedMoment B node1517 node1517Labels := by
  calc
    mixedMoment B raw812 raw812Labels = mixedMoment B raw812step0 raw812step0Labels := by
      have ha : raw812step0 = (fun i j => raw812 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw812step0 raw812; decide +kernel
      have hl : raw812step0Labels = raw812Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw812 raw812Labels permutation32 permutation6
    mixedMoment B raw812step0 raw812step0Labels = mixedMoment B raw812step1 raw812step1Labels := by
      have ha : raw812step1 = -raw812step0 := by apply Matrix.ext; change ∀ i j, raw812step1 i j = -(raw812step0 i j); unfold raw812step1 raw812step0; decide +kernel
      have hl : raw812step1Labels = raw812step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw812step1 raw812step1Labels = mixedMoment B raw812step2 raw812step2Labels := by
      have ha : raw812step2 = raw812step1 := by apply Matrix.ext; unfold raw812step2 raw812step1; decide +kernel
      have hl : raw812step1Labels = labelEmbedding1 ∘ raw812step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw812step1 raw812step1Labels raw812step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1517 node1517Labels := by rfl

theorem canonical822 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw822 raw822Labels = mixedMoment B node4182 node4182Labels := by
  calc
    mixedMoment B raw822 raw822Labels = mixedMoment B raw822step0 raw822step0Labels := by
      have ha : raw822step0 = (fun i j => raw822 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw822step0 raw822; decide +kernel
      have hl : raw822step0Labels = raw822Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw822 raw822Labels permutation32 permutation4
    mixedMoment B raw822step0 raw822step0Labels = mixedMoment B raw822step1 raw822step1Labels := by
      have ha : raw822step1 = raw822step0 := by apply Matrix.ext; unfold raw822step1 raw822step0; decide +kernel
      have hl : raw822step0Labels = labelEmbedding7 ∘ raw822step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw822step0 raw822step0Labels raw822step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4182 node4182Labels := by rfl

theorem canonical823 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw823 raw823Labels = mixedMoment B node610 node610Labels := by
  calc
    mixedMoment B raw823 raw823Labels = mixedMoment B raw823step0 raw823step0Labels := by
      have ha : raw823step0 = (fun i j => raw823 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw823step0 raw823; decide +kernel
      have hl : raw823step0Labels = raw823Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw823 raw823Labels permutation32 permutation4
    _ = mixedMoment B node610 node610Labels := by rfl

theorem canonical824 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw824 raw824Labels = mixedMoment B node1524 node1524Labels := by
  calc
    mixedMoment B raw824 raw824Labels = mixedMoment B raw824step0 raw824step0Labels := by
      have ha : raw824step0 = (fun i j => raw824 (permutation50 i) (permutation6 j)) := by apply Matrix.ext; unfold raw824step0 raw824; decide +kernel
      have hl : raw824step0Labels = raw824Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw824 raw824Labels permutation50 permutation6
    mixedMoment B raw824step0 raw824step0Labels = mixedMoment B raw824step1 raw824step1Labels := by
      have ha : raw824step1 = -raw824step0 := by apply Matrix.ext; change ∀ i j, raw824step1 i j = -(raw824step0 i j); unfold raw824step1 raw824step0; decide +kernel
      have hl : raw824step1Labels = raw824step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw824step1 raw824step1Labels = mixedMoment B raw824step2 raw824step2Labels := by
      have ha : raw824step2 = raw824step1 := by apply Matrix.ext; unfold raw824step2 raw824step1; decide +kernel
      have hl : raw824step1Labels = labelEmbedding1 ∘ raw824step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw824step1 raw824step1Labels raw824step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1524 node1524Labels := by rfl

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

theorem canonical1128 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1128 raw1128Labels = mixedMoment B node4344 node4344Labels := by
  calc
    mixedMoment B raw1128 raw1128Labels = mixedMoment B raw1128step0 raw1128step0Labels := by
      have ha : raw1128step0 = (fun i j => raw1128 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1128step0 raw1128; decide +kernel
      have hl : raw1128step0Labels = raw1128Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1128 raw1128Labels permutation152 permutation4
    mixedMoment B raw1128step0 raw1128step0Labels = mixedMoment B raw1128step1 raw1128step1Labels := by
      have ha : raw1128step1 = raw1128step0 := by apply Matrix.ext; unfold raw1128step1 raw1128step0; decide +kernel
      have hl : raw1128step0Labels = labelEmbedding7 ∘ raw1128step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1128step0 raw1128step0Labels raw1128step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4344 node4344Labels := by rfl

theorem canonical1129 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1129 raw1129Labels = mixedMoment B node922 node922Labels := by
  calc
    mixedMoment B raw1129 raw1129Labels = mixedMoment B raw1129step0 raw1129step0Labels := by
      have ha : raw1129step0 = (fun i j => raw1129 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1129step0 raw1129; decide +kernel
      have hl : raw1129step0Labels = raw1129Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1129 raw1129Labels permutation152 permutation4
    _ = mixedMoment B node922 node922Labels := by rfl

theorem canonical1130 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1130 raw1130Labels = mixedMoment B node1673 node1673Labels := by
  calc
    mixedMoment B raw1130 raw1130Labels = mixedMoment B raw1130step0 raw1130step0Labels := by
      have ha : raw1130step0 = (fun i j => raw1130 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1130step0 raw1130; decide +kernel
      have hl : raw1130step0Labels = raw1130Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1130 raw1130Labels permutation152 permutation6
    mixedMoment B raw1130step0 raw1130step0Labels = mixedMoment B raw1130step1 raw1130step1Labels := by
      have ha : raw1130step1 = -raw1130step0 := by apply Matrix.ext; change ∀ i j, raw1130step1 i j = -(raw1130step0 i j); unfold raw1130step1 raw1130step0; decide +kernel
      have hl : raw1130step1Labels = raw1130step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1130step1 raw1130step1Labels = mixedMoment B raw1130step2 raw1130step2Labels := by
      have ha : raw1130step2 = raw1130step1 := by apply Matrix.ext; unfold raw1130step2 raw1130step1; decide +kernel
      have hl : raw1130step1Labels = labelEmbedding1 ∘ raw1130step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1130step1 raw1130step1Labels raw1130step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1673 node1673Labels := by rfl

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

theorem canonical1254 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1254 raw1254Labels = mixedMoment B node4456 node4456Labels := by
  calc
    mixedMoment B raw1254 raw1254Labels = mixedMoment B raw1254step0 raw1254step0Labels := by
      have ha : raw1254step0 = (fun i j => raw1254 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1254step0 raw1254; decide +kernel
      have hl : raw1254step0Labels = raw1254Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1254 raw1254Labels permutation152 permutation4
    mixedMoment B raw1254step0 raw1254step0Labels = mixedMoment B raw1254step1 raw1254step1Labels := by
      have ha : raw1254step1 = raw1254step0 := by apply Matrix.ext; unfold raw1254step1 raw1254step0; decide +kernel
      have hl : raw1254step0Labels = labelEmbedding7 ∘ raw1254step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1254step0 raw1254step0Labels raw1254step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4456 node4456Labels := by rfl

theorem canonical1255 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1255 raw1255Labels = mixedMoment B node1039 node1039Labels := by
  calc
    mixedMoment B raw1255 raw1255Labels = mixedMoment B raw1255step0 raw1255step0Labels := by
      have ha : raw1255step0 = (fun i j => raw1255 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1255step0 raw1255; decide +kernel
      have hl : raw1255step0Labels = raw1255Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1255 raw1255Labels permutation152 permutation4
    _ = mixedMoment B node1039 node1039Labels := by rfl

theorem canonical1256 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1256 raw1256Labels = mixedMoment B node1706 node1706Labels := by
  calc
    mixedMoment B raw1256 raw1256Labels = mixedMoment B raw1256step0 raw1256step0Labels := by
      have ha : raw1256step0 = (fun i j => raw1256 (permutation182 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1256step0 raw1256; decide +kernel
      have hl : raw1256step0Labels = raw1256Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1256 raw1256Labels permutation182 permutation6
    mixedMoment B raw1256step0 raw1256step0Labels = mixedMoment B raw1256step1 raw1256step1Labels := by
      have ha : raw1256step1 = -raw1256step0 := by apply Matrix.ext; change ∀ i j, raw1256step1 i j = -(raw1256step0 i j); unfold raw1256step1 raw1256step0; decide +kernel
      have hl : raw1256step1Labels = raw1256step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1256step1 raw1256step1Labels = mixedMoment B raw1256step2 raw1256step2Labels := by
      have ha : raw1256step2 = raw1256step1 := by apply Matrix.ext; unfold raw1256step2 raw1256step1; decide +kernel
      have hl : raw1256step1Labels = labelEmbedding1 ∘ raw1256step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1256step1 raw1256step1Labels raw1256step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1706 node1706Labels := by rfl

theorem canonical1260 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1260 raw1260Labels = mixedMoment B node4458 node4458Labels := by
  calc
    mixedMoment B raw1260 raw1260Labels = mixedMoment B raw1260step0 raw1260step0Labels := by
      have ha : raw1260step0 = (fun i j => raw1260 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1260step0 raw1260; decide +kernel
      have hl : raw1260step0Labels = raw1260Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1260 raw1260Labels permutation32 permutation4
    mixedMoment B raw1260step0 raw1260step0Labels = mixedMoment B raw1260step1 raw1260step1Labels := by
      have ha : raw1260step1 = raw1260step0 := by apply Matrix.ext; unfold raw1260step1 raw1260step0; decide +kernel
      have hl : raw1260step0Labels = labelEmbedding7 ∘ raw1260step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1260step0 raw1260step0Labels raw1260step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4458 node4458Labels := by rfl

theorem canonical1261 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1261 raw1261Labels = mixedMoment B node1041 node1041Labels := by
  calc
    mixedMoment B raw1261 raw1261Labels = mixedMoment B raw1261step0 raw1261step0Labels := by
      have ha : raw1261step0 = (fun i j => raw1261 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1261step0 raw1261; decide +kernel
      have hl : raw1261step0Labels = raw1261Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1261 raw1261Labels permutation32 permutation4
    _ = mixedMoment B node1041 node1041Labels := by rfl

theorem canonical1262 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1262 raw1262Labels = mixedMoment B node1724 node1724Labels := by
  calc
    mixedMoment B raw1262 raw1262Labels = mixedMoment B raw1262step0 raw1262step0Labels := by
      have ha : raw1262step0 = (fun i j => raw1262 (permutation38 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1262step0 raw1262; decide +kernel
      have hl : raw1262step0Labels = raw1262Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1262 raw1262Labels permutation38 permutation6
    mixedMoment B raw1262step0 raw1262step0Labels = mixedMoment B raw1262step1 raw1262step1Labels := by
      have ha : raw1262step1 = -raw1262step0 := by apply Matrix.ext; change ∀ i j, raw1262step1 i j = -(raw1262step0 i j); unfold raw1262step1 raw1262step0; decide +kernel
      have hl : raw1262step1Labels = raw1262step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1262step1 raw1262step1Labels = mixedMoment B raw1262step2 raw1262step2Labels := by
      have ha : raw1262step2 = raw1262step1 := by apply Matrix.ext; unfold raw1262step2 raw1262step1; decide +kernel
      have hl : raw1262step1Labels = labelEmbedding1 ∘ raw1262step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1262step1 raw1262step1Labels raw1262step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1724 node1724Labels := by rfl

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

theorem canonical1269 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1269 raw1269Labels = mixedMoment B node4463 node4463Labels := by
  calc
    mixedMoment B raw1269 raw1269Labels = mixedMoment B raw1269step0 raw1269step0Labels := by
      have ha : raw1269step0 = (fun i j => raw1269 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1269step0 raw1269; decide +kernel
      have hl : raw1269step0Labels = raw1269Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1269 raw1269Labels permutation8 permutation4
    mixedMoment B raw1269step0 raw1269step0Labels = mixedMoment B raw1269step1 raw1269step1Labels := by
      have ha : raw1269step1 = raw1269step0 := by apply Matrix.ext; unfold raw1269step1 raw1269step0; decide +kernel
      have hl : raw1269step0Labels = labelEmbedding7 ∘ raw1269step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1269step0 raw1269step0Labels raw1269step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4463 node4463Labels := by rfl

theorem canonical1270 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1270 raw1270Labels = mixedMoment B node1046 node1046Labels := by
  calc
    mixedMoment B raw1270 raw1270Labels = mixedMoment B raw1270step0 raw1270step0Labels := by
      have ha : raw1270step0 = (fun i j => raw1270 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1270step0 raw1270; decide +kernel
      have hl : raw1270step0Labels = raw1270Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1270 raw1270Labels permutation8 permutation4
    _ = mixedMoment B node1046 node1046Labels := by rfl

theorem canonical1271 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1271 raw1271Labels = mixedMoment B node1750 node1750Labels := by
  calc
    mixedMoment B raw1271 raw1271Labels = mixedMoment B raw1271step0 raw1271step0Labels := by
      have ha : raw1271step0 = (fun i j => raw1271 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1271step0 raw1271; decide +kernel
      have hl : raw1271step0Labels = raw1271Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1271 raw1271Labels permutation8 permutation6
    mixedMoment B raw1271step0 raw1271step0Labels = mixedMoment B raw1271step1 raw1271step1Labels := by
      have ha : raw1271step1 = -raw1271step0 := by apply Matrix.ext; change ∀ i j, raw1271step1 i j = -(raw1271step0 i j); unfold raw1271step1 raw1271step0; decide +kernel
      have hl : raw1271step1Labels = raw1271step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1271step1 raw1271step1Labels = mixedMoment B raw1271step2 raw1271step2Labels := by
      have ha : raw1271step2 = raw1271step1 := by apply Matrix.ext; unfold raw1271step2 raw1271step1; decide +kernel
      have hl : raw1271step1Labels = labelEmbedding1 ∘ raw1271step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1271step1 raw1271step1Labels raw1271step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1750 node1750Labels := by rfl

theorem canonical1275 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1275 raw1275Labels = mixedMoment B node4467 node4467Labels := by
  calc
    mixedMoment B raw1275 raw1275Labels = mixedMoment B raw1275step0 raw1275step0Labels := by
      have ha : raw1275step0 = (fun i j => raw1275 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1275step0 raw1275; decide +kernel
      have hl : raw1275step0Labels = raw1275Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1275 raw1275Labels permutation8 permutation4
    mixedMoment B raw1275step0 raw1275step0Labels = mixedMoment B raw1275step1 raw1275step1Labels := by
      have ha : raw1275step1 = raw1275step0 := by apply Matrix.ext; unfold raw1275step1 raw1275step0; decide +kernel
      have hl : raw1275step0Labels = labelEmbedding7 ∘ raw1275step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1275step0 raw1275step0Labels raw1275step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4467 node4467Labels := by rfl

theorem canonical1276 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1276 raw1276Labels = mixedMoment B node1050 node1050Labels := by
  calc
    mixedMoment B raw1276 raw1276Labels = mixedMoment B raw1276step0 raw1276step0Labels := by
      have ha : raw1276step0 = (fun i j => raw1276 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1276step0 raw1276; decide +kernel
      have hl : raw1276step0Labels = raw1276Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1276 raw1276Labels permutation8 permutation4
    _ = mixedMoment B node1050 node1050Labels := by rfl

theorem canonical1277 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1277 raw1277Labels = mixedMoment B node1751 node1751Labels := by
  calc
    mixedMoment B raw1277 raw1277Labels = mixedMoment B raw1277step0 raw1277step0Labels := by
      have ha : raw1277step0 = (fun i j => raw1277 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1277step0 raw1277; decide +kernel
      have hl : raw1277step0Labels = raw1277Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1277 raw1277Labels permutation8 permutation6
    mixedMoment B raw1277step0 raw1277step0Labels = mixedMoment B raw1277step1 raw1277step1Labels := by
      have ha : raw1277step1 = -raw1277step0 := by apply Matrix.ext; change ∀ i j, raw1277step1 i j = -(raw1277step0 i j); unfold raw1277step1 raw1277step0; decide +kernel
      have hl : raw1277step1Labels = raw1277step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1277step1 raw1277step1Labels = mixedMoment B raw1277step2 raw1277step2Labels := by
      have ha : raw1277step2 = raw1277step1 := by apply Matrix.ext; unfold raw1277step2 raw1277step1; decide +kernel
      have hl : raw1277step1Labels = labelEmbedding1 ∘ raw1277step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1277step1 raw1277step1Labels raw1277step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1751 node1751Labels := by rfl

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

theorem singleton4175 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4175 node4175Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node603 node603Labels + mixedMoment B node1517 node1517Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw810 singletonSmall4175
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4175) = raw810Labels := by decide +kernel
  rw [hl, canonical810 B hB] at h
  have hc0 : mixedMoment B raw810 (Fin.cases (0 : Fin 2) singletonSmall4175) =
      mixedMoment B node603 node603Labels := by
    have ha : raw810 = raw811 := by apply Matrix.ext; unfold raw810 raw811; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4175 = raw811Labels := by decide +kernel
    rw [ha, hj, canonical811 B hB]
  have hc1 : mixedMoment B raw810 (Fin.cases (1 : Fin 2) singletonSmall4175) =
      mixedMoment B node1517 node1517Labels := by
    have ha : raw810 = raw812 := by apply Matrix.ext; unfold raw810 raw812; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4175 = raw812Labels := by decide +kernel
    rw [ha, hj, canonical812 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4182 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4182 node4182Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node610 node610Labels + mixedMoment B node1524 node1524Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw822 singletonSmall4182
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4182) = raw822Labels := by decide +kernel
  rw [hl, canonical822 B hB] at h
  have hc0 : mixedMoment B raw822 (Fin.cases (0 : Fin 2) singletonSmall4182) =
      mixedMoment B node610 node610Labels := by
    have ha : raw822 = raw823 := by apply Matrix.ext; unfold raw822 raw823; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4182 = raw823Labels := by decide +kernel
    rw [ha, hj, canonical823 B hB]
  have hc1 : mixedMoment B raw822 (Fin.cases (1 : Fin 2) singletonSmall4182) =
      mixedMoment B node1524 node1524Labels := by
    have ha : raw822 = raw824 := by apply Matrix.ext; unfold raw822 raw824; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4182 = raw824Labels := by decide +kernel
    rw [ha, hj, canonical824 B hB]
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

theorem singleton4344 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4344 node4344Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node922 node922Labels + mixedMoment B node1673 node1673Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1128 singletonSmall4344
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4344) = raw1128Labels := by decide +kernel
  rw [hl, canonical1128 B hB] at h
  have hc0 : mixedMoment B raw1128 (Fin.cases (0 : Fin 2) singletonSmall4344) =
      mixedMoment B node922 node922Labels := by
    have ha : raw1128 = raw1129 := by apply Matrix.ext; unfold raw1128 raw1129; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4344 = raw1129Labels := by decide +kernel
    rw [ha, hj, canonical1129 B hB]
  have hc1 : mixedMoment B raw1128 (Fin.cases (1 : Fin 2) singletonSmall4344) =
      mixedMoment B node1673 node1673Labels := by
    have ha : raw1128 = raw1130 := by apply Matrix.ext; unfold raw1128 raw1130; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4344 = raw1130Labels := by decide +kernel
    rw [ha, hj, canonical1130 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons69
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singleton4456 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4456 node4456Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1039 node1039Labels + mixedMoment B node1706 node1706Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1254 singletonSmall4456
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4456) = raw1254Labels := by decide +kernel
  rw [hl, canonical1254 B hB] at h
  have hc0 : mixedMoment B raw1254 (Fin.cases (0 : Fin 2) singletonSmall4456) =
      mixedMoment B node1039 node1039Labels := by
    have ha : raw1254 = raw1255 := by apply Matrix.ext; unfold raw1254 raw1255; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4456 = raw1255Labels := by decide +kernel
    rw [ha, hj, canonical1255 B hB]
  have hc1 : mixedMoment B raw1254 (Fin.cases (1 : Fin 2) singletonSmall4456) =
      mixedMoment B node1706 node1706Labels := by
    have ha : raw1254 = raw1256 := by apply Matrix.ext; unfold raw1254 raw1256; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4456 = raw1256Labels := by decide +kernel
    rw [ha, hj, canonical1256 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4458 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4458 node4458Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1041 node1041Labels + mixedMoment B node1724 node1724Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1260 singletonSmall4458
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4458) = raw1260Labels := by decide +kernel
  rw [hl, canonical1260 B hB] at h
  have hc0 : mixedMoment B raw1260 (Fin.cases (0 : Fin 2) singletonSmall4458) =
      mixedMoment B node1041 node1041Labels := by
    have ha : raw1260 = raw1261 := by apply Matrix.ext; unfold raw1260 raw1261; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4458 = raw1261Labels := by decide +kernel
    rw [ha, hj, canonical1261 B hB]
  have hc1 : mixedMoment B raw1260 (Fin.cases (1 : Fin 2) singletonSmall4458) =
      mixedMoment B node1724 node1724Labels := by
    have ha : raw1260 = raw1262 := by apply Matrix.ext; unfold raw1260 raw1262; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4458 = raw1262Labels := by decide +kernel
    rw [ha, hj, canonical1262 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

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

theorem singleton4463 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4463 node4463Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1046 node1046Labels + mixedMoment B node1750 node1750Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1269 singletonSmall4463
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4463) = raw1269Labels := by decide +kernel
  rw [hl, canonical1269 B hB] at h
  have hc0 : mixedMoment B raw1269 (Fin.cases (0 : Fin 2) singletonSmall4463) =
      mixedMoment B node1046 node1046Labels := by
    have ha : raw1269 = raw1270 := by apply Matrix.ext; unfold raw1269 raw1270; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4463 = raw1270Labels := by decide +kernel
    rw [ha, hj, canonical1270 B hB]
  have hc1 : mixedMoment B raw1269 (Fin.cases (1 : Fin 2) singletonSmall4463) =
      mixedMoment B node1750 node1750Labels := by
    have ha : raw1269 = raw1271 := by apply Matrix.ext; unfold raw1269 raw1271; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4463 = raw1271Labels := by decide +kernel
    rw [ha, hj, canonical1271 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4467 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4467 node4467Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1050 node1050Labels + mixedMoment B node1751 node1751Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1275 singletonSmall4467
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4467) = raw1275Labels := by decide +kernel
  rw [hl, canonical1275 B hB] at h
  have hc0 : mixedMoment B raw1275 (Fin.cases (0 : Fin 2) singletonSmall4467) =
      mixedMoment B node1050 node1050Labels := by
    have ha : raw1275 = raw1276 := by apply Matrix.ext; unfold raw1275 raw1276; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4467 = raw1276Labels := by decide +kernel
    rw [ha, hj, canonical1276 B hB]
  have hc1 : mixedMoment B raw1275 (Fin.cases (1 : Fin 2) singletonSmall4467) =
      mixedMoment B node1751 node1751Labels := by
    have ha : raw1275 = raw1277 := by apply Matrix.ext; unfold raw1275 raw1277; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4467 = raw1277Labels := by decide +kernel
    rw [ha, hj, canonical1277 B hB]
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

theorem singleton4805 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4805 node4805Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2023 node2023Labels + mixedMoment B node2214 node2214Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1740 singletonSmall4805
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4805) = raw1740Labels := by decide +kernel
  rw [hl, canonical1740 B hB] at h
  have hc0 : mixedMoment B raw1740 (Fin.cases (0 : Fin 2) singletonSmall4805) =
      mixedMoment B node2023 node2023Labels := by
    have ha : raw1740 = raw1741 := by apply Matrix.ext; unfold raw1740 raw1741; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4805 = raw1741Labels := by decide +kernel
    rw [ha, hj, canonical1741 B hB]
  have hc1 : mixedMoment B raw1740 (Fin.cases (1 : Fin 2) singletonSmall4805) =
      mixedMoment B node2214 node2214Labels := by
    have ha : raw1740 = raw1742 := by apply Matrix.ext; unfold raw1740 raw1742; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4805 = raw1742Labels := by decide +kernel
    rw [ha, hj, canonical1742 B hB]
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

theorem singleton4866 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4866 node4866Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2107 node2107Labels + mixedMoment B node2260 node2260Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1794 singletonSmall4866
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4866) = raw1794Labels := by decide +kernel
  rw [hl, canonical1794 B hB] at h
  have hc0 : mixedMoment B raw1794 (Fin.cases (0 : Fin 2) singletonSmall4866) =
      mixedMoment B node2107 node2107Labels := by
    have ha : raw1794 = raw1795 := by apply Matrix.ext; unfold raw1794 raw1795; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4866 = raw1795Labels := by decide +kernel
    rw [ha, hj, canonical1795 B hB]
  have hc1 : mixedMoment B raw1794 (Fin.cases (1 : Fin 2) singletonSmall4866) =
      mixedMoment B node2260 node2260Labels := by
    have ha : raw1794 = raw1796 := by apply Matrix.ext; unfold raw1794 raw1796; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4866 = raw1796Labels := by decide +kernel
    rw [ha, hj, canonical1796 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4869 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4869 node4869Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2110 node2110Labels + mixedMoment B node2275 node2275Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1800 singletonSmall4869
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4869) = raw1800Labels := by decide +kernel
  rw [hl, canonical1800 B hB] at h
  have hc0 : mixedMoment B raw1800 (Fin.cases (0 : Fin 2) singletonSmall4869) =
      mixedMoment B node2110 node2110Labels := by
    have ha : raw1800 = raw1801 := by apply Matrix.ext; unfold raw1800 raw1801; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4869 = raw1801Labels := by decide +kernel
    rw [ha, hj, canonical1801 B hB]
  have hc1 : mixedMoment B raw1800 (Fin.cases (1 : Fin 2) singletonSmall4869) =
      mixedMoment B node2275 node2275Labels := by
    have ha : raw1800 = raw1802 := by apply Matrix.ext; unfold raw1800 raw1802; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4869 = raw1802Labels := by decide +kernel
    rw [ha, hj, canonical1802 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound14
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound922 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node922 node922Labels = Sparse.eval nodeValue922 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 922) = mixedMoment B node922 node922Labels := rfl
  simpa [nodeValue922, Sparse.eval] using hc.symm

theorem sound929 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node929 node929Labels = Sparse.eval nodeValue929 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 929) = mixedMoment B node929 node929Labels := rfl
  simpa [nodeValue929, Sparse.eval] using hc.symm

theorem sound944 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node944 node944Labels = Sparse.eval nodeValue944 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 944) = mixedMoment B node944 node944Labels := rfl
  simpa [nodeValue944, Sparse.eval] using hc.symm

theorem sound949 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node949 node949Labels = Sparse.eval nodeValue949 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 949) = mixedMoment B node949 node949Labels := rfl
  simpa [nodeValue949, Sparse.eval] using hc.symm

theorem sound950 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node950 node950Labels = Sparse.eval nodeValue950 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 950) = mixedMoment B node950 node950Labels := rfl
  simpa [nodeValue950, Sparse.eval] using hc.symm

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

theorem sound987 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node987 node987Labels = Sparse.eval nodeValue987 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 987) = mixedMoment B node987 node987Labels := rfl
  simpa [nodeValue987, Sparse.eval] using hc.symm

theorem sound988 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node988 node988Labels = Sparse.eval nodeValue988 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 988) = mixedMoment B node988 node988Labels := rfl
  simpa [nodeValue988, Sparse.eval] using hc.symm

theorem sound1017 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1017 node1017Labels = Sparse.eval nodeValue1017 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1017) = mixedMoment B node1017 node1017Labels := rfl
  simpa [nodeValue1017, Sparse.eval] using hc.symm

theorem sound1018 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1018 node1018Labels = Sparse.eval nodeValue1018 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1018) = mixedMoment B node1018 node1018Labels := rfl
  simpa [nodeValue1018, Sparse.eval] using hc.symm

theorem sound1023 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1023 node1023Labels = Sparse.eval nodeValue1023 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1023) = mixedMoment B node1023 node1023Labels := rfl
  simpa [nodeValue1023, Sparse.eval] using hc.symm

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

theorem zero1081 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1081 node1081Labels = 0 := by
  exact mixedMoment_order_one B hB node1081 node1081Labels 1
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

theorem sound1032 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1032 node1032Labels = Sparse.eval nodeValue1032 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1032) = mixedMoment B node1032 node1032Labels := rfl
  simpa [nodeValue1032, Sparse.eval] using hc.symm

theorem sound1034 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1034 node1034Labels = Sparse.eval nodeValue1034 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1034) = mixedMoment B node1034 node1034Labels := rfl
  simpa [nodeValue1034, Sparse.eval] using hc.symm

theorem sound1035 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1035 node1035Labels = Sparse.eval nodeValue1035 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1035) = mixedMoment B node1035 node1035Labels := rfl
  simpa [nodeValue1035, Sparse.eval] using hc.symm

theorem sound1036 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1036 node1036Labels = Sparse.eval nodeValue1036 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1036) = mixedMoment B node1036 node1036Labels := rfl
  simpa [nodeValue1036, Sparse.eval] using hc.symm

theorem sound1039 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1039 node1039Labels = Sparse.eval nodeValue1039 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1039) = mixedMoment B node1039 node1039Labels := rfl
  simpa [nodeValue1039, Sparse.eval] using hc.symm

theorem sound1041 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1041 node1041Labels = Sparse.eval nodeValue1041 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1041) = mixedMoment B node1041 node1041Labels := rfl
  simpa [nodeValue1041, Sparse.eval] using hc.symm

theorem sound1044 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1044 node1044Labels = Sparse.eval nodeValue1044 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1044) = mixedMoment B node1044 node1044Labels := rfl
  simpa [nodeValue1044, Sparse.eval] using hc.symm

theorem sound1045 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1045 node1045Labels = Sparse.eval nodeValue1045 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1045) = mixedMoment B node1045 node1045Labels := rfl
  simpa [nodeValue1045, Sparse.eval] using hc.symm

theorem sound1046 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1046 node1046Labels = Sparse.eval nodeValue1046 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1046) = mixedMoment B node1046 node1046Labels := rfl
  simpa [nodeValue1046, Sparse.eval] using hc.symm

theorem sound1050 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1050 node1050Labels = Sparse.eval nodeValue1050 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1050) = mixedMoment B node1050 node1050Labels := rfl
  simpa [nodeValue1050, Sparse.eval] using hc.symm

theorem sound1073 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1073 node1073Labels = Sparse.eval nodeValue1073 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1073) = mixedMoment B node1073 node1073Labels := rfl
  simpa [nodeValue1073, Sparse.eval] using hc.symm

theorem sound1081 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1081 node1081Labels = Sparse.eval nodeValue1081 (mixedVector B) := by
  simpa only [nodeValue1081, Sparse.eval_nil] using zero1081 B _hB _hF

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

theorem sound1510 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1510 node1510Labels = Sparse.eval nodeValue1510 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1510) = mixedMoment B node1510 node1510Labels := rfl
  simpa [nodeValue1510, Sparse.eval] using hc.symm

theorem sound1517 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1517 node1517Labels = Sparse.eval nodeValue1517 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1517) = mixedMoment B node1517 node1517Labels := rfl
  simpa [nodeValue1517, Sparse.eval] using hc.symm

theorem sound1522 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1522 node1522Labels = Sparse.eval nodeValue1522 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1522) = mixedMoment B node1522 node1522Labels := rfl
  simpa [nodeValue1522, Sparse.eval] using hc.symm

theorem sound1524 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1524 node1524Labels = Sparse.eval nodeValue1524 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1524) = mixedMoment B node1524 node1524Labels := rfl
  simpa [nodeValue1524, Sparse.eval] using hc.symm

theorem sound1528 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1528 node1528Labels = Sparse.eval nodeValue1528 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1528) = mixedMoment B node1528 node1528Labels := rfl
  simpa [nodeValue1528, Sparse.eval] using hc.symm

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

theorem zero1726 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1726 node1726Labels = 0 := by
  exact mixedMoment_order_one B hB node1726 node1726Labels 1
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

theorem sound1673 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1673 node1673Labels = Sparse.eval nodeValue1673 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1673) = mixedMoment B node1673 node1673Labels := rfl
  simpa [nodeValue1673, Sparse.eval] using hc.symm

theorem sound1678 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1678 node1678Labels = Sparse.eval nodeValue1678 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1678) = mixedMoment B node1678 node1678Labels := rfl
  simpa [nodeValue1678, Sparse.eval] using hc.symm

theorem sound1680 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1680 node1680Labels = Sparse.eval nodeValue1680 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1680) = mixedMoment B node1680 node1680Labels := rfl
  simpa [nodeValue1680, Sparse.eval] using hc.symm

theorem sound1684 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1684 node1684Labels = Sparse.eval nodeValue1684 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1684) = mixedMoment B node1684 node1684Labels := rfl
  simpa [nodeValue1684, Sparse.eval] using hc.symm

theorem sound1706 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1706 node1706Labels = Sparse.eval nodeValue1706 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1706) = mixedMoment B node1706 node1706Labels := rfl
  simpa [nodeValue1706, Sparse.eval] using hc.symm

theorem sound1711 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1711 node1711Labels = Sparse.eval nodeValue1711 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1711) = mixedMoment B node1711 node1711Labels := rfl
  simpa [nodeValue1711, Sparse.eval] using hc.symm

theorem sound1713 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1713 node1713Labels = Sparse.eval nodeValue1713 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1713) = mixedMoment B node1713 node1713Labels := rfl
  simpa [nodeValue1713, Sparse.eval] using hc.symm

theorem sound1724 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1724 node1724Labels = Sparse.eval nodeValue1724 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1724) = mixedMoment B node1724 node1724Labels := rfl
  simpa [nodeValue1724, Sparse.eval] using hc.symm

theorem sound1726 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1726 node1726Labels = Sparse.eval nodeValue1726 (mixedVector B) := by
  simpa only [nodeValue1726, Sparse.eval_nil] using zero1726 B _hB _hF

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

theorem sound1734 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1734 node1734Labels = Sparse.eval nodeValue1734 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1734) = mixedMoment B node1734 node1734Labels := rfl
  simpa [nodeValue1734, Sparse.eval] using hc.symm

theorem sound1736 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1736 node1736Labels = Sparse.eval nodeValue1736 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1736) = mixedMoment B node1736 node1736Labels := rfl
  simpa [nodeValue1736, Sparse.eval] using hc.symm

theorem sound1737 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1737 node1737Labels = Sparse.eval nodeValue1737 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1737) = mixedMoment B node1737 node1737Labels := rfl
  simpa [nodeValue1737, Sparse.eval] using hc.symm

theorem sound1742 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1742 node1742Labels = Sparse.eval nodeValue1742 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1742) = mixedMoment B node1742 node1742Labels := rfl
  simpa [nodeValue1742, Sparse.eval] using hc.symm

theorem sound1744 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1744 node1744Labels = Sparse.eval nodeValue1744 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1744) = mixedMoment B node1744 node1744Labels := rfl
  simpa [nodeValue1744, Sparse.eval] using hc.symm

theorem sound1750 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1750 node1750Labels = Sparse.eval nodeValue1750 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1750) = mixedMoment B node1750 node1750Labels := rfl
  simpa [nodeValue1750, Sparse.eval] using hc.symm

theorem sound1751 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1751 node1751Labels = Sparse.eval nodeValue1751 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1751) = mixedMoment B node1751 node1751Labels := rfl
  simpa [nodeValue1751, Sparse.eval] using hc.symm

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

theorem sound1921 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1921 node1921Labels = Sparse.eval nodeValue1921 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1921) = mixedMoment B node1921 node1921Labels := rfl
  simpa [nodeValue1921, Sparse.eval] using hc.symm

theorem sound1922 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1922 node1922Labels = Sparse.eval nodeValue1922 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1922) = mixedMoment B node1922 node1922Labels := rfl
  simpa [nodeValue1922, Sparse.eval] using hc.symm

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

theorem sound2017 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2017 node2017Labels = Sparse.eval nodeValue2017 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2017) = mixedMoment B node2017 node2017Labels := rfl
  simpa [nodeValue2017, Sparse.eval] using hc.symm

theorem sound2020 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2020 node2020Labels = Sparse.eval nodeValue2020 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2020) = mixedMoment B node2020 node2020Labels := rfl
  simpa [nodeValue2020, Sparse.eval] using hc.symm

theorem sound2023 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2023 node2023Labels = Sparse.eval nodeValue2023 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2023) = mixedMoment B node2023 node2023Labels := rfl
  simpa [nodeValue2023, Sparse.eval] using hc.symm

theorem sound2024 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2024 node2024Labels = Sparse.eval nodeValue2024 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2024) = mixedMoment B node2024 node2024Labels := rfl
  simpa [nodeValue2024, Sparse.eval] using hc.symm

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

theorem sound2085 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2085 node2085Labels = Sparse.eval nodeValue2085 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2085) = mixedMoment B node2085 node2085Labels := rfl
  simpa [nodeValue2085, Sparse.eval] using hc.symm

theorem sound2086 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2086 node2086Labels = Sparse.eval nodeValue2086 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2086) = mixedMoment B node2086 node2086Labels := rfl
  simpa [nodeValue2086, Sparse.eval] using hc.symm

theorem sound2091 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2091 node2091Labels = Sparse.eval nodeValue2091 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2091) = mixedMoment B node2091 node2091Labels := rfl
  simpa [nodeValue2091, Sparse.eval] using hc.symm

theorem sound2102 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2102 node2102Labels = Sparse.eval nodeValue2102 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2102) = mixedMoment B node2102 node2102Labels := rfl
  simpa [nodeValue2102, Sparse.eval] using hc.symm

theorem sound2107 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2107 node2107Labels = Sparse.eval nodeValue2107 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2107) = mixedMoment B node2107 node2107Labels := rfl
  simpa [nodeValue2107, Sparse.eval] using hc.symm

theorem sound2110 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2110 node2110Labels = Sparse.eval nodeValue2110 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2110) = mixedMoment B node2110 node2110Labels := rfl
  simpa [nodeValue2110, Sparse.eval] using hc.symm

theorem sound2111 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2111 node2111Labels = Sparse.eval nodeValue2111 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2111) = mixedMoment B node2111 node2111Labels := rfl
  simpa [nodeValue2111, Sparse.eval] using hc.symm

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

theorem sound2117 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2117 node2117Labels = Sparse.eval nodeValue2117 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2117) = mixedMoment B node2117 node2117Labels := rfl
  simpa [nodeValue2117, Sparse.eval] using hc.symm

theorem sound2118 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2118 node2118Labels = Sparse.eval nodeValue2118 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2118) = mixedMoment B node2118 node2118Labels := rfl
  simpa [nodeValue2118, Sparse.eval] using hc.symm

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

theorem sound2190 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2190 node2190Labels = Sparse.eval nodeValue2190 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2190) = mixedMoment B node2190 node2190Labels := rfl
  simpa [nodeValue2190, Sparse.eval] using hc.symm

theorem sound2191 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2191 node2191Labels = Sparse.eval nodeValue2191 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2191) = mixedMoment B node2191 node2191Labels := rfl
  simpa [nodeValue2191, Sparse.eval] using hc.symm

theorem sound2195 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2195 node2195Labels = Sparse.eval nodeValue2195 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2195) = mixedMoment B node2195 node2195Labels := rfl
  simpa [nodeValue2195, Sparse.eval] using hc.symm

theorem sound2202 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2202 node2202Labels = Sparse.eval nodeValue2202 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2202) = mixedMoment B node2202 node2202Labels := rfl
  simpa [nodeValue2202, Sparse.eval] using hc.symm

theorem sound2206 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2206 node2206Labels = Sparse.eval nodeValue2206 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2206) = mixedMoment B node2206 node2206Labels := rfl
  simpa [nodeValue2206, Sparse.eval] using hc.symm

theorem sound2213 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2213 node2213Labels = Sparse.eval nodeValue2213 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2213) = mixedMoment B node2213 node2213Labels := rfl
  simpa [nodeValue2213, Sparse.eval] using hc.symm

theorem sound2214 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2214 node2214Labels = Sparse.eval nodeValue2214 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2214) = mixedMoment B node2214 node2214Labels := rfl
  simpa [nodeValue2214, Sparse.eval] using hc.symm

theorem sound2215 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2215 node2215Labels = Sparse.eval nodeValue2215 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2215) = mixedMoment B node2215 node2215Labels := rfl
  simpa [nodeValue2215, Sparse.eval] using hc.symm

theorem sound2216 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2216 node2216Labels = Sparse.eval nodeValue2216 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2216) = mixedMoment B node2216 node2216Labels := rfl
  simpa [nodeValue2216, Sparse.eval] using hc.symm

theorem sound2232 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2232 node2232Labels = Sparse.eval nodeValue2232 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2232) = mixedMoment B node2232 node2232Labels := rfl
  simpa [nodeValue2232, Sparse.eval] using hc.symm

theorem sound2234 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2234 node2234Labels = Sparse.eval nodeValue2234 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2234) = mixedMoment B node2234 node2234Labels := rfl
  simpa [nodeValue2234, Sparse.eval] using hc.symm

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

theorem zero2263 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2263 node2263Labels = 0 := by
  exact mixedMoment_order_one B hB node2263 node2263Labels 1
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

theorem sound2240 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2240 node2240Labels = Sparse.eval nodeValue2240 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2240) = mixedMoment B node2240 node2240Labels := rfl
  simpa [nodeValue2240, Sparse.eval] using hc.symm

theorem sound2241 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2241 node2241Labels = Sparse.eval nodeValue2241 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2241) = mixedMoment B node2241 node2241Labels := rfl
  simpa [nodeValue2241, Sparse.eval] using hc.symm

theorem sound2242 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2242 node2242Labels = Sparse.eval nodeValue2242 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2242) = mixedMoment B node2242 node2242Labels := rfl
  simpa [nodeValue2242, Sparse.eval] using hc.symm

theorem sound2244 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2244 node2244Labels = Sparse.eval nodeValue2244 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2244) = mixedMoment B node2244 node2244Labels := rfl
  simpa [nodeValue2244, Sparse.eval] using hc.symm

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

theorem sound2251 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2251 node2251Labels = Sparse.eval nodeValue2251 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2251) = mixedMoment B node2251 node2251Labels := rfl
  simpa [nodeValue2251, Sparse.eval] using hc.symm

theorem sound2254 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2254 node2254Labels = Sparse.eval nodeValue2254 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2254) = mixedMoment B node2254 node2254Labels := rfl
  simpa [nodeValue2254, Sparse.eval] using hc.symm

theorem sound2260 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2260 node2260Labels = Sparse.eval nodeValue2260 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2260) = mixedMoment B node2260 node2260Labels := rfl
  simpa [nodeValue2260, Sparse.eval] using hc.symm

theorem sound2262 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2262 node2262Labels = Sparse.eval nodeValue2262 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2262) = mixedMoment B node2262 node2262Labels := rfl
  simpa [nodeValue2262, Sparse.eval] using hc.symm

theorem sound2263 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2263 node2263Labels = Sparse.eval nodeValue2263 (mixedVector B) := by
  simpa only [nodeValue2263, Sparse.eval_nil] using zero2263 B _hB _hF

theorem sound2275 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2275 node2275Labels = Sparse.eval nodeValue2275 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2275) = mixedMoment B node2275 node2275Labels := rfl
  simpa [nodeValue2275, Sparse.eval] using hc.symm

theorem sound2277 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2277 node2277Labels = Sparse.eval nodeValue2277 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2277) = mixedMoment B node2277 node2277Labels := rfl
  simpa [nodeValue2277, Sparse.eval] using hc.symm

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

theorem sound4079 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4079 node4079Labels = Sparse.eval nodeValue4079 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4079) = mixedMoment B node4079 node4079Labels := rfl
  simpa [nodeValue4079, Sparse.eval] using hc.symm

theorem sound4080 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4080 node4080Labels = Sparse.eval nodeValue4080 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4080) = mixedMoment B node4080 node4080Labels := rfl
  simpa [nodeValue4080, Sparse.eval] using hc.symm

theorem sound4082 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4082 node4082Labels = Sparse.eval nodeValue4082 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4082) = mixedMoment B node4082 node4082Labels := rfl
  simpa [nodeValue4082, Sparse.eval] using hc.symm

theorem sound4083 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4083 node4083Labels = Sparse.eval nodeValue4083 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4083) = mixedMoment B node4083 node4083Labels := rfl
  simpa [nodeValue4083, Sparse.eval] using hc.symm

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

theorem sound603 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node603 node603Labels = Sparse.eval nodeValue603 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 603) = mixedMoment B node603 node603Labels := rfl
  simpa [nodeValue603, Sparse.eval] using hc.symm

theorem sound610 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node610 node610Labels = Sparse.eval nodeValue610 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 610) = mixedMoment B node610 node610Labels := rfl
  simpa [nodeValue610, Sparse.eval] using hc.symm

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

theorem sound4150 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4150 node4150Labels = Sparse.eval nodeValue4150 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4150) = mixedMoment B node4150 node4150Labels := rfl
  simpa [nodeValue4150, Sparse.eval] using hc.symm

theorem sound4152 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4152 node4152Labels = Sparse.eval nodeValue4152 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4152) = mixedMoment B node4152 node4152Labels := rfl
  simpa [nodeValue4152, Sparse.eval] using hc.symm

theorem sound4153 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4153 node4153Labels = Sparse.eval nodeValue4153 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4153) = mixedMoment B node4153 node4153Labels := rfl
  simpa [nodeValue4153, Sparse.eval] using hc.symm

theorem sound4155 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4155 node4155Labels = Sparse.eval nodeValue4155 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4155) = mixedMoment B node4155 node4155Labels := rfl
  simpa [nodeValue4155, Sparse.eval] using hc.symm

theorem sound4157 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4157 node4157Labels = Sparse.eval nodeValue4157 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4157) = mixedMoment B node4157 node4157Labels := rfl
  simpa [nodeValue4157, Sparse.eval] using hc.symm

theorem sound4158 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4158 node4158Labels = Sparse.eval nodeValue4158 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4158) = mixedMoment B node4158 node4158Labels := rfl
  simpa [nodeValue4158, Sparse.eval] using hc.symm

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

theorem sound4175 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4175 node4175Labels = Sparse.eval nodeValue4175 (mixedVector B) := by
  have h := singleton4175 B _hB
  rw [sound603 B _hB _hF, sound1517 B _hB _hF] at h
  norm_num [nodeValue4175, nodeValue603, nodeValue1517, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4182 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4182 node4182Labels = Sparse.eval nodeValue4182 (mixedVector B) := by
  have h := singleton4182 B _hB
  rw [sound610 B _hB _hF, sound1524 B _hB _hF] at h
  norm_num [nodeValue4182, nodeValue610, nodeValue1524, Sparse.eval] at h ⊢
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

theorem zero4329 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node4329 node4329Labels = 0 := by
  exact mixedMoment_alpha B hF node4329 node4329Labels 1 permutation152
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

theorem sound4327 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4327 node4327Labels = Sparse.eval nodeValue4327 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4327) = mixedMoment B node4327 node4327Labels := rfl
  simpa [nodeValue4327, Sparse.eval] using hc.symm

theorem sound4329 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4329 node4329Labels = Sparse.eval nodeValue4329 (mixedVector B) := by
  simpa only [nodeValue4329, Sparse.eval_nil] using zero4329 B _hB _hF

theorem sound4331 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4331 node4331Labels = Sparse.eval nodeValue4331 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4331) = mixedMoment B node4331 node4331Labels := rfl
  simpa [nodeValue4331, Sparse.eval] using hc.symm

theorem sound4332 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4332 node4332Labels = Sparse.eval nodeValue4332 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4332) = mixedMoment B node4332 node4332Labels := rfl
  simpa [nodeValue4332, Sparse.eval] using hc.symm

theorem sound4344 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4344 node4344Labels = Sparse.eval nodeValue4344 (mixedVector B) := by
  have h := singleton4344 B _hB
  rw [sound922 B _hB _hF, sound1673 B _hB _hF] at h
  norm_num [nodeValue4344, nodeValue922, nodeValue1673, Sparse.eval] at h ⊢
  linarith only [h]

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

theorem sound4364 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4364 node4364Labels = Sparse.eval nodeValue4364 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4364) = mixedMoment B node4364 node4364Labels := rfl
  simpa [nodeValue4364, Sparse.eval] using hc.symm

theorem sound4366 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4366 node4366Labels = Sparse.eval nodeValue4366 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4366) = mixedMoment B node4366 node4366Labels := rfl
  simpa [nodeValue4366, Sparse.eval] using hc.symm

theorem sound4367 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4367 node4367Labels = Sparse.eval nodeValue4367 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4367) = mixedMoment B node4367 node4367Labels := rfl
  simpa [nodeValue4367, Sparse.eval] using hc.symm

theorem sound4369 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4369 node4369Labels = Sparse.eval nodeValue4369 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4369) = mixedMoment B node4369 node4369Labels := rfl
  simpa [nodeValue4369, Sparse.eval] using hc.symm

theorem sound4371 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4371 node4371Labels = Sparse.eval nodeValue4371 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4371) = mixedMoment B node4371 node4371Labels := rfl
  simpa [nodeValue4371, Sparse.eval] using hc.symm

theorem sound4372 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4372 node4372Labels = Sparse.eval nodeValue4372 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4372) = mixedMoment B node4372 node4372Labels := rfl
  simpa [nodeValue4372, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros69
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero4438 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node4438 node4438Labels = 0 := by
  exact mixedMoment_alpha B hF node4438 node4438Labels 1 permutation152
    (by decide +kernel)

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

theorem sound4438 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4438 node4438Labels = Sparse.eval nodeValue4438 (mixedVector B) := by
  simpa only [nodeValue4438, Sparse.eval_nil] using zero4438 B _hB _hF

theorem sound4439 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4439 node4439Labels = Sparse.eval nodeValue4439 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4439) = mixedMoment B node4439 node4439Labels := rfl
  simpa [nodeValue4439, Sparse.eval] using hc.symm

theorem sound4440 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4440 node4440Labels = Sparse.eval nodeValue4440 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4440) = mixedMoment B node4440 node4440Labels := rfl
  simpa [nodeValue4440, Sparse.eval] using hc.symm

theorem sound4442 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4442 node4442Labels = Sparse.eval nodeValue4442 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4442) = mixedMoment B node4442 node4442Labels := rfl
  simpa [nodeValue4442, Sparse.eval] using hc.symm

theorem sound4444 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4444 node4444Labels = Sparse.eval nodeValue4444 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4444) = mixedMoment B node4444 node4444Labels := rfl
  simpa [nodeValue4444, Sparse.eval] using hc.symm

theorem sound4456 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4456 node4456Labels = Sparse.eval nodeValue4456 (mixedVector B) := by
  have h := singleton4456 B _hB
  rw [sound1039 B _hB _hF, sound1706 B _hB _hF] at h
  norm_num [nodeValue4456, nodeValue1039, nodeValue1706, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4458 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4458 node4458Labels = Sparse.eval nodeValue4458 (mixedVector B) := by
  have h := singleton4458 B _hB
  rw [sound1041 B _hB _hF, sound1724 B _hB _hF] at h
  norm_num [nodeValue4458, nodeValue1041, nodeValue1724, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4461 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4461 node4461Labels = Sparse.eval nodeValue4461 (mixedVector B) := by
  have h := singleton4461 B _hB
  rw [sound1044 B _hB _hF, sound1737 B _hB _hF] at h
  norm_num [nodeValue4461, nodeValue1044, nodeValue1737, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4463 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4463 node4463Labels = Sparse.eval nodeValue4463 (mixedVector B) := by
  have h := singleton4463 B _hB
  rw [sound1046 B _hB _hF, sound1750 B _hB _hF] at h
  norm_num [nodeValue4463, nodeValue1046, nodeValue1750, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4467 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4467 node4467Labels = Sparse.eval nodeValue4467 (mixedVector B) := by
  have h := singleton4467 B _hB
  rw [sound1050 B _hB _hF, sound1751 B _hB _hF] at h
  norm_num [nodeValue4467, nodeValue1050, nodeValue1751, Sparse.eval] at h ⊢
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

theorem zero4497 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4497 node4497Labels = 0 := by
  exact mixedMoment_order_one B hB node4497 node4497Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero4502 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4502 node4502Labels = 0 := by
  exact mixedMoment_order_one B hB node4502 node4502Labels 1
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

theorem sound4497 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4497 node4497Labels = Sparse.eval nodeValue4497 (mixedVector B) := by
  simpa only [nodeValue4497, Sparse.eval_nil] using zero4497 B _hB _hF

theorem sound4502 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4502 node4502Labels = Sparse.eval nodeValue4502 (mixedVector B) := by
  simpa only [nodeValue4502, Sparse.eval_nil] using zero4502 B _hB _hF

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

theorem sound4805 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4805 node4805Labels = Sparse.eval nodeValue4805 (mixedVector B) := by
  have h := singleton4805 B _hB
  rw [sound2023 B _hB _hF, sound2214 B _hB _hF] at h
  norm_num [nodeValue4805, nodeValue2023, nodeValue2214, Sparse.eval] at h ⊢
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

theorem zero4893 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4893 node4893Labels = 0 := by
  exact mixedMoment_order_one B hB node4893 node4893Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero4895 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4895 node4895Labels = 0 := by
  exact mixedMoment_order_one B hB node4895 node4895Labels 1
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

theorem sound4866 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4866 node4866Labels = Sparse.eval nodeValue4866 (mixedVector B) := by
  have h := singleton4866 B _hB
  rw [sound2107 B _hB _hF, sound2260 B _hB _hF] at h
  norm_num [nodeValue4866, nodeValue2107, nodeValue2260, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4869 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4869 node4869Labels = Sparse.eval nodeValue4869 (mixedVector B) := by
  have h := singleton4869 B _hB
  rw [sound2110 B _hB _hF, sound2275 B _hB _hF] at h
  norm_num [nodeValue4869, nodeValue2110, nodeValue2275, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4888 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4888 node4888Labels = Sparse.eval nodeValue4888 (mixedVector B) := by
  have h := singleton4888 B _hB
  rw [sound2244 B _hB _hF, sound2262 B _hB _hF] at h
  norm_num [nodeValue4888, nodeValue2244, nodeValue2262, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4889 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4889 node4889Labels = Sparse.eval nodeValue4889 (mixedVector B) := by
  have h := singleton4889 B _hB
  rw [sound2245 B _hB _hF, sound2277 B _hB _hF] at h
  norm_num [nodeValue4889, nodeValue2245, nodeValue2277, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4893 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4893 node4893Labels = Sparse.eval nodeValue4893 (mixedVector B) := by
  simpa only [nodeValue4893, Sparse.eval_nil] using zero4893 B _hB _hF

theorem sound4895 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4895 node4895Labels = Sparse.eval nodeValue4895 (mixedVector B) := by
  simpa only [nodeValue4895, Sparse.eval_nil] using zero4895 B _hB _hF

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources53
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sourceEq1707 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1707 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1707 + difference 0 0) (sourceB1707 + difference 0 0) sourceC1707) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 988) := by
    have ha : (tripleCharges (sourceA1707 + difference 0 0) (sourceB1707 + difference 0 0) sourceC1707) = raw24949 := by
      apply Matrix.ext; unfold tripleCharges sourceA1707 sourceB1707 sourceC1707 difference raw24949; decide +kernel
    rw [ha]
    exact (canonical24949 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1707 + difference 0 1) (sourceB1707 + difference 1 0) sourceC1707) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2118) := by
    have ha : (tripleCharges (sourceA1707 + difference 0 1) (sourceB1707 + difference 1 0) sourceC1707) = raw24950 := by
      apply Matrix.ext; unfold tripleCharges sourceA1707 sourceB1707 sourceC1707 difference raw24950; decide +kernel
    rw [ha]
    exact (canonical24950 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1707 + difference 0 2) (sourceB1707 + difference 2 0) sourceC1707) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1922) := by
    have ha : (tripleCharges (sourceA1707 + difference 0 2) (sourceB1707 + difference 2 0) sourceC1707) = raw24951 := by
      apply Matrix.ext; unfold tripleCharges sourceA1707 sourceB1707 sourceC1707 difference raw24951; decide +kernel
    rw [ha]
    exact (canonical24951 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1707 + difference 0 3) (sourceB1707 + difference 3 0) sourceC1707) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2195) := by
    have ha : (tripleCharges (sourceA1707 + difference 0 3) (sourceB1707 + difference 3 0) sourceC1707) = raw24952 := by
      apply Matrix.ext; unfold tripleCharges sourceA1707 sourceB1707 sourceC1707 difference raw24952; decide +kernel
    rw [ha]
    exact (canonical24952 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1707 + difference 0 4) (sourceB1707 + difference 4 0) sourceC1707) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2216) := by
    have ha : (tripleCharges (sourceA1707 + difference 0 4) (sourceB1707 + difference 4 0) sourceC1707) = raw24953 := by
      apply Matrix.ext; unfold tripleCharges sourceA1707 sourceB1707 sourceC1707 difference raw24953; decide +kernel
    rw [ha]
    exact (canonical24953 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1707 + difference 0 5) (sourceB1707 + difference 5 0) sourceC1707) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2214) := by
    have ha : (tripleCharges (sourceA1707 + difference 0 5) (sourceB1707 + difference 5 0) sourceC1707) = raw24954 := by
      apply Matrix.ext; unfold tripleCharges sourceA1707 sourceB1707 sourceC1707 difference raw24954; decide +kernel
    rw [ha]
    exact (canonical24954 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1707 + sourceB1707) sourceC1707) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4080) := by
    have ha : (doubleCharges (sourceA1707 + sourceB1707) sourceC1707) = raw24955 := by
      apply Matrix.ext; unfold doubleCharges sourceA1707 sourceB1707 sourceC1707 raw24955; decide +kernel
    rw [ha]
    exact (canonical24955 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1707 sourceB1707 sourceC1707
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1707, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1708 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1708 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1708 + difference 0 0) (sourceB1708 + difference 0 0) sourceC1708) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 987) := by
    have ha : (tripleCharges (sourceA1708 + difference 0 0) (sourceB1708 + difference 0 0) sourceC1708) = raw24956 := by
      apply Matrix.ext; unfold tripleCharges sourceA1708 sourceB1708 sourceC1708 difference raw24956; decide +kernel
    rw [ha]
    exact (canonical24956 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1708 + difference 0 1) (sourceB1708 + difference 1 0) sourceC1708) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2117) := by
    have ha : (tripleCharges (sourceA1708 + difference 0 1) (sourceB1708 + difference 1 0) sourceC1708) = raw24957 := by
      apply Matrix.ext; unfold tripleCharges sourceA1708 sourceB1708 sourceC1708 difference raw24957; decide +kernel
    rw [ha]
    exact (canonical24957 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1708 + difference 0 2) (sourceB1708 + difference 2 0) sourceC1708) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1921) := by
    have ha : (tripleCharges (sourceA1708 + difference 0 2) (sourceB1708 + difference 2 0) sourceC1708) = raw24958 := by
      apply Matrix.ext; unfold tripleCharges sourceA1708 sourceB1708 sourceC1708 difference raw24958; decide +kernel
    rw [ha]
    exact (canonical24958 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1708 + difference 0 3) (sourceB1708 + difference 3 0) sourceC1708) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2215) := by
    have ha : (tripleCharges (sourceA1708 + difference 0 3) (sourceB1708 + difference 3 0) sourceC1708) = raw24959 := by
      apply Matrix.ext; unfold tripleCharges sourceA1708 sourceB1708 sourceC1708 difference raw24959; decide +kernel
    rw [ha]
    exact (canonical24959 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1708 + difference 0 4) (sourceB1708 + difference 4 0) sourceC1708) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2215) := by
    have ha : (tripleCharges (sourceA1708 + difference 0 4) (sourceB1708 + difference 4 0) sourceC1708) = raw24960 := by
      apply Matrix.ext; unfold tripleCharges sourceA1708 sourceB1708 sourceC1708 difference raw24960; decide +kernel
    rw [ha]
    exact (canonical24960 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1708 + difference 0 5) (sourceB1708 + difference 5 0) sourceC1708) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2213) := by
    have ha : (tripleCharges (sourceA1708 + difference 0 5) (sourceB1708 + difference 5 0) sourceC1708) = raw24961 := by
      apply Matrix.ext; unfold tripleCharges sourceA1708 sourceB1708 sourceC1708 difference raw24961; decide +kernel
    rw [ha]
    exact (canonical24961 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1708 + sourceB1708) sourceC1708) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4082) := by
    have ha : (doubleCharges (sourceA1708 + sourceB1708) sourceC1708) = raw24962 := by
      apply Matrix.ext; unfold doubleCharges sourceA1708 sourceB1708 sourceC1708 raw24962; decide +kernel
    rw [ha]
    exact (canonical24962 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1708 sourceB1708 sourceC1708
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1708, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1709 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1709 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1709 + difference 0 0) (sourceB1709 + difference 0 0) sourceC1709) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1023) := by
    have ha : (tripleCharges (sourceA1709 + difference 0 0) (sourceB1709 + difference 0 0) sourceC1709) = raw24963 := by
      apply Matrix.ext; unfold tripleCharges sourceA1709 sourceB1709 sourceC1709 difference raw24963; decide +kernel
    rw [ha]
    exact (canonical24963 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1709 + difference 0 1) (sourceB1709 + difference 1 0) sourceC1709) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2091) := by
    have ha : (tripleCharges (sourceA1709 + difference 0 1) (sourceB1709 + difference 1 0) sourceC1709) = raw24964 := by
      apply Matrix.ext; unfold tripleCharges sourceA1709 sourceB1709 sourceC1709 difference raw24964; decide +kernel
    rw [ha]
    exact (canonical24964 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1709 + difference 0 2) (sourceB1709 + difference 2 0) sourceC1709) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2091) := by
    have ha : (tripleCharges (sourceA1709 + difference 0 2) (sourceB1709 + difference 2 0) sourceC1709) = raw24965 := by
      apply Matrix.ext; unfold tripleCharges sourceA1709 sourceB1709 sourceC1709 difference raw24965; decide +kernel
    rw [ha]
    exact (canonical24965 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1709 + difference 0 3) (sourceB1709 + difference 3 0) sourceC1709) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2234) := by
    have ha : (tripleCharges (sourceA1709 + difference 0 3) (sourceB1709 + difference 3 0) sourceC1709) = raw24966 := by
      apply Matrix.ext; unfold tripleCharges sourceA1709 sourceB1709 sourceC1709 difference raw24966; decide +kernel
    rw [ha]
    exact (canonical24966 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1709 + difference 0 4) (sourceB1709 + difference 4 0) sourceC1709) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2234) := by
    have ha : (tripleCharges (sourceA1709 + difference 0 4) (sourceB1709 + difference 4 0) sourceC1709) = raw24967 := by
      apply Matrix.ext; unfold tripleCharges sourceA1709 sourceB1709 sourceC1709 difference raw24967; decide +kernel
    rw [ha]
    exact (canonical24967 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1709 + difference 0 5) (sourceB1709 + difference 5 0) sourceC1709) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2241) := by
    have ha : (tripleCharges (sourceA1709 + difference 0 5) (sourceB1709 + difference 5 0) sourceC1709) = raw24968 := by
      apply Matrix.ext; unfold tripleCharges sourceA1709 sourceB1709 sourceC1709 difference raw24968; decide +kernel
    rw [ha]
    exact (canonical24968 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1709 + sourceB1709) sourceC1709) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4079) := by
    have ha : (doubleCharges (sourceA1709 + sourceB1709) sourceC1709) = raw24969 := by
      apply Matrix.ext; unfold doubleCharges sourceA1709 sourceB1709 sourceC1709 raw24969; decide +kernel
    rw [ha]
    exact (canonical24969 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1709 sourceB1709 sourceC1709
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1709, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1710 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1710 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1710 + difference 0 5) (sourceB1710 + difference 5 0) sourceC1710) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2241) := by
    have ha : (tripleCharges (sourceA1710 + difference 0 5) (sourceB1710 + difference 5 0) sourceC1710) = raw24968 := by
      apply Matrix.ext; unfold tripleCharges sourceA1710 sourceB1710 sourceC1710 difference raw24968; decide +kernel
    rw [ha]
    exact (canonical24968 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1710 + difference 1 5) (sourceB1710 + difference 5 1) sourceC1710) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1034) := by
    have ha : (tripleCharges (sourceA1710 + difference 1 5) (sourceB1710 + difference 5 1) sourceC1710) = raw24970 := by
      apply Matrix.ext; unfold tripleCharges sourceA1710 sourceB1710 sourceC1710 difference raw24970; decide +kernel
    rw [ha]
    exact (canonical24970 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1710 + difference 2 5) (sourceB1710 + difference 5 2) sourceC1710) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1034) := by
    have ha : (tripleCharges (sourceA1710 + difference 2 5) (sourceB1710 + difference 5 2) sourceC1710) = raw24971 := by
      apply Matrix.ext; unfold tripleCharges sourceA1710 sourceB1710 sourceC1710 difference raw24971; decide +kernel
    rw [ha]
    exact (canonical24971 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1710 + difference 3 5) (sourceB1710 + difference 5 3) sourceC1710) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1018) := by
    have ha : (tripleCharges (sourceA1710 + difference 3 5) (sourceB1710 + difference 5 3) sourceC1710) = raw24972 := by
      apply Matrix.ext; unfold tripleCharges sourceA1710 sourceB1710 sourceC1710 difference raw24972; decide +kernel
    rw [ha]
    exact (canonical24972 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1710 + difference 4 5) (sourceB1710 + difference 5 4) sourceC1710) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1018) := by
    have ha : (tripleCharges (sourceA1710 + difference 4 5) (sourceB1710 + difference 5 4) sourceC1710) = raw24973 := by
      apply Matrix.ext; unfold tripleCharges sourceA1710 sourceB1710 sourceC1710 difference raw24973; decide +kernel
    rw [ha]
    exact (canonical24973 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1710 + difference 5 5) (sourceB1710 + difference 5 5) sourceC1710) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1023) := by
    have ha : (tripleCharges (sourceA1710 + difference 5 5) (sourceB1710 + difference 5 5) sourceC1710) = raw24963 := by
      apply Matrix.ext; unfold tripleCharges sourceA1710 sourceB1710 sourceC1710 difference raw24963; decide +kernel
    rw [ha]
    exact (canonical24963 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1710 + sourceB1710) sourceC1710) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4079) := by
    have ha : (doubleCharges (sourceA1710 + sourceB1710) sourceC1710) = raw24969 := by
      apply Matrix.ext; unfold doubleCharges sourceA1710 sourceB1710 sourceC1710 raw24969; decide +kernel
    rw [ha]
    exact (canonical24969 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1710 sourceB1710 sourceC1710
    (0 : Fin 2) 1 (5 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1710, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1711 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1711 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1711 + difference 0 0) (sourceB1711 + difference 0 0) sourceC1711) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1018) := by
    have ha : (tripleCharges (sourceA1711 + difference 0 0) (sourceB1711 + difference 0 0) sourceC1711) = raw24974 := by
      apply Matrix.ext; unfold tripleCharges sourceA1711 sourceB1711 sourceC1711 difference raw24974; decide +kernel
    rw [ha]
    exact (canonical24974 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1711 + difference 0 1) (sourceB1711 + difference 1 0) sourceC1711) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2086) := by
    have ha : (tripleCharges (sourceA1711 + difference 0 1) (sourceB1711 + difference 1 0) sourceC1711) = raw24975 := by
      apply Matrix.ext; unfold tripleCharges sourceA1711 sourceB1711 sourceC1711 difference raw24975; decide +kernel
    rw [ha]
    exact (canonical24975 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1711 + difference 0 2) (sourceB1711 + difference 2 0) sourceC1711) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2086) := by
    have ha : (tripleCharges (sourceA1711 + difference 0 2) (sourceB1711 + difference 2 0) sourceC1711) = raw24976 := by
      apply Matrix.ext; unfold tripleCharges sourceA1711 sourceB1711 sourceC1711 difference raw24976; decide +kernel
    rw [ha]
    exact (canonical24976 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1711 + difference 0 3) (sourceB1711 + difference 3 0) sourceC1711) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2232) := by
    have ha : (tripleCharges (sourceA1711 + difference 0 3) (sourceB1711 + difference 3 0) sourceC1711) = raw24977 := by
      apply Matrix.ext; unfold tripleCharges sourceA1711 sourceB1711 sourceC1711 difference raw24977; decide +kernel
    rw [ha]
    exact (canonical24977 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1711 + difference 0 4) (sourceB1711 + difference 4 0) sourceC1711) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2191) := by
    have ha : (tripleCharges (sourceA1711 + difference 0 4) (sourceB1711 + difference 4 0) sourceC1711) = raw24978 := by
      apply Matrix.ext; unfold tripleCharges sourceA1711 sourceB1711 sourceC1711 difference raw24978; decide +kernel
    rw [ha]
    exact (canonical24978 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1711 + difference 0 5) (sourceB1711 + difference 5 0) sourceC1711) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2241) := by
    have ha : (tripleCharges (sourceA1711 + difference 0 5) (sourceB1711 + difference 5 0) sourceC1711) = raw24979 := by
      apply Matrix.ext; unfold tripleCharges sourceA1711 sourceB1711 sourceC1711 difference raw24979; decide +kernel
    rw [ha]
    exact (canonical24979 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1711 + sourceB1711) sourceC1711) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4079) := by
    have ha : (doubleCharges (sourceA1711 + sourceB1711) sourceC1711) = raw24980 := by
      apply Matrix.ext; unfold doubleCharges sourceA1711 sourceB1711 sourceC1711 raw24980; decide +kernel
    rw [ha]
    exact (canonical24980 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1711 sourceB1711 sourceC1711
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1711, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1712 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1712 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1712 + difference 0 0) (sourceB1712 + difference 0 0) sourceC1712) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1017) := by
    have ha : (tripleCharges (sourceA1712 + difference 0 0) (sourceB1712 + difference 0 0) sourceC1712) = raw21120 := by
      apply Matrix.ext; unfold tripleCharges sourceA1712 sourceB1712 sourceC1712 difference raw21120; decide +kernel
    rw [ha]
    exact (canonical21120 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1712 + difference 0 1) (sourceB1712 + difference 1 0) sourceC1712) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2085) := by
    have ha : (tripleCharges (sourceA1712 + difference 0 1) (sourceB1712 + difference 1 0) sourceC1712) = raw24981 := by
      apply Matrix.ext; unfold tripleCharges sourceA1712 sourceB1712 sourceC1712 difference raw24981; decide +kernel
    rw [ha]
    exact (canonical24981 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1712 + difference 0 2) (sourceB1712 + difference 2 0) sourceC1712) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2085) := by
    have ha : (tripleCharges (sourceA1712 + difference 0 2) (sourceB1712 + difference 2 0) sourceC1712) = raw24982 := by
      apply Matrix.ext; unfold tripleCharges sourceA1712 sourceB1712 sourceC1712 difference raw24982; decide +kernel
    rw [ha]
    exact (canonical24982 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1712 + difference 0 3) (sourceB1712 + difference 3 0) sourceC1712) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2242) := by
    have ha : (tripleCharges (sourceA1712 + difference 0 3) (sourceB1712 + difference 3 0) sourceC1712) = raw21116 := by
      apply Matrix.ext; unfold tripleCharges sourceA1712 sourceB1712 sourceC1712 difference raw21116; decide +kernel
    rw [ha]
    exact (canonical21116 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1712 + difference 0 4) (sourceB1712 + difference 4 0) sourceC1712) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2190) := by
    have ha : (tripleCharges (sourceA1712 + difference 0 4) (sourceB1712 + difference 4 0) sourceC1712) = raw24983 := by
      apply Matrix.ext; unfold tripleCharges sourceA1712 sourceB1712 sourceC1712 difference raw24983; decide +kernel
    rw [ha]
    exact (canonical24983 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1712 + difference 0 5) (sourceB1712 + difference 5 0) sourceC1712) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2240) := by
    have ha : (tripleCharges (sourceA1712 + difference 0 5) (sourceB1712 + difference 5 0) sourceC1712) = raw24984 := by
      apply Matrix.ext; unfold tripleCharges sourceA1712 sourceB1712 sourceC1712 difference raw24984; decide +kernel
    rw [ha]
    exact (canonical24984 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1712 + sourceB1712) sourceC1712) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4080) := by
    have ha : (doubleCharges (sourceA1712 + sourceB1712) sourceC1712) = raw21117 := by
      apply Matrix.ext; unfold doubleCharges sourceA1712 sourceB1712 sourceC1712 raw21117; decide +kernel
    rw [ha]
    exact (canonical21117 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1712 sourceB1712 sourceC1712
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1712, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1713 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1713 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1713 + difference 0 0) (sourceB1713 + difference 0 0) sourceC1713) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1045) := by
    have ha : (tripleCharges (sourceA1713 + difference 0 0) (sourceB1713 + difference 0 0) sourceC1713) = raw24985 := by
      apply Matrix.ext; unfold tripleCharges sourceA1713 sourceB1713 sourceC1713 difference raw24985; decide +kernel
    rw [ha]
    exact (canonical24985 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1713 + difference 0 1) (sourceB1713 + difference 1 0) sourceC1713) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2111) := by
    have ha : (tripleCharges (sourceA1713 + difference 0 1) (sourceB1713 + difference 1 0) sourceC1713) = raw24986 := by
      apply Matrix.ext; unfold tripleCharges sourceA1713 sourceB1713 sourceC1713 difference raw24986; decide +kernel
    rw [ha]
    exact (canonical24986 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1713 + difference 0 2) (sourceB1713 + difference 2 0) sourceC1713) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2024) := by
    have ha : (tripleCharges (sourceA1713 + difference 0 2) (sourceB1713 + difference 2 0) sourceC1713) = raw24987 := by
      apply Matrix.ext; unfold tripleCharges sourceA1713 sourceB1713 sourceC1713 difference raw24987; decide +kernel
    rw [ha]
    exact (canonical24987 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1713 + difference 0 3) (sourceB1713 + difference 3 0) sourceC1713) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2254) := by
    have ha : (tripleCharges (sourceA1713 + difference 0 3) (sourceB1713 + difference 3 0) sourceC1713) = raw24988 := by
      apply Matrix.ext; unfold tripleCharges sourceA1713 sourceB1713 sourceC1713 difference raw24988; decide +kernel
    rw [ha]
    exact (canonical24988 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1713 + difference 0 4) (sourceB1713 + difference 4 0) sourceC1713) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2246) := by
    have ha : (tripleCharges (sourceA1713 + difference 0 4) (sourceB1713 + difference 4 0) sourceC1713) = raw24989 := by
      apply Matrix.ext; unfold tripleCharges sourceA1713 sourceB1713 sourceC1713 difference raw24989; decide +kernel
    rw [ha]
    exact (canonical24989 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1713 + difference 0 5) (sourceB1713 + difference 5 0) sourceC1713) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2260) := by
    have ha : (tripleCharges (sourceA1713 + difference 0 5) (sourceB1713 + difference 5 0) sourceC1713) = raw24990 := by
      apply Matrix.ext; unfold tripleCharges sourceA1713 sourceB1713 sourceC1713 difference raw24990; decide +kernel
    rw [ha]
    exact (canonical24990 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1713 + sourceB1713) sourceC1713) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4080) := by
    have ha : (doubleCharges (sourceA1713 + sourceB1713) sourceC1713) = raw24991 := by
      apply Matrix.ext; unfold doubleCharges sourceA1713 sourceB1713 sourceC1713 raw24991; decide +kernel
    rw [ha]
    exact (canonical24991 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1713 sourceB1713 sourceC1713
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1713, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1714 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1714 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1714 + difference 0 5) (sourceB1714 + difference 5 0) sourceC1714) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2260) := by
    have ha : (tripleCharges (sourceA1714 + difference 0 5) (sourceB1714 + difference 5 0) sourceC1714) = raw24990 := by
      apply Matrix.ext; unfold tripleCharges sourceA1714 sourceB1714 sourceC1714 difference raw24990; decide +kernel
    rw [ha]
    exact (canonical24990 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1714 + difference 1 5) (sourceB1714 + difference 5 1) sourceC1714) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1073) := by
    have ha : (tripleCharges (sourceA1714 + difference 1 5) (sourceB1714 + difference 5 1) sourceC1714) = raw24992 := by
      apply Matrix.ext; unfold tripleCharges sourceA1714 sourceB1714 sourceC1714 difference raw24992; decide +kernel
    rw [ha]
    exact (canonical24992 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1714 + difference 2 5) (sourceB1714 + difference 5 2) sourceC1714) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1032) := by
    have ha : (tripleCharges (sourceA1714 + difference 2 5) (sourceB1714 + difference 5 2) sourceC1714) = raw24993 := by
      apply Matrix.ext; unfold tripleCharges sourceA1714 sourceB1714 sourceC1714 difference raw24993; decide +kernel
    rw [ha]
    exact (canonical24993 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1714 + difference 3 5) (sourceB1714 + difference 5 3) sourceC1714) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1035) := by
    have ha : (tripleCharges (sourceA1714 + difference 3 5) (sourceB1714 + difference 5 3) sourceC1714) = raw24994 := by
      apply Matrix.ext; unfold tripleCharges sourceA1714 sourceB1714 sourceC1714 difference raw24994; decide +kernel
    rw [ha]
    exact (canonical24994 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1714 + difference 4 5) (sourceB1714 + difference 5 4) sourceC1714) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1036) := by
    have ha : (tripleCharges (sourceA1714 + difference 4 5) (sourceB1714 + difference 5 4) sourceC1714) = raw24995 := by
      apply Matrix.ext; unfold tripleCharges sourceA1714 sourceB1714 sourceC1714 difference raw24995; decide +kernel
    rw [ha]
    exact (canonical24995 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1714 + difference 5 5) (sourceB1714 + difference 5 5) sourceC1714) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1045) := by
    have ha : (tripleCharges (sourceA1714 + difference 5 5) (sourceB1714 + difference 5 5) sourceC1714) = raw24985 := by
      apply Matrix.ext; unfold tripleCharges sourceA1714 sourceB1714 sourceC1714 difference raw24985; decide +kernel
    rw [ha]
    exact (canonical24985 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1714 + sourceB1714) sourceC1714) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4080) := by
    have ha : (doubleCharges (sourceA1714 + sourceB1714) sourceC1714) = raw24991 := by
      apply Matrix.ext; unfold doubleCharges sourceA1714 sourceB1714 sourceC1714 raw24991; decide +kernel
    rw [ha]
    exact (canonical24991 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1714 sourceB1714 sourceC1714
    (0 : Fin 2) 1 (5 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1714, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1715 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1715 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1715 + difference 0 0) (sourceB1715 + difference 0 0) sourceC1715) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1036) := by
    have ha : (tripleCharges (sourceA1715 + difference 0 0) (sourceB1715 + difference 0 0) sourceC1715) = raw24996 := by
      apply Matrix.ext; unfold tripleCharges sourceA1715 sourceB1715 sourceC1715 difference raw24996; decide +kernel
    rw [ha]
    exact (canonical24996 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1715 + difference 0 1) (sourceB1715 + difference 1 0) sourceC1715) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2102) := by
    have ha : (tripleCharges (sourceA1715 + difference 0 1) (sourceB1715 + difference 1 0) sourceC1715) = raw24997 := by
      apply Matrix.ext; unfold tripleCharges sourceA1715 sourceB1715 sourceC1715 difference raw24997; decide +kernel
    rw [ha]
    exact (canonical24997 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1715 + difference 0 2) (sourceB1715 + difference 2 0) sourceC1715) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2017) := by
    have ha : (tripleCharges (sourceA1715 + difference 0 2) (sourceB1715 + difference 2 0) sourceC1715) = raw24998 := by
      apply Matrix.ext; unfold tripleCharges sourceA1715 sourceB1715 sourceC1715 difference raw24998; decide +kernel
    rw [ha]
    exact (canonical24998 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1715 + difference 0 3) (sourceB1715 + difference 3 0) sourceC1715) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2251) := by
    have ha : (tripleCharges (sourceA1715 + difference 0 3) (sourceB1715 + difference 3 0) sourceC1715) = raw24999 := by
      apply Matrix.ext; unfold tripleCharges sourceA1715 sourceB1715 sourceC1715 difference raw24999; decide +kernel
    rw [ha]
    exact (canonical24999 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1715 + difference 0 4) (sourceB1715 + difference 4 0) sourceC1715) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2206) := by
    have ha : (tripleCharges (sourceA1715 + difference 0 4) (sourceB1715 + difference 4 0) sourceC1715) = raw25000 := by
      apply Matrix.ext; unfold tripleCharges sourceA1715 sourceB1715 sourceC1715 difference raw25000; decide +kernel
    rw [ha]
    exact (canonical25000 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1715 + difference 0 5) (sourceB1715 + difference 5 0) sourceC1715) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2260) := by
    have ha : (tripleCharges (sourceA1715 + difference 0 5) (sourceB1715 + difference 5 0) sourceC1715) = raw25001 := by
      apply Matrix.ext; unfold tripleCharges sourceA1715 sourceB1715 sourceC1715 difference raw25001; decide +kernel
    rw [ha]
    exact (canonical25001 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1715 + sourceB1715) sourceC1715) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4080) := by
    have ha : (doubleCharges (sourceA1715 + sourceB1715) sourceC1715) = raw25002 := by
      apply Matrix.ext; unfold doubleCharges sourceA1715 sourceB1715 sourceC1715 raw25002; decide +kernel
    rw [ha]
    exact (canonical25002 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1715 sourceB1715 sourceC1715
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1715, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1716 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1716 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1716 + difference 0 1) (sourceB1716 + difference 1 0) sourceC1716) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4869) := by
    have ha : (tripleCharges (sourceA1716 + difference 0 1) (sourceB1716 + difference 1 0) sourceC1716) = raw14356 := by
      apply Matrix.ext; unfold tripleCharges sourceA1716 sourceB1716 sourceC1716 difference raw14356; decide +kernel
    rw [ha]
    exact (canonical14356 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1716 + difference 0 2) (sourceB1716 + difference 2 0) sourceC1716) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4805) := by
    have ha : (tripleCharges (sourceA1716 + difference 0 2) (sourceB1716 + difference 2 0) sourceC1716) = raw14357 := by
      apply Matrix.ext; unfold tripleCharges sourceA1716 sourceB1716 sourceC1716 difference raw14357; decide +kernel
    rw [ha]
    exact (canonical14357 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1716 + difference 0 3) (sourceB1716 + difference 3 0) sourceC1716) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4889) := by
    have ha : (tripleCharges (sourceA1716 + difference 0 3) (sourceB1716 + difference 3 0) sourceC1716) = raw14358 := by
      apply Matrix.ext; unfold tripleCharges sourceA1716 sourceB1716 sourceC1716 difference raw14358; decide +kernel
    rw [ha]
    exact (canonical14358 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1716 + difference 0 4) (sourceB1716 + difference 4 0) sourceC1716) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4889) := by
    have ha : (tripleCharges (sourceA1716 + difference 0 4) (sourceB1716 + difference 4 0) sourceC1716) = raw14359 := by
      apply Matrix.ext; unfold tripleCharges sourceA1716 sourceB1716 sourceC1716 difference raw14359; decide +kernel
    rw [ha]
    exact (canonical14359 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1716 + difference 0 5) (sourceB1716 + difference 5 0) sourceC1716) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4893) := by
    have ha : (tripleCharges (sourceA1716 + difference 0 5) (sourceB1716 + difference 5 0) sourceC1716) = raw25003 := by
      apply Matrix.ext; unfold tripleCharges sourceA1716 sourceB1716 sourceC1716 difference raw25003; decide +kernel
    rw [ha]
    exact (canonical25003 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1716 + difference 1 0) (sourceB1716 + difference 0 1) sourceC1716) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4182) := by
    have ha : (tripleCharges (sourceA1716 + difference 1 0) (sourceB1716 + difference 0 1) sourceC1716) = raw25004 := by
      apply Matrix.ext; unfold tripleCharges sourceA1716 sourceB1716 sourceC1716 difference raw25004; decide +kernel
    rw [ha]
    exact (canonical25004 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1716 + difference 1 2) (sourceB1716 + difference 2 1) sourceC1716) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4351) := by
    have ha : (tripleCharges (sourceA1716 + difference 1 2) (sourceB1716 + difference 2 1) sourceC1716) = raw25005 := by
      apply Matrix.ext; unfold tripleCharges sourceA1716 sourceB1716 sourceC1716 difference raw25005; decide +kernel
    rw [ha]
    exact (canonical25005 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1716 + difference 1 3) (sourceB1716 + difference 3 1) sourceC1716) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4461) := by
    have ha : (tripleCharges (sourceA1716 + difference 1 3) (sourceB1716 + difference 3 1) sourceC1716) = raw25006 := by
      apply Matrix.ext; unfold tripleCharges sourceA1716 sourceB1716 sourceC1716 difference raw25006; decide +kernel
    rw [ha]
    exact (canonical25006 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1716 + difference 1 4) (sourceB1716 + difference 4 1) sourceC1716) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4461) := by
    have ha : (tripleCharges (sourceA1716 + difference 1 4) (sourceB1716 + difference 4 1) sourceC1716) = raw25007 := by
      apply Matrix.ext; unfold tripleCharges sourceA1716 sourceB1716 sourceC1716 difference raw25007; decide +kernel
    rw [ha]
    exact (canonical25007 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1716 + difference 1 5) (sourceB1716 + difference 5 1) sourceC1716) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4497) := by
    have ha : (tripleCharges (sourceA1716 + difference 1 5) (sourceB1716 + difference 5 1) sourceC1716) = raw14335 := by
      apply Matrix.ext; unfold tripleCharges sourceA1716 sourceB1716 sourceC1716 difference raw14335; decide +kernel
    rw [ha]
    exact (canonical14335 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1716 + difference 2 0) (sourceB1716 + difference 0 2) sourceC1716) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4152) := by
    have ha : (tripleCharges (sourceA1716 + difference 2 0) (sourceB1716 + difference 0 2) sourceC1716) = raw25008 := by
      apply Matrix.ext; unfold tripleCharges sourceA1716 sourceB1716 sourceC1716 difference raw25008; decide +kernel
    rw [ha]
    exact (canonical25008 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1716 + difference 2 1) (sourceB1716 + difference 1 2) sourceC1716) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4366) := by
    have ha : (tripleCharges (sourceA1716 + difference 2 1) (sourceB1716 + difference 1 2) sourceC1716) = raw25009 := by
      apply Matrix.ext; unfold tripleCharges sourceA1716 sourceB1716 sourceC1716 difference raw25009; decide +kernel
    rw [ha]
    exact (canonical25009 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1716 + difference 2 3) (sourceB1716 + difference 3 2) sourceC1716) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4439) := by
    have ha : (tripleCharges (sourceA1716 + difference 2 3) (sourceB1716 + difference 3 2) sourceC1716) = raw25010 := by
      apply Matrix.ext; unfold tripleCharges sourceA1716 sourceB1716 sourceC1716 difference raw25010; decide +kernel
    rw [ha]
    exact (canonical25010 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1716 + difference 2 4) (sourceB1716 + difference 4 2) sourceC1716) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4439) := by
    have ha : (tripleCharges (sourceA1716 + difference 2 4) (sourceB1716 + difference 4 2) sourceC1716) = raw25011 := by
      apply Matrix.ext; unfold tripleCharges sourceA1716 sourceB1716 sourceC1716 difference raw25011; decide +kernel
    rw [ha]
    exact (canonical25011 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1716 + difference 2 5) (sourceB1716 + difference 5 2) sourceC1716) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4456) := by
    have ha : (tripleCharges (sourceA1716 + difference 2 5) (sourceB1716 + difference 5 2) sourceC1716) = raw14340 := by
      apply Matrix.ext; unfold tripleCharges sourceA1716 sourceB1716 sourceC1716 difference raw14340; decide +kernel
    rw [ha]
    exact (canonical14340 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1716 + difference 3 0) (sourceB1716 + difference 0 3) sourceC1716) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4158) := by
    have ha : (tripleCharges (sourceA1716 + difference 3 0) (sourceB1716 + difference 0 3) sourceC1716) = raw25012 := by
      apply Matrix.ext; unfold tripleCharges sourceA1716 sourceB1716 sourceC1716 difference raw25012; decide +kernel
    rw [ha]
    exact (canonical25012 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1716 + difference 3 1) (sourceB1716 + difference 1 3) sourceC1716) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4372) := by
    have ha : (tripleCharges (sourceA1716 + difference 3 1) (sourceB1716 + difference 1 3) sourceC1716) = raw25013 := by
      apply Matrix.ext; unfold tripleCharges sourceA1716 sourceB1716 sourceC1716 difference raw25013; decide +kernel
    rw [ha]
    exact (canonical25013 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1716 + difference 3 2) (sourceB1716 + difference 2 3) sourceC1716) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4332) := by
    have ha : (tripleCharges (sourceA1716 + difference 3 2) (sourceB1716 + difference 2 3) sourceC1716) = raw25014 := by
      apply Matrix.ext; unfold tripleCharges sourceA1716 sourceB1716 sourceC1716 difference raw25014; decide +kernel
    rw [ha]
    exact (canonical25014 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1716 + difference 3 4) (sourceB1716 + difference 4 3) sourceC1716) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4444) := by
    have ha : (tripleCharges (sourceA1716 + difference 3 4) (sourceB1716 + difference 4 3) sourceC1716) = raw25015 := by
      apply Matrix.ext; unfold tripleCharges sourceA1716 sourceB1716 sourceC1716 difference raw25015; decide +kernel
    rw [ha]
    exact (canonical25015 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1716 + difference 3 5) (sourceB1716 + difference 5 3) sourceC1716) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4458) := by
    have ha : (tripleCharges (sourceA1716 + difference 3 5) (sourceB1716 + difference 5 3) sourceC1716) = raw14345 := by
      apply Matrix.ext; unfold tripleCharges sourceA1716 sourceB1716 sourceC1716 difference raw14345; decide +kernel
    rw [ha]
    exact (canonical14345 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1716 + difference 4 0) (sourceB1716 + difference 0 4) sourceC1716) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4158) := by
    have ha : (tripleCharges (sourceA1716 + difference 4 0) (sourceB1716 + difference 0 4) sourceC1716) = raw25016 := by
      apply Matrix.ext; unfold tripleCharges sourceA1716 sourceB1716 sourceC1716 difference raw25016; decide +kernel
    rw [ha]
    exact (canonical25016 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1716 + difference 4 1) (sourceB1716 + difference 1 4) sourceC1716) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4372) := by
    have ha : (tripleCharges (sourceA1716 + difference 4 1) (sourceB1716 + difference 1 4) sourceC1716) = raw25017 := by
      apply Matrix.ext; unfold tripleCharges sourceA1716 sourceB1716 sourceC1716 difference raw25017; decide +kernel
    rw [ha]
    exact (canonical25017 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1716 + difference 4 2) (sourceB1716 + difference 2 4) sourceC1716) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4332) := by
    have ha : (tripleCharges (sourceA1716 + difference 4 2) (sourceB1716 + difference 2 4) sourceC1716) = raw25018 := by
      apply Matrix.ext; unfold tripleCharges sourceA1716 sourceB1716 sourceC1716 difference raw25018; decide +kernel
    rw [ha]
    exact (canonical25018 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1716 + difference 4 3) (sourceB1716 + difference 3 4) sourceC1716) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4444) := by
    have ha : (tripleCharges (sourceA1716 + difference 4 3) (sourceB1716 + difference 3 4) sourceC1716) = raw25019 := by
      apply Matrix.ext; unfold tripleCharges sourceA1716 sourceB1716 sourceC1716 difference raw25019; decide +kernel
    rw [ha]
    exact (canonical25019 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1716 + difference 4 5) (sourceB1716 + difference 5 4) sourceC1716) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4458) := by
    have ha : (tripleCharges (sourceA1716 + difference 4 5) (sourceB1716 + difference 5 4) sourceC1716) = raw14350 := by
      apply Matrix.ext; unfold tripleCharges sourceA1716 sourceB1716 sourceC1716 difference raw14350; decide +kernel
    rw [ha]
    exact (canonical14350 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1716 + difference 5 0) (sourceB1716 + difference 0 5) sourceC1716) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4157) := by
    have ha : (tripleCharges (sourceA1716 + difference 5 0) (sourceB1716 + difference 0 5) sourceC1716) = raw25020 := by
      apply Matrix.ext; unfold tripleCharges sourceA1716 sourceB1716 sourceC1716 difference raw25020; decide +kernel
    rw [ha]
    exact (canonical25020 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1716 + difference 5 1) (sourceB1716 + difference 1 5) sourceC1716) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4371) := by
    have ha : (tripleCharges (sourceA1716 + difference 5 1) (sourceB1716 + difference 1 5) sourceC1716) = raw25021 := by
      apply Matrix.ext; unfold tripleCharges sourceA1716 sourceB1716 sourceC1716 difference raw25021; decide +kernel
    rw [ha]
    exact (canonical25021 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1716 + difference 5 2) (sourceB1716 + difference 2 5) sourceC1716) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4331) := by
    have ha : (tripleCharges (sourceA1716 + difference 5 2) (sourceB1716 + difference 2 5) sourceC1716) = raw25022 := by
      apply Matrix.ext; unfold tripleCharges sourceA1716 sourceB1716 sourceC1716 difference raw25022; decide +kernel
    rw [ha]
    exact (canonical25022 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1716 + difference 5 3) (sourceB1716 + difference 3 5) sourceC1716) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4442) := by
    have ha : (tripleCharges (sourceA1716 + difference 5 3) (sourceB1716 + difference 3 5) sourceC1716) = raw25023 := by
      apply Matrix.ext; unfold tripleCharges sourceA1716 sourceB1716 sourceC1716 difference raw25023; decide +kernel
    rw [ha]
    exact (canonical25023 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1716 + difference 5 4) (sourceB1716 + difference 4 5) sourceC1716) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4442) := by
    have ha : (tripleCharges (sourceA1716 + difference 5 4) (sourceB1716 + difference 4 5) sourceC1716) = raw25024 := by
      apply Matrix.ext; unfold tripleCharges sourceA1716 sourceB1716 sourceC1716 difference raw25024; decide +kernel
    rw [ha]
    exact (canonical25024 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1716 sourceB1716 sourceC1716
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1716, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1717 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1717 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1717 + difference 0 1) (sourceB1717 + difference 1 0) sourceC1717) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2275) := by
    have ha : (tripleCharges (sourceA1717 + difference 0 1) (sourceB1717 + difference 1 0) sourceC1717) = raw25025 := by
      apply Matrix.ext; unfold tripleCharges sourceA1717 sourceB1717 sourceC1717 difference raw25025; decide +kernel
    rw [ha]
    exact (canonical25025 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1717 + difference 0 2) (sourceB1717 + difference 2 0) sourceC1717) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2214) := by
    have ha : (tripleCharges (sourceA1717 + difference 0 2) (sourceB1717 + difference 2 0) sourceC1717) = raw25026 := by
      apply Matrix.ext; unfold tripleCharges sourceA1717 sourceB1717 sourceC1717 difference raw25026; decide +kernel
    rw [ha]
    exact (canonical25026 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1717 + difference 0 3) (sourceB1717 + difference 3 0) sourceC1717) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2277) := by
    have ha : (tripleCharges (sourceA1717 + difference 0 3) (sourceB1717 + difference 3 0) sourceC1717) = raw25027 := by
      apply Matrix.ext; unfold tripleCharges sourceA1717 sourceB1717 sourceC1717 difference raw25027; decide +kernel
    rw [ha]
    exact (canonical25027 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1717 + difference 0 4) (sourceB1717 + difference 4 0) sourceC1717) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2277) := by
    have ha : (tripleCharges (sourceA1717 + difference 0 4) (sourceB1717 + difference 4 0) sourceC1717) = raw25028 := by
      apply Matrix.ext; unfold tripleCharges sourceA1717 sourceB1717 sourceC1717 difference raw25028; decide +kernel
    rw [ha]
    exact (canonical25028 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1717 + difference 0 5) (sourceB1717 + difference 5 0) sourceC1717) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2263) := by
    have ha : (tripleCharges (sourceA1717 + difference 0 5) (sourceB1717 + difference 5 0) sourceC1717) = raw25029 := by
      apply Matrix.ext; unfold tripleCharges sourceA1717 sourceB1717 sourceC1717 difference raw25029; decide +kernel
    rw [ha]
    exact (canonical25029 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1717 + difference 1 0) (sourceB1717 + difference 0 1) sourceC1717) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1524) := by
    have ha : (tripleCharges (sourceA1717 + difference 1 0) (sourceB1717 + difference 0 1) sourceC1717) = raw25030 := by
      apply Matrix.ext; unfold tripleCharges sourceA1717 sourceB1717 sourceC1717 difference raw25030; decide +kernel
    rw [ha]
    exact (canonical25030 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1717 + difference 1 2) (sourceB1717 + difference 2 1) sourceC1717) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1680) := by
    have ha : (tripleCharges (sourceA1717 + difference 1 2) (sourceB1717 + difference 2 1) sourceC1717) = raw25031 := by
      apply Matrix.ext; unfold tripleCharges sourceA1717 sourceB1717 sourceC1717 difference raw25031; decide +kernel
    rw [ha]
    exact (canonical25031 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1717 + difference 1 3) (sourceB1717 + difference 3 1) sourceC1717) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1737) := by
    have ha : (tripleCharges (sourceA1717 + difference 1 3) (sourceB1717 + difference 3 1) sourceC1717) = raw25032 := by
      apply Matrix.ext; unfold tripleCharges sourceA1717 sourceB1717 sourceC1717 difference raw25032; decide +kernel
    rw [ha]
    exact (canonical25032 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1717 + difference 1 4) (sourceB1717 + difference 4 1) sourceC1717) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1737) := by
    have ha : (tripleCharges (sourceA1717 + difference 1 4) (sourceB1717 + difference 4 1) sourceC1717) = raw25033 := by
      apply Matrix.ext; unfold tripleCharges sourceA1717 sourceB1717 sourceC1717 difference raw25033; decide +kernel
    rw [ha]
    exact (canonical25033 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1717 + difference 1 5) (sourceB1717 + difference 5 1) sourceC1717) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1726) := by
    have ha : (tripleCharges (sourceA1717 + difference 1 5) (sourceB1717 + difference 5 1) sourceC1717) = raw25034 := by
      apply Matrix.ext; unfold tripleCharges sourceA1717 sourceB1717 sourceC1717 difference raw25034; decide +kernel
    rw [ha]
    exact (canonical25034 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1717 + difference 2 0) (sourceB1717 + difference 0 2) sourceC1717) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1510) := by
    have ha : (tripleCharges (sourceA1717 + difference 2 0) (sourceB1717 + difference 0 2) sourceC1717) = raw25035 := by
      apply Matrix.ext; unfold tripleCharges sourceA1717 sourceB1717 sourceC1717 difference raw25035; decide +kernel
    rw [ha]
    exact (canonical25035 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1717 + difference 2 1) (sourceB1717 + difference 1 2) sourceC1717) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1711) := by
    have ha : (tripleCharges (sourceA1717 + difference 2 1) (sourceB1717 + difference 1 2) sourceC1717) = raw25036 := by
      apply Matrix.ext; unfold tripleCharges sourceA1717 sourceB1717 sourceC1717 difference raw25036; decide +kernel
    rw [ha]
    exact (canonical25036 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1717 + difference 2 3) (sourceB1717 + difference 3 2) sourceC1717) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1713) := by
    have ha : (tripleCharges (sourceA1717 + difference 2 3) (sourceB1717 + difference 3 2) sourceC1717) = raw25037 := by
      apply Matrix.ext; unfold tripleCharges sourceA1717 sourceB1717 sourceC1717 difference raw25037; decide +kernel
    rw [ha]
    exact (canonical25037 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1717 + difference 2 4) (sourceB1717 + difference 4 2) sourceC1717) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1713) := by
    have ha : (tripleCharges (sourceA1717 + difference 2 4) (sourceB1717 + difference 4 2) sourceC1717) = raw25038 := by
      apply Matrix.ext; unfold tripleCharges sourceA1717 sourceB1717 sourceC1717 difference raw25038; decide +kernel
    rw [ha]
    exact (canonical25038 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1717 + difference 2 5) (sourceB1717 + difference 5 2) sourceC1717) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1706) := by
    have ha : (tripleCharges (sourceA1717 + difference 2 5) (sourceB1717 + difference 5 2) sourceC1717) = raw25039 := by
      apply Matrix.ext; unfold tripleCharges sourceA1717 sourceB1717 sourceC1717 difference raw25039; decide +kernel
    rw [ha]
    exact (canonical25039 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1717 + difference 3 0) (sourceB1717 + difference 0 3) sourceC1717) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1522) := by
    have ha : (tripleCharges (sourceA1717 + difference 3 0) (sourceB1717 + difference 0 3) sourceC1717) = raw25040 := by
      apply Matrix.ext; unfold tripleCharges sourceA1717 sourceB1717 sourceC1717 difference raw25040; decide +kernel
    rw [ha]
    exact (canonical25040 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1717 + difference 3 1) (sourceB1717 + difference 1 3) sourceC1717) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1734) := by
    have ha : (tripleCharges (sourceA1717 + difference 3 1) (sourceB1717 + difference 1 3) sourceC1717) = raw25041 := by
      apply Matrix.ext; unfold tripleCharges sourceA1717 sourceB1717 sourceC1717 difference raw25041; decide +kernel
    rw [ha]
    exact (canonical25041 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1717 + difference 3 2) (sourceB1717 + difference 2 3) sourceC1717) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1678) := by
    have ha : (tripleCharges (sourceA1717 + difference 3 2) (sourceB1717 + difference 2 3) sourceC1717) = raw25042 := by
      apply Matrix.ext; unfold tripleCharges sourceA1717 sourceB1717 sourceC1717 difference raw25042; decide +kernel
    rw [ha]
    exact (canonical25042 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1717 + difference 3 4) (sourceB1717 + difference 4 3) sourceC1717) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1736) := by
    have ha : (tripleCharges (sourceA1717 + difference 3 4) (sourceB1717 + difference 4 3) sourceC1717) = raw25043 := by
      apply Matrix.ext; unfold tripleCharges sourceA1717 sourceB1717 sourceC1717 difference raw25043; decide +kernel
    rw [ha]
    exact (canonical25043 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1717 + difference 3 5) (sourceB1717 + difference 5 3) sourceC1717) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1724) := by
    have ha : (tripleCharges (sourceA1717 + difference 3 5) (sourceB1717 + difference 5 3) sourceC1717) = raw25044 := by
      apply Matrix.ext; unfold tripleCharges sourceA1717 sourceB1717 sourceC1717 difference raw25044; decide +kernel
    rw [ha]
    exact (canonical25044 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1717 + difference 4 0) (sourceB1717 + difference 0 4) sourceC1717) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1522) := by
    have ha : (tripleCharges (sourceA1717 + difference 4 0) (sourceB1717 + difference 0 4) sourceC1717) = raw25045 := by
      apply Matrix.ext; unfold tripleCharges sourceA1717 sourceB1717 sourceC1717 difference raw25045; decide +kernel
    rw [ha]
    exact (canonical25045 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1717 + difference 4 1) (sourceB1717 + difference 1 4) sourceC1717) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1734) := by
    have ha : (tripleCharges (sourceA1717 + difference 4 1) (sourceB1717 + difference 1 4) sourceC1717) = raw25046 := by
      apply Matrix.ext; unfold tripleCharges sourceA1717 sourceB1717 sourceC1717 difference raw25046; decide +kernel
    rw [ha]
    exact (canonical25046 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1717 + difference 4 2) (sourceB1717 + difference 2 4) sourceC1717) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1678) := by
    have ha : (tripleCharges (sourceA1717 + difference 4 2) (sourceB1717 + difference 2 4) sourceC1717) = raw25047 := by
      apply Matrix.ext; unfold tripleCharges sourceA1717 sourceB1717 sourceC1717 difference raw25047; decide +kernel
    rw [ha]
    exact (canonical25047 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1717 + difference 4 3) (sourceB1717 + difference 3 4) sourceC1717) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1736) := by
    have ha : (tripleCharges (sourceA1717 + difference 4 3) (sourceB1717 + difference 3 4) sourceC1717) = raw25048 := by
      apply Matrix.ext; unfold tripleCharges sourceA1717 sourceB1717 sourceC1717 difference raw25048; decide +kernel
    rw [ha]
    exact (canonical25048 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1717 + difference 4 5) (sourceB1717 + difference 5 4) sourceC1717) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1724) := by
    have ha : (tripleCharges (sourceA1717 + difference 4 5) (sourceB1717 + difference 5 4) sourceC1717) = raw25049 := by
      apply Matrix.ext; unfold tripleCharges sourceA1717 sourceB1717 sourceC1717 difference raw25049; decide +kernel
    rw [ha]
    exact (canonical25049 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1717 + difference 5 0) (sourceB1717 + difference 0 5) sourceC1717) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1528) := by
    have ha : (tripleCharges (sourceA1717 + difference 5 0) (sourceB1717 + difference 0 5) sourceC1717) = raw25050 := by
      apply Matrix.ext; unfold tripleCharges sourceA1717 sourceB1717 sourceC1717 difference raw25050; decide +kernel
    rw [ha]
    exact (canonical25050 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1717 + difference 5 1) (sourceB1717 + difference 1 5) sourceC1717) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1742) := by
    have ha : (tripleCharges (sourceA1717 + difference 5 1) (sourceB1717 + difference 1 5) sourceC1717) = raw25051 := by
      apply Matrix.ext; unfold tripleCharges sourceA1717 sourceB1717 sourceC1717 difference raw25051; decide +kernel
    rw [ha]
    exact (canonical25051 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1717 + difference 5 2) (sourceB1717 + difference 2 5) sourceC1717) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1684) := by
    have ha : (tripleCharges (sourceA1717 + difference 5 2) (sourceB1717 + difference 2 5) sourceC1717) = raw25052 := by
      apply Matrix.ext; unfold tripleCharges sourceA1717 sourceB1717 sourceC1717 difference raw25052; decide +kernel
    rw [ha]
    exact (canonical25052 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1717 + difference 5 3) (sourceB1717 + difference 3 5) sourceC1717) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1744) := by
    have ha : (tripleCharges (sourceA1717 + difference 5 3) (sourceB1717 + difference 3 5) sourceC1717) = raw25053 := by
      apply Matrix.ext; unfold tripleCharges sourceA1717 sourceB1717 sourceC1717 difference raw25053; decide +kernel
    rw [ha]
    exact (canonical25053 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1717 + difference 5 4) (sourceB1717 + difference 4 5) sourceC1717) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1744) := by
    have ha : (tripleCharges (sourceA1717 + difference 5 4) (sourceB1717 + difference 4 5) sourceC1717) = raw25054 := by
      apply Matrix.ext; unfold tripleCharges sourceA1717 sourceB1717 sourceC1717 difference raw25054; decide +kernel
    rw [ha]
    exact (canonical25054 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1717 sourceB1717 sourceC1717
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1717, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1718 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1718 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1718 + difference 1 0) (sourceB1718 + difference 0 1) sourceC1718) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 610) := by
    have ha : (tripleCharges (sourceA1718 + difference 1 0) (sourceB1718 + difference 0 1) sourceC1718) = raw25055 := by
      apply Matrix.ext; unfold tripleCharges sourceA1718 sourceB1718 sourceC1718 difference raw25055; decide +kernel
    rw [ha]
    exact (canonical25055 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1718 + difference 1 1) (sourceB1718 + difference 1 1) sourceC1718) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1044) := by
    have ha : (tripleCharges (sourceA1718 + difference 1 1) (sourceB1718 + difference 1 1) sourceC1718) = raw25056 := by
      apply Matrix.ext; unfold tripleCharges sourceA1718 sourceB1718 sourceC1718 difference raw25056; decide +kernel
    rw [ha]
    exact (canonical25056 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1718 + difference 1 2) (sourceB1718 + difference 2 1) sourceC1718) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 929) := by
    have ha : (tripleCharges (sourceA1718 + difference 1 2) (sourceB1718 + difference 2 1) sourceC1718) = raw25057 := by
      apply Matrix.ext; unfold tripleCharges sourceA1718 sourceB1718 sourceC1718 difference raw25057; decide +kernel
    rw [ha]
    exact (canonical25057 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1718 + difference 1 3) (sourceB1718 + difference 3 1) sourceC1718) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1044) := by
    have ha : (tripleCharges (sourceA1718 + difference 1 3) (sourceB1718 + difference 3 1) sourceC1718) = raw25058 := by
      apply Matrix.ext; unfold tripleCharges sourceA1718 sourceB1718 sourceC1718 difference raw25058; decide +kernel
    rw [ha]
    exact (canonical25058 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1718 + difference 1 4) (sourceB1718 + difference 4 1) sourceC1718) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1044) := by
    have ha : (tripleCharges (sourceA1718 + difference 1 4) (sourceB1718 + difference 4 1) sourceC1718) = raw25059 := by
      apply Matrix.ext; unfold tripleCharges sourceA1718 sourceB1718 sourceC1718 difference raw25059; decide +kernel
    rw [ha]
    exact (canonical25059 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1718 + difference 1 5) (sourceB1718 + difference 5 1) sourceC1718) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1081) := by
    have ha : (tripleCharges (sourceA1718 + difference 1 5) (sourceB1718 + difference 5 1) sourceC1718) = raw25060 := by
      apply Matrix.ext; unfold tripleCharges sourceA1718 sourceB1718 sourceC1718 difference raw25060; decide +kernel
    rw [ha]
    exact (canonical25060 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1718 + sourceB1718) sourceC1718) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4083) := by
    have ha : (doubleCharges (sourceA1718 + sourceB1718) sourceC1718) = raw25061 := by
      apply Matrix.ext; unfold doubleCharges sourceA1718 sourceB1718 sourceC1718 raw25061; decide +kernel
    rw [ha]
    exact (canonical25061 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1718 sourceB1718 sourceC1718
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1718, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1719 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1719 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1719 + difference 0 1) (sourceB1719 + difference 1 0) sourceC1719) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2110) := by
    have ha : (tripleCharges (sourceA1719 + difference 0 1) (sourceB1719 + difference 1 0) sourceC1719) = raw25062 := by
      apply Matrix.ext; unfold tripleCharges sourceA1719 sourceB1719 sourceC1719 difference raw25062; decide +kernel
    rw [ha]
    exact (canonical25062 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1719 + difference 1 1) (sourceB1719 + difference 1 1) sourceC1719) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1044) := by
    have ha : (tripleCharges (sourceA1719 + difference 1 1) (sourceB1719 + difference 1 1) sourceC1719) = raw25056 := by
      apply Matrix.ext; unfold tripleCharges sourceA1719 sourceB1719 sourceC1719 difference raw25056; decide +kernel
    rw [ha]
    exact (canonical25056 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1719 + difference 2 1) (sourceB1719 + difference 1 2) sourceC1719) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 944) := by
    have ha : (tripleCharges (sourceA1719 + difference 2 1) (sourceB1719 + difference 1 2) sourceC1719) = raw25063 := by
      apply Matrix.ext; unfold tripleCharges sourceA1719 sourceB1719 sourceC1719 difference raw25063; decide +kernel
    rw [ha]
    exact (canonical25063 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1719 + difference 3 1) (sourceB1719 + difference 1 3) sourceC1719) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 950) := by
    have ha : (tripleCharges (sourceA1719 + difference 3 1) (sourceB1719 + difference 1 3) sourceC1719) = raw25064 := by
      apply Matrix.ext; unfold tripleCharges sourceA1719 sourceB1719 sourceC1719 difference raw25064; decide +kernel
    rw [ha]
    exact (canonical25064 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1719 + difference 4 1) (sourceB1719 + difference 1 4) sourceC1719) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 950) := by
    have ha : (tripleCharges (sourceA1719 + difference 4 1) (sourceB1719 + difference 1 4) sourceC1719) = raw25065 := by
      apply Matrix.ext; unfold tripleCharges sourceA1719 sourceB1719 sourceC1719 difference raw25065; decide +kernel
    rw [ha]
    exact (canonical25065 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1719 + difference 5 1) (sourceB1719 + difference 1 5) sourceC1719) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 949) := by
    have ha : (tripleCharges (sourceA1719 + difference 5 1) (sourceB1719 + difference 1 5) sourceC1719) = raw25066 := by
      apply Matrix.ext; unfold tripleCharges sourceA1719 sourceB1719 sourceC1719 difference raw25066; decide +kernel
    rw [ha]
    exact (canonical25066 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1719 + sourceB1719) sourceC1719) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4083) := by
    have ha : (doubleCharges (sourceA1719 + sourceB1719) sourceC1719) = raw25061 := by
      apply Matrix.ext; unfold doubleCharges sourceA1719 sourceB1719 sourceC1719 raw25061; decide +kernel
    rw [ha]
    exact (canonical25061 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1719 sourceB1719 sourceC1719
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1719, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1724 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1724 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1724 + difference 0 1) (sourceB1724 + difference 1 0) sourceC1724) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4866) := by
    have ha : (tripleCharges (sourceA1724 + difference 0 1) (sourceB1724 + difference 1 0) sourceC1724) = raw25135 := by
      apply Matrix.ext; unfold tripleCharges sourceA1724 sourceB1724 sourceC1724 difference raw25135; decide +kernel
    rw [ha]
    exact (canonical25135 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1724 + difference 0 2) (sourceB1724 + difference 2 0) sourceC1724) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4802) := by
    have ha : (tripleCharges (sourceA1724 + difference 0 2) (sourceB1724 + difference 2 0) sourceC1724) = raw25136 := by
      apply Matrix.ext; unfold tripleCharges sourceA1724 sourceB1724 sourceC1724 difference raw25136; decide +kernel
    rw [ha]
    exact (canonical25136 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1724 + difference 0 3) (sourceB1724 + difference 3 0) sourceC1724) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4888) := by
    have ha : (tripleCharges (sourceA1724 + difference 0 3) (sourceB1724 + difference 3 0) sourceC1724) = raw25137 := by
      apply Matrix.ext; unfold tripleCharges sourceA1724 sourceB1724 sourceC1724 difference raw25137; decide +kernel
    rw [ha]
    exact (canonical25137 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1724 + difference 0 4) (sourceB1724 + difference 4 0) sourceC1724) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4895) := by
    have ha : (tripleCharges (sourceA1724 + difference 0 4) (sourceB1724 + difference 4 0) sourceC1724) = raw25138 := by
      apply Matrix.ext; unfold tripleCharges sourceA1724 sourceB1724 sourceC1724 difference raw25138; decide +kernel
    rw [ha]
    exact (canonical25138 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1724 + difference 0 5) (sourceB1724 + difference 5 0) sourceC1724) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4893) := by
    have ha : (tripleCharges (sourceA1724 + difference 0 5) (sourceB1724 + difference 5 0) sourceC1724) = raw25139 := by
      apply Matrix.ext; unfold tripleCharges sourceA1724 sourceB1724 sourceC1724 difference raw25139; decide +kernel
    rw [ha]
    exact (canonical25139 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1724 + difference 1 0) (sourceB1724 + difference 0 1) sourceC1724) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4175) := by
    have ha : (tripleCharges (sourceA1724 + difference 1 0) (sourceB1724 + difference 0 1) sourceC1724) = raw25140 := by
      apply Matrix.ext; unfold tripleCharges sourceA1724 sourceB1724 sourceC1724 difference raw25140; decide +kernel
    rw [ha]
    exact (canonical25140 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1724 + difference 1 2) (sourceB1724 + difference 2 1) sourceC1724) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4344) := by
    have ha : (tripleCharges (sourceA1724 + difference 1 2) (sourceB1724 + difference 2 1) sourceC1724) = raw25141 := by
      apply Matrix.ext; unfold tripleCharges sourceA1724 sourceB1724 sourceC1724 difference raw25141; decide +kernel
    rw [ha]
    exact (canonical25141 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1724 + difference 1 3) (sourceB1724 + difference 3 1) sourceC1724) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4458) := by
    have ha : (tripleCharges (sourceA1724 + difference 1 3) (sourceB1724 + difference 3 1) sourceC1724) = raw25142 := by
      apply Matrix.ext; unfold tripleCharges sourceA1724 sourceB1724 sourceC1724 difference raw25142; decide +kernel
    rw [ha]
    exact (canonical25142 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1724 + difference 1 4) (sourceB1724 + difference 4 1) sourceC1724) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4502) := by
    have ha : (tripleCharges (sourceA1724 + difference 1 4) (sourceB1724 + difference 4 1) sourceC1724) = raw25143 := by
      apply Matrix.ext; unfold tripleCharges sourceA1724 sourceB1724 sourceC1724 difference raw25143; decide +kernel
    rw [ha]
    exact (canonical25143 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1724 + difference 1 5) (sourceB1724 + difference 5 1) sourceC1724) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4497) := by
    have ha : (tripleCharges (sourceA1724 + difference 1 5) (sourceB1724 + difference 5 1) sourceC1724) = raw25144 := by
      apply Matrix.ext; unfold tripleCharges sourceA1724 sourceB1724 sourceC1724 difference raw25144; decide +kernel
    rw [ha]
    exact (canonical25144 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1724 + difference 2 0) (sourceB1724 + difference 0 2) sourceC1724) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4150) := by
    have ha : (tripleCharges (sourceA1724 + difference 2 0) (sourceB1724 + difference 0 2) sourceC1724) = raw25145 := by
      apply Matrix.ext; unfold tripleCharges sourceA1724 sourceB1724 sourceC1724 difference raw25145; decide +kernel
    rw [ha]
    exact (canonical25145 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1724 + difference 2 1) (sourceB1724 + difference 1 2) sourceC1724) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4364) := by
    have ha : (tripleCharges (sourceA1724 + difference 2 1) (sourceB1724 + difference 1 2) sourceC1724) = raw25146 := by
      apply Matrix.ext; unfold tripleCharges sourceA1724 sourceB1724 sourceC1724 difference raw25146; decide +kernel
    rw [ha]
    exact (canonical25146 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1724 + difference 2 3) (sourceB1724 + difference 3 2) sourceC1724) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4438) := by
    have ha : (tripleCharges (sourceA1724 + difference 2 3) (sourceB1724 + difference 3 2) sourceC1724) = raw25147 := by
      apply Matrix.ext; unfold tripleCharges sourceA1724 sourceB1724 sourceC1724 difference raw25147; decide +kernel
    rw [ha]
    exact (canonical25147 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1724 + difference 2 4) (sourceB1724 + difference 4 2) sourceC1724) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4458) := by
    have ha : (tripleCharges (sourceA1724 + difference 2 4) (sourceB1724 + difference 4 2) sourceC1724) = raw25148 := by
      apply Matrix.ext; unfold tripleCharges sourceA1724 sourceB1724 sourceC1724 difference raw25148; decide +kernel
    rw [ha]
    exact (canonical25148 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1724 + difference 2 5) (sourceB1724 + difference 5 2) sourceC1724) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4456) := by
    have ha : (tripleCharges (sourceA1724 + difference 2 5) (sourceB1724 + difference 5 2) sourceC1724) = raw25149 := by
      apply Matrix.ext; unfold tripleCharges sourceA1724 sourceB1724 sourceC1724 difference raw25149; decide +kernel
    rw [ha]
    exact (canonical25149 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1724 + difference 3 0) (sourceB1724 + difference 0 3) sourceC1724) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4155) := by
    have ha : (tripleCharges (sourceA1724 + difference 3 0) (sourceB1724 + difference 0 3) sourceC1724) = raw25150 := by
      apply Matrix.ext; unfold tripleCharges sourceA1724 sourceB1724 sourceC1724 difference raw25150; decide +kernel
    rw [ha]
    exact (canonical25150 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1724 + difference 3 1) (sourceB1724 + difference 1 3) sourceC1724) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4369) := by
    have ha : (tripleCharges (sourceA1724 + difference 3 1) (sourceB1724 + difference 1 3) sourceC1724) = raw25151 := by
      apply Matrix.ext; unfold tripleCharges sourceA1724 sourceB1724 sourceC1724 difference raw25151; decide +kernel
    rw [ha]
    exact (canonical25151 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1724 + difference 3 2) (sourceB1724 + difference 2 3) sourceC1724) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4329) := by
    have ha : (tripleCharges (sourceA1724 + difference 3 2) (sourceB1724 + difference 2 3) sourceC1724) = raw25152 := by
      apply Matrix.ext; unfold tripleCharges sourceA1724 sourceB1724 sourceC1724 difference raw25152; decide +kernel
    rw [ha]
    exact (canonical25152 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1724 + difference 3 4) (sourceB1724 + difference 4 3) sourceC1724) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4467) := by
    have ha : (tripleCharges (sourceA1724 + difference 3 4) (sourceB1724 + difference 4 3) sourceC1724) = raw25153 := by
      apply Matrix.ext; unfold tripleCharges sourceA1724 sourceB1724 sourceC1724 difference raw25153; decide +kernel
    rw [ha]
    exact (canonical25153 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1724 + difference 3 5) (sourceB1724 + difference 5 3) sourceC1724) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4458) := by
    have ha : (tripleCharges (sourceA1724 + difference 3 5) (sourceB1724 + difference 5 3) sourceC1724) = raw25154 := by
      apply Matrix.ext; unfold tripleCharges sourceA1724 sourceB1724 sourceC1724 difference raw25154; decide +kernel
    rw [ha]
    exact (canonical25154 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1724 + difference 4 0) (sourceB1724 + difference 0 4) sourceC1724) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4158) := by
    have ha : (tripleCharges (sourceA1724 + difference 4 0) (sourceB1724 + difference 0 4) sourceC1724) = raw25155 := by
      apply Matrix.ext; unfold tripleCharges sourceA1724 sourceB1724 sourceC1724 difference raw25155; decide +kernel
    rw [ha]
    exact (canonical25155 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1724 + difference 4 1) (sourceB1724 + difference 1 4) sourceC1724) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4372) := by
    have ha : (tripleCharges (sourceA1724 + difference 4 1) (sourceB1724 + difference 1 4) sourceC1724) = raw25156 := by
      apply Matrix.ext; unfold tripleCharges sourceA1724 sourceB1724 sourceC1724 difference raw25156; decide +kernel
    rw [ha]
    exact (canonical25156 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1724 + difference 4 2) (sourceB1724 + difference 2 4) sourceC1724) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4332) := by
    have ha : (tripleCharges (sourceA1724 + difference 4 2) (sourceB1724 + difference 2 4) sourceC1724) = raw25157 := by
      apply Matrix.ext; unfold tripleCharges sourceA1724 sourceB1724 sourceC1724 difference raw25157; decide +kernel
    rw [ha]
    exact (canonical25157 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1724 + difference 4 3) (sourceB1724 + difference 3 4) sourceC1724) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4444) := by
    have ha : (tripleCharges (sourceA1724 + difference 4 3) (sourceB1724 + difference 3 4) sourceC1724) = raw25158 := by
      apply Matrix.ext; unfold tripleCharges sourceA1724 sourceB1724 sourceC1724 difference raw25158; decide +kernel
    rw [ha]
    exact (canonical25158 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1724 + difference 4 5) (sourceB1724 + difference 5 4) sourceC1724) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4461) := by
    have ha : (tripleCharges (sourceA1724 + difference 4 5) (sourceB1724 + difference 5 4) sourceC1724) = raw25159 := by
      apply Matrix.ext; unfold tripleCharges sourceA1724 sourceB1724 sourceC1724 difference raw25159; decide +kernel
    rw [ha]
    exact (canonical25159 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1724 + difference 5 0) (sourceB1724 + difference 0 5) sourceC1724) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4153) := by
    have ha : (tripleCharges (sourceA1724 + difference 5 0) (sourceB1724 + difference 0 5) sourceC1724) = raw25160 := by
      apply Matrix.ext; unfold tripleCharges sourceA1724 sourceB1724 sourceC1724 difference raw25160; decide +kernel
    rw [ha]
    exact (canonical25160 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1724 + difference 5 1) (sourceB1724 + difference 1 5) sourceC1724) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4367) := by
    have ha : (tripleCharges (sourceA1724 + difference 5 1) (sourceB1724 + difference 1 5) sourceC1724) = raw25161 := by
      apply Matrix.ext; unfold tripleCharges sourceA1724 sourceB1724 sourceC1724 difference raw25161; decide +kernel
    rw [ha]
    exact (canonical25161 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1724 + difference 5 2) (sourceB1724 + difference 2 5) sourceC1724) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4327) := by
    have ha : (tripleCharges (sourceA1724 + difference 5 2) (sourceB1724 + difference 2 5) sourceC1724) = raw25162 := by
      apply Matrix.ext; unfold tripleCharges sourceA1724 sourceB1724 sourceC1724 difference raw25162; decide +kernel
    rw [ha]
    exact (canonical25162 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1724 + difference 5 3) (sourceB1724 + difference 3 5) sourceC1724) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4440) := by
    have ha : (tripleCharges (sourceA1724 + difference 5 3) (sourceB1724 + difference 3 5) sourceC1724) = raw25163 := by
      apply Matrix.ext; unfold tripleCharges sourceA1724 sourceB1724 sourceC1724 difference raw25163; decide +kernel
    rw [ha]
    exact (canonical25163 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1724 + difference 5 4) (sourceB1724 + difference 4 5) sourceC1724) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4463) := by
    have ha : (tripleCharges (sourceA1724 + difference 5 4) (sourceB1724 + difference 4 5) sourceC1724) = raw25164 := by
      apply Matrix.ext; unfold tripleCharges sourceA1724 sourceB1724 sourceC1724 difference raw25164; decide +kernel
    rw [ha]
    exact (canonical25164 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1724 sourceB1724 sourceC1724
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1724, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic91
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reindexCheck1456 : Integer.Sparse.reindex keyMap MixedData.row1456 = numericRow1456 := by decide +kernel

theorem numericCheck1456 (x : Master → ℝ) : Integer.Sparse.eval numericRow1456 x =
    (1 : ℝ) * reducedSource1456 x := by
  norm_num [numericRow1456, reducedSource1456, Integer.Sparse.eval, Sparse.eval, nodeValue988, nodeValue1922, nodeValue2118, nodeValue2195, nodeValue2214, nodeValue2216, nodeValue4080]

theorem reindexCheck1457 : Integer.Sparse.reindex keyMap MixedData.row1457 = numericRow1457 := by decide +kernel

theorem numericCheck1457 (x : Master → ℝ) : Integer.Sparse.eval numericRow1457 x =
    (1 : ℝ) * reducedSource1457 x := by
  norm_num [numericRow1457, reducedSource1457, Integer.Sparse.eval, Sparse.eval, nodeValue987, nodeValue1921, nodeValue2117, nodeValue2213, nodeValue2215, nodeValue4082]

theorem reindexCheck1458 : Integer.Sparse.reindex keyMap MixedData.row1458 = numericRow1458 := by decide +kernel

theorem numericCheck1458 (x : Master → ℝ) : Integer.Sparse.eval numericRow1458 x =
    (1 : ℝ) * reducedSource1458 x := by
  norm_num [numericRow1458, reducedSource1458, Integer.Sparse.eval, Sparse.eval, nodeValue1023, nodeValue2091, nodeValue2234, nodeValue2241, nodeValue4079]

theorem reindexCheck1459 : Integer.Sparse.reindex keyMap MixedData.row1459 = numericRow1459 := by decide +kernel

theorem numericCheck1459 (x : Master → ℝ) : Integer.Sparse.eval numericRow1459 x =
    (1 : ℝ) * reducedSource1459 x := by
  norm_num [numericRow1459, reducedSource1459, Integer.Sparse.eval, Sparse.eval, nodeValue1018, nodeValue1023, nodeValue1034, nodeValue2241, nodeValue4079]

theorem reindexCheck1460 : Integer.Sparse.reindex keyMap MixedData.row1460 = numericRow1460 := by decide +kernel

theorem numericCheck1460 (x : Master → ℝ) : Integer.Sparse.eval numericRow1460 x =
    (1 : ℝ) * reducedSource1460 x := by
  norm_num [numericRow1460, reducedSource1460, Integer.Sparse.eval, Sparse.eval, nodeValue1018, nodeValue2086, nodeValue2191, nodeValue2232, nodeValue2241, nodeValue4079]

theorem reindexCheck1461 : Integer.Sparse.reindex keyMap MixedData.row1461 = numericRow1461 := by decide +kernel

theorem numericCheck1461 (x : Master → ℝ) : Integer.Sparse.eval numericRow1461 x =
    (1 : ℝ) * reducedSource1461 x := by
  norm_num [numericRow1461, reducedSource1461, Integer.Sparse.eval, Sparse.eval, nodeValue1017, nodeValue2085, nodeValue2190, nodeValue2240, nodeValue2242, nodeValue4080]

theorem reindexCheck1462 : Integer.Sparse.reindex keyMap MixedData.row1462 = numericRow1462 := by decide +kernel

theorem numericCheck1462 (x : Master → ℝ) : Integer.Sparse.eval numericRow1462 x =
    (1 : ℝ) * reducedSource1462 x := by
  norm_num [numericRow1462, reducedSource1462, Integer.Sparse.eval, Sparse.eval, nodeValue1045, nodeValue2024, nodeValue2111, nodeValue2246, nodeValue2254, nodeValue2260, nodeValue4080]

theorem reindexCheck1463 : Integer.Sparse.reindex keyMap MixedData.row1463 = numericRow1463 := by decide +kernel

theorem numericCheck1463 (x : Master → ℝ) : Integer.Sparse.eval numericRow1463 x =
    (1 : ℝ) * reducedSource1463 x := by
  norm_num [numericRow1463, reducedSource1463, Integer.Sparse.eval, Sparse.eval, nodeValue1032, nodeValue1035, nodeValue1036, nodeValue1045, nodeValue1073, nodeValue2260, nodeValue4080]

theorem reindexCheck1464 : Integer.Sparse.reindex keyMap MixedData.row1464 = numericRow1464 := by decide +kernel

theorem numericCheck1464 (x : Master → ℝ) : Integer.Sparse.eval numericRow1464 x =
    (1 : ℝ) * reducedSource1464 x := by
  norm_num [numericRow1464, reducedSource1464, Integer.Sparse.eval, Sparse.eval, nodeValue1036, nodeValue2017, nodeValue2102, nodeValue2206, nodeValue2251, nodeValue2260, nodeValue4080]

theorem reindexCheck1465 : Integer.Sparse.reindex keyMap MixedData.row1465 = numericRow1465 := by decide +kernel

theorem numericCheck1465 (x : Master → ℝ) : Integer.Sparse.eval numericRow1465 x =
    (4 : ℝ) * reducedSource1465 x := by
  norm_num [numericRow1465, reducedSource1465, Integer.Sparse.eval, Sparse.eval, nodeValue4152, nodeValue4157, nodeValue4158, nodeValue4182, nodeValue4331, nodeValue4332, nodeValue4351, nodeValue4366, nodeValue4371, nodeValue4372, nodeValue4439, nodeValue4442, nodeValue4444, nodeValue4456, nodeValue4458, nodeValue4461, nodeValue4497, nodeValue4805, nodeValue4869, nodeValue4889, nodeValue4893] <;> ring

theorem reindexCheck1466 : Integer.Sparse.reindex keyMap MixedData.row1466 = numericRow1466 := by decide +kernel

theorem numericCheck1466 (x : Master → ℝ) : Integer.Sparse.eval numericRow1466 x =
    (1 : ℝ) * reducedSource1466 x := by
  norm_num [numericRow1466, reducedSource1466, Integer.Sparse.eval, Sparse.eval, nodeValue1510, nodeValue1522, nodeValue1524, nodeValue1528, nodeValue1678, nodeValue1680, nodeValue1684, nodeValue1706, nodeValue1711, nodeValue1713, nodeValue1724, nodeValue1726, nodeValue1734, nodeValue1736, nodeValue1737, nodeValue1742, nodeValue1744, nodeValue2214, nodeValue2263, nodeValue2275, nodeValue2277]

theorem reindexCheck1467 : Integer.Sparse.reindex keyMap MixedData.row1467 = numericRow1467 := by decide +kernel

theorem numericCheck1467 (x : Master → ℝ) : Integer.Sparse.eval numericRow1467 x =
    (1 : ℝ) * reducedSource1467 x := by
  norm_num [numericRow1467, reducedSource1467, Integer.Sparse.eval, Sparse.eval, nodeValue610, nodeValue929, nodeValue1044, nodeValue1081, nodeValue4083]

theorem reindexCheck1468 : Integer.Sparse.reindex keyMap MixedData.row1468 = numericRow1468 := by decide +kernel

theorem numericCheck1468 (x : Master → ℝ) : Integer.Sparse.eval numericRow1468 x =
    (1 : ℝ) * reducedSource1468 x := by
  norm_num [numericRow1468, reducedSource1468, Integer.Sparse.eval, Sparse.eval, nodeValue944, nodeValue949, nodeValue950, nodeValue1044, nodeValue2110, nodeValue4083]

theorem reindexCheck1471 : Integer.Sparse.reindex keyMap MixedData.row1471 = numericRow1471 := by decide +kernel

theorem numericCheck1471 (x : Master → ℝ) : Integer.Sparse.eval numericRow1471 x =
    (4 : ℝ) * reducedSource1471 x := by
  norm_num [numericRow1471, reducedSource1471, Integer.Sparse.eval, Sparse.eval, nodeValue4150, nodeValue4153, nodeValue4155, nodeValue4158, nodeValue4175, nodeValue4327, nodeValue4329, nodeValue4332, nodeValue4344, nodeValue4364, nodeValue4367, nodeValue4369, nodeValue4372, nodeValue4438, nodeValue4440, nodeValue4444, nodeValue4456, nodeValue4458, nodeValue4461, nodeValue4463, nodeValue4467, nodeValue4497, nodeValue4502, nodeValue4802, nodeValue4866, nodeValue4888, nodeValue4893, nodeValue4895] <;> ring

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Rows91
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero1456 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1456 (mixedVector B) = 0 := by
  have h988 : mixedVector B (Sum.inr 988) = Sparse.eval nodeValue988 (mixedVector B) := by
    change mixedMoment B node988 node988Labels = _
    exact sound988 B hB hF
  have h1922 : mixedVector B (Sum.inr 1922) = Sparse.eval nodeValue1922 (mixedVector B) := by
    change mixedMoment B node1922 node1922Labels = _
    exact sound1922 B hB hF
  have h2118 : mixedVector B (Sum.inr 2118) = Sparse.eval nodeValue2118 (mixedVector B) := by
    change mixedMoment B node2118 node2118Labels = _
    exact sound2118 B hB hF
  have h2195 : mixedVector B (Sum.inr 2195) = Sparse.eval nodeValue2195 (mixedVector B) := by
    change mixedMoment B node2195 node2195Labels = _
    exact sound2195 B hB hF
  have h2214 : mixedVector B (Sum.inr 2214) = Sparse.eval nodeValue2214 (mixedVector B) := by
    change mixedMoment B node2214 node2214Labels = _
    exact sound2214 B hB hF
  have h2216 : mixedVector B (Sum.inr 2216) = Sparse.eval nodeValue2216 (mixedVector B) := by
    change mixedMoment B node2216 node2216Labels = _
    exact sound2216 B hB hF
  have h4080 : mixedVector B (Sum.inr 4080) = Sparse.eval nodeValue4080 (mixedVector B) := by
    change mixedMoment B node4080 node4080Labels = _
    exact sound4080 B hB hF
  simpa only [sourceForm1707, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h988, h1922, h2118, h2195, h2214, h2216, h4080, reducedSource1456] using sourceEq1707 B hB

theorem rowSound1456 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1456 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1456, numericCheck1456, reducedZero1456 B hB hF, mul_zero]

theorem reducedZero1457 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1457 (mixedVector B) = 0 := by
  have h987 : mixedVector B (Sum.inr 987) = Sparse.eval nodeValue987 (mixedVector B) := by
    change mixedMoment B node987 node987Labels = _
    exact sound987 B hB hF
  have h1921 : mixedVector B (Sum.inr 1921) = Sparse.eval nodeValue1921 (mixedVector B) := by
    change mixedMoment B node1921 node1921Labels = _
    exact sound1921 B hB hF
  have h2117 : mixedVector B (Sum.inr 2117) = Sparse.eval nodeValue2117 (mixedVector B) := by
    change mixedMoment B node2117 node2117Labels = _
    exact sound2117 B hB hF
  have h2213 : mixedVector B (Sum.inr 2213) = Sparse.eval nodeValue2213 (mixedVector B) := by
    change mixedMoment B node2213 node2213Labels = _
    exact sound2213 B hB hF
  have h2215 : mixedVector B (Sum.inr 2215) = Sparse.eval nodeValue2215 (mixedVector B) := by
    change mixedMoment B node2215 node2215Labels = _
    exact sound2215 B hB hF
  have h4082 : mixedVector B (Sum.inr 4082) = Sparse.eval nodeValue4082 (mixedVector B) := by
    change mixedMoment B node4082 node4082Labels = _
    exact sound4082 B hB hF
  simpa only [sourceForm1708, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h987, h1921, h2117, h2213, h2215, h4082, reducedSource1457] using sourceEq1708 B hB

theorem rowSound1457 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1457 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1457, numericCheck1457, reducedZero1457 B hB hF, mul_zero]

theorem reducedZero1458 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1458 (mixedVector B) = 0 := by
  have h1023 : mixedVector B (Sum.inr 1023) = Sparse.eval nodeValue1023 (mixedVector B) := by
    change mixedMoment B node1023 node1023Labels = _
    exact sound1023 B hB hF
  have h2091 : mixedVector B (Sum.inr 2091) = Sparse.eval nodeValue2091 (mixedVector B) := by
    change mixedMoment B node2091 node2091Labels = _
    exact sound2091 B hB hF
  have h2234 : mixedVector B (Sum.inr 2234) = Sparse.eval nodeValue2234 (mixedVector B) := by
    change mixedMoment B node2234 node2234Labels = _
    exact sound2234 B hB hF
  have h2241 : mixedVector B (Sum.inr 2241) = Sparse.eval nodeValue2241 (mixedVector B) := by
    change mixedMoment B node2241 node2241Labels = _
    exact sound2241 B hB hF
  have h4079 : mixedVector B (Sum.inr 4079) = Sparse.eval nodeValue4079 (mixedVector B) := by
    change mixedMoment B node4079 node4079Labels = _
    exact sound4079 B hB hF
  simpa only [sourceForm1709, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1023, h2091, h2234, h2241, h4079, reducedSource1458] using sourceEq1709 B hB

theorem rowSound1458 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1458 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1458, numericCheck1458, reducedZero1458 B hB hF, mul_zero]

theorem reducedZero1459 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1459 (mixedVector B) = 0 := by
  have h1018 : mixedVector B (Sum.inr 1018) = Sparse.eval nodeValue1018 (mixedVector B) := by
    change mixedMoment B node1018 node1018Labels = _
    exact sound1018 B hB hF
  have h1023 : mixedVector B (Sum.inr 1023) = Sparse.eval nodeValue1023 (mixedVector B) := by
    change mixedMoment B node1023 node1023Labels = _
    exact sound1023 B hB hF
  have h1034 : mixedVector B (Sum.inr 1034) = Sparse.eval nodeValue1034 (mixedVector B) := by
    change mixedMoment B node1034 node1034Labels = _
    exact sound1034 B hB hF
  have h2241 : mixedVector B (Sum.inr 2241) = Sparse.eval nodeValue2241 (mixedVector B) := by
    change mixedMoment B node2241 node2241Labels = _
    exact sound2241 B hB hF
  have h4079 : mixedVector B (Sum.inr 4079) = Sparse.eval nodeValue4079 (mixedVector B) := by
    change mixedMoment B node4079 node4079Labels = _
    exact sound4079 B hB hF
  simpa only [sourceForm1710, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1018, h1023, h1034, h2241, h4079, reducedSource1459] using sourceEq1710 B hB

theorem rowSound1459 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1459 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1459, numericCheck1459, reducedZero1459 B hB hF, mul_zero]

theorem reducedZero1460 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1460 (mixedVector B) = 0 := by
  have h1018 : mixedVector B (Sum.inr 1018) = Sparse.eval nodeValue1018 (mixedVector B) := by
    change mixedMoment B node1018 node1018Labels = _
    exact sound1018 B hB hF
  have h2086 : mixedVector B (Sum.inr 2086) = Sparse.eval nodeValue2086 (mixedVector B) := by
    change mixedMoment B node2086 node2086Labels = _
    exact sound2086 B hB hF
  have h2191 : mixedVector B (Sum.inr 2191) = Sparse.eval nodeValue2191 (mixedVector B) := by
    change mixedMoment B node2191 node2191Labels = _
    exact sound2191 B hB hF
  have h2232 : mixedVector B (Sum.inr 2232) = Sparse.eval nodeValue2232 (mixedVector B) := by
    change mixedMoment B node2232 node2232Labels = _
    exact sound2232 B hB hF
  have h2241 : mixedVector B (Sum.inr 2241) = Sparse.eval nodeValue2241 (mixedVector B) := by
    change mixedMoment B node2241 node2241Labels = _
    exact sound2241 B hB hF
  have h4079 : mixedVector B (Sum.inr 4079) = Sparse.eval nodeValue4079 (mixedVector B) := by
    change mixedMoment B node4079 node4079Labels = _
    exact sound4079 B hB hF
  simpa only [sourceForm1711, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1018, h2086, h2191, h2232, h2241, h4079, reducedSource1460] using sourceEq1711 B hB

theorem rowSound1460 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1460 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1460, numericCheck1460, reducedZero1460 B hB hF, mul_zero]

theorem reducedZero1461 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1461 (mixedVector B) = 0 := by
  have h1017 : mixedVector B (Sum.inr 1017) = Sparse.eval nodeValue1017 (mixedVector B) := by
    change mixedMoment B node1017 node1017Labels = _
    exact sound1017 B hB hF
  have h2085 : mixedVector B (Sum.inr 2085) = Sparse.eval nodeValue2085 (mixedVector B) := by
    change mixedMoment B node2085 node2085Labels = _
    exact sound2085 B hB hF
  have h2190 : mixedVector B (Sum.inr 2190) = Sparse.eval nodeValue2190 (mixedVector B) := by
    change mixedMoment B node2190 node2190Labels = _
    exact sound2190 B hB hF
  have h2240 : mixedVector B (Sum.inr 2240) = Sparse.eval nodeValue2240 (mixedVector B) := by
    change mixedMoment B node2240 node2240Labels = _
    exact sound2240 B hB hF
  have h2242 : mixedVector B (Sum.inr 2242) = Sparse.eval nodeValue2242 (mixedVector B) := by
    change mixedMoment B node2242 node2242Labels = _
    exact sound2242 B hB hF
  have h4080 : mixedVector B (Sum.inr 4080) = Sparse.eval nodeValue4080 (mixedVector B) := by
    change mixedMoment B node4080 node4080Labels = _
    exact sound4080 B hB hF
  simpa only [sourceForm1712, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1017, h2085, h2190, h2240, h2242, h4080, reducedSource1461] using sourceEq1712 B hB

theorem rowSound1461 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1461 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1461, numericCheck1461, reducedZero1461 B hB hF, mul_zero]

theorem reducedZero1462 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1462 (mixedVector B) = 0 := by
  have h1045 : mixedVector B (Sum.inr 1045) = Sparse.eval nodeValue1045 (mixedVector B) := by
    change mixedMoment B node1045 node1045Labels = _
    exact sound1045 B hB hF
  have h2024 : mixedVector B (Sum.inr 2024) = Sparse.eval nodeValue2024 (mixedVector B) := by
    change mixedMoment B node2024 node2024Labels = _
    exact sound2024 B hB hF
  have h2111 : mixedVector B (Sum.inr 2111) = Sparse.eval nodeValue2111 (mixedVector B) := by
    change mixedMoment B node2111 node2111Labels = _
    exact sound2111 B hB hF
  have h2246 : mixedVector B (Sum.inr 2246) = Sparse.eval nodeValue2246 (mixedVector B) := by
    change mixedMoment B node2246 node2246Labels = _
    exact sound2246 B hB hF
  have h2254 : mixedVector B (Sum.inr 2254) = Sparse.eval nodeValue2254 (mixedVector B) := by
    change mixedMoment B node2254 node2254Labels = _
    exact sound2254 B hB hF
  have h2260 : mixedVector B (Sum.inr 2260) = Sparse.eval nodeValue2260 (mixedVector B) := by
    change mixedMoment B node2260 node2260Labels = _
    exact sound2260 B hB hF
  have h4080 : mixedVector B (Sum.inr 4080) = Sparse.eval nodeValue4080 (mixedVector B) := by
    change mixedMoment B node4080 node4080Labels = _
    exact sound4080 B hB hF
  simpa only [sourceForm1713, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1045, h2024, h2111, h2246, h2254, h2260, h4080, reducedSource1462] using sourceEq1713 B hB

theorem rowSound1462 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1462 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1462, numericCheck1462, reducedZero1462 B hB hF, mul_zero]

theorem reducedZero1463 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1463 (mixedVector B) = 0 := by
  have h1032 : mixedVector B (Sum.inr 1032) = Sparse.eval nodeValue1032 (mixedVector B) := by
    change mixedMoment B node1032 node1032Labels = _
    exact sound1032 B hB hF
  have h1035 : mixedVector B (Sum.inr 1035) = Sparse.eval nodeValue1035 (mixedVector B) := by
    change mixedMoment B node1035 node1035Labels = _
    exact sound1035 B hB hF
  have h1036 : mixedVector B (Sum.inr 1036) = Sparse.eval nodeValue1036 (mixedVector B) := by
    change mixedMoment B node1036 node1036Labels = _
    exact sound1036 B hB hF
  have h1045 : mixedVector B (Sum.inr 1045) = Sparse.eval nodeValue1045 (mixedVector B) := by
    change mixedMoment B node1045 node1045Labels = _
    exact sound1045 B hB hF
  have h1073 : mixedVector B (Sum.inr 1073) = Sparse.eval nodeValue1073 (mixedVector B) := by
    change mixedMoment B node1073 node1073Labels = _
    exact sound1073 B hB hF
  have h2260 : mixedVector B (Sum.inr 2260) = Sparse.eval nodeValue2260 (mixedVector B) := by
    change mixedMoment B node2260 node2260Labels = _
    exact sound2260 B hB hF
  have h4080 : mixedVector B (Sum.inr 4080) = Sparse.eval nodeValue4080 (mixedVector B) := by
    change mixedMoment B node4080 node4080Labels = _
    exact sound4080 B hB hF
  simpa only [sourceForm1714, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1032, h1035, h1036, h1045, h1073, h2260, h4080, reducedSource1463] using sourceEq1714 B hB

theorem rowSound1463 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1463 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1463, numericCheck1463, reducedZero1463 B hB hF, mul_zero]

theorem reducedZero1464 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1464 (mixedVector B) = 0 := by
  have h1036 : mixedVector B (Sum.inr 1036) = Sparse.eval nodeValue1036 (mixedVector B) := by
    change mixedMoment B node1036 node1036Labels = _
    exact sound1036 B hB hF
  have h2017 : mixedVector B (Sum.inr 2017) = Sparse.eval nodeValue2017 (mixedVector B) := by
    change mixedMoment B node2017 node2017Labels = _
    exact sound2017 B hB hF
  have h2102 : mixedVector B (Sum.inr 2102) = Sparse.eval nodeValue2102 (mixedVector B) := by
    change mixedMoment B node2102 node2102Labels = _
    exact sound2102 B hB hF
  have h2206 : mixedVector B (Sum.inr 2206) = Sparse.eval nodeValue2206 (mixedVector B) := by
    change mixedMoment B node2206 node2206Labels = _
    exact sound2206 B hB hF
  have h2251 : mixedVector B (Sum.inr 2251) = Sparse.eval nodeValue2251 (mixedVector B) := by
    change mixedMoment B node2251 node2251Labels = _
    exact sound2251 B hB hF
  have h2260 : mixedVector B (Sum.inr 2260) = Sparse.eval nodeValue2260 (mixedVector B) := by
    change mixedMoment B node2260 node2260Labels = _
    exact sound2260 B hB hF
  have h4080 : mixedVector B (Sum.inr 4080) = Sparse.eval nodeValue4080 (mixedVector B) := by
    change mixedMoment B node4080 node4080Labels = _
    exact sound4080 B hB hF
  simpa only [sourceForm1715, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1036, h2017, h2102, h2206, h2251, h2260, h4080, reducedSource1464] using sourceEq1715 B hB

theorem rowSound1464 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1464 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1464, numericCheck1464, reducedZero1464 B hB hF, mul_zero]

theorem reducedZero1465 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1465 (mixedVector B) = 0 := by
  have h4152 : mixedVector B (Sum.inr 4152) = Sparse.eval nodeValue4152 (mixedVector B) := by
    change mixedMoment B node4152 node4152Labels = _
    exact sound4152 B hB hF
  have h4157 : mixedVector B (Sum.inr 4157) = Sparse.eval nodeValue4157 (mixedVector B) := by
    change mixedMoment B node4157 node4157Labels = _
    exact sound4157 B hB hF
  have h4158 : mixedVector B (Sum.inr 4158) = Sparse.eval nodeValue4158 (mixedVector B) := by
    change mixedMoment B node4158 node4158Labels = _
    exact sound4158 B hB hF
  have h4182 : mixedVector B (Sum.inr 4182) = Sparse.eval nodeValue4182 (mixedVector B) := by
    change mixedMoment B node4182 node4182Labels = _
    exact sound4182 B hB hF
  have h4331 : mixedVector B (Sum.inr 4331) = Sparse.eval nodeValue4331 (mixedVector B) := by
    change mixedMoment B node4331 node4331Labels = _
    exact sound4331 B hB hF
  have h4332 : mixedVector B (Sum.inr 4332) = Sparse.eval nodeValue4332 (mixedVector B) := by
    change mixedMoment B node4332 node4332Labels = _
    exact sound4332 B hB hF
  have h4351 : mixedVector B (Sum.inr 4351) = Sparse.eval nodeValue4351 (mixedVector B) := by
    change mixedMoment B node4351 node4351Labels = _
    exact sound4351 B hB hF
  have h4366 : mixedVector B (Sum.inr 4366) = Sparse.eval nodeValue4366 (mixedVector B) := by
    change mixedMoment B node4366 node4366Labels = _
    exact sound4366 B hB hF
  have h4371 : mixedVector B (Sum.inr 4371) = Sparse.eval nodeValue4371 (mixedVector B) := by
    change mixedMoment B node4371 node4371Labels = _
    exact sound4371 B hB hF
  have h4372 : mixedVector B (Sum.inr 4372) = Sparse.eval nodeValue4372 (mixedVector B) := by
    change mixedMoment B node4372 node4372Labels = _
    exact sound4372 B hB hF
  have h4439 : mixedVector B (Sum.inr 4439) = Sparse.eval nodeValue4439 (mixedVector B) := by
    change mixedMoment B node4439 node4439Labels = _
    exact sound4439 B hB hF
  have h4442 : mixedVector B (Sum.inr 4442) = Sparse.eval nodeValue4442 (mixedVector B) := by
    change mixedMoment B node4442 node4442Labels = _
    exact sound4442 B hB hF
  have h4444 : mixedVector B (Sum.inr 4444) = Sparse.eval nodeValue4444 (mixedVector B) := by
    change mixedMoment B node4444 node4444Labels = _
    exact sound4444 B hB hF
  have h4456 : mixedVector B (Sum.inr 4456) = Sparse.eval nodeValue4456 (mixedVector B) := by
    change mixedMoment B node4456 node4456Labels = _
    exact sound4456 B hB hF
  have h4458 : mixedVector B (Sum.inr 4458) = Sparse.eval nodeValue4458 (mixedVector B) := by
    change mixedMoment B node4458 node4458Labels = _
    exact sound4458 B hB hF
  have h4461 : mixedVector B (Sum.inr 4461) = Sparse.eval nodeValue4461 (mixedVector B) := by
    change mixedMoment B node4461 node4461Labels = _
    exact sound4461 B hB hF
  have h4497 : mixedVector B (Sum.inr 4497) = Sparse.eval nodeValue4497 (mixedVector B) := by
    change mixedMoment B node4497 node4497Labels = _
    exact sound4497 B hB hF
  have h4805 : mixedVector B (Sum.inr 4805) = Sparse.eval nodeValue4805 (mixedVector B) := by
    change mixedMoment B node4805 node4805Labels = _
    exact sound4805 B hB hF
  have h4869 : mixedVector B (Sum.inr 4869) = Sparse.eval nodeValue4869 (mixedVector B) := by
    change mixedMoment B node4869 node4869Labels = _
    exact sound4869 B hB hF
  have h4889 : mixedVector B (Sum.inr 4889) = Sparse.eval nodeValue4889 (mixedVector B) := by
    change mixedMoment B node4889 node4889Labels = _
    exact sound4889 B hB hF
  have h4893 : mixedVector B (Sum.inr 4893) = Sparse.eval nodeValue4893 (mixedVector B) := by
    change mixedMoment B node4893 node4893Labels = _
    exact sound4893 B hB hF
  simpa only [sourceForm1716, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4152, h4157, h4158, h4182, h4331, h4332, h4351, h4366, h4371, h4372, h4439, h4442, h4444, h4456, h4458, h4461, h4497, h4805, h4869, h4889, h4893, reducedSource1465] using sourceEq1716 B hB

theorem rowSound1465 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1465 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1465, numericCheck1465, reducedZero1465 B hB hF, mul_zero]

theorem reducedZero1466 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1466 (mixedVector B) = 0 := by
  have h1510 : mixedVector B (Sum.inr 1510) = Sparse.eval nodeValue1510 (mixedVector B) := by
    change mixedMoment B node1510 node1510Labels = _
    exact sound1510 B hB hF
  have h1522 : mixedVector B (Sum.inr 1522) = Sparse.eval nodeValue1522 (mixedVector B) := by
    change mixedMoment B node1522 node1522Labels = _
    exact sound1522 B hB hF
  have h1524 : mixedVector B (Sum.inr 1524) = Sparse.eval nodeValue1524 (mixedVector B) := by
    change mixedMoment B node1524 node1524Labels = _
    exact sound1524 B hB hF
  have h1528 : mixedVector B (Sum.inr 1528) = Sparse.eval nodeValue1528 (mixedVector B) := by
    change mixedMoment B node1528 node1528Labels = _
    exact sound1528 B hB hF
  have h1678 : mixedVector B (Sum.inr 1678) = Sparse.eval nodeValue1678 (mixedVector B) := by
    change mixedMoment B node1678 node1678Labels = _
    exact sound1678 B hB hF
  have h1680 : mixedVector B (Sum.inr 1680) = Sparse.eval nodeValue1680 (mixedVector B) := by
    change mixedMoment B node1680 node1680Labels = _
    exact sound1680 B hB hF
  have h1684 : mixedVector B (Sum.inr 1684) = Sparse.eval nodeValue1684 (mixedVector B) := by
    change mixedMoment B node1684 node1684Labels = _
    exact sound1684 B hB hF
  have h1706 : mixedVector B (Sum.inr 1706) = Sparse.eval nodeValue1706 (mixedVector B) := by
    change mixedMoment B node1706 node1706Labels = _
    exact sound1706 B hB hF
  have h1711 : mixedVector B (Sum.inr 1711) = Sparse.eval nodeValue1711 (mixedVector B) := by
    change mixedMoment B node1711 node1711Labels = _
    exact sound1711 B hB hF
  have h1713 : mixedVector B (Sum.inr 1713) = Sparse.eval nodeValue1713 (mixedVector B) := by
    change mixedMoment B node1713 node1713Labels = _
    exact sound1713 B hB hF
  have h1724 : mixedVector B (Sum.inr 1724) = Sparse.eval nodeValue1724 (mixedVector B) := by
    change mixedMoment B node1724 node1724Labels = _
    exact sound1724 B hB hF
  have h1726 : mixedVector B (Sum.inr 1726) = Sparse.eval nodeValue1726 (mixedVector B) := by
    change mixedMoment B node1726 node1726Labels = _
    exact sound1726 B hB hF
  have h1734 : mixedVector B (Sum.inr 1734) = Sparse.eval nodeValue1734 (mixedVector B) := by
    change mixedMoment B node1734 node1734Labels = _
    exact sound1734 B hB hF
  have h1736 : mixedVector B (Sum.inr 1736) = Sparse.eval nodeValue1736 (mixedVector B) := by
    change mixedMoment B node1736 node1736Labels = _
    exact sound1736 B hB hF
  have h1737 : mixedVector B (Sum.inr 1737) = Sparse.eval nodeValue1737 (mixedVector B) := by
    change mixedMoment B node1737 node1737Labels = _
    exact sound1737 B hB hF
  have h1742 : mixedVector B (Sum.inr 1742) = Sparse.eval nodeValue1742 (mixedVector B) := by
    change mixedMoment B node1742 node1742Labels = _
    exact sound1742 B hB hF
  have h1744 : mixedVector B (Sum.inr 1744) = Sparse.eval nodeValue1744 (mixedVector B) := by
    change mixedMoment B node1744 node1744Labels = _
    exact sound1744 B hB hF
  have h2214 : mixedVector B (Sum.inr 2214) = Sparse.eval nodeValue2214 (mixedVector B) := by
    change mixedMoment B node2214 node2214Labels = _
    exact sound2214 B hB hF
  have h2263 : mixedVector B (Sum.inr 2263) = Sparse.eval nodeValue2263 (mixedVector B) := by
    change mixedMoment B node2263 node2263Labels = _
    exact sound2263 B hB hF
  have h2275 : mixedVector B (Sum.inr 2275) = Sparse.eval nodeValue2275 (mixedVector B) := by
    change mixedMoment B node2275 node2275Labels = _
    exact sound2275 B hB hF
  have h2277 : mixedVector B (Sum.inr 2277) = Sparse.eval nodeValue2277 (mixedVector B) := by
    change mixedMoment B node2277 node2277Labels = _
    exact sound2277 B hB hF
  simpa only [sourceForm1717, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1510, h1522, h1524, h1528, h1678, h1680, h1684, h1706, h1711, h1713, h1724, h1726, h1734, h1736, h1737, h1742, h1744, h2214, h2263, h2275, h2277, reducedSource1466] using sourceEq1717 B hB

theorem rowSound1466 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1466 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1466, numericCheck1466, reducedZero1466 B hB hF, mul_zero]

theorem reducedZero1467 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1467 (mixedVector B) = 0 := by
  have h610 : mixedVector B (Sum.inr 610) = Sparse.eval nodeValue610 (mixedVector B) := by
    change mixedMoment B node610 node610Labels = _
    exact sound610 B hB hF
  have h929 : mixedVector B (Sum.inr 929) = Sparse.eval nodeValue929 (mixedVector B) := by
    change mixedMoment B node929 node929Labels = _
    exact sound929 B hB hF
  have h1044 : mixedVector B (Sum.inr 1044) = Sparse.eval nodeValue1044 (mixedVector B) := by
    change mixedMoment B node1044 node1044Labels = _
    exact sound1044 B hB hF
  have h1081 : mixedVector B (Sum.inr 1081) = Sparse.eval nodeValue1081 (mixedVector B) := by
    change mixedMoment B node1081 node1081Labels = _
    exact sound1081 B hB hF
  have h4083 : mixedVector B (Sum.inr 4083) = Sparse.eval nodeValue4083 (mixedVector B) := by
    change mixedMoment B node4083 node4083Labels = _
    exact sound4083 B hB hF
  simpa only [sourceForm1718, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h610, h929, h1044, h1081, h4083, reducedSource1467] using sourceEq1718 B hB

theorem rowSound1467 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1467 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1467, numericCheck1467, reducedZero1467 B hB hF, mul_zero]

theorem reducedZero1468 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1468 (mixedVector B) = 0 := by
  have h944 : mixedVector B (Sum.inr 944) = Sparse.eval nodeValue944 (mixedVector B) := by
    change mixedMoment B node944 node944Labels = _
    exact sound944 B hB hF
  have h949 : mixedVector B (Sum.inr 949) = Sparse.eval nodeValue949 (mixedVector B) := by
    change mixedMoment B node949 node949Labels = _
    exact sound949 B hB hF
  have h950 : mixedVector B (Sum.inr 950) = Sparse.eval nodeValue950 (mixedVector B) := by
    change mixedMoment B node950 node950Labels = _
    exact sound950 B hB hF
  have h1044 : mixedVector B (Sum.inr 1044) = Sparse.eval nodeValue1044 (mixedVector B) := by
    change mixedMoment B node1044 node1044Labels = _
    exact sound1044 B hB hF
  have h2110 : mixedVector B (Sum.inr 2110) = Sparse.eval nodeValue2110 (mixedVector B) := by
    change mixedMoment B node2110 node2110Labels = _
    exact sound2110 B hB hF
  have h4083 : mixedVector B (Sum.inr 4083) = Sparse.eval nodeValue4083 (mixedVector B) := by
    change mixedMoment B node4083 node4083Labels = _
    exact sound4083 B hB hF
  simpa only [sourceForm1719, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h944, h949, h950, h1044, h2110, h4083, reducedSource1468] using sourceEq1719 B hB

theorem rowSound1468 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1468 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1468, numericCheck1468, reducedZero1468 B hB hF, mul_zero]

theorem reducedZero1471 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1471 (mixedVector B) = 0 := by
  have h4150 : mixedVector B (Sum.inr 4150) = Sparse.eval nodeValue4150 (mixedVector B) := by
    change mixedMoment B node4150 node4150Labels = _
    exact sound4150 B hB hF
  have h4153 : mixedVector B (Sum.inr 4153) = Sparse.eval nodeValue4153 (mixedVector B) := by
    change mixedMoment B node4153 node4153Labels = _
    exact sound4153 B hB hF
  have h4155 : mixedVector B (Sum.inr 4155) = Sparse.eval nodeValue4155 (mixedVector B) := by
    change mixedMoment B node4155 node4155Labels = _
    exact sound4155 B hB hF
  have h4158 : mixedVector B (Sum.inr 4158) = Sparse.eval nodeValue4158 (mixedVector B) := by
    change mixedMoment B node4158 node4158Labels = _
    exact sound4158 B hB hF
  have h4175 : mixedVector B (Sum.inr 4175) = Sparse.eval nodeValue4175 (mixedVector B) := by
    change mixedMoment B node4175 node4175Labels = _
    exact sound4175 B hB hF
  have h4327 : mixedVector B (Sum.inr 4327) = Sparse.eval nodeValue4327 (mixedVector B) := by
    change mixedMoment B node4327 node4327Labels = _
    exact sound4327 B hB hF
  have h4329 : mixedVector B (Sum.inr 4329) = Sparse.eval nodeValue4329 (mixedVector B) := by
    change mixedMoment B node4329 node4329Labels = _
    exact sound4329 B hB hF
  have h4332 : mixedVector B (Sum.inr 4332) = Sparse.eval nodeValue4332 (mixedVector B) := by
    change mixedMoment B node4332 node4332Labels = _
    exact sound4332 B hB hF
  have h4344 : mixedVector B (Sum.inr 4344) = Sparse.eval nodeValue4344 (mixedVector B) := by
    change mixedMoment B node4344 node4344Labels = _
    exact sound4344 B hB hF
  have h4364 : mixedVector B (Sum.inr 4364) = Sparse.eval nodeValue4364 (mixedVector B) := by
    change mixedMoment B node4364 node4364Labels = _
    exact sound4364 B hB hF
  have h4367 : mixedVector B (Sum.inr 4367) = Sparse.eval nodeValue4367 (mixedVector B) := by
    change mixedMoment B node4367 node4367Labels = _
    exact sound4367 B hB hF
  have h4369 : mixedVector B (Sum.inr 4369) = Sparse.eval nodeValue4369 (mixedVector B) := by
    change mixedMoment B node4369 node4369Labels = _
    exact sound4369 B hB hF
  have h4372 : mixedVector B (Sum.inr 4372) = Sparse.eval nodeValue4372 (mixedVector B) := by
    change mixedMoment B node4372 node4372Labels = _
    exact sound4372 B hB hF
  have h4438 : mixedVector B (Sum.inr 4438) = Sparse.eval nodeValue4438 (mixedVector B) := by
    change mixedMoment B node4438 node4438Labels = _
    exact sound4438 B hB hF
  have h4440 : mixedVector B (Sum.inr 4440) = Sparse.eval nodeValue4440 (mixedVector B) := by
    change mixedMoment B node4440 node4440Labels = _
    exact sound4440 B hB hF
  have h4444 : mixedVector B (Sum.inr 4444) = Sparse.eval nodeValue4444 (mixedVector B) := by
    change mixedMoment B node4444 node4444Labels = _
    exact sound4444 B hB hF
  have h4456 : mixedVector B (Sum.inr 4456) = Sparse.eval nodeValue4456 (mixedVector B) := by
    change mixedMoment B node4456 node4456Labels = _
    exact sound4456 B hB hF
  have h4458 : mixedVector B (Sum.inr 4458) = Sparse.eval nodeValue4458 (mixedVector B) := by
    change mixedMoment B node4458 node4458Labels = _
    exact sound4458 B hB hF
  have h4461 : mixedVector B (Sum.inr 4461) = Sparse.eval nodeValue4461 (mixedVector B) := by
    change mixedMoment B node4461 node4461Labels = _
    exact sound4461 B hB hF
  have h4463 : mixedVector B (Sum.inr 4463) = Sparse.eval nodeValue4463 (mixedVector B) := by
    change mixedMoment B node4463 node4463Labels = _
    exact sound4463 B hB hF
  have h4467 : mixedVector B (Sum.inr 4467) = Sparse.eval nodeValue4467 (mixedVector B) := by
    change mixedMoment B node4467 node4467Labels = _
    exact sound4467 B hB hF
  have h4497 : mixedVector B (Sum.inr 4497) = Sparse.eval nodeValue4497 (mixedVector B) := by
    change mixedMoment B node4497 node4497Labels = _
    exact sound4497 B hB hF
  have h4502 : mixedVector B (Sum.inr 4502) = Sparse.eval nodeValue4502 (mixedVector B) := by
    change mixedMoment B node4502 node4502Labels = _
    exact sound4502 B hB hF
  have h4802 : mixedVector B (Sum.inr 4802) = Sparse.eval nodeValue4802 (mixedVector B) := by
    change mixedMoment B node4802 node4802Labels = _
    exact sound4802 B hB hF
  have h4866 : mixedVector B (Sum.inr 4866) = Sparse.eval nodeValue4866 (mixedVector B) := by
    change mixedMoment B node4866 node4866Labels = _
    exact sound4866 B hB hF
  have h4888 : mixedVector B (Sum.inr 4888) = Sparse.eval nodeValue4888 (mixedVector B) := by
    change mixedMoment B node4888 node4888Labels = _
    exact sound4888 B hB hF
  have h4893 : mixedVector B (Sum.inr 4893) = Sparse.eval nodeValue4893 (mixedVector B) := by
    change mixedMoment B node4893 node4893Labels = _
    exact sound4893 B hB hF
  have h4895 : mixedVector B (Sum.inr 4895) = Sparse.eval nodeValue4895 (mixedVector B) := by
    change mixedMoment B node4895 node4895Labels = _
    exact sound4895 B hB hF
  simpa only [sourceForm1724, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4150, h4153, h4155, h4158, h4175, h4327, h4329, h4332, h4344, h4364, h4367, h4369, h4372, h4438, h4440, h4444, h4456, h4458, h4461, h4463, h4467, h4497, h4502, h4802, h4866, h4888, h4893, h4895, reducedSource1471] using sourceEq1724 B hB

theorem rowSound1471 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1471 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1471, numericCheck1471, reducedZero1471 B hB hF, mul_zero]

theorem sourceRowsAt1456 : MixedData.sourceRows (1456 : Fin 2425) =
    MixedData.row1456 := by decide +kernel

theorem sourceRowsAt1457 : MixedData.sourceRows (1457 : Fin 2425) =
    MixedData.row1457 := by decide +kernel

theorem sourceRowsAt1458 : MixedData.sourceRows (1458 : Fin 2425) =
    MixedData.row1458 := by decide +kernel

theorem sourceRowsAt1459 : MixedData.sourceRows (1459 : Fin 2425) =
    MixedData.row1459 := by decide +kernel

theorem sourceRowsAt1460 : MixedData.sourceRows (1460 : Fin 2425) =
    MixedData.row1460 := by decide +kernel

theorem sourceRowsAt1461 : MixedData.sourceRows (1461 : Fin 2425) =
    MixedData.row1461 := by decide +kernel

theorem sourceRowsAt1462 : MixedData.sourceRows (1462 : Fin 2425) =
    MixedData.row1462 := by decide +kernel

theorem sourceRowsAt1463 : MixedData.sourceRows (1463 : Fin 2425) =
    MixedData.row1463 := by decide +kernel

theorem sourceRowsAt1464 : MixedData.sourceRows (1464 : Fin 2425) =
    MixedData.row1464 := by decide +kernel

theorem sourceRowsAt1465 : MixedData.sourceRows (1465 : Fin 2425) =
    MixedData.row1465 := by decide +kernel

theorem sourceRowsAt1466 : MixedData.sourceRows (1466 : Fin 2425) =
    MixedData.row1466 := by decide +kernel

theorem sourceRowsAt1467 : MixedData.sourceRows (1467 : Fin 2425) =
    MixedData.row1467 := by decide +kernel

theorem sourceRowsAt1468 : MixedData.sourceRows (1468 : Fin 2425) =
    MixedData.row1468 := by decide +kernel

theorem sourceRowsAt1469 : MixedData.sourceRows (1469 : Fin 2425) =
    MixedData.row1469 := by decide +kernel

theorem sourceRowsAt1470 : MixedData.sourceRows (1470 : Fin 2425) =
    MixedData.row1470 := by decide +kernel

theorem sourceRowsAt1471 : MixedData.sourceRows (1471 : Fin 2425) =
    MixedData.row1471 := by decide +kernel

theorem chunkSound91_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) (k : Fin 2425)
    (hk : k.val / 16 = 91) :
    Integer.Sparse.eval (MixedData.sourceRows k) (numericVector B) = 0 := by
  have heq : k.val = 1456 ∨ k.val = 1457 ∨ k.val = 1458 ∨ k.val = 1459 ∨ k.val = 1460 ∨ k.val = 1461 ∨ k.val = 1462 ∨ k.val = 1463 ∨ k.val = 1464 ∨ k.val = 1465 ∨ k.val = 1466 ∨ k.val = 1467 ∨ k.val = 1468 ∨ k.val = 1469 ∨ k.val = 1470 ∨ k.val = 1471 := by omega
  rcases heq with h1456 | h1457 | h1458 | h1459 | h1460 | h1461 | h1462 | h1463 | h1464 | h1465 | h1466 | h1467 | h1468 | h1469 | h1470 | h1471
  · have he : k = (1456 : Fin 2425) := Fin.ext h1456
    subst k
    rw [sourceRowsAt1456]
    exact rowSound1456 B hB hF
  · have he : k = (1457 : Fin 2425) := Fin.ext h1457
    subst k
    rw [sourceRowsAt1457]
    exact rowSound1457 B hB hF
  · have he : k = (1458 : Fin 2425) := Fin.ext h1458
    subst k
    rw [sourceRowsAt1458]
    exact rowSound1458 B hB hF
  · have he : k = (1459 : Fin 2425) := Fin.ext h1459
    subst k
    rw [sourceRowsAt1459]
    exact rowSound1459 B hB hF
  · have he : k = (1460 : Fin 2425) := Fin.ext h1460
    subst k
    rw [sourceRowsAt1460]
    exact rowSound1460 B hB hF
  · have he : k = (1461 : Fin 2425) := Fin.ext h1461
    subst k
    rw [sourceRowsAt1461]
    exact rowSound1461 B hB hF
  · have he : k = (1462 : Fin 2425) := Fin.ext h1462
    subst k
    rw [sourceRowsAt1462]
    exact rowSound1462 B hB hF
  · have he : k = (1463 : Fin 2425) := Fin.ext h1463
    subst k
    rw [sourceRowsAt1463]
    exact rowSound1463 B hB hF
  · have he : k = (1464 : Fin 2425) := Fin.ext h1464
    subst k
    rw [sourceRowsAt1464]
    exact rowSound1464 B hB hF
  · have he : k = (1465 : Fin 2425) := Fin.ext h1465
    subst k
    rw [sourceRowsAt1465]
    exact rowSound1465 B hB hF
  · have he : k = (1466 : Fin 2425) := Fin.ext h1466
    subst k
    rw [sourceRowsAt1466]
    exact rowSound1466 B hB hF
  · have he : k = (1467 : Fin 2425) := Fin.ext h1467
    subst k
    rw [sourceRowsAt1467]
    exact rowSound1467 B hB hF
  · have he : k = (1468 : Fin 2425) := Fin.ext h1468
    subst k
    rw [sourceRowsAt1468]
    exact rowSound1468 B hB hF
  · have he : k = (1469 : Fin 2425) := Fin.ext h1469
    subst k
    rw [sourceRowsAt1469]
    exact rowSound1469_e B hB hF
  · have he : k = (1470 : Fin 2425) := Fin.ext h1470
    subst k
    rw [sourceRowsAt1470]
    exact rowSound1470_e B hB hF
  · have he : k = (1471 : Fin 2425) := Fin.ext h1471
    subst k
    rw [sourceRowsAt1471]
    exact rowSound1471 B hB hF

end MUB6.Certificate.MixedSourceBridge

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedSourceBridge.chunkSound91_e_oai := @OAI.MUB6.Certificate.MixedSourceBridge.chunkSound91_e_oai
