-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedSourceBridge.chunkSound98_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T04:42:45.299472+00:00
-- url     : https://prove2.me/submissions/55f73a5b-316c-4d85-983a-07f4b63b51e6

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E077
import Definitions.Def_OAIQ106E086
import Definitions.Def_OAIQ106E089
import Definitions.Def_OAIQ106E090
import Definitions.Def_OAIQ106E190
import Definitions.Def_OAIQ106E194
import Definitions.Def_OAIQ106E101
import Definitions.Def_OAIQ106E102
import Definitions.Def_OAIQ106E117
import Definitions.Def_OAIQ106E119
import Definitions.Def_OAIQ106E120
import Definitions.Def_OAIQ106E124
import Definitions.Def_OAIQ106E140
import Definitions.Def_OAIQ106E147
import Definitions.Def_OAIQ106E170
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound1299_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound3100_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound1568_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound1572_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound1575_e

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

theorem canonical1293 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1293 raw1293Labels = mixedMoment B node4495 node4495Labels := by
  calc
    mixedMoment B raw1293 raw1293Labels = mixedMoment B raw1293step0 raw1293step0Labels := by
      have ha : raw1293step0 = (fun i j => raw1293 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1293step0 raw1293; decide +kernel
      have hl : raw1293step0Labels = raw1293Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1293 raw1293Labels permutation32 permutation4
    mixedMoment B raw1293step0 raw1293step0Labels = mixedMoment B raw1293step1 raw1293step1Labels := by
      have ha : raw1293step1 = raw1293step0 := by apply Matrix.ext; unfold raw1293step1 raw1293step0; decide +kernel
      have hl : raw1293step0Labels = labelEmbedding7 ∘ raw1293step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1293step0 raw1293step0Labels raw1293step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4495 node4495Labels := by rfl

theorem canonical1294 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1294 raw1294Labels = mixedMoment B node1079 node1079Labels := by
  calc
    mixedMoment B raw1294 raw1294Labels = mixedMoment B raw1294step0 raw1294step0Labels := by
      have ha : raw1294step0 = (fun i j => raw1294 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1294step0 raw1294; decide +kernel
      have hl : raw1294step0Labels = raw1294Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1294 raw1294Labels permutation32 permutation4
    _ = mixedMoment B node1079 node1079Labels := by rfl

theorem canonical1295 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1295 raw1295Labels = mixedMoment B node1708 node1708Labels := by
  calc
    mixedMoment B raw1295 raw1295Labels = mixedMoment B raw1295step0 raw1295step0Labels := by
      have ha : raw1295step0 = (fun i j => raw1295 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1295step0 raw1295; decide +kernel
      have hl : raw1295step0Labels = raw1295Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1295 raw1295Labels permutation32 permutation6
    mixedMoment B raw1295step0 raw1295step0Labels = mixedMoment B raw1295step1 raw1295step1Labels := by
      have ha : raw1295step1 = -raw1295step0 := by apply Matrix.ext; change ∀ i j, raw1295step1 i j = -(raw1295step0 i j); unfold raw1295step1 raw1295step0; decide +kernel
      have hl : raw1295step1Labels = raw1295step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1295step1 raw1295step1Labels = mixedMoment B raw1295step2 raw1295step2Labels := by
      have ha : raw1295step2 = raw1295step1 := by apply Matrix.ext; unfold raw1295step2 raw1295step1; decide +kernel
      have hl : raw1295step1Labels = labelEmbedding1 ∘ raw1295step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1295step1 raw1295step1Labels raw1295step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1708 node1708Labels := by rfl

theorem canonical1368 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1368 raw1368Labels = mixedMoment B node4544 node4544Labels := by
  calc
    mixedMoment B raw1368 raw1368Labels = mixedMoment B raw1368step0 raw1368step0Labels := by
      have ha : raw1368step0 = (fun i j => raw1368 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1368step0 raw1368; decide +kernel
      have hl : raw1368step0Labels = raw1368Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1368 raw1368Labels permutation152 permutation4
    mixedMoment B raw1368step0 raw1368step0Labels = mixedMoment B raw1368step1 raw1368step1Labels := by
      have ha : raw1368step1 = raw1368step0 := by apply Matrix.ext; unfold raw1368step1 raw1368step0; decide +kernel
      have hl : raw1368step0Labels = labelEmbedding7 ∘ raw1368step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1368step0 raw1368step0Labels raw1368step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4544 node4544Labels := by rfl

theorem canonical1369 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1369 raw1369Labels = mixedMoment B node1129 node1129Labels := by
  calc
    mixedMoment B raw1369 raw1369Labels = mixedMoment B raw1369step0 raw1369step0Labels := by
      have ha : raw1369step0 = (fun i j => raw1369 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1369step0 raw1369; decide +kernel
      have hl : raw1369step0Labels = raw1369Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1369 raw1369Labels permutation152 permutation4
    _ = mixedMoment B node1129 node1129Labels := by rfl

theorem canonical1370 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1370 raw1370Labels = mixedMoment B node3263 node3263Labels := by
  calc
    mixedMoment B raw1370 raw1370Labels = mixedMoment B raw1370step0 raw1370step0Labels := by
      have ha : raw1370step0 = (fun i j => raw1370 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1370step0 raw1370; decide +kernel
      have hl : raw1370step0Labels = raw1370Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1370 raw1370Labels permutation152 permutation6
    mixedMoment B raw1370step0 raw1370step0Labels = mixedMoment B raw1370step1 raw1370step1Labels := by
      have ha : raw1370step1 = -raw1370step0 := by apply Matrix.ext; change ∀ i j, raw1370step1 i j = -(raw1370step0 i j); unfold raw1370step1 raw1370step0; decide +kernel
      have hl : raw1370step1Labels = raw1370step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1370step1 raw1370step1Labels = mixedMoment B raw1370step2 raw1370step2Labels := by
      have ha : raw1370step2 = raw1370step1 := by apply Matrix.ext; unfold raw1370step2 raw1370step1; decide +kernel
      have hl : raw1370step1Labels = labelEmbedding1 ∘ raw1370step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1370step1 raw1370step1Labels raw1370step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3263 node3263Labels := by rfl

theorem canonical1377 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1377 raw1377Labels = mixedMoment B node4550 node4550Labels := by
  calc
    mixedMoment B raw1377 raw1377Labels = mixedMoment B raw1377step0 raw1377step0Labels := by
      have ha : raw1377step0 = (fun i j => raw1377 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1377step0 raw1377; decide +kernel
      have hl : raw1377step0Labels = raw1377Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1377 raw1377Labels permutation152 permutation4
    mixedMoment B raw1377step0 raw1377step0Labels = mixedMoment B raw1377step1 raw1377step1Labels := by
      have ha : raw1377step1 = raw1377step0 := by apply Matrix.ext; unfold raw1377step1 raw1377step0; decide +kernel
      have hl : raw1377step0Labels = labelEmbedding7 ∘ raw1377step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1377step0 raw1377step0Labels raw1377step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4550 node4550Labels := by rfl

theorem canonical1378 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1378 raw1378Labels = mixedMoment B node1135 node1135Labels := by
  calc
    mixedMoment B raw1378 raw1378Labels = mixedMoment B raw1378step0 raw1378step0Labels := by
      have ha : raw1378step0 = (fun i j => raw1378 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1378step0 raw1378; decide +kernel
      have hl : raw1378step0Labels = raw1378Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1378 raw1378Labels permutation152 permutation4
    _ = mixedMoment B node1135 node1135Labels := by rfl

theorem canonical1379 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1379 raw1379Labels = mixedMoment B node3269 node3269Labels := by
  calc
    mixedMoment B raw1379 raw1379Labels = mixedMoment B raw1379step0 raw1379step0Labels := by
      have ha : raw1379step0 = (fun i j => raw1379 (permutation170 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1379step0 raw1379; decide +kernel
      have hl : raw1379step0Labels = raw1379Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1379 raw1379Labels permutation170 permutation6
    mixedMoment B raw1379step0 raw1379step0Labels = mixedMoment B raw1379step1 raw1379step1Labels := by
      have ha : raw1379step1 = -raw1379step0 := by apply Matrix.ext; change ∀ i j, raw1379step1 i j = -(raw1379step0 i j); unfold raw1379step1 raw1379step0; decide +kernel
      have hl : raw1379step1Labels = raw1379step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1379step1 raw1379step1Labels = mixedMoment B raw1379step2 raw1379step2Labels := by
      have ha : raw1379step2 = raw1379step1 := by apply Matrix.ext; unfold raw1379step2 raw1379step1; decide +kernel
      have hl : raw1379step1Labels = labelEmbedding1 ∘ raw1379step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1379step1 raw1379step1Labels raw1379step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3269 node3269Labels := by rfl

end MUB6.Certificate.MixedSemantics

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

theorem canonical1422 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1422 raw1422Labels = mixedMoment B node4601 node4601Labels := by
  calc
    mixedMoment B raw1422 raw1422Labels = mixedMoment B raw1422step0 raw1422step0Labels := by
      have ha : raw1422step0 = (fun i j => raw1422 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1422step0 raw1422; decide +kernel
      have hl : raw1422step0Labels = raw1422Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1422 raw1422Labels permutation152 permutation4
    mixedMoment B raw1422step0 raw1422step0Labels = mixedMoment B raw1422step1 raw1422step1Labels := by
      have ha : raw1422step1 = raw1422step0 := by apply Matrix.ext; unfold raw1422step1 raw1422step0; decide +kernel
      have hl : raw1422step0Labels = labelEmbedding7 ∘ raw1422step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1422step0 raw1422step0Labels raw1422step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4601 node4601Labels := by rfl

theorem canonical1423 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1423 raw1423Labels = mixedMoment B node1235 node1235Labels := by
  calc
    mixedMoment B raw1423 raw1423Labels = mixedMoment B raw1423step0 raw1423step0Labels := by
      have ha : raw1423step0 = (fun i j => raw1423 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1423step0 raw1423; decide +kernel
      have hl : raw1423step0Labels = raw1423Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1423 raw1423Labels permutation152 permutation4
    _ = mixedMoment B node1235 node1235Labels := by rfl

theorem canonical1424 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1424 raw1424Labels = mixedMoment B node3292 node3292Labels := by
  calc
    mixedMoment B raw1424 raw1424Labels = mixedMoment B raw1424step0 raw1424step0Labels := by
      have ha : raw1424step0 = (fun i j => raw1424 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1424step0 raw1424; decide +kernel
      have hl : raw1424step0Labels = raw1424Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1424 raw1424Labels permutation152 permutation6
    mixedMoment B raw1424step0 raw1424step0Labels = mixedMoment B raw1424step1 raw1424step1Labels := by
      have ha : raw1424step1 = -raw1424step0 := by apply Matrix.ext; change ∀ i j, raw1424step1 i j = -(raw1424step0 i j); unfold raw1424step1 raw1424step0; decide +kernel
      have hl : raw1424step1Labels = raw1424step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1424step1 raw1424step1Labels = mixedMoment B raw1424step2 raw1424step2Labels := by
      have ha : raw1424step2 = raw1424step1 := by apply Matrix.ext; unfold raw1424step2 raw1424step1; decide +kernel
      have hl : raw1424step1Labels = labelEmbedding1 ∘ raw1424step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1424step1 raw1424step1Labels raw1424step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3292 node3292Labels := by rfl

theorem canonical1431 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1431 raw1431Labels = mixedMoment B node4606 node4606Labels := by
  calc
    mixedMoment B raw1431 raw1431Labels = mixedMoment B raw1431step0 raw1431step0Labels := by
      have ha : raw1431step0 = (fun i j => raw1431 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1431step0 raw1431; decide +kernel
      have hl : raw1431step0Labels = raw1431Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1431 raw1431Labels permutation32 permutation4
    mixedMoment B raw1431step0 raw1431step0Labels = mixedMoment B raw1431step1 raw1431step1Labels := by
      have ha : raw1431step1 = raw1431step0 := by apply Matrix.ext; unfold raw1431step1 raw1431step0; decide +kernel
      have hl : raw1431step0Labels = labelEmbedding7 ∘ raw1431step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1431step0 raw1431step0Labels raw1431step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4606 node4606Labels := by rfl

theorem canonical1432 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1432 raw1432Labels = mixedMoment B node1240 node1240Labels := by
  calc
    mixedMoment B raw1432 raw1432Labels = mixedMoment B raw1432step0 raw1432step0Labels := by
      have ha : raw1432step0 = (fun i j => raw1432 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1432step0 raw1432; decide +kernel
      have hl : raw1432step0Labels = raw1432Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1432 raw1432Labels permutation32 permutation4
    _ = mixedMoment B node1240 node1240Labels := by rfl

theorem canonical1433 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1433 raw1433Labels = mixedMoment B node3299 node3299Labels := by
  calc
    mixedMoment B raw1433 raw1433Labels = mixedMoment B raw1433step0 raw1433step0Labels := by
      have ha : raw1433step0 = (fun i j => raw1433 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1433step0 raw1433; decide +kernel
      have hl : raw1433step0Labels = raw1433Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1433 raw1433Labels permutation32 permutation6
    mixedMoment B raw1433step0 raw1433step0Labels = mixedMoment B raw1433step1 raw1433step1Labels := by
      have ha : raw1433step1 = -raw1433step0 := by apply Matrix.ext; change ∀ i j, raw1433step1 i j = -(raw1433step0 i j); unfold raw1433step1 raw1433step0; decide +kernel
      have hl : raw1433step1Labels = raw1433step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1433step1 raw1433step1Labels = mixedMoment B raw1433step2 raw1433step2Labels := by
      have ha : raw1433step2 = raw1433step1 := by apply Matrix.ext; unfold raw1433step2 raw1433step1; decide +kernel
      have hl : raw1433step1Labels = labelEmbedding1 ∘ raw1433step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1433step1 raw1433step1Labels raw1433step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3299 node3299Labels := by rfl

theorem canonical1440 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1440 raw1440Labels = mixedMoment B node4618 node4618Labels := by
  calc
    mixedMoment B raw1440 raw1440Labels = mixedMoment B raw1440step0 raw1440step0Labels := by
      have ha : raw1440step0 = (fun i j => raw1440 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1440step0 raw1440; decide +kernel
      have hl : raw1440step0Labels = raw1440Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1440 raw1440Labels permutation32 permutation4
    mixedMoment B raw1440step0 raw1440step0Labels = mixedMoment B raw1440step1 raw1440step1Labels := by
      have ha : raw1440step1 = raw1440step0 := by apply Matrix.ext; unfold raw1440step1 raw1440step0; decide +kernel
      have hl : raw1440step0Labels = labelEmbedding7 ∘ raw1440step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1440step0 raw1440step0Labels raw1440step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4618 node4618Labels := by rfl

theorem canonical1441 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1441 raw1441Labels = mixedMoment B node1293 node1293Labels := by
  calc
    mixedMoment B raw1441 raw1441Labels = mixedMoment B raw1441step0 raw1441step0Labels := by
      have ha : raw1441step0 = (fun i j => raw1441 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1441step0 raw1441; decide +kernel
      have hl : raw1441step0Labels = raw1441Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1441 raw1441Labels permutation32 permutation4
    _ = mixedMoment B node1293 node1293Labels := by rfl

theorem canonical1442 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1442 raw1442Labels = mixedMoment B node3304 node3304Labels := by
  calc
    mixedMoment B raw1442 raw1442Labels = mixedMoment B raw1442step0 raw1442step0Labels := by
      have ha : raw1442step0 = (fun i j => raw1442 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1442step0 raw1442; decide +kernel
      have hl : raw1442step0Labels = raw1442Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1442 raw1442Labels permutation32 permutation6
    mixedMoment B raw1442step0 raw1442step0Labels = mixedMoment B raw1442step1 raw1442step1Labels := by
      have ha : raw1442step1 = -raw1442step0 := by apply Matrix.ext; change ∀ i j, raw1442step1 i j = -(raw1442step0 i j); unfold raw1442step1 raw1442step0; decide +kernel
      have hl : raw1442step1Labels = raw1442step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1442step1 raw1442step1Labels = mixedMoment B raw1442step2 raw1442step2Labels := by
      have ha : raw1442step2 = raw1442step1 := by apply Matrix.ext; unfold raw1442step2 raw1442step1; decide +kernel
      have hl : raw1442step1Labels = labelEmbedding1 ∘ raw1442step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1442step1 raw1442step1Labels raw1442step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3304 node3304Labels := by rfl

theorem canonical1449 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1449 raw1449Labels = mixedMoment B node4622 node4622Labels := by
  calc
    mixedMoment B raw1449 raw1449Labels = mixedMoment B raw1449step0 raw1449step0Labels := by
      have ha : raw1449step0 = (fun i j => raw1449 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1449step0 raw1449; decide +kernel
      have hl : raw1449step0Labels = raw1449Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1449 raw1449Labels permutation32 permutation4
    mixedMoment B raw1449step0 raw1449step0Labels = mixedMoment B raw1449step1 raw1449step1Labels := by
      have ha : raw1449step1 = raw1449step0 := by apply Matrix.ext; unfold raw1449step1 raw1449step0; decide +kernel
      have hl : raw1449step0Labels = labelEmbedding7 ∘ raw1449step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1449step0 raw1449step0Labels raw1449step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4622 node4622Labels := by rfl

theorem canonical1450 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1450 raw1450Labels = mixedMoment B node1299 node1299Labels := by
  calc
    mixedMoment B raw1450 raw1450Labels = mixedMoment B raw1450step0 raw1450step0Labels := by
      have ha : raw1450step0 = (fun i j => raw1450 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1450step0 raw1450; decide +kernel
      have hl : raw1450step0Labels = raw1450Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1450 raw1450Labels permutation32 permutation4
    _ = mixedMoment B node1299 node1299Labels := by rfl

theorem canonical1451 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1451 raw1451Labels = mixedMoment B node3307 node3307Labels := by
  calc
    mixedMoment B raw1451 raw1451Labels = mixedMoment B raw1451step0 raw1451step0Labels := by
      have ha : raw1451step0 = (fun i j => raw1451 (permutation48 i) (permutation3 j)) := by apply Matrix.ext; unfold raw1451step0 raw1451; decide +kernel
      have hl : raw1451step0Labels = raw1451Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1451 raw1451Labels permutation48 permutation3
    mixedMoment B raw1451step0 raw1451step0Labels = mixedMoment B raw1451step1 raw1451step1Labels := by
      have ha : raw1451step1 = -raw1451step0 := by apply Matrix.ext; change ∀ i j, raw1451step1 i j = -(raw1451step0 i j); unfold raw1451step1 raw1451step0; decide +kernel
      have hl : raw1451step1Labels = raw1451step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1451step1 raw1451step1Labels = mixedMoment B raw1451step2 raw1451step2Labels := by
      have ha : raw1451step2 = raw1451step1 := by apply Matrix.ext; unfold raw1451step2 raw1451step1; decide +kernel
      have hl : raw1451step1Labels = labelEmbedding1 ∘ raw1451step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1451step1 raw1451step1Labels raw1451step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3307 node3307Labels := by rfl

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

theorem canonical2268 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2268 raw2268Labels = mixedMoment B node5257 node5257Labels := by
  calc
    mixedMoment B raw2268 raw2268Labels = mixedMoment B raw2268step0 raw2268step0Labels := by
      have ha : raw2268step0 = (fun i j => raw2268 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2268step0 raw2268; decide +kernel
      have hl : raw2268step0Labels = raw2268Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2268 raw2268Labels permutation152 permutation4
    mixedMoment B raw2268step0 raw2268step0Labels = mixedMoment B raw2268step1 raw2268step1Labels := by
      have ha : raw2268step1 = raw2268step0 := by apply Matrix.ext; unfold raw2268step1 raw2268step0; decide +kernel
      have hl : raw2268step0Labels = labelEmbedding7 ∘ raw2268step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2268step0 raw2268step0Labels raw2268step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5257 node5257Labels := by rfl

theorem canonical2269 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2269 raw2269Labels = mixedMoment B node2721 node2721Labels := by
  calc
    mixedMoment B raw2269 raw2269Labels = mixedMoment B raw2269step0 raw2269step0Labels := by
      have ha : raw2269step0 = (fun i j => raw2269 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2269step0 raw2269; decide +kernel
      have hl : raw2269step0Labels = raw2269Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2269 raw2269Labels permutation152 permutation4
    _ = mixedMoment B node2721 node2721Labels := by rfl

theorem canonical2270 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2270 raw2270Labels = mixedMoment B node3532 node3532Labels := by
  calc
    mixedMoment B raw2270 raw2270Labels = mixedMoment B raw2270step0 raw2270step0Labels := by
      have ha : raw2270step0 = (fun i j => raw2270 (permutation158 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2270step0 raw2270; decide +kernel
      have hl : raw2270step0Labels = raw2270Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2270 raw2270Labels permutation158 permutation6
    mixedMoment B raw2270step0 raw2270step0Labels = mixedMoment B raw2270step1 raw2270step1Labels := by
      have ha : raw2270step1 = -raw2270step0 := by apply Matrix.ext; change ∀ i j, raw2270step1 i j = -(raw2270step0 i j); unfold raw2270step1 raw2270step0; decide +kernel
      have hl : raw2270step1Labels = raw2270step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2270step1 raw2270step1Labels = mixedMoment B raw2270step2 raw2270step2Labels := by
      have ha : raw2270step2 = raw2270step1 := by apply Matrix.ext; unfold raw2270step2 raw2270step1; decide +kernel
      have hl : raw2270step1Labels = labelEmbedding1 ∘ raw2270step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2270step1 raw2270step1Labels raw2270step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3532 node3532Labels := by rfl

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

theorem canonical24971 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24971 raw24971Labels = mixedMoment B node1034 node1034Labels := by
  calc
    mixedMoment B raw24971 raw24971Labels = mixedMoment B raw24971step0 raw24971step0Labels := by
      have ha : raw24971step0 = (fun i j => raw24971 (permutation170 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24971step0 raw24971; decide +kernel
      have hl : raw24971step0Labels = raw24971Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24971 raw24971Labels permutation170 permutation2
    _ = mixedMoment B node1034 node1034Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical206
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical26370 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26370 raw26370Labels = mixedMoment B node4068 node4068Labels := by
  calc
    mixedMoment B raw26370 raw26370Labels = mixedMoment B raw26370step0 raw26370step0Labels := by
      have hz : ∀ j, raw26370 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26370step0 = (fun i j => raw26370 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26370step0 raw26370; decide +kernel
      have hl : raw26370step0Labels = raw26370Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26370 raw26370Labels permutation265 hz
    mixedMoment B raw26370step0 raw26370step0Labels = mixedMoment B raw26370step1 raw26370step1Labels := by
      have ha : raw26370step1 = -raw26370step0 := by apply Matrix.ext; change ∀ i j, raw26370step1 i j = -(raw26370step0 i j); unfold raw26370step1 raw26370step0; decide +kernel
      have hl : raw26370step1Labels = raw26370step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4068 node4068Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical207
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical26581 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26581 raw26581Labels = mixedMoment B node4497 node4497Labels := by
  calc
    mixedMoment B raw26581 raw26581Labels = mixedMoment B raw26581step0 raw26581step0Labels := by
      have hz : ∀ j, raw26581 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26581step0 = (fun i j => raw26581 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26581step0 raw26581; decide +kernel
      have hl : raw26581step0Labels = raw26581Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26581 raw26581Labels permutation265 hz
    mixedMoment B raw26581step0 raw26581step0Labels = mixedMoment B raw26581step1 raw26581step1Labels := by
      have ha : raw26581step1 = (fun i j => raw26581step0 (permutation50 i) (permutation7 j)) := by apply Matrix.ext; unfold raw26581step1 raw26581step0; decide +kernel
      have hl : raw26581step1Labels = raw26581step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26581step0 raw26581step0Labels permutation50 permutation7
    mixedMoment B raw26581step1 raw26581step1Labels = mixedMoment B raw26581step2 raw26581step2Labels := by
      have ha : raw26581step2 = raw26581step1 := by apply Matrix.ext; unfold raw26581step2 raw26581step1; decide +kernel
      have hl : raw26581step1Labels = labelEmbedding10 ∘ raw26581step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26581step1 raw26581step1Labels raw26581step2Labels labelEmbedding10 hl
    _ = mixedMoment B node4497 node4497Labels := by rfl

theorem canonical26586 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26586 raw26586Labels = mixedMoment B node4601 node4601Labels := by
  calc
    mixedMoment B raw26586 raw26586Labels = mixedMoment B raw26586step0 raw26586step0Labels := by
      have ha : raw26586step0 = (fun i j => raw26586 (permutation170 i) (permutation7 j)) := by apply Matrix.ext; unfold raw26586step0 raw26586; decide +kernel
      have hl : raw26586step0Labels = raw26586Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26586 raw26586Labels permutation170 permutation7
    mixedMoment B raw26586step0 raw26586step0Labels = mixedMoment B raw26586step1 raw26586step1Labels := by
      have ha : raw26586step1 = raw26586step0 := by apply Matrix.ext; unfold raw26586step1 raw26586step0; decide +kernel
      have hl : raw26586step0Labels = labelEmbedding10 ∘ raw26586step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26586step0 raw26586step0Labels raw26586step1Labels labelEmbedding10 hl
    _ = mixedMoment B node4601 node4601Labels := by rfl

theorem canonical26591 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26591 raw26591Labels = mixedMoment B node4622 node4622Labels := by
  calc
    mixedMoment B raw26591 raw26591Labels = mixedMoment B raw26591step0 raw26591step0Labels := by
      have hz : ∀ j, raw26591 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26591step0 = (fun i j => raw26591 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26591step0 raw26591; decide +kernel
      have hl : raw26591step0Labels = raw26591Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26591 raw26591Labels permutation265 hz
    mixedMoment B raw26591step0 raw26591step0Labels = mixedMoment B raw26591step1 raw26591step1Labels := by
      have ha : raw26591step1 = (fun i j => raw26591step0 (permutation40 i) (permutation6 j)) := by apply Matrix.ext; unfold raw26591step1 raw26591step0; decide +kernel
      have hl : raw26591step1Labels = raw26591step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26591step0 raw26591step0Labels permutation40 permutation6
    mixedMoment B raw26591step1 raw26591step1Labels = mixedMoment B raw26591step2 raw26591step2Labels := by
      have ha : raw26591step2 = raw26591step1 := by apply Matrix.ext; unfold raw26591step2 raw26591step1; decide +kernel
      have hl : raw26591step1Labels = labelEmbedding9 ∘ raw26591step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26591step1 raw26591step1Labels raw26591step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4622 node4622Labels := by rfl

theorem canonical26596 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26596 raw26596Labels = mixedMoment B node4622 node4622Labels := by
  calc
    mixedMoment B raw26596 raw26596Labels = mixedMoment B raw26596step0 raw26596step0Labels := by
      have hz : ∀ j, raw26596 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26596step0 = (fun i j => raw26596 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26596step0 raw26596; decide +kernel
      have hl : raw26596step0Labels = raw26596Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26596 raw26596Labels permutation265 hz
    mixedMoment B raw26596step0 raw26596step0Labels = mixedMoment B raw26596step1 raw26596step1Labels := by
      have ha : raw26596step1 = (fun i j => raw26596step0 (permutation34 i) (permutation6 j)) := by apply Matrix.ext; unfold raw26596step1 raw26596step0; decide +kernel
      have hl : raw26596step1Labels = raw26596step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26596step0 raw26596step0Labels permutation34 permutation6
    mixedMoment B raw26596step1 raw26596step1Labels = mixedMoment B raw26596step2 raw26596step2Labels := by
      have ha : raw26596step2 = raw26596step1 := by apply Matrix.ext; unfold raw26596step2 raw26596step1; decide +kernel
      have hl : raw26596step1Labels = labelEmbedding9 ∘ raw26596step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26596step1 raw26596step1Labels raw26596step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4622 node4622Labels := by rfl

theorem canonical26597 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26597 raw26597Labels = mixedMoment B node4495 node4495Labels := by
  calc
    mixedMoment B raw26597 raw26597Labels = mixedMoment B raw26597step0 raw26597step0Labels := by
      have hz : ∀ j, raw26597 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26597step0 = (fun i j => raw26597 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26597step0 raw26597; decide +kernel
      have hl : raw26597step0Labels = raw26597Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26597 raw26597Labels permutation265 hz
    mixedMoment B raw26597step0 raw26597step0Labels = mixedMoment B raw26597step1 raw26597step1Labels := by
      have ha : raw26597step1 = (fun i j => raw26597step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw26597step1 raw26597step0; decide +kernel
      have hl : raw26597step1Labels = raw26597step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26597step0 raw26597step0Labels permutation32 permutation6
    mixedMoment B raw26597step1 raw26597step1Labels = mixedMoment B raw26597step2 raw26597step2Labels := by
      have ha : raw26597step2 = raw26597step1 := by apply Matrix.ext; unfold raw26597step2 raw26597step1; decide +kernel
      have hl : raw26597step1Labels = labelEmbedding9 ∘ raw26597step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26597step1 raw26597step1Labels raw26597step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4495 node4495Labels := by rfl

theorem canonical26598 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26598 raw26598Labels = mixedMoment B node4599 node4599Labels := by
  calc
    mixedMoment B raw26598 raw26598Labels = mixedMoment B raw26598step0 raw26598step0Labels := by
      have ha : raw26598step0 = (fun i j => raw26598 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw26598step0 raw26598; decide +kernel
      have hl : raw26598step0Labels = raw26598Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26598 raw26598Labels permutation152 permutation6
    mixedMoment B raw26598step0 raw26598step0Labels = mixedMoment B raw26598step1 raw26598step1Labels := by
      have ha : raw26598step1 = raw26598step0 := by apply Matrix.ext; unfold raw26598step1 raw26598step0; decide +kernel
      have hl : raw26598step0Labels = labelEmbedding9 ∘ raw26598step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26598step0 raw26598step0Labels raw26598step1Labels labelEmbedding9 hl
    _ = mixedMoment B node4599 node4599Labels := by rfl

theorem canonical26599 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26599 raw26599Labels = mixedMoment B node4616 node4616Labels := by
  calc
    mixedMoment B raw26599 raw26599Labels = mixedMoment B raw26599step0 raw26599step0Labels := by
      have hz : ∀ j, raw26599 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26599step0 = (fun i j => raw26599 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26599step0 raw26599; decide +kernel
      have hl : raw26599step0Labels = raw26599Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26599 raw26599Labels permutation265 hz
    mixedMoment B raw26599step0 raw26599step0Labels = mixedMoment B raw26599step1 raw26599step1Labels := by
      have ha : raw26599step1 = (fun i j => raw26599step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw26599step1 raw26599step0; decide +kernel
      have hl : raw26599step1Labels = raw26599step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26599step0 raw26599step0Labels permutation32 permutation6
    mixedMoment B raw26599step1 raw26599step1Labels = mixedMoment B raw26599step2 raw26599step2Labels := by
      have ha : raw26599step2 = raw26599step1 := by apply Matrix.ext; unfold raw26599step2 raw26599step1; decide +kernel
      have hl : raw26599step1Labels = labelEmbedding9 ∘ raw26599step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26599step1 raw26599step1Labels raw26599step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4616 node4616Labels := by rfl

theorem canonical26600 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26600 raw26600Labels = mixedMoment B node4616 node4616Labels := by
  calc
    mixedMoment B raw26600 raw26600Labels = mixedMoment B raw26600step0 raw26600step0Labels := by
      have hz : ∀ j, raw26600 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26600step0 = (fun i j => raw26600 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26600step0 raw26600; decide +kernel
      have hl : raw26600step0Labels = raw26600Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26600 raw26600Labels permutation265 hz
    mixedMoment B raw26600step0 raw26600step0Labels = mixedMoment B raw26600step1 raw26600step1Labels := by
      have ha : raw26600step1 = (fun i j => raw26600step0 (permutation38 i) (permutation6 j)) := by apply Matrix.ext; unfold raw26600step1 raw26600step0; decide +kernel
      have hl : raw26600step1Labels = raw26600step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26600step0 raw26600step0Labels permutation38 permutation6
    mixedMoment B raw26600step1 raw26600step1Labels = mixedMoment B raw26600step2 raw26600step2Labels := by
      have ha : raw26600step2 = raw26600step1 := by apply Matrix.ext; unfold raw26600step2 raw26600step1; decide +kernel
      have hl : raw26600step1Labels = labelEmbedding9 ∘ raw26600step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26600step1 raw26600step1Labels raw26600step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4616 node4616Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical208
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical26679 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26679 raw26679Labels = mixedMoment B node4456 node4456Labels := by
  calc
    mixedMoment B raw26679 raw26679Labels = mixedMoment B raw26679step0 raw26679step0Labels := by
      have ha : raw26679step0 = (fun i j => raw26679 (permutation168 i) (permutation7 j)) := by apply Matrix.ext; unfold raw26679step0 raw26679; decide +kernel
      have hl : raw26679step0Labels = raw26679Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26679 raw26679Labels permutation168 permutation7
    mixedMoment B raw26679step0 raw26679step0Labels = mixedMoment B raw26679step1 raw26679step1Labels := by
      have ha : raw26679step1 = raw26679step0 := by apply Matrix.ext; unfold raw26679step1 raw26679step0; decide +kernel
      have hl : raw26679step0Labels = labelEmbedding10 ∘ raw26679step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26679step0 raw26679step0Labels raw26679step1Labels labelEmbedding10 hl
    _ = mixedMoment B node4456 node4456Labels := by rfl

theorem canonical26680 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26680 raw26680Labels = mixedMoment B node4495 node4495Labels := by
  calc
    mixedMoment B raw26680 raw26680Labels = mixedMoment B raw26680step0 raw26680step0Labels := by
      have hz : ∀ j, raw26680 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26680step0 = (fun i j => raw26680 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26680step0 raw26680; decide +kernel
      have hl : raw26680step0Labels = raw26680Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26680 raw26680Labels permutation265 hz
    mixedMoment B raw26680step0 raw26680step0Labels = mixedMoment B raw26680step1 raw26680step1Labels := by
      have ha : raw26680step1 = (fun i j => raw26680step0 (permutation49 i) (permutation7 j)) := by apply Matrix.ext; unfold raw26680step1 raw26680step0; decide +kernel
      have hl : raw26680step1Labels = raw26680step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26680step0 raw26680step0Labels permutation49 permutation7
    mixedMoment B raw26680step1 raw26680step1Labels = mixedMoment B raw26680step2 raw26680step2Labels := by
      have ha : raw26680step2 = raw26680step1 := by apply Matrix.ext; unfold raw26680step2 raw26680step1; decide +kernel
      have hl : raw26680step1Labels = labelEmbedding10 ∘ raw26680step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26680step1 raw26680step1Labels raw26680step2Labels labelEmbedding10 hl
    _ = mixedMoment B node4495 node4495Labels := by rfl

theorem canonical26681 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26681 raw26681Labels = mixedMoment B node4495 node4495Labels := by
  calc
    mixedMoment B raw26681 raw26681Labels = mixedMoment B raw26681step0 raw26681step0Labels := by
      have hz : ∀ j, raw26681 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26681step0 = (fun i j => raw26681 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26681step0 raw26681; decide +kernel
      have hl : raw26681step0Labels = raw26681Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26681 raw26681Labels permutation265 hz
    mixedMoment B raw26681step0 raw26681step0Labels = mixedMoment B raw26681step1 raw26681step1Labels := by
      have ha : raw26681step1 = (fun i j => raw26681step0 (permutation48 i) (permutation7 j)) := by apply Matrix.ext; unfold raw26681step1 raw26681step0; decide +kernel
      have hl : raw26681step1Labels = raw26681step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26681step0 raw26681step0Labels permutation48 permutation7
    mixedMoment B raw26681step1 raw26681step1Labels = mixedMoment B raw26681step2 raw26681step2Labels := by
      have ha : raw26681step2 = raw26681step1 := by apply Matrix.ext; unfold raw26681step2 raw26681step1; decide +kernel
      have hl : raw26681step1Labels = labelEmbedding10 ∘ raw26681step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26681step1 raw26681step1Labels raw26681step2Labels labelEmbedding10 hl
    _ = mixedMoment B node4495 node4495Labels := by rfl

theorem canonical26682 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26682 raw26682Labels = mixedMoment B node4497 node4497Labels := by
  calc
    mixedMoment B raw26682 raw26682Labels = mixedMoment B raw26682step0 raw26682step0Labels := by
      have hz : ∀ j, raw26682 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26682step0 = (fun i j => raw26682 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26682step0 raw26682; decide +kernel
      have hl : raw26682step0Labels = raw26682Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26682 raw26682Labels permutation265 hz
    mixedMoment B raw26682step0 raw26682step0Labels = mixedMoment B raw26682step1 raw26682step1Labels := by
      have ha : raw26682step1 = (fun i j => raw26682step0 (permutation44 i) (permutation7 j)) := by apply Matrix.ext; unfold raw26682step1 raw26682step0; decide +kernel
      have hl : raw26682step1Labels = raw26682step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26682step0 raw26682step0Labels permutation44 permutation7
    mixedMoment B raw26682step1 raw26682step1Labels = mixedMoment B raw26682step2 raw26682step2Labels := by
      have ha : raw26682step2 = raw26682step1 := by apply Matrix.ext; unfold raw26682step2 raw26682step1; decide +kernel
      have hl : raw26682step1Labels = labelEmbedding10 ∘ raw26682step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26682step1 raw26682step1Labels raw26682step2Labels labelEmbedding10 hl
    _ = mixedMoment B node4497 node4497Labels := by rfl

theorem canonical26683 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26683 raw26683Labels = mixedMoment B node4456 node4456Labels := by
  calc
    mixedMoment B raw26683 raw26683Labels = mixedMoment B raw26683step0 raw26683step0Labels := by
      have ha : raw26683step0 = (fun i j => raw26683 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw26683step0 raw26683; decide +kernel
      have hl : raw26683step0Labels = raw26683Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26683 raw26683Labels permutation152 permutation6
    mixedMoment B raw26683step0 raw26683step0Labels = mixedMoment B raw26683step1 raw26683step1Labels := by
      have ha : raw26683step1 = raw26683step0 := by apply Matrix.ext; unfold raw26683step1 raw26683step0; decide +kernel
      have hl : raw26683step0Labels = labelEmbedding9 ∘ raw26683step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26683step0 raw26683step0Labels raw26683step1Labels labelEmbedding9 hl
    _ = mixedMoment B node4456 node4456Labels := by rfl

theorem canonical26684 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26684 raw26684Labels = mixedMoment B node4599 node4599Labels := by
  calc
    mixedMoment B raw26684 raw26684Labels = mixedMoment B raw26684step0 raw26684step0Labels := by
      have ha : raw26684step0 = (fun i j => raw26684 (permutation169 i) (permutation7 j)) := by apply Matrix.ext; unfold raw26684step0 raw26684; decide +kernel
      have hl : raw26684step0Labels = raw26684Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26684 raw26684Labels permutation169 permutation7
    mixedMoment B raw26684step0 raw26684step0Labels = mixedMoment B raw26684step1 raw26684step1Labels := by
      have ha : raw26684step1 = raw26684step0 := by apply Matrix.ext; unfold raw26684step1 raw26684step0; decide +kernel
      have hl : raw26684step0Labels = labelEmbedding10 ∘ raw26684step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26684step0 raw26684step0Labels raw26684step1Labels labelEmbedding10 hl
    _ = mixedMoment B node4599 node4599Labels := by rfl

theorem canonical26685 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26685 raw26685Labels = mixedMoment B node4599 node4599Labels := by
  calc
    mixedMoment B raw26685 raw26685Labels = mixedMoment B raw26685step0 raw26685step0Labels := by
      have ha : raw26685step0 = (fun i j => raw26685 (permutation168 i) (permutation7 j)) := by apply Matrix.ext; unfold raw26685step0 raw26685; decide +kernel
      have hl : raw26685step0Labels = raw26685Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26685 raw26685Labels permutation168 permutation7
    mixedMoment B raw26685step0 raw26685step0Labels = mixedMoment B raw26685step1 raw26685step1Labels := by
      have ha : raw26685step1 = raw26685step0 := by apply Matrix.ext; unfold raw26685step1 raw26685step0; decide +kernel
      have hl : raw26685step0Labels = labelEmbedding10 ∘ raw26685step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26685step0 raw26685step0Labels raw26685step1Labels labelEmbedding10 hl
    _ = mixedMoment B node4599 node4599Labels := by rfl

theorem canonical26686 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26686 raw26686Labels = mixedMoment B node4601 node4601Labels := by
  calc
    mixedMoment B raw26686 raw26686Labels = mixedMoment B raw26686step0 raw26686step0Labels := by
      have ha : raw26686step0 = (fun i j => raw26686 (permutation164 i) (permutation7 j)) := by apply Matrix.ext; unfold raw26686step0 raw26686; decide +kernel
      have hl : raw26686step0Labels = raw26686Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26686 raw26686Labels permutation164 permutation7
    mixedMoment B raw26686step0 raw26686step0Labels = mixedMoment B raw26686step1 raw26686step1Labels := by
      have ha : raw26686step1 = raw26686step0 := by apply Matrix.ext; unfold raw26686step1 raw26686step0; decide +kernel
      have hl : raw26686step0Labels = labelEmbedding10 ∘ raw26686step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26686step0 raw26686step0Labels raw26686step1Labels labelEmbedding10 hl
    _ = mixedMoment B node4601 node4601Labels := by rfl

theorem canonical26687 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26687 raw26687Labels = mixedMoment B node4497 node4497Labels := by
  calc
    mixedMoment B raw26687 raw26687Labels = mixedMoment B raw26687step0 raw26687step0Labels := by
      have hz : ∀ j, raw26687 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26687step0 = (fun i j => raw26687 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26687step0 raw26687; decide +kernel
      have hl : raw26687step0Labels = raw26687Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26687 raw26687Labels permutation265 hz
    mixedMoment B raw26687step0 raw26687step0Labels = mixedMoment B raw26687step1 raw26687step1Labels := by
      have ha : raw26687step1 = (fun i j => raw26687step0 (permutation38 i) (permutation6 j)) := by apply Matrix.ext; unfold raw26687step1 raw26687step0; decide +kernel
      have hl : raw26687step1Labels = raw26687step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26687step0 raw26687step0Labels permutation38 permutation6
    mixedMoment B raw26687step1 raw26687step1Labels = mixedMoment B raw26687step2 raw26687step2Labels := by
      have ha : raw26687step2 = raw26687step1 := by apply Matrix.ext; unfold raw26687step2 raw26687step1; decide +kernel
      have hl : raw26687step1Labels = labelEmbedding9 ∘ raw26687step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26687step1 raw26687step1Labels raw26687step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4497 node4497Labels := by rfl

theorem canonical26688 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26688 raw26688Labels = mixedMoment B node4601 node4601Labels := by
  calc
    mixedMoment B raw26688 raw26688Labels = mixedMoment B raw26688step0 raw26688step0Labels := by
      have ha : raw26688step0 = (fun i j => raw26688 (permutation158 i) (permutation6 j)) := by apply Matrix.ext; unfold raw26688step0 raw26688; decide +kernel
      have hl : raw26688step0Labels = raw26688Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26688 raw26688Labels permutation158 permutation6
    mixedMoment B raw26688step0 raw26688step0Labels = mixedMoment B raw26688step1 raw26688step1Labels := by
      have ha : raw26688step1 = raw26688step0 := by apply Matrix.ext; unfold raw26688step1 raw26688step0; decide +kernel
      have hl : raw26688step0Labels = labelEmbedding9 ∘ raw26688step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26688step0 raw26688step0Labels raw26688step1Labels labelEmbedding9 hl
    _ = mixedMoment B node4601 node4601Labels := by rfl

theorem canonical26689 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26689 raw26689Labels = mixedMoment B node4618 node4618Labels := by
  calc
    mixedMoment B raw26689 raw26689Labels = mixedMoment B raw26689step0 raw26689step0Labels := by
      have hz : ∀ j, raw26689 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26689step0 = (fun i j => raw26689 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26689step0 raw26689; decide +kernel
      have hl : raw26689step0Labels = raw26689Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26689 raw26689Labels permutation265 hz
    mixedMoment B raw26689step0 raw26689step0Labels = mixedMoment B raw26689step1 raw26689step1Labels := by
      have ha : raw26689step1 = (fun i j => raw26689step0 (permutation38 i) (permutation6 j)) := by apply Matrix.ext; unfold raw26689step1 raw26689step0; decide +kernel
      have hl : raw26689step1Labels = raw26689step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26689step0 raw26689step0Labels permutation38 permutation6
    mixedMoment B raw26689step1 raw26689step1Labels = mixedMoment B raw26689step2 raw26689step2Labels := by
      have ha : raw26689step2 = raw26689step1 := by apply Matrix.ext; unfold raw26689step2 raw26689step1; decide +kernel
      have hl : raw26689step1Labels = labelEmbedding9 ∘ raw26689step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26689step1 raw26689step1Labels raw26689step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4618 node4618Labels := by rfl

theorem canonical26690 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26690 raw26690Labels = mixedMoment B node4622 node4622Labels := by
  calc
    mixedMoment B raw26690 raw26690Labels = mixedMoment B raw26690step0 raw26690step0Labels := by
      have hz : ∀ j, raw26690 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26690step0 = (fun i j => raw26690 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26690step0 raw26690; decide +kernel
      have hl : raw26690step0Labels = raw26690Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26690 raw26690Labels permutation265 hz
    mixedMoment B raw26690step0 raw26690step0Labels = mixedMoment B raw26690step1 raw26690step1Labels := by
      have ha : raw26690step1 = (fun i j => raw26690step0 (permutation42 i) (permutation6 j)) := by apply Matrix.ext; unfold raw26690step1 raw26690step0; decide +kernel
      have hl : raw26690step1Labels = raw26690step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26690step0 raw26690step0Labels permutation42 permutation6
    mixedMoment B raw26690step1 raw26690step1Labels = mixedMoment B raw26690step2 raw26690step2Labels := by
      have ha : raw26690step2 = raw26690step1 := by apply Matrix.ext; unfold raw26690step2 raw26690step1; decide +kernel
      have hl : raw26690step1Labels = labelEmbedding9 ∘ raw26690step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26690step1 raw26690step1Labels raw26690step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4622 node4622Labels := by rfl

theorem canonical26691 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26691 raw26691Labels = mixedMoment B node4497 node4497Labels := by
  calc
    mixedMoment B raw26691 raw26691Labels = mixedMoment B raw26691step0 raw26691step0Labels := by
      have hz : ∀ j, raw26691 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26691step0 = (fun i j => raw26691 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26691step0 raw26691; decide +kernel
      have hl : raw26691step0Labels = raw26691Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26691 raw26691Labels permutation265 hz
    mixedMoment B raw26691step0 raw26691step0Labels = mixedMoment B raw26691step1 raw26691step1Labels := by
      have ha : raw26691step1 = (fun i j => raw26691step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw26691step1 raw26691step0; decide +kernel
      have hl : raw26691step1Labels = raw26691step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26691step0 raw26691step0Labels permutation32 permutation6
    mixedMoment B raw26691step1 raw26691step1Labels = mixedMoment B raw26691step2 raw26691step2Labels := by
      have ha : raw26691step2 = raw26691step1 := by apply Matrix.ext; unfold raw26691step2 raw26691step1; decide +kernel
      have hl : raw26691step1Labels = labelEmbedding9 ∘ raw26691step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26691step1 raw26691step1Labels raw26691step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4497 node4497Labels := by rfl

theorem canonical26692 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26692 raw26692Labels = mixedMoment B node4601 node4601Labels := by
  calc
    mixedMoment B raw26692 raw26692Labels = mixedMoment B raw26692step0 raw26692step0Labels := by
      have ha : raw26692step0 = (fun i j => raw26692 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw26692step0 raw26692; decide +kernel
      have hl : raw26692step0Labels = raw26692Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26692 raw26692Labels permutation152 permutation6
    mixedMoment B raw26692step0 raw26692step0Labels = mixedMoment B raw26692step1 raw26692step1Labels := by
      have ha : raw26692step1 = raw26692step0 := by apply Matrix.ext; unfold raw26692step1 raw26692step0; decide +kernel
      have hl : raw26692step0Labels = labelEmbedding9 ∘ raw26692step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26692step0 raw26692step0Labels raw26692step1Labels labelEmbedding9 hl
    _ = mixedMoment B node4601 node4601Labels := by rfl

theorem canonical26693 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26693 raw26693Labels = mixedMoment B node4618 node4618Labels := by
  calc
    mixedMoment B raw26693 raw26693Labels = mixedMoment B raw26693step0 raw26693step0Labels := by
      have hz : ∀ j, raw26693 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26693step0 = (fun i j => raw26693 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26693step0 raw26693; decide +kernel
      have hl : raw26693step0Labels = raw26693Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26693 raw26693Labels permutation265 hz
    mixedMoment B raw26693step0 raw26693step0Labels = mixedMoment B raw26693step1 raw26693step1Labels := by
      have ha : raw26693step1 = (fun i j => raw26693step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw26693step1 raw26693step0; decide +kernel
      have hl : raw26693step1Labels = raw26693step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26693step0 raw26693step0Labels permutation32 permutation6
    mixedMoment B raw26693step1 raw26693step1Labels = mixedMoment B raw26693step2 raw26693step2Labels := by
      have ha : raw26693step2 = raw26693step1 := by apply Matrix.ext; unfold raw26693step2 raw26693step1; decide +kernel
      have hl : raw26693step1Labels = labelEmbedding9 ∘ raw26693step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26693step1 raw26693step1Labels raw26693step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4618 node4618Labels := by rfl

theorem canonical26694 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26694 raw26694Labels = mixedMoment B node4622 node4622Labels := by
  calc
    mixedMoment B raw26694 raw26694Labels = mixedMoment B raw26694step0 raw26694step0Labels := by
      have hz : ∀ j, raw26694 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26694step0 = (fun i j => raw26694 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26694step0 raw26694; decide +kernel
      have hl : raw26694step0Labels = raw26694Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26694 raw26694Labels permutation265 hz
    mixedMoment B raw26694step0 raw26694step0Labels = mixedMoment B raw26694step1 raw26694step1Labels := by
      have ha : raw26694step1 = (fun i j => raw26694step0 (permutation36 i) (permutation6 j)) := by apply Matrix.ext; unfold raw26694step1 raw26694step0; decide +kernel
      have hl : raw26694step1Labels = raw26694step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26694step0 raw26694step0Labels permutation36 permutation6
    mixedMoment B raw26694step1 raw26694step1Labels = mixedMoment B raw26694step2 raw26694step2Labels := by
      have ha : raw26694step2 = raw26694step1 := by apply Matrix.ext; unfold raw26694step2 raw26694step1; decide +kernel
      have hl : raw26694step1Labels = labelEmbedding9 ∘ raw26694step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26694step1 raw26694step1Labels raw26694step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4622 node4622Labels := by rfl

theorem canonical26695 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26695 raw26695Labels = mixedMoment B node4495 node4495Labels := by
  calc
    mixedMoment B raw26695 raw26695Labels = mixedMoment B raw26695step0 raw26695step0Labels := by
      have hz : ∀ j, raw26695 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26695step0 = (fun i j => raw26695 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26695step0 raw26695; decide +kernel
      have hl : raw26695step0Labels = raw26695Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26695 raw26695Labels permutation265 hz
    mixedMoment B raw26695step0 raw26695step0Labels = mixedMoment B raw26695step1 raw26695step1Labels := by
      have ha : raw26695step1 = (fun i j => raw26695step0 (permutation33 i) (permutation6 j)) := by apply Matrix.ext; unfold raw26695step1 raw26695step0; decide +kernel
      have hl : raw26695step1Labels = raw26695step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26695step0 raw26695step0Labels permutation33 permutation6
    mixedMoment B raw26695step1 raw26695step1Labels = mixedMoment B raw26695step2 raw26695step2Labels := by
      have ha : raw26695step2 = raw26695step1 := by apply Matrix.ext; unfold raw26695step2 raw26695step1; decide +kernel
      have hl : raw26695step1Labels = labelEmbedding9 ∘ raw26695step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26695step1 raw26695step1Labels raw26695step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4495 node4495Labels := by rfl

theorem canonical26696 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26696 raw26696Labels = mixedMoment B node4599 node4599Labels := by
  calc
    mixedMoment B raw26696 raw26696Labels = mixedMoment B raw26696step0 raw26696step0Labels := by
      have ha : raw26696step0 = (fun i j => raw26696 (permutation153 i) (permutation6 j)) := by apply Matrix.ext; unfold raw26696step0 raw26696; decide +kernel
      have hl : raw26696step0Labels = raw26696Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26696 raw26696Labels permutation153 permutation6
    mixedMoment B raw26696step0 raw26696step0Labels = mixedMoment B raw26696step1 raw26696step1Labels := by
      have ha : raw26696step1 = raw26696step0 := by apply Matrix.ext; unfold raw26696step1 raw26696step0; decide +kernel
      have hl : raw26696step0Labels = labelEmbedding9 ∘ raw26696step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26696step0 raw26696step0Labels raw26696step1Labels labelEmbedding9 hl
    _ = mixedMoment B node4599 node4599Labels := by rfl

theorem canonical26697 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26697 raw26697Labels = mixedMoment B node4616 node4616Labels := by
  calc
    mixedMoment B raw26697 raw26697Labels = mixedMoment B raw26697step0 raw26697step0Labels := by
      have hz : ∀ j, raw26697 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26697step0 = (fun i j => raw26697 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26697step0 raw26697; decide +kernel
      have hl : raw26697step0Labels = raw26697Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26697 raw26697Labels permutation265 hz
    mixedMoment B raw26697step0 raw26697step0Labels = mixedMoment B raw26697step1 raw26697step1Labels := by
      have ha : raw26697step1 = (fun i j => raw26697step0 (permutation33 i) (permutation6 j)) := by apply Matrix.ext; unfold raw26697step1 raw26697step0; decide +kernel
      have hl : raw26697step1Labels = raw26697step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26697step0 raw26697step0Labels permutation33 permutation6
    mixedMoment B raw26697step1 raw26697step1Labels = mixedMoment B raw26697step2 raw26697step2Labels := by
      have ha : raw26697step2 = raw26697step1 := by apply Matrix.ext; unfold raw26697step2 raw26697step1; decide +kernel
      have hl : raw26697step1Labels = labelEmbedding9 ∘ raw26697step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26697step1 raw26697step1Labels raw26697step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4616 node4616Labels := by rfl

theorem canonical26698 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26698 raw26698Labels = mixedMoment B node4616 node4616Labels := by
  calc
    mixedMoment B raw26698 raw26698Labels = mixedMoment B raw26698step0 raw26698step0Labels := by
      have hz : ∀ j, raw26698 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26698step0 = (fun i j => raw26698 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26698step0 raw26698; decide +kernel
      have hl : raw26698step0Labels = raw26698Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26698 raw26698Labels permutation265 hz
    mixedMoment B raw26698step0 raw26698step0Labels = mixedMoment B raw26698step1 raw26698step1Labels := by
      have ha : raw26698step1 = (fun i j => raw26698step0 (permutation39 i) (permutation6 j)) := by apply Matrix.ext; unfold raw26698step1 raw26698step0; decide +kernel
      have hl : raw26698step1Labels = raw26698step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26698step0 raw26698step0Labels permutation39 permutation6
    mixedMoment B raw26698step1 raw26698step1Labels = mixedMoment B raw26698step2 raw26698step2Labels := by
      have ha : raw26698step2 = raw26698step1 := by apply Matrix.ext; unfold raw26698step2 raw26698step1; decide +kernel
      have hl : raw26698step1Labels = labelEmbedding9 ∘ raw26698step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26698step1 raw26698step1Labels raw26698step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4616 node4616Labels := by rfl

theorem canonical26699 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26699 raw26699Labels = mixedMoment B node4618 node4618Labels := by
  calc
    mixedMoment B raw26699 raw26699Labels = mixedMoment B raw26699step0 raw26699step0Labels := by
      have hz : ∀ j, raw26699 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26699step0 = (fun i j => raw26699 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26699step0 raw26699; decide +kernel
      have hl : raw26699step0Labels = raw26699Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26699 raw26699Labels permutation265 hz
    mixedMoment B raw26699step0 raw26699step0Labels = mixedMoment B raw26699step1 raw26699step1Labels := by
      have ha : raw26699step1 = (fun i j => raw26699step0 (permutation44 i) (permutation7 j)) := by apply Matrix.ext; unfold raw26699step1 raw26699step0; decide +kernel
      have hl : raw26699step1Labels = raw26699step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26699step0 raw26699step0Labels permutation44 permutation7
    mixedMoment B raw26699step1 raw26699step1Labels = mixedMoment B raw26699step2 raw26699step2Labels := by
      have ha : raw26699step2 = raw26699step1 := by apply Matrix.ext; unfold raw26699step2 raw26699step1; decide +kernel
      have hl : raw26699step1Labels = labelEmbedding10 ∘ raw26699step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26699step1 raw26699step1Labels raw26699step2Labels labelEmbedding10 hl
    _ = mixedMoment B node4618 node4618Labels := by rfl

theorem canonical26700 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26700 raw26700Labels = mixedMoment B node4618 node4618Labels := by
  calc
    mixedMoment B raw26700 raw26700Labels = mixedMoment B raw26700step0 raw26700step0Labels := by
      have hz : ∀ j, raw26700 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26700step0 = (fun i j => raw26700 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26700step0 raw26700; decide +kernel
      have hl : raw26700step0Labels = raw26700Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26700 raw26700Labels permutation265 hz
    mixedMoment B raw26700step0 raw26700step0Labels = mixedMoment B raw26700step1 raw26700step1Labels := by
      have ha : raw26700step1 = (fun i j => raw26700step0 (permutation50 i) (permutation7 j)) := by apply Matrix.ext; unfold raw26700step1 raw26700step0; decide +kernel
      have hl : raw26700step1Labels = raw26700step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26700step0 raw26700step0Labels permutation50 permutation7
    mixedMoment B raw26700step1 raw26700step1Labels = mixedMoment B raw26700step2 raw26700step2Labels := by
      have ha : raw26700step2 = raw26700step1 := by apply Matrix.ext; unfold raw26700step2 raw26700step1; decide +kernel
      have hl : raw26700step1Labels = labelEmbedding10 ∘ raw26700step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26700step1 raw26700step1Labels raw26700step2Labels labelEmbedding10 hl
    _ = mixedMoment B node4618 node4618Labels := by rfl

theorem canonical26701 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26701 raw26701Labels = mixedMoment B node1228 node1228Labels := by
  calc
    mixedMoment B raw26701 raw26701Labels = mixedMoment B raw26701step0 raw26701step0Labels := by
      have ha : raw26701step0 = (fun i j => raw26701 (permutation173 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26701step0 raw26701; decide +kernel
      have hl : raw26701step0Labels = raw26701Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26701 raw26701Labels permutation173 permutation2
    _ = mixedMoment B node1228 node1228Labels := by rfl

theorem canonical26702 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26702 raw26702Labels = mixedMoment B node2503 node2503Labels := by
  calc
    mixedMoment B raw26702 raw26702Labels = mixedMoment B raw26702step0 raw26702step0Labels := by
      have ha : raw26702step0 = (fun i j => raw26702 (permutation173 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26702step0 raw26702; decide +kernel
      have hl : raw26702step0Labels = raw26702Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26702 raw26702Labels permutation173 permutation2
    _ = mixedMoment B node2503 node2503Labels := by rfl

theorem canonical26703 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26703 raw26703Labels = mixedMoment B node2728 node2728Labels := by
  calc
    mixedMoment B raw26703 raw26703Labels = mixedMoment B raw26703step0 raw26703step0Labels := by
      have ha : raw26703step0 = (fun i j => raw26703 (permutation156 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26703step0 raw26703; decide +kernel
      have hl : raw26703step0Labels = raw26703Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26703 raw26703Labels permutation156 permutation2
    _ = mixedMoment B node2728 node2728Labels := by rfl

theorem canonical26704 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26704 raw26704Labels = mixedMoment B node2718 node2718Labels := by
  calc
    mixedMoment B raw26704 raw26704Labels = mixedMoment B raw26704step0 raw26704step0Labels := by
      have ha : raw26704step0 = (fun i j => raw26704 (permutation163 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26704step0 raw26704; decide +kernel
      have hl : raw26704step0Labels = raw26704Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26704 raw26704Labels permutation163 permutation2
    _ = mixedMoment B node2718 node2718Labels := by rfl

theorem canonical26705 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26705 raw26705Labels = mixedMoment B node2718 node2718Labels := by
  calc
    mixedMoment B raw26705 raw26705Labels = mixedMoment B raw26705step0 raw26705step0Labels := by
      have ha : raw26705step0 = (fun i j => raw26705 (permutation169 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26705step0 raw26705; decide +kernel
      have hl : raw26705step0Labels = raw26705Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26705 raw26705Labels permutation169 permutation2
    _ = mixedMoment B node2718 node2718Labels := by rfl

theorem canonical26706 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26706 raw26706Labels = mixedMoment B node2703 node2703Labels := by
  calc
    mixedMoment B raw26706 raw26706Labels = mixedMoment B raw26706step0 raw26706step0Labels := by
      have ha : raw26706step0 = (fun i j => raw26706 (permutation173 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26706step0 raw26706; decide +kernel
      have hl : raw26706step0Labels = raw26706Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26706 raw26706Labels permutation173 permutation2
    _ = mixedMoment B node2703 node2703Labels := by rfl

theorem canonical26707 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26707 raw26707Labels = mixedMoment B node4090 node4090Labels := by
  calc
    mixedMoment B raw26707 raw26707Labels = mixedMoment B raw26707step0 raw26707step0Labels := by
      have ha : raw26707step0 = (fun i j => raw26707 (permutation173 i) (permutation0 j)) := by apply Matrix.ext; unfold raw26707step0 raw26707; decide +kernel
      have hl : raw26707step0Labels = raw26707Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26707 raw26707Labels permutation173 permutation0
    _ = mixedMoment B node4090 node4090Labels := by rfl

theorem canonical26708 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26708 raw26708Labels = mixedMoment B node5100 node5100Labels := by
  calc
    mixedMoment B raw26708 raw26708Labels = mixedMoment B raw26708step0 raw26708step0Labels := by
      have ha : raw26708step0 = (fun i j => raw26708 (permutation170 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26708step0 raw26708; decide +kernel
      have hl : raw26708step0Labels = raw26708Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26708 raw26708Labels permutation170 permutation2
    _ = mixedMoment B node5100 node5100Labels := by rfl

theorem canonical26709 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26709 raw26709Labels = mixedMoment B node5257 node5257Labels := by
  calc
    mixedMoment B raw26709 raw26709Labels = mixedMoment B raw26709step0 raw26709step0Labels := by
      have ha : raw26709step0 = (fun i j => raw26709 (permutation168 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26709step0 raw26709; decide +kernel
      have hl : raw26709step0Labels = raw26709Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26709 raw26709Labels permutation168 permutation2
    _ = mixedMoment B node5257 node5257Labels := by rfl

theorem canonical26710 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26710 raw26710Labels = mixedMoment B node5273 node5273Labels := by
  calc
    mixedMoment B raw26710 raw26710Labels = mixedMoment B raw26710step0 raw26710step0Labels := by
      have hz : ∀ j, raw26710 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw26710step0 = (fun i j => raw26710 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw26710step0 raw26710; decide +kernel
      have hl : raw26710step0Labels = raw26710Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26710 raw26710Labels permutation590 hz
    _ = mixedMoment B node5273 node5273Labels := by rfl

theorem canonical26711 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26711 raw26711Labels = mixedMoment B node4169 node4169Labels := by
  calc
    mixedMoment B raw26711 raw26711Labels = mixedMoment B raw26711step0 raw26711step0Labels := by
      have ha : raw26711step0 = (fun i j => raw26711 (permutation185 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26711step0 raw26711; decide +kernel
      have hl : raw26711step0Labels = raw26711Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26711 raw26711Labels permutation185 permutation3
    mixedMoment B raw26711step0 raw26711step0Labels = mixedMoment B raw26711step1 raw26711step1Labels := by
      have ha : raw26711step1 = raw26711step0 := by apply Matrix.ext; unfold raw26711step1 raw26711step0; decide +kernel
      have hl : raw26711step0Labels = labelEmbedding6 ∘ raw26711step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26711step0 raw26711step0Labels raw26711step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4169 node4169Labels := by rfl

theorem canonical26712 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26712 raw26712Labels = mixedMoment B node4599 node4599Labels := by
  calc
    mixedMoment B raw26712 raw26712Labels = mixedMoment B raw26712step0 raw26712step0Labels := by
      have ha : raw26712step0 = (fun i j => raw26712 (permutation185 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26712step0 raw26712; decide +kernel
      have hl : raw26712step0Labels = raw26712Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26712 raw26712Labels permutation185 permutation3
    mixedMoment B raw26712step0 raw26712step0Labels = mixedMoment B raw26712step1 raw26712step1Labels := by
      have ha : raw26712step1 = raw26712step0 := by apply Matrix.ext; unfold raw26712step1 raw26712step0; decide +kernel
      have hl : raw26712step0Labels = labelEmbedding6 ∘ raw26712step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26712step0 raw26712step0Labels raw26712step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4599 node4599Labels := by rfl

theorem canonical26713 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26713 raw26713Labels = mixedMoment B node4599 node4599Labels := by
  calc
    mixedMoment B raw26713 raw26713Labels = mixedMoment B raw26713step0 raw26713step0Labels := by
      have ha : raw26713step0 = (fun i j => raw26713 (permutation209 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26713step0 raw26713; decide +kernel
      have hl : raw26713step0Labels = raw26713Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26713 raw26713Labels permutation209 permutation3
    mixedMoment B raw26713step0 raw26713step0Labels = mixedMoment B raw26713step1 raw26713step1Labels := by
      have ha : raw26713step1 = raw26713step0 := by apply Matrix.ext; unfold raw26713step1 raw26713step0; decide +kernel
      have hl : raw26713step0Labels = labelEmbedding6 ∘ raw26713step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26713step0 raw26713step0Labels raw26713step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4599 node4599Labels := by rfl

theorem canonical26714 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26714 raw26714Labels = mixedMoment B node4599 node4599Labels := by
  calc
    mixedMoment B raw26714 raw26714Labels = mixedMoment B raw26714step0 raw26714step0Labels := by
      have ha : raw26714step0 = (fun i j => raw26714 (permutation233 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26714step0 raw26714; decide +kernel
      have hl : raw26714step0Labels = raw26714Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26714 raw26714Labels permutation233 permutation3
    mixedMoment B raw26714step0 raw26714step0Labels = mixedMoment B raw26714step1 raw26714step1Labels := by
      have ha : raw26714step1 = raw26714step0 := by apply Matrix.ext; unfold raw26714step1 raw26714step0; decide +kernel
      have hl : raw26714step0Labels = labelEmbedding6 ∘ raw26714step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26714step0 raw26714step0Labels raw26714step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4599 node4599Labels := by rfl

theorem canonical26715 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26715 raw26715Labels = mixedMoment B node4618 node4618Labels := by
  calc
    mixedMoment B raw26715 raw26715Labels = mixedMoment B raw26715step0 raw26715step0Labels := by
      have hz : ∀ j, raw26715 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw26715step0 = (fun i j => raw26715 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw26715step0 raw26715; decide +kernel
      have hl : raw26715step0Labels = raw26715Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26715 raw26715Labels permutation590 hz
    _ = mixedMoment B node4618 node4618Labels := by rfl

theorem canonical26716 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26716 raw26716Labels = mixedMoment B node4150 node4150Labels := by
  calc
    mixedMoment B raw26716 raw26716Labels = mixedMoment B raw26716step0 raw26716step0Labels := by
      have ha : raw26716step0 = (fun i j => raw26716 (permutation161 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26716step0 raw26716; decide +kernel
      have hl : raw26716step0Labels = raw26716Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26716 raw26716Labels permutation161 permutation3
    mixedMoment B raw26716step0 raw26716step0Labels = mixedMoment B raw26716step1 raw26716step1Labels := by
      have ha : raw26716step1 = raw26716step0 := by apply Matrix.ext; unfold raw26716step1 raw26716step0; decide +kernel
      have hl : raw26716step0Labels = labelEmbedding6 ∘ raw26716step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26716step0 raw26716step0Labels raw26716step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4150 node4150Labels := by rfl

theorem canonical26717 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26717 raw26717Labels = mixedMoment B node4544 node4544Labels := by
  calc
    mixedMoment B raw26717 raw26717Labels = mixedMoment B raw26717step0 raw26717step0Labels := by
      have ha : raw26717step0 = (fun i j => raw26717 (permutation173 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26717step0 raw26717; decide +kernel
      have hl : raw26717step0Labels = raw26717Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26717 raw26717Labels permutation173 permutation2
    _ = mixedMoment B node4544 node4544Labels := by rfl

theorem canonical26718 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26718 raw26718Labels = mixedMoment B node4590 node4590Labels := by
  calc
    mixedMoment B raw26718 raw26718Labels = mixedMoment B raw26718step0 raw26718step0Labels := by
      have ha : raw26718step0 = (fun i j => raw26718 (permutation163 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26718step0 raw26718; decide +kernel
      have hl : raw26718step0Labels = raw26718Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26718 raw26718Labels permutation163 permutation2
    _ = mixedMoment B node4590 node4590Labels := by rfl

theorem canonical26719 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26719 raw26719Labels = mixedMoment B node4590 node4590Labels := by
  calc
    mixedMoment B raw26719 raw26719Labels = mixedMoment B raw26719step0 raw26719step0Labels := by
      have ha : raw26719step0 = (fun i j => raw26719 (permutation169 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26719step0 raw26719; decide +kernel
      have hl : raw26719step0Labels = raw26719Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26719 raw26719Labels permutation169 permutation2
    _ = mixedMoment B node4590 node4590Labels := by rfl

theorem canonical26720 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26720 raw26720Labels = mixedMoment B node4606 node4606Labels := by
  calc
    mixedMoment B raw26720 raw26720Labels = mixedMoment B raw26720step0 raw26720step0Labels := by
      have hz : ∀ j, raw26720 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw26720step0 = (fun i j => raw26720 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw26720step0 raw26720; decide +kernel
      have hl : raw26720step0Labels = raw26720Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26720 raw26720Labels permutation590 hz
    mixedMoment B raw26720step0 raw26720step0Labels = mixedMoment B raw26720step1 raw26720step1Labels := by
      have ha : raw26720step1 = (fun i j => raw26720step0 (permutation35 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26720step1 raw26720step0; decide +kernel
      have hl : raw26720step1Labels = raw26720step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26720step0 raw26720step0Labels permutation35 permutation2
    _ = mixedMoment B node4606 node4606Labels := by rfl

theorem canonical26721 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26721 raw26721Labels = mixedMoment B node4150 node4150Labels := by
  calc
    mixedMoment B raw26721 raw26721Labels = mixedMoment B raw26721step0 raw26721step0Labels := by
      have ha : raw26721step0 = (fun i j => raw26721 (permutation155 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26721step0 raw26721; decide +kernel
      have hl : raw26721step0Labels = raw26721Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26721 raw26721Labels permutation155 permutation3
    mixedMoment B raw26721step0 raw26721step0Labels = mixedMoment B raw26721step1 raw26721step1Labels := by
      have ha : raw26721step1 = raw26721step0 := by apply Matrix.ext; unfold raw26721step1 raw26721step0; decide +kernel
      have hl : raw26721step0Labels = labelEmbedding6 ∘ raw26721step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26721step0 raw26721step0Labels raw26721step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4150 node4150Labels := by rfl

theorem canonical26722 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26722 raw26722Labels = mixedMoment B node4544 node4544Labels := by
  calc
    mixedMoment B raw26722 raw26722Labels = mixedMoment B raw26722step0 raw26722step0Labels := by
      have ha : raw26722step0 = (fun i j => raw26722 (permutation171 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26722step0 raw26722; decide +kernel
      have hl : raw26722step0Labels = raw26722Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26722 raw26722Labels permutation171 permutation2
    _ = mixedMoment B node4544 node4544Labels := by rfl

theorem canonical26723 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26723 raw26723Labels = mixedMoment B node4590 node4590Labels := by
  calc
    mixedMoment B raw26723 raw26723Labels = mixedMoment B raw26723step0 raw26723step0Labels := by
      have ha : raw26723step0 = (fun i j => raw26723 (permutation157 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26723step0 raw26723; decide +kernel
      have hl : raw26723step0Labels = raw26723Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26723 raw26723Labels permutation157 permutation2
    _ = mixedMoment B node4590 node4590Labels := by rfl

theorem canonical26724 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26724 raw26724Labels = mixedMoment B node4590 node4590Labels := by
  calc
    mixedMoment B raw26724 raw26724Labels = mixedMoment B raw26724step0 raw26724step0Labels := by
      have ha : raw26724step0 = (fun i j => raw26724 (permutation168 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26724step0 raw26724; decide +kernel
      have hl : raw26724step0Labels = raw26724Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26724 raw26724Labels permutation168 permutation2
    _ = mixedMoment B node4590 node4590Labels := by rfl

theorem canonical26725 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26725 raw26725Labels = mixedMoment B node4606 node4606Labels := by
  calc
    mixedMoment B raw26725 raw26725Labels = mixedMoment B raw26725step0 raw26725step0Labels := by
      have hz : ∀ j, raw26725 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw26725step0 = (fun i j => raw26725 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw26725step0 raw26725; decide +kernel
      have hl : raw26725step0Labels = raw26725Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26725 raw26725Labels permutation590 hz
    mixedMoment B raw26725step0 raw26725step0Labels = mixedMoment B raw26725step1 raw26725step1Labels := by
      have ha : raw26725step1 = (fun i j => raw26725step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26725step1 raw26725step0; decide +kernel
      have hl : raw26725step1Labels = raw26725step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26725step0 raw26725step0Labels permutation33 permutation2
    _ = mixedMoment B node4606 node4606Labels := by rfl

theorem canonical26726 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26726 raw26726Labels = mixedMoment B node4150 node4150Labels := by
  calc
    mixedMoment B raw26726 raw26726Labels = mixedMoment B raw26726step0 raw26726step0Labels := by
      have ha : raw26726step0 = (fun i j => raw26726 (permutation153 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26726step0 raw26726; decide +kernel
      have hl : raw26726step0Labels = raw26726Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26726 raw26726Labels permutation153 permutation3
    mixedMoment B raw26726step0 raw26726step0Labels = mixedMoment B raw26726step1 raw26726step1Labels := by
      have ha : raw26726step1 = raw26726step0 := by apply Matrix.ext; unfold raw26726step1 raw26726step0; decide +kernel
      have hl : raw26726step0Labels = labelEmbedding6 ∘ raw26726step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26726step0 raw26726step0Labels raw26726step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4150 node4150Labels := by rfl

theorem canonical26727 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26727 raw26727Labels = mixedMoment B node4544 node4544Labels := by
  calc
    mixedMoment B raw26727 raw26727Labels = mixedMoment B raw26727step0 raw26727step0Labels := by
      have ha : raw26727step0 = (fun i j => raw26727 (permutation170 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26727step0 raw26727; decide +kernel
      have hl : raw26727step0Labels = raw26727Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26727 raw26727Labels permutation170 permutation2
    _ = mixedMoment B node4544 node4544Labels := by rfl

theorem canonical26728 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26728 raw26728Labels = mixedMoment B node4590 node4590Labels := by
  calc
    mixedMoment B raw26728 raw26728Labels = mixedMoment B raw26728step0 raw26728step0Labels := by
      have ha : raw26728step0 = (fun i j => raw26728 (permutation156 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26728step0 raw26728; decide +kernel
      have hl : raw26728step0Labels = raw26728Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26728 raw26728Labels permutation156 permutation2
    _ = mixedMoment B node4590 node4590Labels := by rfl

theorem canonical26729 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26729 raw26729Labels = mixedMoment B node4590 node4590Labels := by
  calc
    mixedMoment B raw26729 raw26729Labels = mixedMoment B raw26729step0 raw26729step0Labels := by
      have ha : raw26729step0 = (fun i j => raw26729 (permutation162 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26729step0 raw26729; decide +kernel
      have hl : raw26729step0Labels = raw26729Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26729 raw26729Labels permutation162 permutation2
    _ = mixedMoment B node4590 node4590Labels := by rfl

theorem canonical26730 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26730 raw26730Labels = mixedMoment B node4606 node4606Labels := by
  calc
    mixedMoment B raw26730 raw26730Labels = mixedMoment B raw26730step0 raw26730step0Labels := by
      have hz : ∀ j, raw26730 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw26730step0 = (fun i j => raw26730 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw26730step0 raw26730; decide +kernel
      have hl : raw26730step0Labels = raw26730Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26730 raw26730Labels permutation590 hz
    _ = mixedMoment B node4606 node4606Labels := by rfl

theorem canonical26731 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26731 raw26731Labels = mixedMoment B node4149 node4149Labels := by
  calc
    mixedMoment B raw26731 raw26731Labels = mixedMoment B raw26731step0 raw26731step0Labels := by
      have ha : raw26731step0 = (fun i j => raw26731 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26731step0 raw26731; decide +kernel
      have hl : raw26731step0Labels = raw26731Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26731 raw26731Labels permutation152 permutation3
    mixedMoment B raw26731step0 raw26731step0Labels = mixedMoment B raw26731step1 raw26731step1Labels := by
      have ha : raw26731step1 = raw26731step0 := by apply Matrix.ext; unfold raw26731step1 raw26731step0; decide +kernel
      have hl : raw26731step0Labels = labelEmbedding6 ∘ raw26731step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26731step0 raw26731step0Labels raw26731step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4149 node4149Labels := by rfl

theorem canonical26732 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26732 raw26732Labels = mixedMoment B node4550 node4550Labels := by
  calc
    _ = mixedMoment B node4550 node4550Labels := by rfl

theorem canonical26733 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26733 raw26733Labels = mixedMoment B node4589 node4589Labels := by
  calc
    mixedMoment B raw26733 raw26733Labels = mixedMoment B raw26733step0 raw26733step0Labels := by
      have ha : raw26733step0 = (fun i j => raw26733 (permutation224 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26733step0 raw26733; decide +kernel
      have hl : raw26733step0Labels = raw26733Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26733 raw26733Labels permutation224 permutation3
    mixedMoment B raw26733step0 raw26733step0Labels = mixedMoment B raw26733step1 raw26733step1Labels := by
      have ha : raw26733step1 = raw26733step0 := by apply Matrix.ext; unfold raw26733step1 raw26733step0; decide +kernel
      have hl : raw26733step0Labels = labelEmbedding6 ∘ raw26733step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26733step0 raw26733step0Labels raw26733step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4589 node4589Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical209
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical26760 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26760 raw26760Labels = mixedMoment B node3469 node3469Labels := by
  calc
    mixedMoment B raw26760 raw26760Labels = mixedMoment B raw26760step0 raw26760step0Labels := by
      have ha : raw26760step0 = (fun i j => raw26760 (permutation170 i) (permutation7 j)) := by apply Matrix.ext; unfold raw26760step0 raw26760; decide +kernel
      have hl : raw26760step0Labels = raw26760Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26760 raw26760Labels permutation170 permutation7
    mixedMoment B raw26760step0 raw26760step0Labels = mixedMoment B raw26760step1 raw26760step1Labels := by
      have ha : raw26760step1 = -raw26760step0 := by apply Matrix.ext; change ∀ i j, raw26760step1 i j = -(raw26760step0 i j); unfold raw26760step1 raw26760step0; decide +kernel
      have hl : raw26760step1Labels = raw26760step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw26760step1 raw26760step1Labels = mixedMoment B raw26760step2 raw26760step2Labels := by
      have ha : raw26760step2 = raw26760step1 := by apply Matrix.ext; unfold raw26760step2 raw26760step1; decide +kernel
      have hl : raw26760step1Labels = labelEmbedding1 ∘ raw26760step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26760step1 raw26760step1Labels raw26760step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3469 node3469Labels := by rfl

theorem canonical26761 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26761 raw26761Labels = mixedMoment B node3532 node3532Labels := by
  calc
    mixedMoment B raw26761 raw26761Labels = mixedMoment B raw26761step0 raw26761step0Labels := by
      have ha : raw26761step0 = (fun i j => raw26761 (permutation174 i) (permutation7 j)) := by apply Matrix.ext; unfold raw26761step0 raw26761; decide +kernel
      have hl : raw26761step0Labels = raw26761Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26761 raw26761Labels permutation174 permutation7
    mixedMoment B raw26761step0 raw26761step0Labels = mixedMoment B raw26761step1 raw26761step1Labels := by
      have ha : raw26761step1 = -raw26761step0 := by apply Matrix.ext; change ∀ i j, raw26761step1 i j = -(raw26761step0 i j); unfold raw26761step1 raw26761step0; decide +kernel
      have hl : raw26761step1Labels = raw26761step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw26761step1 raw26761step1Labels = mixedMoment B raw26761step2 raw26761step2Labels := by
      have ha : raw26761step2 = raw26761step1 := by apply Matrix.ext; unfold raw26761step2 raw26761step1; decide +kernel
      have hl : raw26761step1Labels = labelEmbedding1 ∘ raw26761step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26761step1 raw26761step1Labels raw26761step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3532 node3532Labels := by rfl

theorem canonical26762 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26762 raw26762Labels = mixedMoment B node3546 node3546Labels := by
  calc
    mixedMoment B raw26762 raw26762Labels = mixedMoment B raw26762step0 raw26762step0Labels := by
      have hz : ∀ j, raw26762 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw26762step0 = (fun i j => raw26762 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw26762step0 raw26762; decide +kernel
      have hl : raw26762step0Labels = raw26762Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26762 raw26762Labels permutation590 hz
    mixedMoment B raw26762step0 raw26762step0Labels = mixedMoment B raw26762step1 raw26762step1Labels := by
      have ha : raw26762step1 = (fun i j => raw26762step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw26762step1 raw26762step0; decide +kernel
      have hl : raw26762step1Labels = raw26762step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26762step0 raw26762step0Labels permutation32 permutation7
    mixedMoment B raw26762step1 raw26762step1Labels = mixedMoment B raw26762step2 raw26762step2Labels := by
      have ha : raw26762step2 = -raw26762step1 := by apply Matrix.ext; change ∀ i j, raw26762step2 i j = -(raw26762step1 i j); unfold raw26762step2 raw26762step1; decide +kernel
      have hl : raw26762step2Labels = raw26762step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw26762step2 raw26762step2Labels = mixedMoment B raw26762step3 raw26762step3Labels := by
      have ha : raw26762step3 = raw26762step2 := by apply Matrix.ext; unfold raw26762step3 raw26762step2; decide +kernel
      have hl : raw26762step2Labels = labelEmbedding1 ∘ raw26762step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26762step2 raw26762step2Labels raw26762step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3546 node3546Labels := by rfl

theorem canonical26763 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26763 raw26763Labels = mixedMoment B node1502 node1502Labels := by
  calc
    mixedMoment B raw26763 raw26763Labels = mixedMoment B raw26763step0 raw26763step0Labels := by
      have ha : raw26763step0 = (fun i j => raw26763 (permutation185 i) (permutation5 j)) := by apply Matrix.ext; unfold raw26763step0 raw26763; decide +kernel
      have hl : raw26763step0Labels = raw26763Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26763 raw26763Labels permutation185 permutation5
    mixedMoment B raw26763step0 raw26763step0Labels = mixedMoment B raw26763step1 raw26763step1Labels := by
      have ha : raw26763step1 = -raw26763step0 := by apply Matrix.ext; change ∀ i j, raw26763step1 i j = -(raw26763step0 i j); unfold raw26763step1 raw26763step0; decide +kernel
      have hl : raw26763step1Labels = raw26763step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw26763step1 raw26763step1Labels = mixedMoment B raw26763step2 raw26763step2Labels := by
      have ha : raw26763step2 = raw26763step1 := by apply Matrix.ext; unfold raw26763step2 raw26763step1; decide +kernel
      have hl : raw26763step1Labels = labelEmbedding1 ∘ raw26763step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26763step1 raw26763step1Labels raw26763step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1502 node1502Labels := by rfl

theorem canonical26764 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26764 raw26764Labels = mixedMoment B node3289 node3289Labels := by
  calc
    mixedMoment B raw26764 raw26764Labels = mixedMoment B raw26764step0 raw26764step0Labels := by
      have ha : raw26764step0 = (fun i j => raw26764 (permutation185 i) (permutation5 j)) := by apply Matrix.ext; unfold raw26764step0 raw26764; decide +kernel
      have hl : raw26764step0Labels = raw26764Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26764 raw26764Labels permutation185 permutation5
    mixedMoment B raw26764step0 raw26764step0Labels = mixedMoment B raw26764step1 raw26764step1Labels := by
      have ha : raw26764step1 = -raw26764step0 := by apply Matrix.ext; change ∀ i j, raw26764step1 i j = -(raw26764step0 i j); unfold raw26764step1 raw26764step0; decide +kernel
      have hl : raw26764step1Labels = raw26764step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw26764step1 raw26764step1Labels = mixedMoment B raw26764step2 raw26764step2Labels := by
      have ha : raw26764step2 = raw26764step1 := by apply Matrix.ext; unfold raw26764step2 raw26764step1; decide +kernel
      have hl : raw26764step1Labels = labelEmbedding1 ∘ raw26764step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26764step1 raw26764step1Labels raw26764step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3289 node3289Labels := by rfl

theorem canonical26765 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26765 raw26765Labels = mixedMoment B node3289 node3289Labels := by
  calc
    mixedMoment B raw26765 raw26765Labels = mixedMoment B raw26765step0 raw26765step0Labels := by
      have ha : raw26765step0 = (fun i j => raw26765 (permutation209 i) (permutation5 j)) := by apply Matrix.ext; unfold raw26765step0 raw26765; decide +kernel
      have hl : raw26765step0Labels = raw26765Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26765 raw26765Labels permutation209 permutation5
    mixedMoment B raw26765step0 raw26765step0Labels = mixedMoment B raw26765step1 raw26765step1Labels := by
      have ha : raw26765step1 = -raw26765step0 := by apply Matrix.ext; change ∀ i j, raw26765step1 i j = -(raw26765step0 i j); unfold raw26765step1 raw26765step0; decide +kernel
      have hl : raw26765step1Labels = raw26765step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw26765step1 raw26765step1Labels = mixedMoment B raw26765step2 raw26765step2Labels := by
      have ha : raw26765step2 = raw26765step1 := by apply Matrix.ext; unfold raw26765step2 raw26765step1; decide +kernel
      have hl : raw26765step1Labels = labelEmbedding1 ∘ raw26765step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26765step1 raw26765step1Labels raw26765step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3289 node3289Labels := by rfl

theorem canonical26766 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26766 raw26766Labels = mixedMoment B node3289 node3289Labels := by
  calc
    mixedMoment B raw26766 raw26766Labels = mixedMoment B raw26766step0 raw26766step0Labels := by
      have ha : raw26766step0 = (fun i j => raw26766 (permutation233 i) (permutation5 j)) := by apply Matrix.ext; unfold raw26766step0 raw26766; decide +kernel
      have hl : raw26766step0Labels = raw26766Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26766 raw26766Labels permutation233 permutation5
    mixedMoment B raw26766step0 raw26766step0Labels = mixedMoment B raw26766step1 raw26766step1Labels := by
      have ha : raw26766step1 = -raw26766step0 := by apply Matrix.ext; change ∀ i j, raw26766step1 i j = -(raw26766step0 i j); unfold raw26766step1 raw26766step0; decide +kernel
      have hl : raw26766step1Labels = raw26766step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw26766step1 raw26766step1Labels = mixedMoment B raw26766step2 raw26766step2Labels := by
      have ha : raw26766step2 = raw26766step1 := by apply Matrix.ext; unfold raw26766step2 raw26766step1; decide +kernel
      have hl : raw26766step1Labels = labelEmbedding1 ∘ raw26766step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26766step1 raw26766step1Labels raw26766step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3289 node3289Labels := by rfl

theorem canonical26767 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26767 raw26767Labels = mixedMoment B node3304 node3304Labels := by
  calc
    mixedMoment B raw26767 raw26767Labels = mixedMoment B raw26767step0 raw26767step0Labels := by
      have hz : ∀ j, raw26767 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw26767step0 = (fun i j => raw26767 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw26767step0 raw26767; decide +kernel
      have hl : raw26767step0Labels = raw26767Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26767 raw26767Labels permutation590 hz
    mixedMoment B raw26767step0 raw26767step0Labels = mixedMoment B raw26767step1 raw26767step1Labels := by
      have ha : raw26767step1 = (fun i j => raw26767step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw26767step1 raw26767step0; decide +kernel
      have hl : raw26767step1Labels = raw26767step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26767step0 raw26767step0Labels permutation32 permutation7
    mixedMoment B raw26767step1 raw26767step1Labels = mixedMoment B raw26767step2 raw26767step2Labels := by
      have ha : raw26767step2 = -raw26767step1 := by apply Matrix.ext; change ∀ i j, raw26767step2 i j = -(raw26767step1 i j); unfold raw26767step2 raw26767step1; decide +kernel
      have hl : raw26767step2Labels = raw26767step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw26767step2 raw26767step2Labels = mixedMoment B raw26767step3 raw26767step3Labels := by
      have ha : raw26767step3 = raw26767step2 := by apply Matrix.ext; unfold raw26767step3 raw26767step2; decide +kernel
      have hl : raw26767step2Labels = labelEmbedding1 ∘ raw26767step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26767step2 raw26767step2Labels raw26767step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3304 node3304Labels := by rfl

theorem canonical26768 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26768 raw26768Labels = mixedMoment B node1504 node1504Labels := by
  calc
    mixedMoment B raw26768 raw26768Labels = mixedMoment B raw26768step0 raw26768step0Labels := by
      have ha : raw26768step0 = (fun i j => raw26768 (permutation213 i) (permutation5 j)) := by apply Matrix.ext; unfold raw26768step0 raw26768; decide +kernel
      have hl : raw26768step0Labels = raw26768Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26768 raw26768Labels permutation213 permutation5
    mixedMoment B raw26768step0 raw26768step0Labels = mixedMoment B raw26768step1 raw26768step1Labels := by
      have ha : raw26768step1 = -raw26768step0 := by apply Matrix.ext; change ∀ i j, raw26768step1 i j = -(raw26768step0 i j); unfold raw26768step1 raw26768step0; decide +kernel
      have hl : raw26768step1Labels = raw26768step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw26768step1 raw26768step1Labels = mixedMoment B raw26768step2 raw26768step2Labels := by
      have ha : raw26768step2 = raw26768step1 := by apply Matrix.ext; unfold raw26768step2 raw26768step1; decide +kernel
      have hl : raw26768step1Labels = labelEmbedding1 ∘ raw26768step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26768step1 raw26768step1Labels raw26768step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1504 node1504Labels := by rfl

theorem canonical26769 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26769 raw26769Labels = mixedMoment B node3263 node3263Labels := by
  calc
    mixedMoment B raw26769 raw26769Labels = mixedMoment B raw26769step0 raw26769step0Labels := by
      have ha : raw26769step0 = (fun i j => raw26769 (permutation173 i) (permutation7 j)) := by apply Matrix.ext; unfold raw26769step0 raw26769; decide +kernel
      have hl : raw26769step0Labels = raw26769Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26769 raw26769Labels permutation173 permutation7
    mixedMoment B raw26769step0 raw26769step0Labels = mixedMoment B raw26769step1 raw26769step1Labels := by
      have ha : raw26769step1 = -raw26769step0 := by apply Matrix.ext; change ∀ i j, raw26769step1 i j = -(raw26769step0 i j); unfold raw26769step1 raw26769step0; decide +kernel
      have hl : raw26769step1Labels = raw26769step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw26769step1 raw26769step1Labels = mixedMoment B raw26769step2 raw26769step2Labels := by
      have ha : raw26769step2 = raw26769step1 := by apply Matrix.ext; unfold raw26769step2 raw26769step1; decide +kernel
      have hl : raw26769step1Labels = labelEmbedding1 ∘ raw26769step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26769step1 raw26769step1Labels raw26769step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3263 node3263Labels := by rfl

theorem canonical26770 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26770 raw26770Labels = mixedMoment B node3290 node3290Labels := by
  calc
    mixedMoment B raw26770 raw26770Labels = mixedMoment B raw26770step0 raw26770step0Labels := by
      have ha : raw26770step0 = (fun i j => raw26770 (permutation213 i) (permutation5 j)) := by apply Matrix.ext; unfold raw26770step0 raw26770; decide +kernel
      have hl : raw26770step0Labels = raw26770Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26770 raw26770Labels permutation213 permutation5
    mixedMoment B raw26770step0 raw26770step0Labels = mixedMoment B raw26770step1 raw26770step1Labels := by
      have ha : raw26770step1 = -raw26770step0 := by apply Matrix.ext; change ∀ i j, raw26770step1 i j = -(raw26770step0 i j); unfold raw26770step1 raw26770step0; decide +kernel
      have hl : raw26770step1Labels = raw26770step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw26770step1 raw26770step1Labels = mixedMoment B raw26770step2 raw26770step2Labels := by
      have ha : raw26770step2 = raw26770step1 := by apply Matrix.ext; unfold raw26770step2 raw26770step1; decide +kernel
      have hl : raw26770step1Labels = labelEmbedding1 ∘ raw26770step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26770step1 raw26770step1Labels raw26770step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3290 node3290Labels := by rfl

theorem canonical26771 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26771 raw26771Labels = mixedMoment B node3290 node3290Labels := by
  calc
    mixedMoment B raw26771 raw26771Labels = mixedMoment B raw26771step0 raw26771step0Labels := by
      have ha : raw26771step0 = (fun i j => raw26771 (permutation235 i) (permutation5 j)) := by apply Matrix.ext; unfold raw26771step0 raw26771; decide +kernel
      have hl : raw26771step0Labels = raw26771Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26771 raw26771Labels permutation235 permutation5
    mixedMoment B raw26771step0 raw26771step0Labels = mixedMoment B raw26771step1 raw26771step1Labels := by
      have ha : raw26771step1 = -raw26771step0 := by apply Matrix.ext; change ∀ i j, raw26771step1 i j = -(raw26771step0 i j); unfold raw26771step1 raw26771step0; decide +kernel
      have hl : raw26771step1Labels = raw26771step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw26771step1 raw26771step1Labels = mixedMoment B raw26771step2 raw26771step2Labels := by
      have ha : raw26771step2 = raw26771step1 := by apply Matrix.ext; unfold raw26771step2 raw26771step1; decide +kernel
      have hl : raw26771step1Labels = labelEmbedding1 ∘ raw26771step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26771step1 raw26771step1Labels raw26771step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3290 node3290Labels := by rfl

theorem canonical26772 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26772 raw26772Labels = mixedMoment B node3299 node3299Labels := by
  calc
    mixedMoment B raw26772 raw26772Labels = mixedMoment B raw26772step0 raw26772step0Labels := by
      have hz : ∀ j, raw26772 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw26772step0 = (fun i j => raw26772 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw26772step0 raw26772; decide +kernel
      have hl : raw26772step0Labels = raw26772Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26772 raw26772Labels permutation590 hz
    mixedMoment B raw26772step0 raw26772step0Labels = mixedMoment B raw26772step1 raw26772step1Labels := by
      have ha : raw26772step1 = (fun i j => raw26772step0 (permutation35 i) (permutation7 j)) := by apply Matrix.ext; unfold raw26772step1 raw26772step0; decide +kernel
      have hl : raw26772step1Labels = raw26772step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26772step0 raw26772step0Labels permutation35 permutation7
    mixedMoment B raw26772step1 raw26772step1Labels = mixedMoment B raw26772step2 raw26772step2Labels := by
      have ha : raw26772step2 = -raw26772step1 := by apply Matrix.ext; change ∀ i j, raw26772step2 i j = -(raw26772step1 i j); unfold raw26772step2 raw26772step1; decide +kernel
      have hl : raw26772step2Labels = raw26772step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw26772step2 raw26772step2Labels = mixedMoment B raw26772step3 raw26772step3Labels := by
      have ha : raw26772step3 = raw26772step2 := by apply Matrix.ext; unfold raw26772step3 raw26772step2; decide +kernel
      have hl : raw26772step2Labels = labelEmbedding1 ∘ raw26772step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26772step2 raw26772step2Labels raw26772step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3299 node3299Labels := by rfl

theorem canonical26773 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26773 raw26773Labels = mixedMoment B node1504 node1504Labels := by
  calc
    mixedMoment B raw26773 raw26773Labels = mixedMoment B raw26773step0 raw26773step0Labels := by
      have ha : raw26773step0 = (fun i j => raw26773 (permutation189 i) (permutation5 j)) := by apply Matrix.ext; unfold raw26773step0 raw26773; decide +kernel
      have hl : raw26773step0Labels = raw26773Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26773 raw26773Labels permutation189 permutation5
    mixedMoment B raw26773step0 raw26773step0Labels = mixedMoment B raw26773step1 raw26773step1Labels := by
      have ha : raw26773step1 = -raw26773step0 := by apply Matrix.ext; change ∀ i j, raw26773step1 i j = -(raw26773step0 i j); unfold raw26773step1 raw26773step0; decide +kernel
      have hl : raw26773step1Labels = raw26773step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw26773step1 raw26773step1Labels = mixedMoment B raw26773step2 raw26773step2Labels := by
      have ha : raw26773step2 = raw26773step1 := by apply Matrix.ext; unfold raw26773step2 raw26773step1; decide +kernel
      have hl : raw26773step1Labels = labelEmbedding1 ∘ raw26773step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26773step1 raw26773step1Labels raw26773step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1504 node1504Labels := by rfl

theorem canonical26774 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26774 raw26774Labels = mixedMoment B node3263 node3263Labels := by
  calc
    mixedMoment B raw26774 raw26774Labels = mixedMoment B raw26774step0 raw26774step0Labels := by
      have ha : raw26774step0 = (fun i j => raw26774 (permutation171 i) (permutation7 j)) := by apply Matrix.ext; unfold raw26774step0 raw26774; decide +kernel
      have hl : raw26774step0Labels = raw26774Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26774 raw26774Labels permutation171 permutation7
    mixedMoment B raw26774step0 raw26774step0Labels = mixedMoment B raw26774step1 raw26774step1Labels := by
      have ha : raw26774step1 = -raw26774step0 := by apply Matrix.ext; change ∀ i j, raw26774step1 i j = -(raw26774step0 i j); unfold raw26774step1 raw26774step0; decide +kernel
      have hl : raw26774step1Labels = raw26774step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw26774step1 raw26774step1Labels = mixedMoment B raw26774step2 raw26774step2Labels := by
      have ha : raw26774step2 = raw26774step1 := by apply Matrix.ext; unfold raw26774step2 raw26774step1; decide +kernel
      have hl : raw26774step1Labels = labelEmbedding1 ∘ raw26774step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26774step1 raw26774step1Labels raw26774step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3263 node3263Labels := by rfl

theorem canonical26775 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26775 raw26775Labels = mixedMoment B node3290 node3290Labels := by
  calc
    mixedMoment B raw26775 raw26775Labels = mixedMoment B raw26775step0 raw26775step0Labels := by
      have ha : raw26775step0 = (fun i j => raw26775 (permutation189 i) (permutation5 j)) := by apply Matrix.ext; unfold raw26775step0 raw26775; decide +kernel
      have hl : raw26775step0Labels = raw26775Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26775 raw26775Labels permutation189 permutation5
    mixedMoment B raw26775step0 raw26775step0Labels = mixedMoment B raw26775step1 raw26775step1Labels := by
      have ha : raw26775step1 = -raw26775step0 := by apply Matrix.ext; change ∀ i j, raw26775step1 i j = -(raw26775step0 i j); unfold raw26775step1 raw26775step0; decide +kernel
      have hl : raw26775step1Labels = raw26775step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw26775step1 raw26775step1Labels = mixedMoment B raw26775step2 raw26775step2Labels := by
      have ha : raw26775step2 = raw26775step1 := by apply Matrix.ext; unfold raw26775step2 raw26775step1; decide +kernel
      have hl : raw26775step1Labels = labelEmbedding1 ∘ raw26775step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26775step1 raw26775step1Labels raw26775step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3290 node3290Labels := by rfl

theorem canonical26776 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26776 raw26776Labels = mixedMoment B node3290 node3290Labels := by
  calc
    mixedMoment B raw26776 raw26776Labels = mixedMoment B raw26776step0 raw26776step0Labels := by
      have ha : raw26776step0 = (fun i j => raw26776 (permutation231 i) (permutation5 j)) := by apply Matrix.ext; unfold raw26776step0 raw26776; decide +kernel
      have hl : raw26776step0Labels = raw26776Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26776 raw26776Labels permutation231 permutation5
    mixedMoment B raw26776step0 raw26776step0Labels = mixedMoment B raw26776step1 raw26776step1Labels := by
      have ha : raw26776step1 = -raw26776step0 := by apply Matrix.ext; change ∀ i j, raw26776step1 i j = -(raw26776step0 i j); unfold raw26776step1 raw26776step0; decide +kernel
      have hl : raw26776step1Labels = raw26776step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw26776step1 raw26776step1Labels = mixedMoment B raw26776step2 raw26776step2Labels := by
      have ha : raw26776step2 = raw26776step1 := by apply Matrix.ext; unfold raw26776step2 raw26776step1; decide +kernel
      have hl : raw26776step1Labels = labelEmbedding1 ∘ raw26776step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26776step1 raw26776step1Labels raw26776step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3290 node3290Labels := by rfl

theorem canonical26777 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26777 raw26777Labels = mixedMoment B node3299 node3299Labels := by
  calc
    mixedMoment B raw26777 raw26777Labels = mixedMoment B raw26777step0 raw26777step0Labels := by
      have hz : ∀ j, raw26777 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw26777step0 = (fun i j => raw26777 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw26777step0 raw26777; decide +kernel
      have hl : raw26777step0Labels = raw26777Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26777 raw26777Labels permutation590 hz
    mixedMoment B raw26777step0 raw26777step0Labels = mixedMoment B raw26777step1 raw26777step1Labels := by
      have ha : raw26777step1 = (fun i j => raw26777step0 (permutation33 i) (permutation7 j)) := by apply Matrix.ext; unfold raw26777step1 raw26777step0; decide +kernel
      have hl : raw26777step1Labels = raw26777step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26777step0 raw26777step0Labels permutation33 permutation7
    mixedMoment B raw26777step1 raw26777step1Labels = mixedMoment B raw26777step2 raw26777step2Labels := by
      have ha : raw26777step2 = -raw26777step1 := by apply Matrix.ext; change ∀ i j, raw26777step2 i j = -(raw26777step1 i j); unfold raw26777step2 raw26777step1; decide +kernel
      have hl : raw26777step2Labels = raw26777step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw26777step2 raw26777step2Labels = mixedMoment B raw26777step3 raw26777step3Labels := by
      have ha : raw26777step3 = raw26777step2 := by apply Matrix.ext; unfold raw26777step3 raw26777step2; decide +kernel
      have hl : raw26777step2Labels = labelEmbedding1 ∘ raw26777step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26777step2 raw26777step2Labels raw26777step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3299 node3299Labels := by rfl

theorem canonical26778 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26778 raw26778Labels = mixedMoment B node1504 node1504Labels := by
  calc
    mixedMoment B raw26778 raw26778Labels = mixedMoment B raw26778step0 raw26778step0Labels := by
      have ha : raw26778step0 = (fun i j => raw26778 (permutation183 i) (permutation5 j)) := by apply Matrix.ext; unfold raw26778step0 raw26778; decide +kernel
      have hl : raw26778step0Labels = raw26778Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26778 raw26778Labels permutation183 permutation5
    mixedMoment B raw26778step0 raw26778step0Labels = mixedMoment B raw26778step1 raw26778step1Labels := by
      have ha : raw26778step1 = -raw26778step0 := by apply Matrix.ext; change ∀ i j, raw26778step1 i j = -(raw26778step0 i j); unfold raw26778step1 raw26778step0; decide +kernel
      have hl : raw26778step1Labels = raw26778step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw26778step1 raw26778step1Labels = mixedMoment B raw26778step2 raw26778step2Labels := by
      have ha : raw26778step2 = raw26778step1 := by apply Matrix.ext; unfold raw26778step2 raw26778step1; decide +kernel
      have hl : raw26778step1Labels = labelEmbedding1 ∘ raw26778step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26778step1 raw26778step1Labels raw26778step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1504 node1504Labels := by rfl

theorem canonical26779 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26779 raw26779Labels = mixedMoment B node3263 node3263Labels := by
  calc
    mixedMoment B raw26779 raw26779Labels = mixedMoment B raw26779step0 raw26779step0Labels := by
      have ha : raw26779step0 = (fun i j => raw26779 (permutation170 i) (permutation7 j)) := by apply Matrix.ext; unfold raw26779step0 raw26779; decide +kernel
      have hl : raw26779step0Labels = raw26779Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26779 raw26779Labels permutation170 permutation7
    mixedMoment B raw26779step0 raw26779step0Labels = mixedMoment B raw26779step1 raw26779step1Labels := by
      have ha : raw26779step1 = -raw26779step0 := by apply Matrix.ext; change ∀ i j, raw26779step1 i j = -(raw26779step0 i j); unfold raw26779step1 raw26779step0; decide +kernel
      have hl : raw26779step1Labels = raw26779step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw26779step1 raw26779step1Labels = mixedMoment B raw26779step2 raw26779step2Labels := by
      have ha : raw26779step2 = raw26779step1 := by apply Matrix.ext; unfold raw26779step2 raw26779step1; decide +kernel
      have hl : raw26779step1Labels = labelEmbedding1 ∘ raw26779step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26779step1 raw26779step1Labels raw26779step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3263 node3263Labels := by rfl

theorem canonical26780 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26780 raw26780Labels = mixedMoment B node3290 node3290Labels := by
  calc
    mixedMoment B raw26780 raw26780Labels = mixedMoment B raw26780step0 raw26780step0Labels := by
      have ha : raw26780step0 = (fun i j => raw26780 (permutation183 i) (permutation5 j)) := by apply Matrix.ext; unfold raw26780step0 raw26780; decide +kernel
      have hl : raw26780step0Labels = raw26780Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26780 raw26780Labels permutation183 permutation5
    mixedMoment B raw26780step0 raw26780step0Labels = mixedMoment B raw26780step1 raw26780step1Labels := by
      have ha : raw26780step1 = -raw26780step0 := by apply Matrix.ext; change ∀ i j, raw26780step1 i j = -(raw26780step0 i j); unfold raw26780step1 raw26780step0; decide +kernel
      have hl : raw26780step1Labels = raw26780step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw26780step1 raw26780step1Labels = mixedMoment B raw26780step2 raw26780step2Labels := by
      have ha : raw26780step2 = raw26780step1 := by apply Matrix.ext; unfold raw26780step2 raw26780step1; decide +kernel
      have hl : raw26780step1Labels = labelEmbedding1 ∘ raw26780step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26780step1 raw26780step1Labels raw26780step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3290 node3290Labels := by rfl

theorem canonical26781 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26781 raw26781Labels = mixedMoment B node3290 node3290Labels := by
  calc
    mixedMoment B raw26781 raw26781Labels = mixedMoment B raw26781step0 raw26781step0Labels := by
      have ha : raw26781step0 = (fun i j => raw26781 (permutation207 i) (permutation5 j)) := by apply Matrix.ext; unfold raw26781step0 raw26781; decide +kernel
      have hl : raw26781step0Labels = raw26781Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26781 raw26781Labels permutation207 permutation5
    mixedMoment B raw26781step0 raw26781step0Labels = mixedMoment B raw26781step1 raw26781step1Labels := by
      have ha : raw26781step1 = -raw26781step0 := by apply Matrix.ext; change ∀ i j, raw26781step1 i j = -(raw26781step0 i j); unfold raw26781step1 raw26781step0; decide +kernel
      have hl : raw26781step1Labels = raw26781step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw26781step1 raw26781step1Labels = mixedMoment B raw26781step2 raw26781step2Labels := by
      have ha : raw26781step2 = raw26781step1 := by apply Matrix.ext; unfold raw26781step2 raw26781step1; decide +kernel
      have hl : raw26781step1Labels = labelEmbedding1 ∘ raw26781step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26781step1 raw26781step1Labels raw26781step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3290 node3290Labels := by rfl

theorem canonical26782 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26782 raw26782Labels = mixedMoment B node3299 node3299Labels := by
  calc
    mixedMoment B raw26782 raw26782Labels = mixedMoment B raw26782step0 raw26782step0Labels := by
      have hz : ∀ j, raw26782 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw26782step0 = (fun i j => raw26782 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw26782step0 raw26782; decide +kernel
      have hl : raw26782step0Labels = raw26782Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26782 raw26782Labels permutation590 hz
    mixedMoment B raw26782step0 raw26782step0Labels = mixedMoment B raw26782step1 raw26782step1Labels := by
      have ha : raw26782step1 = (fun i j => raw26782step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw26782step1 raw26782step0; decide +kernel
      have hl : raw26782step1Labels = raw26782step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26782step0 raw26782step0Labels permutation32 permutation7
    mixedMoment B raw26782step1 raw26782step1Labels = mixedMoment B raw26782step2 raw26782step2Labels := by
      have ha : raw26782step2 = -raw26782step1 := by apply Matrix.ext; change ∀ i j, raw26782step2 i j = -(raw26782step1 i j); unfold raw26782step2 raw26782step1; decide +kernel
      have hl : raw26782step2Labels = raw26782step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw26782step2 raw26782step2Labels = mixedMoment B raw26782step3 raw26782step3Labels := by
      have ha : raw26782step3 = raw26782step2 := by apply Matrix.ext; unfold raw26782step3 raw26782step2; decide +kernel
      have hl : raw26782step2Labels = labelEmbedding1 ∘ raw26782step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26782step2 raw26782step2Labels raw26782step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3299 node3299Labels := by rfl

theorem canonical26783 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26783 raw26783Labels = mixedMoment B node1501 node1501Labels := by
  calc
    mixedMoment B raw26783 raw26783Labels = mixedMoment B raw26783step0 raw26783step0Labels := by
      have ha : raw26783step0 = (fun i j => raw26783 (permutation184 i) (permutation5 j)) := by apply Matrix.ext; unfold raw26783step0 raw26783; decide +kernel
      have hl : raw26783step0Labels = raw26783Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26783 raw26783Labels permutation184 permutation5
    mixedMoment B raw26783step0 raw26783step0Labels = mixedMoment B raw26783step1 raw26783step1Labels := by
      have ha : raw26783step1 = -raw26783step0 := by apply Matrix.ext; change ∀ i j, raw26783step1 i j = -(raw26783step0 i j); unfold raw26783step1 raw26783step0; decide +kernel
      have hl : raw26783step1Labels = raw26783step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw26783step1 raw26783step1Labels = mixedMoment B raw26783step2 raw26783step2Labels := by
      have ha : raw26783step2 = raw26783step1 := by apply Matrix.ext; unfold raw26783step2 raw26783step1; decide +kernel
      have hl : raw26783step1Labels = labelEmbedding1 ∘ raw26783step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26783step1 raw26783step1Labels raw26783step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1501 node1501Labels := by rfl

theorem canonical26784 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26784 raw26784Labels = mixedMoment B node3269 node3269Labels := by
  calc
    mixedMoment B raw26784 raw26784Labels = mixedMoment B raw26784step0 raw26784step0Labels := by
      have ha : raw26784step0 = (fun i j => raw26784 (permutation170 i) (permutation7 j)) := by apply Matrix.ext; unfold raw26784step0 raw26784; decide +kernel
      have hl : raw26784step0Labels = raw26784Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26784 raw26784Labels permutation170 permutation7
    mixedMoment B raw26784step0 raw26784step0Labels = mixedMoment B raw26784step1 raw26784step1Labels := by
      have ha : raw26784step1 = -raw26784step0 := by apply Matrix.ext; change ∀ i j, raw26784step1 i j = -(raw26784step0 i j); unfold raw26784step1 raw26784step0; decide +kernel
      have hl : raw26784step1Labels = raw26784step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw26784step1 raw26784step1Labels = mixedMoment B raw26784step2 raw26784step2Labels := by
      have ha : raw26784step2 = raw26784step1 := by apply Matrix.ext; unfold raw26784step2 raw26784step1; decide +kernel
      have hl : raw26784step1Labels = labelEmbedding1 ∘ raw26784step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26784step1 raw26784step1Labels raw26784step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3269 node3269Labels := by rfl

theorem canonical26785 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26785 raw26785Labels = mixedMoment B node3288 node3288Labels := by
  calc
    mixedMoment B raw26785 raw26785Labels = mixedMoment B raw26785step0 raw26785step0Labels := by
      have ha : raw26785step0 = (fun i j => raw26785 (permutation232 i) (permutation5 j)) := by apply Matrix.ext; unfold raw26785step0 raw26785; decide +kernel
      have hl : raw26785step0Labels = raw26785Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26785 raw26785Labels permutation232 permutation5
    mixedMoment B raw26785step0 raw26785step0Labels = mixedMoment B raw26785step1 raw26785step1Labels := by
      have ha : raw26785step1 = -raw26785step0 := by apply Matrix.ext; change ∀ i j, raw26785step1 i j = -(raw26785step0 i j); unfold raw26785step1 raw26785step0; decide +kernel
      have hl : raw26785step1Labels = raw26785step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw26785step1 raw26785step1Labels = mixedMoment B raw26785step2 raw26785step2Labels := by
      have ha : raw26785step2 = raw26785step1 := by apply Matrix.ext; unfold raw26785step2 raw26785step1; decide +kernel
      have hl : raw26785step1Labels = labelEmbedding1 ∘ raw26785step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26785step1 raw26785step1Labels raw26785step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3288 node3288Labels := by rfl

theorem canonical26786 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26786 raw26786Labels = mixedMoment B node1235 node1235Labels := by
  calc
    mixedMoment B raw26786 raw26786Labels = mixedMoment B raw26786step0 raw26786step0Labels := by
      have ha : raw26786step0 = (fun i j => raw26786 (permutation170 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26786step0 raw26786; decide +kernel
      have hl : raw26786step0Labels = raw26786Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26786 raw26786Labels permutation170 permutation2
    _ = mixedMoment B node1235 node1235Labels := by rfl

theorem canonical26787 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26787 raw26787Labels = mixedMoment B node637 node637Labels := by
  calc
    mixedMoment B raw26787 raw26787Labels = mixedMoment B raw26787step0 raw26787step0Labels := by
      have ha : raw26787step0 = (fun i j => raw26787 (permutation170 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26787step0 raw26787; decide +kernel
      have hl : raw26787step0Labels = raw26787Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26787 raw26787Labels permutation170 permutation2
    _ = mixedMoment B node637 node637Labels := by rfl

theorem canonical26788 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26788 raw26788Labels = mixedMoment B node625 node625Labels := by
  calc
    mixedMoment B raw26788 raw26788Labels = mixedMoment B raw26788step0 raw26788step0Labels := by
      have ha : raw26788step0 = (fun i j => raw26788 (permutation173 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26788step0 raw26788; decide +kernel
      have hl : raw26788step0Labels = raw26788Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26788 raw26788Labels permutation173 permutation2
    _ = mixedMoment B node625 node625Labels := by rfl

theorem canonical26789 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26789 raw26789Labels = mixedMoment B node625 node625Labels := by
  calc
    mixedMoment B raw26789 raw26789Labels = mixedMoment B raw26789step0 raw26789step0Labels := by
      have ha : raw26789step0 = (fun i j => raw26789 (permutation171 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26789step0 raw26789; decide +kernel
      have hl : raw26789step0Labels = raw26789Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26789 raw26789Labels permutation171 permutation2
    _ = mixedMoment B node625 node625Labels := by rfl

theorem canonical26790 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26790 raw26790Labels = mixedMoment B node625 node625Labels := by
  calc
    mixedMoment B raw26790 raw26790Labels = mixedMoment B raw26790step0 raw26790step0Labels := by
      have ha : raw26790step0 = (fun i j => raw26790 (permutation170 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26790step0 raw26790; decide +kernel
      have hl : raw26790step0Labels = raw26790Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26790 raw26790Labels permutation170 permutation2
    _ = mixedMoment B node625 node625Labels := by rfl

theorem canonical26791 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26791 raw26791Labels = mixedMoment B node629 node629Labels := by
  calc
    _ = mixedMoment B node629 node629Labels := by rfl

theorem canonical26822 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26822 raw26822Labels = mixedMoment B node2880 node2880Labels := by
  calc
    mixedMoment B raw26822 raw26822Labels = mixedMoment B raw26822step0 raw26822step0Labels := by
      have ha : raw26822step0 = (fun i j => raw26822 (permutation170 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26822step0 raw26822; decide +kernel
      have hl : raw26822step0Labels = raw26822Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26822 raw26822Labels permutation170 permutation3
    _ = mixedMoment B node2880 node2880Labels := by rfl

theorem canonical26823 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26823 raw26823Labels = mixedMoment B node3100 node3100Labels := by
  calc
    mixedMoment B raw26823 raw26823Labels = mixedMoment B raw26823step0 raw26823step0Labels := by
      have hz : ∀ j, raw26823 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw26823step0 = (fun i j => raw26823 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw26823step0 raw26823; decide +kernel
      have hl : raw26823step0Labels = raw26823Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26823 raw26823Labels permutation346 hz
    mixedMoment B raw26823step0 raw26823step0Labels = mixedMoment B raw26823step1 raw26823step1Labels := by
      have ha : raw26823step1 = (fun i j => raw26823step0 (permutation36 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26823step1 raw26823step0; decide +kernel
      have hl : raw26823step1Labels = raw26823step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26823step0 raw26823step0Labels permutation36 permutation3
    _ = mixedMoment B node3100 node3100Labels := by rfl

theorem canonical26824 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26824 raw26824Labels = mixedMoment B node3100 node3100Labels := by
  calc
    mixedMoment B raw26824 raw26824Labels = mixedMoment B raw26824step0 raw26824step0Labels := by
      have hz : ∀ j, raw26824 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw26824step0 = (fun i j => raw26824 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw26824step0 raw26824; decide +kernel
      have hl : raw26824step0Labels = raw26824Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26824 raw26824Labels permutation434 hz
    mixedMoment B raw26824step0 raw26824step0Labels = mixedMoment B raw26824step1 raw26824step1Labels := by
      have ha : raw26824step1 = (fun i j => raw26824step0 (permutation36 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26824step1 raw26824step0; decide +kernel
      have hl : raw26824step1Labels = raw26824step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26824step0 raw26824step0Labels permutation36 permutation3
    _ = mixedMoment B node3100 node3100Labels := by rfl

theorem canonical26825 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26825 raw26825Labels = mixedMoment B node3100 node3100Labels := by
  calc
    mixedMoment B raw26825 raw26825Labels = mixedMoment B raw26825step0 raw26825step0Labels := by
      have hz : ∀ j, raw26825 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw26825step0 = (fun i j => raw26825 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw26825step0 raw26825; decide +kernel
      have hl : raw26825step0Labels = raw26825Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26825 raw26825Labels permutation520 hz
    mixedMoment B raw26825step0 raw26825step0Labels = mixedMoment B raw26825step1 raw26825step1Labels := by
      have ha : raw26825step1 = (fun i j => raw26825step0 (permutation36 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26825step1 raw26825step0; decide +kernel
      have hl : raw26825step1Labels = raw26825step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26825step0 raw26825step0Labels permutation36 permutation3
    _ = mixedMoment B node3100 node3100Labels := by rfl

theorem canonical26826 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26826 raw26826Labels = mixedMoment B node3076 node3076Labels := by
  calc
    mixedMoment B raw26826 raw26826Labels = mixedMoment B raw26826step0 raw26826step0Labels := by
      have ha : raw26826step0 = (fun i j => raw26826 (permutation170 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26826step0 raw26826; decide +kernel
      have hl : raw26826step0Labels = raw26826Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26826 raw26826Labels permutation170 permutation3
    _ = mixedMoment B node3076 node3076Labels := by rfl

theorem canonical26827 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26827 raw26827Labels = mixedMoment B node599 node599Labels := by
  calc
    mixedMoment B raw26827 raw26827Labels = mixedMoment B raw26827step0 raw26827step0Labels := by
      have ha : raw26827step0 = (fun i j => raw26827 (permutation170 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26827step0 raw26827; decide +kernel
      have hl : raw26827step0Labels = raw26827Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26827 raw26827Labels permutation170 permutation3
    _ = mixedMoment B node599 node599Labels := by rfl

theorem canonical26828 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26828 raw26828Labels = mixedMoment B node1299 node1299Labels := by
  calc
    mixedMoment B raw26828 raw26828Labels = mixedMoment B raw26828step0 raw26828step0Labels := by
      have hz : ∀ j, raw26828 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw26828step0 = (fun i j => raw26828 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw26828step0 raw26828; decide +kernel
      have hl : raw26828step0Labels = raw26828Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26828 raw26828Labels permutation346 hz
    mixedMoment B raw26828step0 raw26828step0Labels = mixedMoment B raw26828step1 raw26828step1Labels := by
      have ha : raw26828step1 = (fun i j => raw26828step0 (permutation36 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26828step1 raw26828step0; decide +kernel
      have hl : raw26828step1Labels = raw26828step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26828step0 raw26828step0Labels permutation36 permutation3
    _ = mixedMoment B node1299 node1299Labels := by rfl

theorem canonical26829 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26829 raw26829Labels = mixedMoment B node1299 node1299Labels := by
  calc
    mixedMoment B raw26829 raw26829Labels = mixedMoment B raw26829step0 raw26829step0Labels := by
      have hz : ∀ j, raw26829 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw26829step0 = (fun i j => raw26829 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw26829step0 raw26829; decide +kernel
      have hl : raw26829step0Labels = raw26829Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26829 raw26829Labels permutation434 hz
    mixedMoment B raw26829step0 raw26829step0Labels = mixedMoment B raw26829step1 raw26829step1Labels := by
      have ha : raw26829step1 = (fun i j => raw26829step0 (permutation36 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26829step1 raw26829step0; decide +kernel
      have hl : raw26829step1Labels = raw26829step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26829step0 raw26829step0Labels permutation36 permutation3
    _ = mixedMoment B node1299 node1299Labels := by rfl

theorem canonical26830 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26830 raw26830Labels = mixedMoment B node1299 node1299Labels := by
  calc
    mixedMoment B raw26830 raw26830Labels = mixedMoment B raw26830step0 raw26830step0Labels := by
      have hz : ∀ j, raw26830 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw26830step0 = (fun i j => raw26830 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw26830step0 raw26830; decide +kernel
      have hl : raw26830step0Labels = raw26830Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26830 raw26830Labels permutation520 hz
    mixedMoment B raw26830step0 raw26830step0Labels = mixedMoment B raw26830step1 raw26830step1Labels := by
      have ha : raw26830step1 = (fun i j => raw26830step0 (permutation36 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26830step1 raw26830step0; decide +kernel
      have hl : raw26830step1Labels = raw26830step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26830step0 raw26830step0Labels permutation36 permutation3
    _ = mixedMoment B node1299 node1299Labels := by rfl

theorem canonical26831 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26831 raw26831Labels = mixedMoment B node1235 node1235Labels := by
  calc
    mixedMoment B raw26831 raw26831Labels = mixedMoment B raw26831step0 raw26831step0Labels := by
      have ha : raw26831step0 = (fun i j => raw26831 (permutation246 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26831step0 raw26831; decide +kernel
      have hl : raw26831step0Labels = raw26831Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26831 raw26831Labels permutation246 permutation3
    _ = mixedMoment B node1235 node1235Labels := by rfl

theorem canonical26832 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26832 raw26832Labels = mixedMoment B node567 node567Labels := by
  calc
    mixedMoment B raw26832 raw26832Labels = mixedMoment B raw26832step0 raw26832step0Labels := by
      have ha : raw26832step0 = (fun i j => raw26832 (permutation173 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26832step0 raw26832; decide +kernel
      have hl : raw26832step0Labels = raw26832Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26832 raw26832Labels permutation173 permutation3
    _ = mixedMoment B node567 node567Labels := by rfl

theorem canonical26833 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26833 raw26833Labels = mixedMoment B node1097 node1097Labels := by
  calc
    mixedMoment B raw26833 raw26833Labels = mixedMoment B raw26833step0 raw26833step0Labels := by
      have ha : raw26833step0 = (fun i j => raw26833 (permutation173 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26833step0 raw26833; decide +kernel
      have hl : raw26833step0Labels = raw26833Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26833 raw26833Labels permutation173 permutation3
    _ = mixedMoment B node1097 node1097Labels := by rfl

theorem canonical26834 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26834 raw26834Labels = mixedMoment B node1236 node1236Labels := by
  calc
    mixedMoment B raw26834 raw26834Labels = mixedMoment B raw26834step0 raw26834step0Labels := by
      have hz : ∀ j, raw26834 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw26834step0 = (fun i j => raw26834 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw26834step0 raw26834; decide +kernel
      have hl : raw26834step0Labels = raw26834Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26834 raw26834Labels permutation434 hz
    mixedMoment B raw26834step0 raw26834step0Labels = mixedMoment B raw26834step1 raw26834step1Labels := by
      have ha : raw26834step1 = (fun i j => raw26834step0 (permutation37 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26834step1 raw26834step0; decide +kernel
      have hl : raw26834step1Labels = raw26834step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26834step0 raw26834step0Labels permutation37 permutation3
    _ = mixedMoment B node1236 node1236Labels := by rfl

theorem canonical26835 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26835 raw26835Labels = mixedMoment B node1236 node1236Labels := by
  calc
    mixedMoment B raw26835 raw26835Labels = mixedMoment B raw26835step0 raw26835step0Labels := by
      have hz : ∀ j, raw26835 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw26835step0 = (fun i j => raw26835 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw26835step0 raw26835; decide +kernel
      have hl : raw26835step0Labels = raw26835Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26835 raw26835Labels permutation520 hz
    mixedMoment B raw26835step0 raw26835step0Labels = mixedMoment B raw26835step1 raw26835step1Labels := by
      have ha : raw26835step1 = (fun i j => raw26835step0 (permutation37 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26835step1 raw26835step0; decide +kernel
      have hl : raw26835step1Labels = raw26835step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26835step0 raw26835step0Labels permutation37 permutation3
    _ = mixedMoment B node1236 node1236Labels := by rfl

theorem canonical26836 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26836 raw26836Labels = mixedMoment B node1200 node1200Labels := by
  calc
    mixedMoment B raw26836 raw26836Labels = mixedMoment B raw26836step0 raw26836step0Labels := by
      have ha : raw26836step0 = (fun i j => raw26836 (permutation173 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26836step0 raw26836; decide +kernel
      have hl : raw26836step0Labels = raw26836Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26836 raw26836Labels permutation173 permutation3
    _ = mixedMoment B node1200 node1200Labels := by rfl

theorem canonical26837 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26837 raw26837Labels = mixedMoment B node567 node567Labels := by
  calc
    mixedMoment B raw26837 raw26837Labels = mixedMoment B raw26837step0 raw26837step0Labels := by
      have ha : raw26837step0 = (fun i j => raw26837 (permutation171 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26837step0 raw26837; decide +kernel
      have hl : raw26837step0Labels = raw26837Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26837 raw26837Labels permutation171 permutation3
    _ = mixedMoment B node567 node567Labels := by rfl

theorem canonical26838 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26838 raw26838Labels = mixedMoment B node1097 node1097Labels := by
  calc
    mixedMoment B raw26838 raw26838Labels = mixedMoment B raw26838step0 raw26838step0Labels := by
      have ha : raw26838step0 = (fun i j => raw26838 (permutation171 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26838step0 raw26838; decide +kernel
      have hl : raw26838step0Labels = raw26838Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26838 raw26838Labels permutation171 permutation3
    _ = mixedMoment B node1097 node1097Labels := by rfl

theorem canonical26839 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26839 raw26839Labels = mixedMoment B node1236 node1236Labels := by
  calc
    mixedMoment B raw26839 raw26839Labels = mixedMoment B raw26839step0 raw26839step0Labels := by
      have hz : ∀ j, raw26839 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw26839step0 = (fun i j => raw26839 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw26839step0 raw26839; decide +kernel
      have hl : raw26839step0Labels = raw26839Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26839 raw26839Labels permutation346 hz
    mixedMoment B raw26839step0 raw26839step0Labels = mixedMoment B raw26839step1 raw26839step1Labels := by
      have ha : raw26839step1 = (fun i j => raw26839step0 (permutation37 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26839step1 raw26839step0; decide +kernel
      have hl : raw26839step1Labels = raw26839step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26839step0 raw26839step0Labels permutation37 permutation3
    _ = mixedMoment B node1236 node1236Labels := by rfl

theorem canonical26840 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26840 raw26840Labels = mixedMoment B node1236 node1236Labels := by
  calc
    mixedMoment B raw26840 raw26840Labels = mixedMoment B raw26840step0 raw26840step0Labels := by
      have hz : ∀ j, raw26840 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw26840step0 = (fun i j => raw26840 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw26840step0 raw26840; decide +kernel
      have hl : raw26840step0Labels = raw26840Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26840 raw26840Labels permutation520 hz
    mixedMoment B raw26840step0 raw26840step0Labels = mixedMoment B raw26840step1 raw26840step1Labels := by
      have ha : raw26840step1 = (fun i j => raw26840step0 (permutation36 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26840step1 raw26840step0; decide +kernel
      have hl : raw26840step1Labels = raw26840step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26840step0 raw26840step0Labels permutation36 permutation3
    _ = mixedMoment B node1236 node1236Labels := by rfl

theorem canonical26841 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26841 raw26841Labels = mixedMoment B node1200 node1200Labels := by
  calc
    mixedMoment B raw26841 raw26841Labels = mixedMoment B raw26841step0 raw26841step0Labels := by
      have ha : raw26841step0 = (fun i j => raw26841 (permutation171 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26841step0 raw26841; decide +kernel
      have hl : raw26841step0Labels = raw26841Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26841 raw26841Labels permutation171 permutation3
    _ = mixedMoment B node1200 node1200Labels := by rfl

theorem canonical26842 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26842 raw26842Labels = mixedMoment B node567 node567Labels := by
  calc
    mixedMoment B raw26842 raw26842Labels = mixedMoment B raw26842step0 raw26842step0Labels := by
      have ha : raw26842step0 = (fun i j => raw26842 (permutation170 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26842step0 raw26842; decide +kernel
      have hl : raw26842step0Labels = raw26842Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26842 raw26842Labels permutation170 permutation3
    _ = mixedMoment B node567 node567Labels := by rfl

theorem canonical26843 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26843 raw26843Labels = mixedMoment B node1097 node1097Labels := by
  calc
    mixedMoment B raw26843 raw26843Labels = mixedMoment B raw26843step0 raw26843step0Labels := by
      have ha : raw26843step0 = (fun i j => raw26843 (permutation170 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26843step0 raw26843; decide +kernel
      have hl : raw26843step0Labels = raw26843Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26843 raw26843Labels permutation170 permutation3
    _ = mixedMoment B node1097 node1097Labels := by rfl

theorem canonical26844 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26844 raw26844Labels = mixedMoment B node1236 node1236Labels := by
  calc
    mixedMoment B raw26844 raw26844Labels = mixedMoment B raw26844step0 raw26844step0Labels := by
      have hz : ∀ j, raw26844 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw26844step0 = (fun i j => raw26844 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw26844step0 raw26844; decide +kernel
      have hl : raw26844step0Labels = raw26844Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26844 raw26844Labels permutation346 hz
    mixedMoment B raw26844step0 raw26844step0Labels = mixedMoment B raw26844step1 raw26844step1Labels := by
      have ha : raw26844step1 = (fun i j => raw26844step0 (permutation36 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26844step1 raw26844step0; decide +kernel
      have hl : raw26844step1Labels = raw26844step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26844step0 raw26844step0Labels permutation36 permutation3
    _ = mixedMoment B node1236 node1236Labels := by rfl

theorem canonical26845 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26845 raw26845Labels = mixedMoment B node1236 node1236Labels := by
  calc
    mixedMoment B raw26845 raw26845Labels = mixedMoment B raw26845step0 raw26845step0Labels := by
      have hz : ∀ j, raw26845 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw26845step0 = (fun i j => raw26845 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw26845step0 raw26845; decide +kernel
      have hl : raw26845step0Labels = raw26845Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26845 raw26845Labels permutation434 hz
    mixedMoment B raw26845step0 raw26845step0Labels = mixedMoment B raw26845step1 raw26845step1Labels := by
      have ha : raw26845step1 = (fun i j => raw26845step0 (permutation36 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26845step1 raw26845step0; decide +kernel
      have hl : raw26845step1Labels = raw26845step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26845step0 raw26845step0Labels permutation36 permutation3
    _ = mixedMoment B node1236 node1236Labels := by rfl

theorem canonical26846 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26846 raw26846Labels = mixedMoment B node1200 node1200Labels := by
  calc
    mixedMoment B raw26846 raw26846Labels = mixedMoment B raw26846step0 raw26846step0Labels := by
      have ha : raw26846step0 = (fun i j => raw26846 (permutation170 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26846step0 raw26846; decide +kernel
      have hl : raw26846step0Labels = raw26846Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26846 raw26846Labels permutation170 permutation3
    _ = mixedMoment B node1200 node1200Labels := by rfl

theorem canonical26847 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26847 raw26847Labels = mixedMoment B node571 node571Labels := by
  calc
    mixedMoment B raw26847 raw26847Labels = mixedMoment B raw26847step0 raw26847step0Labels := by
      have ha : raw26847step0 = (fun i j => raw26847 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26847step0 raw26847; decide +kernel
      have hl : raw26847step0Labels = raw26847Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26847 raw26847Labels permutation152 permutation3
    _ = mixedMoment B node571 node571Labels := by rfl

theorem canonical26848 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26848 raw26848Labels = mixedMoment B node1100 node1100Labels := by
  calc
    mixedMoment B raw26848 raw26848Labels = mixedMoment B raw26848step0 raw26848step0Labels := by
      have ha : raw26848step0 = (fun i j => raw26848 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26848step0 raw26848; decide +kernel
      have hl : raw26848step0Labels = raw26848Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26848 raw26848Labels permutation152 permutation3
    _ = mixedMoment B node1100 node1100Labels := by rfl

theorem canonical26849 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26849 raw26849Labels = mixedMoment B node1240 node1240Labels := by
  calc
    mixedMoment B raw26849 raw26849Labels = mixedMoment B raw26849step0 raw26849step0Labels := by
      have hz : ∀ j, raw26849 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw26849step0 = (fun i j => raw26849 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw26849step0 raw26849; decide +kernel
      have hl : raw26849step0Labels = raw26849Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26849 raw26849Labels permutation346 hz
    mixedMoment B raw26849step0 raw26849step0Labels = mixedMoment B raw26849step1 raw26849step1Labels := by
      have ha : raw26849step1 = (fun i j => raw26849step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26849step1 raw26849step0; decide +kernel
      have hl : raw26849step1Labels = raw26849step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26849step0 raw26849step0Labels permutation32 permutation3
    _ = mixedMoment B node1240 node1240Labels := by rfl

theorem canonical26850 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26850 raw26850Labels = mixedMoment B node1240 node1240Labels := by
  calc
    mixedMoment B raw26850 raw26850Labels = mixedMoment B raw26850step0 raw26850step0Labels := by
      have hz : ∀ j, raw26850 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw26850step0 = (fun i j => raw26850 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw26850step0 raw26850; decide +kernel
      have hl : raw26850step0Labels = raw26850Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26850 raw26850Labels permutation434 hz
    mixedMoment B raw26850step0 raw26850step0Labels = mixedMoment B raw26850step1 raw26850step1Labels := by
      have ha : raw26850step1 = (fun i j => raw26850step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26850step1 raw26850step0; decide +kernel
      have hl : raw26850step1Labels = raw26850step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26850step0 raw26850step0Labels permutation32 permutation3
    _ = mixedMoment B node1240 node1240Labels := by rfl

theorem canonical26851 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26851 raw26851Labels = mixedMoment B node1240 node1240Labels := by
  calc
    mixedMoment B raw26851 raw26851Labels = mixedMoment B raw26851step0 raw26851step0Labels := by
      have hz : ∀ j, raw26851 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw26851step0 = (fun i j => raw26851 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw26851step0 raw26851; decide +kernel
      have hl : raw26851step0Labels = raw26851Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26851 raw26851Labels permutation520 hz
    mixedMoment B raw26851step0 raw26851step0Labels = mixedMoment B raw26851step1 raw26851step1Labels := by
      have ha : raw26851step1 = (fun i j => raw26851step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26851step1 raw26851step0; decide +kernel
      have hl : raw26851step1Labels = raw26851step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26851step0 raw26851step0Labels permutation32 permutation3
    _ = mixedMoment B node1240 node1240Labels := by rfl

theorem canonical26878 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26878 raw26878Labels = mixedMoment B node1183 node1183Labels := by
  calc
    mixedMoment B raw26878 raw26878Labels = mixedMoment B raw26878step0 raw26878step0Labels := by
      have ha : raw26878step0 = (fun i j => raw26878 (permutation173 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26878step0 raw26878; decide +kernel
      have hl : raw26878step0Labels = raw26878Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26878 raw26878Labels permutation173 permutation2
    _ = mixedMoment B node1183 node1183Labels := by rfl

theorem canonical26879 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26879 raw26879Labels = mixedMoment B node2398 node2398Labels := by
  calc
    mixedMoment B raw26879 raw26879Labels = mixedMoment B raw26879step0 raw26879step0Labels := by
      have ha : raw26879step0 = (fun i j => raw26879 (permutation173 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26879step0 raw26879; decide +kernel
      have hl : raw26879step0Labels = raw26879Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26879 raw26879Labels permutation173 permutation2
    _ = mixedMoment B node2398 node2398Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical210
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical26880 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26880 raw26880Labels = mixedMoment B node2676 node2676Labels := by
  calc
    mixedMoment B raw26880 raw26880Labels = mixedMoment B raw26880step0 raw26880step0Labels := by
      have ha : raw26880step0 = (fun i j => raw26880 (permutation156 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26880step0 raw26880; decide +kernel
      have hl : raw26880step0Labels = raw26880Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26880 raw26880Labels permutation156 permutation2
    _ = mixedMoment B node2676 node2676Labels := by rfl

theorem canonical26881 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26881 raw26881Labels = mixedMoment B node2669 node2669Labels := by
  calc
    mixedMoment B raw26881 raw26881Labels = mixedMoment B raw26881step0 raw26881step0Labels := by
      have ha : raw26881step0 = (fun i j => raw26881 (permutation163 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26881step0 raw26881; decide +kernel
      have hl : raw26881step0Labels = raw26881Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26881 raw26881Labels permutation163 permutation2
    _ = mixedMoment B node2669 node2669Labels := by rfl

theorem canonical26882 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26882 raw26882Labels = mixedMoment B node2669 node2669Labels := by
  calc
    mixedMoment B raw26882 raw26882Labels = mixedMoment B raw26882step0 raw26882step0Labels := by
      have ha : raw26882step0 = (fun i j => raw26882 (permutation169 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26882step0 raw26882; decide +kernel
      have hl : raw26882step0Labels = raw26882Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26882 raw26882Labels permutation169 permutation2
    _ = mixedMoment B node2669 node2669Labels := by rfl

theorem canonical26883 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26883 raw26883Labels = mixedMoment B node2684 node2684Labels := by
  calc
    mixedMoment B raw26883 raw26883Labels = mixedMoment B raw26883step0 raw26883step0Labels := by
      have hz : ∀ j, raw26883 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw26883step0 = (fun i j => raw26883 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw26883step0 raw26883; decide +kernel
      have hl : raw26883step0Labels = raw26883Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26883 raw26883Labels permutation590 hz
    mixedMoment B raw26883step0 raw26883step0Labels = mixedMoment B raw26883step1 raw26883step1Labels := by
      have ha : raw26883step1 = (fun i j => raw26883step0 (permutation35 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26883step1 raw26883step0; decide +kernel
      have hl : raw26883step1Labels = raw26883step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26883step0 raw26883step0Labels permutation35 permutation2
    _ = mixedMoment B node2684 node2684Labels := by rfl

theorem canonical26884 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26884 raw26884Labels = mixedMoment B node4088 node4088Labels := by
  calc
    mixedMoment B raw26884 raw26884Labels = mixedMoment B raw26884step0 raw26884step0Labels := by
      have hz : ∀ j, raw26884 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw26884step0 = (fun i j => raw26884 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw26884step0 raw26884; decide +kernel
      have hl : raw26884step0Labels = raw26884Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26884 raw26884Labels permutation590 hz
    mixedMoment B raw26884step0 raw26884step0Labels = mixedMoment B raw26884step1 raw26884step1Labels := by
      have ha : raw26884step1 = (fun i j => raw26884step0 (permutation35 i) (permutation0 j)) := by apply Matrix.ext; unfold raw26884step1 raw26884step0; decide +kernel
      have hl : raw26884step1Labels = raw26884step0Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26884step0 raw26884step0Labels permutation35 permutation0
    _ = mixedMoment B node4088 node4088Labels := by rfl

theorem canonical26885 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26885 raw26885Labels = mixedMoment B node1187 node1187Labels := by
  calc
    _ = mixedMoment B node1187 node1187Labels := by rfl

theorem canonical26886 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26886 raw26886Labels = mixedMoment B node2402 node2402Labels := by
  calc
    _ = mixedMoment B node2402 node2402Labels := by rfl

theorem canonical26887 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26887 raw26887Labels = mixedMoment B node2671 node2671Labels := by
  calc
    _ = mixedMoment B node2671 node2671Labels := by rfl

theorem canonical26888 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26888 raw26888Labels = mixedMoment B node2671 node2671Labels := by
  calc
    mixedMoment B raw26888 raw26888Labels = mixedMoment B raw26888step0 raw26888step0Labels := by
      have ha : raw26888step0 = (fun i j => raw26888 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26888step0 raw26888; decide +kernel
      have hl : raw26888step0Labels = raw26888Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26888 raw26888Labels permutation158 permutation2
    _ = mixedMoment B node2671 node2671Labels := by rfl

theorem canonical26889 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26889 raw26889Labels = mixedMoment B node2671 node2671Labels := by
  calc
    mixedMoment B raw26889 raw26889Labels = mixedMoment B raw26889step0 raw26889step0Labels := by
      have ha : raw26889step0 = (fun i j => raw26889 (permutation164 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26889step0 raw26889; decide +kernel
      have hl : raw26889step0Labels = raw26889Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26889 raw26889Labels permutation164 permutation2
    _ = mixedMoment B node2671 node2671Labels := by rfl

theorem canonical26890 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26890 raw26890Labels = mixedMoment B node2671 node2671Labels := by
  calc
    mixedMoment B raw26890 raw26890Labels = mixedMoment B raw26890step0 raw26890step0Labels := by
      have ha : raw26890step0 = (fun i j => raw26890 (permutation170 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26890step0 raw26890; decide +kernel
      have hl : raw26890step0Labels = raw26890Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26890 raw26890Labels permutation170 permutation2
    _ = mixedMoment B node2671 node2671Labels := by rfl

theorem canonical26891 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26891 raw26891Labels = mixedMoment B node4087 node4087Labels := by
  calc
    _ = mixedMoment B node4087 node4087Labels := by rfl

theorem canonical26892 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26892 raw26892Labels = mixedMoment B node1100 node1100Labels := by
  calc
    mixedMoment B raw26892 raw26892Labels = mixedMoment B raw26892step0 raw26892step0Labels := by
      have ha : raw26892step0 = (fun i j => raw26892 (permutation161 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26892step0 raw26892; decide +kernel
      have hl : raw26892step0Labels = raw26892Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26892 raw26892Labels permutation161 permutation2
    _ = mixedMoment B node1100 node1100Labels := by rfl

theorem canonical26893 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26893 raw26893Labels = mixedMoment B node1100 node1100Labels := by
  calc
    mixedMoment B raw26893 raw26893Labels = mixedMoment B raw26893step0 raw26893step0Labels := by
      have ha : raw26893step0 = (fun i j => raw26893 (permutation155 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26893step0 raw26893; decide +kernel
      have hl : raw26893step0Labels = raw26893Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26893 raw26893Labels permutation155 permutation2
    _ = mixedMoment B node1100 node1100Labels := by rfl

theorem canonical26894 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26894 raw26894Labels = mixedMoment B node1100 node1100Labels := by
  calc
    mixedMoment B raw26894 raw26894Labels = mixedMoment B raw26894step0 raw26894step0Labels := by
      have ha : raw26894step0 = (fun i j => raw26894 (permutation153 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26894step0 raw26894; decide +kernel
      have hl : raw26894step0Labels = raw26894Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26894 raw26894Labels permutation153 permutation2
    _ = mixedMoment B node1100 node1100Labels := by rfl

theorem canonical26895 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26895 raw26895Labels = mixedMoment B node1100 node1100Labels := by
  calc
    _ = mixedMoment B node1100 node1100Labels := by rfl

theorem canonical26902 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26902 raw26902Labels = mixedMoment B node1052 node1052Labels := by
  calc
    mixedMoment B raw26902 raw26902Labels = mixedMoment B raw26902step0 raw26902step0Labels := by
      have ha : raw26902step0 = (fun i j => raw26902 (permutation174 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26902step0 raw26902; decide +kernel
      have hl : raw26902step0Labels = raw26902Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26902 raw26902Labels permutation174 permutation2
    _ = mixedMoment B node1052 node1052Labels := by rfl

theorem canonical26903 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26903 raw26903Labels = mixedMoment B node2127 node2127Labels := by
  calc
    mixedMoment B raw26903 raw26903Labels = mixedMoment B raw26903step0 raw26903step0Labels := by
      have ha : raw26903step0 = (fun i j => raw26903 (permutation174 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26903step0 raw26903; decide +kernel
      have hl : raw26903step0Labels = raw26903Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26903 raw26903Labels permutation174 permutation2
    _ = mixedMoment B node2127 node2127Labels := by rfl

theorem canonical26904 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26904 raw26904Labels = mixedMoment B node2250 node2250Labels := by
  calc
    mixedMoment B raw26904 raw26904Labels = mixedMoment B raw26904step0 raw26904step0Labels := by
      have ha : raw26904step0 = (fun i j => raw26904 (permutation181 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26904step0 raw26904; decide +kernel
      have hl : raw26904step0Labels = raw26904Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26904 raw26904Labels permutation181 permutation2
    _ = mixedMoment B node2250 node2250Labels := by rfl

theorem canonical26905 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26905 raw26905Labels = mixedMoment B node2250 node2250Labels := by
  calc
    mixedMoment B raw26905 raw26905Labels = mixedMoment B raw26905step0 raw26905step0Labels := by
      have ha : raw26905step0 = (fun i j => raw26905 (permutation205 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26905step0 raw26905; decide +kernel
      have hl : raw26905step0Labels = raw26905Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26905 raw26905Labels permutation205 permutation2
    _ = mixedMoment B node2250 node2250Labels := by rfl

theorem canonical26906 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26906 raw26906Labels = mixedMoment B node2275 node2275Labels := by
  calc
    mixedMoment B raw26906 raw26906Labels = mixedMoment B raw26906step0 raw26906step0Labels := by
      have hz : ∀ j, raw26906 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw26906step0 = (fun i j => raw26906 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw26906step0 raw26906; decide +kernel
      have hl : raw26906step0Labels = raw26906Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26906 raw26906Labels permutation520 hz
    mixedMoment B raw26906step0 raw26906step0Labels = mixedMoment B raw26906step1 raw26906step1Labels := by
      have ha : raw26906step1 = (fun i j => raw26906step0 (permutation36 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26906step1 raw26906step0; decide +kernel
      have hl : raw26906step1Labels = raw26906step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26906step0 raw26906step0Labels permutation36 permutation2
    _ = mixedMoment B node2275 node2275Labels := by rfl

theorem canonical26907 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26907 raw26907Labels = mixedMoment B node2214 node2214Labels := by
  calc
    mixedMoment B raw26907 raw26907Labels = mixedMoment B raw26907step0 raw26907step0Labels := by
      have ha : raw26907step0 = (fun i j => raw26907 (permutation250 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26907step0 raw26907; decide +kernel
      have hl : raw26907step0Labels = raw26907Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26907 raw26907Labels permutation250 permutation2
    _ = mixedMoment B node2214 node2214Labels := by rfl

theorem canonical26908 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26908 raw26908Labels = mixedMoment B node4080 node4080Labels := by
  calc
    mixedMoment B raw26908 raw26908Labels = mixedMoment B raw26908step0 raw26908step0Labels := by
      have hz : ∀ j, raw26908 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw26908step0 = (fun i j => raw26908 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw26908step0 raw26908; decide +kernel
      have hl : raw26908step0Labels = raw26908Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26908 raw26908Labels permutation520 hz
    mixedMoment B raw26908step0 raw26908step0Labels = mixedMoment B raw26908step1 raw26908step1Labels := by
      have ha : raw26908step1 = (fun i j => raw26908step0 (permutation53 i) (permutation0 j)) := by apply Matrix.ext; unfold raw26908step1 raw26908step0; decide +kernel
      have hl : raw26908step1Labels = raw26908step0Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26908step0 raw26908step0Labels permutation53 permutation0
    _ = mixedMoment B node4080 node4080Labels := by rfl

theorem canonical26909 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26909 raw26909Labels = mixedMoment B node1032 node1032Labels := by
  calc
    mixedMoment B raw26909 raw26909Labels = mixedMoment B raw26909step0 raw26909step0Labels := by
      have ha : raw26909step0 = (fun i j => raw26909 (permutation175 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26909step0 raw26909; decide +kernel
      have hl : raw26909step0Labels = raw26909Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26909 raw26909Labels permutation175 permutation2
    _ = mixedMoment B node1032 node1032Labels := by rfl

theorem canonical26910 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26910 raw26910Labels = mixedMoment B node2098 node2098Labels := by
  calc
    mixedMoment B raw26910 raw26910Labels = mixedMoment B raw26910step0 raw26910step0Labels := by
      have ha : raw26910step0 = (fun i j => raw26910 (permutation175 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26910step0 raw26910; decide +kernel
      have hl : raw26910step0Labels = raw26910Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26910 raw26910Labels permutation175 permutation2
    _ = mixedMoment B node2098 node2098Labels := by rfl

theorem canonical26911 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26911 raw26911Labels = mixedMoment B node2250 node2250Labels := by
  calc
    mixedMoment B raw26911 raw26911Labels = mixedMoment B raw26911step0 raw26911step0Labels := by
      have ha : raw26911step0 = (fun i j => raw26911 (permutation157 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26911step0 raw26911; decide +kernel
      have hl : raw26911step0Labels = raw26911Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26911 raw26911Labels permutation157 permutation2
    _ = mixedMoment B node2250 node2250Labels := by rfl

theorem canonical26912 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26912 raw26912Labels = mixedMoment B node2240 node2240Labels := by
  calc
    mixedMoment B raw26912 raw26912Labels = mixedMoment B raw26912step0 raw26912step0Labels := by
      have ha : raw26912step0 = (fun i j => raw26912 (permutation163 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26912step0 raw26912; decide +kernel
      have hl : raw26912step0Labels = raw26912Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26912 raw26912Labels permutation163 permutation2
    _ = mixedMoment B node2240 node2240Labels := by rfl

theorem canonical26913 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26913 raw26913Labels = mixedMoment B node2260 node2260Labels := by
  calc
    mixedMoment B raw26913 raw26913Labels = mixedMoment B raw26913step0 raw26913step0Labels := by
      have hz : ∀ j, raw26913 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw26913step0 = (fun i j => raw26913 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw26913step0 raw26913; decide +kernel
      have hl : raw26913step0Labels = raw26913Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26913 raw26913Labels permutation520 hz
    mixedMoment B raw26913step0 raw26913step0Labels = mixedMoment B raw26913step1 raw26913step1Labels := by
      have ha : raw26913step1 = (fun i j => raw26913step0 (permutation37 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26913step1 raw26913step0; decide +kernel
      have hl : raw26913step1Labels = raw26913step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26913step0 raw26913step0Labels permutation37 permutation2
    _ = mixedMoment B node2260 node2260Labels := by rfl

theorem canonical26914 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26914 raw26914Labels = mixedMoment B node2202 node2202Labels := by
  calc
    mixedMoment B raw26914 raw26914Labels = mixedMoment B raw26914step0 raw26914step0Labels := by
      have ha : raw26914step0 = (fun i j => raw26914 (permutation251 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26914step0 raw26914; decide +kernel
      have hl : raw26914step0Labels = raw26914Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26914 raw26914Labels permutation251 permutation2
    _ = mixedMoment B node2202 node2202Labels := by rfl

theorem canonical26915 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26915 raw26915Labels = mixedMoment B node4080 node4080Labels := by
  calc
    mixedMoment B raw26915 raw26915Labels = mixedMoment B raw26915step0 raw26915step0Labels := by
      have hz : ∀ j, raw26915 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw26915step0 = (fun i j => raw26915 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw26915step0 raw26915; decide +kernel
      have hl : raw26915step0Labels = raw26915Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26915 raw26915Labels permutation520 hz
    mixedMoment B raw26915step0 raw26915step0Labels = mixedMoment B raw26915step1 raw26915step1Labels := by
      have ha : raw26915step1 = (fun i j => raw26915step0 (permutation51 i) (permutation0 j)) := by apply Matrix.ext; unfold raw26915step1 raw26915step0; decide +kernel
      have hl : raw26915step1Labels = raw26915step0Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26915step0 raw26915step0Labels permutation51 permutation0
    _ = mixedMoment B node4080 node4080Labels := by rfl

theorem canonical26916 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26916 raw26916Labels = mixedMoment B node2100 node2100Labels := by
  calc
    mixedMoment B raw26916 raw26916Labels = mixedMoment B raw26916step0 raw26916step0Labels := by
      have ha : raw26916step0 = (fun i j => raw26916 (permutation170 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26916step0 raw26916; decide +kernel
      have hl : raw26916step0Labels = raw26916Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26916 raw26916Labels permutation170 permutation2
    _ = mixedMoment B node2100 node2100Labels := by rfl

theorem canonical26917 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26917 raw26917Labels = mixedMoment B node2241 node2241Labels := by
  calc
    mixedMoment B raw26917 raw26917Labels = mixedMoment B raw26917step0 raw26917step0Labels := by
      have ha : raw26917step0 = (fun i j => raw26917 (permutation162 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26917step0 raw26917; decide +kernel
      have hl : raw26917step0Labels = raw26917Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26917 raw26917Labels permutation162 permutation2
    _ = mixedMoment B node2241 node2241Labels := by rfl

theorem canonical26918 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26918 raw26918Labels = mixedMoment B node2241 node2241Labels := by
  calc
    mixedMoment B raw26918 raw26918Labels = mixedMoment B raw26918step0 raw26918step0Labels := by
      have ha : raw26918step0 = (fun i j => raw26918 (permutation168 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26918step0 raw26918; decide +kernel
      have hl : raw26918step0Labels = raw26918Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26918 raw26918Labels permutation168 permutation2
    _ = mixedMoment B node2241 node2241Labels := by rfl

theorem canonical26919 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26919 raw26919Labels = mixedMoment B node2204 node2204Labels := by
  calc
    mixedMoment B raw26919 raw26919Labels = mixedMoment B raw26919step0 raw26919step0Labels := by
      have ha : raw26919step0 = (fun i j => raw26919 (permutation246 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26919step0 raw26919; decide +kernel
      have hl : raw26919step0Labels = raw26919Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26919 raw26919Labels permutation246 permutation2
    _ = mixedMoment B node2204 node2204Labels := by rfl

theorem canonical26920 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26920 raw26920Labels = mixedMoment B node1644 node1644Labels := by
  calc
    mixedMoment B raw26920 raw26920Labels = mixedMoment B raw26920step0 raw26920step0Labels := by
      have ha : raw26920step0 = (fun i j => raw26920 (permutation246 i) (permutation4 j)) := by apply Matrix.ext; unfold raw26920step0 raw26920; decide +kernel
      have hl : raw26920step0Labels = raw26920Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26920 raw26920Labels permutation246 permutation4
    mixedMoment B raw26920step0 raw26920step0Labels = mixedMoment B raw26920step1 raw26920step1Labels := by
      have ha : raw26920step1 = -raw26920step0 := by apply Matrix.ext; change ∀ i j, raw26920step1 i j = -(raw26920step0 i j); unfold raw26920step1 raw26920step0; decide +kernel
      have hl : raw26920step1Labels = raw26920step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1644 node1644Labels := by rfl

theorem canonical26921 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26921 raw26921Labels = mixedMoment B node736 node736Labels := by
  calc
    mixedMoment B raw26921 raw26921Labels = mixedMoment B raw26921step0 raw26921step0Labels := by
      have ha : raw26921step0 = (fun i j => raw26921 (permutation255 i) (permutation4 j)) := by apply Matrix.ext; unfold raw26921step0 raw26921; decide +kernel
      have hl : raw26921step0Labels = raw26921Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26921 raw26921Labels permutation255 permutation4
    mixedMoment B raw26921step0 raw26921step0Labels = mixedMoment B raw26921step1 raw26921step1Labels := by
      have ha : raw26921step1 = -raw26921step0 := by apply Matrix.ext; change ∀ i j, raw26921step1 i j = -(raw26921step0 i j); unfold raw26921step1 raw26921step0; decide +kernel
      have hl : raw26921step1Labels = raw26921step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node736 node736Labels := by rfl

theorem canonical26922 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26922 raw26922Labels = mixedMoment B node732 node732Labels := by
  calc
    mixedMoment B raw26922 raw26922Labels = mixedMoment B raw26922step0 raw26922step0Labels := by
      have ha : raw26922step0 = (fun i j => raw26922 (permutation249 i) (permutation4 j)) := by apply Matrix.ext; unfold raw26922step0 raw26922; decide +kernel
      have hl : raw26922step0Labels = raw26922Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26922 raw26922Labels permutation249 permutation4
    mixedMoment B raw26922step0 raw26922step0Labels = mixedMoment B raw26922step1 raw26922step1Labels := by
      have ha : raw26922step1 = -raw26922step0 := by apply Matrix.ext; change ∀ i j, raw26922step1 i j = -(raw26922step0 i j); unfold raw26922step1 raw26922step0; decide +kernel
      have hl : raw26922step1Labels = raw26922step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node732 node732Labels := by rfl

theorem canonical26923 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26923 raw26923Labels = mixedMoment B node732 node732Labels := by
  calc
    mixedMoment B raw26923 raw26923Labels = mixedMoment B raw26923step0 raw26923step0Labels := by
      have ha : raw26923step0 = (fun i j => raw26923 (permutation247 i) (permutation4 j)) := by apply Matrix.ext; unfold raw26923step0 raw26923; decide +kernel
      have hl : raw26923step0Labels = raw26923Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26923 raw26923Labels permutation247 permutation4
    mixedMoment B raw26923step0 raw26923step0Labels = mixedMoment B raw26923step1 raw26923step1Labels := by
      have ha : raw26923step1 = -raw26923step0 := by apply Matrix.ext; change ∀ i j, raw26923step1 i j = -(raw26923step0 i j); unfold raw26923step1 raw26923step0; decide +kernel
      have hl : raw26923step1Labels = raw26923step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node732 node732Labels := by rfl

theorem canonical26924 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26924 raw26924Labels = mixedMoment B node732 node732Labels := by
  calc
    mixedMoment B raw26924 raw26924Labels = mixedMoment B raw26924step0 raw26924step0Labels := by
      have ha : raw26924step0 = (fun i j => raw26924 (permutation246 i) (permutation4 j)) := by apply Matrix.ext; unfold raw26924step0 raw26924; decide +kernel
      have hl : raw26924step0Labels = raw26924Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26924 raw26924Labels permutation246 permutation4
    mixedMoment B raw26924step0 raw26924step0Labels = mixedMoment B raw26924step1 raw26924step1Labels := by
      have ha : raw26924step1 = -raw26924step0 := by apply Matrix.ext; change ∀ i j, raw26924step1 i j = -(raw26924step0 i j); unfold raw26924step1 raw26924step0; decide +kernel
      have hl : raw26924step1Labels = raw26924step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node732 node732Labels := by rfl

theorem canonical26925 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26925 raw26925Labels = mixedMoment B node805 node805Labels := by
  calc
    mixedMoment B raw26925 raw26925Labels = mixedMoment B raw26925step0 raw26925step0Labels := by
      have ha : raw26925step0 = (fun i j => raw26925 (permutation246 i) (permutation4 j)) := by apply Matrix.ext; unfold raw26925step0 raw26925; decide +kernel
      have hl : raw26925step0Labels = raw26925Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26925 raw26925Labels permutation246 permutation4
    mixedMoment B raw26925step0 raw26925step0Labels = mixedMoment B raw26925step1 raw26925step1Labels := by
      have ha : raw26925step1 = -raw26925step0 := by apply Matrix.ext; change ∀ i j, raw26925step1 i j = -(raw26925step0 i j); unfold raw26925step1 raw26925step0; decide +kernel
      have hl : raw26925step1Labels = raw26925step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node805 node805Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical57
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical7301 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7301 raw7301Labels = mixedMoment B node4589 node4589Labels := by
  calc
    mixedMoment B raw7301 raw7301Labels = mixedMoment B raw7301step0 raw7301step0Labels := by
      have ha : raw7301step0 = (fun i j => raw7301 (permutation200 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7301step0 raw7301; decide +kernel
      have hl : raw7301step0Labels = raw7301Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7301 raw7301Labels permutation200 permutation3
    mixedMoment B raw7301step0 raw7301step0Labels = mixedMoment B raw7301step1 raw7301step1Labels := by
      have ha : raw7301step1 = raw7301step0 := by apply Matrix.ext; unfold raw7301step1 raw7301step0; decide +kernel
      have hl : raw7301step0Labels = labelEmbedding6 ∘ raw7301step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7301step0 raw7301step0Labels raw7301step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4589 node4589Labels := by rfl

theorem canonical7305 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7305 raw7305Labels = mixedMoment B node5257 node5257Labels := by
  calc
    mixedMoment B raw7305 raw7305Labels = mixedMoment B raw7305step0 raw7305step0Labels := by
      have ha : raw7305step0 = (fun i j => raw7305 (permutation162 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7305step0 raw7305; decide +kernel
      have hl : raw7305step0Labels = raw7305Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7305 raw7305Labels permutation162 permutation2
    _ = mixedMoment B node5257 node5257Labels := by rfl

theorem canonical7306 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7306 raw7306Labels = mixedMoment B node4589 node4589Labels := by
  calc
    mixedMoment B raw7306 raw7306Labels = mixedMoment B raw7306step0 raw7306step0Labels := by
      have ha : raw7306step0 = (fun i j => raw7306 (permutation176 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7306step0 raw7306; decide +kernel
      have hl : raw7306step0Labels = raw7306Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7306 raw7306Labels permutation176 permutation3
    mixedMoment B raw7306step0 raw7306step0Labels = mixedMoment B raw7306step1 raw7306step1Labels := by
      have ha : raw7306step1 = raw7306step0 := by apply Matrix.ext; unfold raw7306step1 raw7306step0; decide +kernel
      have hl : raw7306step0Labels = labelEmbedding6 ∘ raw7306step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7306step0 raw7306step0Labels raw7306step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4589 node4589Labels := by rfl

theorem canonical7310 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7310 raw7310Labels = mixedMoment B node5257 node5257Labels := by
  calc
    mixedMoment B raw7310 raw7310Labels = mixedMoment B raw7310step0 raw7310step0Labels := by
      have ha : raw7310step0 = (fun i j => raw7310 (permutation156 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7310step0 raw7310; decide +kernel
      have hl : raw7310step0Labels = raw7310Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7310 raw7310Labels permutation156 permutation2
    _ = mixedMoment B node5257 node5257Labels := by rfl

theorem canonical7361 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7361 raw7361Labels = mixedMoment B node3288 node3288Labels := by
  calc
    mixedMoment B raw7361 raw7361Labels = mixedMoment B raw7361step0 raw7361step0Labels := by
      have ha : raw7361step0 = (fun i j => raw7361 (permutation208 i) (permutation5 j)) := by apply Matrix.ext; unfold raw7361step0 raw7361; decide +kernel
      have hl : raw7361step0Labels = raw7361Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7361 raw7361Labels permutation208 permutation5
    mixedMoment B raw7361step0 raw7361step0Labels = mixedMoment B raw7361step1 raw7361step1Labels := by
      have ha : raw7361step1 = -raw7361step0 := by apply Matrix.ext; change ∀ i j, raw7361step1 i j = -(raw7361step0 i j); unfold raw7361step1 raw7361step0; decide +kernel
      have hl : raw7361step1Labels = raw7361step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw7361step1 raw7361step1Labels = mixedMoment B raw7361step2 raw7361step2Labels := by
      have ha : raw7361step2 = raw7361step1 := by apply Matrix.ext; unfold raw7361step2 raw7361step1; decide +kernel
      have hl : raw7361step1Labels = labelEmbedding1 ∘ raw7361step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7361step1 raw7361step1Labels raw7361step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3288 node3288Labels := by rfl

theorem canonical7365 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7365 raw7365Labels = mixedMoment B node3532 node3532Labels := by
  calc
    mixedMoment B raw7365 raw7365Labels = mixedMoment B raw7365step0 raw7365step0Labels := by
      have ha : raw7365step0 = (fun i j => raw7365 (permutation172 i) (permutation7 j)) := by apply Matrix.ext; unfold raw7365step0 raw7365; decide +kernel
      have hl : raw7365step0Labels = raw7365Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7365 raw7365Labels permutation172 permutation7
    mixedMoment B raw7365step0 raw7365step0Labels = mixedMoment B raw7365step1 raw7365step1Labels := by
      have ha : raw7365step1 = -raw7365step0 := by apply Matrix.ext; change ∀ i j, raw7365step1 i j = -(raw7365step0 i j); unfold raw7365step1 raw7365step0; decide +kernel
      have hl : raw7365step1Labels = raw7365step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw7365step1 raw7365step1Labels = mixedMoment B raw7365step2 raw7365step2Labels := by
      have ha : raw7365step2 = raw7365step1 := by apply Matrix.ext; unfold raw7365step2 raw7365step1; decide +kernel
      have hl : raw7365step1Labels = labelEmbedding1 ∘ raw7365step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7365step1 raw7365step1Labels raw7365step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3532 node3532Labels := by rfl

theorem canonical7366 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7366 raw7366Labels = mixedMoment B node3288 node3288Labels := by
  calc
    mixedMoment B raw7366 raw7366Labels = mixedMoment B raw7366step0 raw7366step0Labels := by
      have ha : raw7366step0 = (fun i j => raw7366 (permutation184 i) (permutation5 j)) := by apply Matrix.ext; unfold raw7366step0 raw7366; decide +kernel
      have hl : raw7366step0Labels = raw7366Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7366 raw7366Labels permutation184 permutation5
    mixedMoment B raw7366step0 raw7366step0Labels = mixedMoment B raw7366step1 raw7366step1Labels := by
      have ha : raw7366step1 = -raw7366step0 := by apply Matrix.ext; change ∀ i j, raw7366step1 i j = -(raw7366step0 i j); unfold raw7366step1 raw7366step0; decide +kernel
      have hl : raw7366step1Labels = raw7366step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw7366step1 raw7366step1Labels = mixedMoment B raw7366step2 raw7366step2Labels := by
      have ha : raw7366step2 = raw7366step1 := by apply Matrix.ext; unfold raw7366step2 raw7366step1; decide +kernel
      have hl : raw7366step1Labels = labelEmbedding1 ∘ raw7366step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7366step1 raw7366step1Labels raw7366step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3288 node3288Labels := by rfl

theorem canonical7370 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7370 raw7370Labels = mixedMoment B node3532 node3532Labels := by
  calc
    mixedMoment B raw7370 raw7370Labels = mixedMoment B raw7370step0 raw7370step0Labels := by
      have ha : raw7370step0 = (fun i j => raw7370 (permutation170 i) (permutation7 j)) := by apply Matrix.ext; unfold raw7370step0 raw7370; decide +kernel
      have hl : raw7370step0Labels = raw7370Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7370 raw7370Labels permutation170 permutation7
    mixedMoment B raw7370step0 raw7370step0Labels = mixedMoment B raw7370step1 raw7370step1Labels := by
      have ha : raw7370step1 = -raw7370step0 := by apply Matrix.ext; change ∀ i j, raw7370step1 i j = -(raw7370step0 i j); unfold raw7370step1 raw7370step0; decide +kernel
      have hl : raw7370step1Labels = raw7370step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw7370step1 raw7370step1Labels = mixedMoment B raw7370step2 raw7370step2Labels := by
      have ha : raw7370step2 = raw7370step1 := by apply Matrix.ext; unfold raw7370step2 raw7370step1; decide +kernel
      have hl : raw7370step1Labels = labelEmbedding1 ∘ raw7370step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7370step1 raw7370step1Labels raw7370step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3532 node3532Labels := by rfl

theorem canonical7387 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7387 raw7387Labels = mixedMoment B node4091 node4091Labels := by
  calc
    mixedMoment B raw7387 raw7387Labels = mixedMoment B raw7387step0 raw7387step0Labels := by
      have hz : ∀ j, raw7387 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw7387step0 = (fun i j => raw7387 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw7387step0 raw7387; decide +kernel
      have hl : raw7387step0Labels = raw7387Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7387 raw7387Labels permutation590 hz
    _ = mixedMoment B node4091 node4091Labels := by rfl

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

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons70
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singleton4495 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4495 node4495Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1079 node1079Labels + mixedMoment B node1708 node1708Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1293 singletonSmall4495
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4495) = raw1293Labels := by decide +kernel
  rw [hl, canonical1293 B hB] at h
  have hc0 : mixedMoment B raw1293 (Fin.cases (0 : Fin 2) singletonSmall4495) =
      mixedMoment B node1079 node1079Labels := by
    have ha : raw1293 = raw1294 := by apply Matrix.ext; unfold raw1293 raw1294; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4495 = raw1294Labels := by decide +kernel
    rw [ha, hj, canonical1294 B hB]
  have hc1 : mixedMoment B raw1293 (Fin.cases (1 : Fin 2) singletonSmall4495) =
      mixedMoment B node1708 node1708Labels := by
    have ha : raw1293 = raw1295 := by apply Matrix.ext; unfold raw1293 raw1295; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4495 = raw1295Labels := by decide +kernel
    rw [ha, hj, canonical1295 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

end MUB6.Certificate.MixedSemantics

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

theorem singleton4544 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4544 node4544Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1129 node1129Labels + mixedMoment B node3263 node3263Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1368 singletonSmall4544
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4544) = raw1368Labels := by decide +kernel
  rw [hl, canonical1368 B hB] at h
  have hc0 : mixedMoment B raw1368 (Fin.cases (0 : Fin 2) singletonSmall4544) =
      mixedMoment B node1129 node1129Labels := by
    have ha : raw1368 = raw1369 := by apply Matrix.ext; unfold raw1368 raw1369; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4544 = raw1369Labels := by decide +kernel
    rw [ha, hj, canonical1369 B hB]
  have hc1 : mixedMoment B raw1368 (Fin.cases (1 : Fin 2) singletonSmall4544) =
      mixedMoment B node3263 node3263Labels := by
    have ha : raw1368 = raw1370 := by apply Matrix.ext; unfold raw1368 raw1370; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4544 = raw1370Labels := by decide +kernel
    rw [ha, hj, canonical1370 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4550 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4550 node4550Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1135 node1135Labels + mixedMoment B node3269 node3269Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1377 singletonSmall4550
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4550) = raw1377Labels := by decide +kernel
  rw [hl, canonical1377 B hB] at h
  have hc0 : mixedMoment B raw1377 (Fin.cases (0 : Fin 2) singletonSmall4550) =
      mixedMoment B node1135 node1135Labels := by
    have ha : raw1377 = raw1378 := by apply Matrix.ext; unfold raw1377 raw1378; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4550 = raw1378Labels := by decide +kernel
    rw [ha, hj, canonical1378 B hB]
  have hc1 : mixedMoment B raw1377 (Fin.cases (1 : Fin 2) singletonSmall4550) =
      mixedMoment B node3269 node3269Labels := by
    have ha : raw1377 = raw1379 := by apply Matrix.ext; unfold raw1377 raw1379; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4550 = raw1379Labels := by decide +kernel
    rw [ha, hj, canonical1379 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4601 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4601 node4601Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1235 node1235Labels + mixedMoment B node3292 node3292Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1422 singletonSmall4601
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4601) = raw1422Labels := by decide +kernel
  rw [hl, canonical1422 B hB] at h
  have hc0 : mixedMoment B raw1422 (Fin.cases (0 : Fin 2) singletonSmall4601) =
      mixedMoment B node1235 node1235Labels := by
    have ha : raw1422 = raw1423 := by apply Matrix.ext; unfold raw1422 raw1423; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4601 = raw1423Labels := by decide +kernel
    rw [ha, hj, canonical1423 B hB]
  have hc1 : mixedMoment B raw1422 (Fin.cases (1 : Fin 2) singletonSmall4601) =
      mixedMoment B node3292 node3292Labels := by
    have ha : raw1422 = raw1424 := by apply Matrix.ext; unfold raw1422 raw1424; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4601 = raw1424Labels := by decide +kernel
    rw [ha, hj, canonical1424 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4606 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4606 node4606Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1240 node1240Labels + mixedMoment B node3299 node3299Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1431 singletonSmall4606
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4606) = raw1431Labels := by decide +kernel
  rw [hl, canonical1431 B hB] at h
  have hc0 : mixedMoment B raw1431 (Fin.cases (0 : Fin 2) singletonSmall4606) =
      mixedMoment B node1240 node1240Labels := by
    have ha : raw1431 = raw1432 := by apply Matrix.ext; unfold raw1431 raw1432; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4606 = raw1432Labels := by decide +kernel
    rw [ha, hj, canonical1432 B hB]
  have hc1 : mixedMoment B raw1431 (Fin.cases (1 : Fin 2) singletonSmall4606) =
      mixedMoment B node3299 node3299Labels := by
    have ha : raw1431 = raw1433 := by apply Matrix.ext; unfold raw1431 raw1433; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4606 = raw1433Labels := by decide +kernel
    rw [ha, hj, canonical1433 B hB]
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

theorem singleton4618 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4618 node4618Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1293 node1293Labels + mixedMoment B node3304 node3304Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1440 singletonSmall4618
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4618) = raw1440Labels := by decide +kernel
  rw [hl, canonical1440 B hB] at h
  have hc0 : mixedMoment B raw1440 (Fin.cases (0 : Fin 2) singletonSmall4618) =
      mixedMoment B node1293 node1293Labels := by
    have ha : raw1440 = raw1441 := by apply Matrix.ext; unfold raw1440 raw1441; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4618 = raw1441Labels := by decide +kernel
    rw [ha, hj, canonical1441 B hB]
  have hc1 : mixedMoment B raw1440 (Fin.cases (1 : Fin 2) singletonSmall4618) =
      mixedMoment B node3304 node3304Labels := by
    have ha : raw1440 = raw1442 := by apply Matrix.ext; unfold raw1440 raw1442; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4618 = raw1442Labels := by decide +kernel
    rw [ha, hj, canonical1442 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4622 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4622 node4622Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1299 node1299Labels + mixedMoment B node3307 node3307Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1449 singletonSmall4622
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4622) = raw1449Labels := by decide +kernel
  rw [hl, canonical1449 B hB] at h
  have hc0 : mixedMoment B raw1449 (Fin.cases (0 : Fin 2) singletonSmall4622) =
      mixedMoment B node1299 node1299Labels := by
    have ha : raw1449 = raw1450 := by apply Matrix.ext; unfold raw1449 raw1450; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4622 = raw1450Labels := by decide +kernel
    rw [ha, hj, canonical1450 B hB]
  have hc1 : mixedMoment B raw1449 (Fin.cases (1 : Fin 2) singletonSmall4622) =
      mixedMoment B node3307 node3307Labels := by
    have ha : raw1449 = raw1451 := by apply Matrix.ext; unfold raw1449 raw1451; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4622 = raw1451Labels := by decide +kernel
    rw [ha, hj, canonical1451 B hB]
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

theorem singleton5257 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5257 node5257Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2721 node2721Labels + mixedMoment B node3532 node3532Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2268 singletonSmall5257
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5257) = raw2268Labels := by decide +kernel
  rw [hl, canonical2268 B hB] at h
  have hc0 : mixedMoment B raw2268 (Fin.cases (0 : Fin 2) singletonSmall5257) =
      mixedMoment B node2721 node2721Labels := by
    have ha : raw2268 = raw2269 := by apply Matrix.ext; unfold raw2268 raw2269; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5257 = raw2269Labels := by decide +kernel
    rw [ha, hj, canonical2269 B hB]
  have hc1 : mixedMoment B raw2268 (Fin.cases (1 : Fin 2) singletonSmall5257) =
      mixedMoment B node3532 node3532Labels := by
    have ha : raw2268 = raw2270 := by apply Matrix.ext; unfold raw2268 raw2270; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5257 = raw2270Labels := by decide +kernel
    rw [ha, hj, canonical2270 B hB]
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

theorem sound732 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node732 node732Labels = Sparse.eval nodeValue732 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 732) = mixedMoment B node732 node732Labels := rfl
  simpa [nodeValue732, Sparse.eval] using hc.symm

theorem sound736 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node736 node736Labels = Sparse.eval nodeValue736 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 736) = mixedMoment B node736 node736Labels := rfl
  simpa [nodeValue736, Sparse.eval] using hc.symm

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

theorem zero805 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node805 node805Labels = 0 := by
  exact mixedMoment_order_one B hB node805 node805Labels 1
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

theorem sound805 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node805 node805Labels = Sparse.eval nodeValue805 (mixedVector B) := by
  simpa only [nodeValue805, Sparse.eval_nil] using zero805 B _hB _hF

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

theorem sound1039 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1039 node1039Labels = Sparse.eval nodeValue1039 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1039) = mixedMoment B node1039 node1039Labels := rfl
  simpa [nodeValue1039, Sparse.eval] using hc.symm

theorem sound1052 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1052 node1052Labels = Sparse.eval nodeValue1052 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1052) = mixedMoment B node1052 node1052Labels := rfl
  simpa [nodeValue1052, Sparse.eval] using hc.symm

theorem sound1079 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1079 node1079Labels = Sparse.eval nodeValue1079 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1079) = mixedMoment B node1079 node1079Labels := rfl
  simpa [nodeValue1079, Sparse.eval] using hc.symm

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

theorem sound1097 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1097 node1097Labels = Sparse.eval nodeValue1097 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1097) = mixedMoment B node1097 node1097Labels := rfl
  simpa [nodeValue1097, Sparse.eval] using hc.symm

theorem sound1100 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1100 node1100Labels = Sparse.eval nodeValue1100 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1100) = mixedMoment B node1100 node1100Labels := rfl
  simpa [nodeValue1100, Sparse.eval] using hc.symm

theorem sound1129 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1129 node1129Labels = Sparse.eval nodeValue1129 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1129) = mixedMoment B node1129 node1129Labels := rfl
  simpa [nodeValue1129, Sparse.eval] using hc.symm

theorem sound1135 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1135 node1135Labels = Sparse.eval nodeValue1135 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1135) = mixedMoment B node1135 node1135Labels := rfl
  simpa [nodeValue1135, Sparse.eval] using hc.symm

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

theorem sound1183 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1183 node1183Labels = Sparse.eval nodeValue1183 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1183) = mixedMoment B node1183 node1183Labels := rfl
  simpa [nodeValue1183, Sparse.eval] using hc.symm

theorem sound1187 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1187 node1187Labels = Sparse.eval nodeValue1187 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1187) = mixedMoment B node1187 node1187Labels := rfl
  simpa [nodeValue1187, Sparse.eval] using hc.symm

theorem sound1200 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1200 node1200Labels = Sparse.eval nodeValue1200 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1200) = mixedMoment B node1200 node1200Labels := rfl
  simpa [nodeValue1200, Sparse.eval] using hc.symm

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

theorem sound1228 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1228 node1228Labels = Sparse.eval nodeValue1228 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1228) = mixedMoment B node1228 node1228Labels := rfl
  simpa [nodeValue1228, Sparse.eval] using hc.symm

theorem sound1235 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1235 node1235Labels = Sparse.eval nodeValue1235 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1235) = mixedMoment B node1235 node1235Labels := rfl
  simpa [nodeValue1235, Sparse.eval] using hc.symm

theorem sound1236 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1236 node1236Labels = Sparse.eval nodeValue1236 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1236) = mixedMoment B node1236 node1236Labels := rfl
  simpa [nodeValue1236, Sparse.eval] using hc.symm

theorem sound1240 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1240 node1240Labels = Sparse.eval nodeValue1240 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1240) = mixedMoment B node1240 node1240Labels := rfl
  simpa [nodeValue1240, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound20
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound1293 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1293 node1293Labels = Sparse.eval nodeValue1293 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1293) = mixedMoment B node1293 node1293Labels := rfl
  simpa [nodeValue1293, Sparse.eval] using hc.symm

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

theorem sound1501 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1501 node1501Labels = Sparse.eval nodeValue1501 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1501) = mixedMoment B node1501 node1501Labels := rfl
  simpa [nodeValue1501, Sparse.eval] using hc.symm

theorem sound1502 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1502 node1502Labels = Sparse.eval nodeValue1502 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1502) = mixedMoment B node1502 node1502Labels := rfl
  simpa [nodeValue1502, Sparse.eval] using hc.symm

theorem sound1504 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1504 node1504Labels = Sparse.eval nodeValue1504 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1504) = mixedMoment B node1504 node1504Labels := rfl
  simpa [nodeValue1504, Sparse.eval] using hc.symm

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

theorem sound1644 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1644 node1644Labels = Sparse.eval nodeValue1644 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1644) = mixedMoment B node1644 node1644Labels := rfl
  simpa [nodeValue1644, Sparse.eval] using hc.symm

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

theorem sound1706 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1706 node1706Labels = Sparse.eval nodeValue1706 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1706) = mixedMoment B node1706 node1706Labels := rfl
  simpa [nodeValue1706, Sparse.eval] using hc.symm

theorem sound1708 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1708 node1708Labels = Sparse.eval nodeValue1708 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1708) = mixedMoment B node1708 node1708Labels := rfl
  simpa [nodeValue1708, Sparse.eval] using hc.symm

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

theorem sound2098 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2098 node2098Labels = Sparse.eval nodeValue2098 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2098) = mixedMoment B node2098 node2098Labels := rfl
  simpa [nodeValue2098, Sparse.eval] using hc.symm

theorem sound2100 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2100 node2100Labels = Sparse.eval nodeValue2100 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2100) = mixedMoment B node2100 node2100Labels := rfl
  simpa [nodeValue2100, Sparse.eval] using hc.symm

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

theorem sound2127 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2127 node2127Labels = Sparse.eval nodeValue2127 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2127) = mixedMoment B node2127 node2127Labels := rfl
  simpa [nodeValue2127, Sparse.eval] using hc.symm

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

theorem zero2204 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2204 node2204Labels = 0 := by
  exact mixedMoment_order_one B hB node2204 node2204Labels 1
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

theorem sound2202 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2202 node2202Labels = Sparse.eval nodeValue2202 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2202) = mixedMoment B node2202 node2202Labels := rfl
  simpa [nodeValue2202, Sparse.eval] using hc.symm

theorem sound2204 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2204 node2204Labels = Sparse.eval nodeValue2204 (mixedVector B) := by
  simpa only [nodeValue2204, Sparse.eval_nil] using zero2204 B _hB _hF

theorem sound2214 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2214 node2214Labels = Sparse.eval nodeValue2214 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2214) = mixedMoment B node2214 node2214Labels := rfl
  simpa [nodeValue2214, Sparse.eval] using hc.symm

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

theorem sound2250 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2250 node2250Labels = Sparse.eval nodeValue2250 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2250) = mixedMoment B node2250 node2250Labels := rfl
  simpa [nodeValue2250, Sparse.eval] using hc.symm

theorem sound2260 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2260 node2260Labels = Sparse.eval nodeValue2260 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2260) = mixedMoment B node2260 node2260Labels := rfl
  simpa [nodeValue2260, Sparse.eval] using hc.symm

theorem sound2275 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2275 node2275Labels = Sparse.eval nodeValue2275 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2275) = mixedMoment B node2275 node2275Labels := rfl
  simpa [nodeValue2275, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros37
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero2402 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2402 node2402Labels = 0 := by
  exact mixedMoment_order_one B hB node2402 node2402Labels 1
    (by decide +kernel) (by decide +kernel)

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

theorem sound2398 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2398 node2398Labels = Sparse.eval nodeValue2398 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2398) = mixedMoment B node2398 node2398Labels := rfl
  simpa [nodeValue2398, Sparse.eval] using hc.symm

theorem sound2402 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2402 node2402Labels = Sparse.eval nodeValue2402 (mixedVector B) := by
  simpa only [nodeValue2402, Sparse.eval_nil] using zero2402 B _hB _hF

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

theorem sound2503 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2503 node2503Labels = Sparse.eval nodeValue2503 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2503) = mixedMoment B node2503 node2503Labels := rfl
  simpa [nodeValue2503, Sparse.eval] using hc.symm

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

theorem sound2669 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2669 node2669Labels = Sparse.eval nodeValue2669 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2669) = mixedMoment B node2669 node2669Labels := rfl
  simpa [nodeValue2669, Sparse.eval] using hc.symm

theorem sound2671 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2671 node2671Labels = Sparse.eval nodeValue2671 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2671) = mixedMoment B node2671 node2671Labels := rfl
  simpa [nodeValue2671, Sparse.eval] using hc.symm

theorem sound2676 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2676 node2676Labels = Sparse.eval nodeValue2676 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2676) = mixedMoment B node2676 node2676Labels := rfl
  simpa [nodeValue2676, Sparse.eval] using hc.symm

theorem sound2684 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2684 node2684Labels = Sparse.eval nodeValue2684 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2684) = mixedMoment B node2684 node2684Labels := rfl
  simpa [nodeValue2684, Sparse.eval] using hc.symm

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

theorem sound2703 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2703 node2703Labels = Sparse.eval nodeValue2703 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2703) = mixedMoment B node2703 node2703Labels := rfl
  simpa [nodeValue2703, Sparse.eval] using hc.symm

theorem sound2718 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2718 node2718Labels = Sparse.eval nodeValue2718 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2718) = mixedMoment B node2718 node2718Labels := rfl
  simpa [nodeValue2718, Sparse.eval] using hc.symm

theorem sound2721 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2721 node2721Labels = Sparse.eval nodeValue2721 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2721) = mixedMoment B node2721 node2721Labels := rfl
  simpa [nodeValue2721, Sparse.eval] using hc.symm

theorem sound2728 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2728 node2728Labels = Sparse.eval nodeValue2728 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2728) = mixedMoment B node2728 node2728Labels := rfl
  simpa [nodeValue2728, Sparse.eval] using hc.symm

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

theorem sound2880 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2880 node2880Labels = Sparse.eval nodeValue2880 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2880) = mixedMoment B node2880 node2880Labels := rfl
  simpa [nodeValue2880, Sparse.eval] using hc.symm

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

theorem sound3263 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3263 node3263Labels = Sparse.eval nodeValue3263 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3263) = mixedMoment B node3263 node3263Labels := rfl
  simpa [nodeValue3263, Sparse.eval] using hc.symm

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

theorem sound3269 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3269 node3269Labels = Sparse.eval nodeValue3269 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3269) = mixedMoment B node3269 node3269Labels := rfl
  simpa [nodeValue3269, Sparse.eval] using hc.symm

theorem sound3288 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3288 node3288Labels = Sparse.eval nodeValue3288 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3288) = mixedMoment B node3288 node3288Labels := rfl
  simpa [nodeValue3288, Sparse.eval] using hc.symm

theorem sound3289 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3289 node3289Labels = Sparse.eval nodeValue3289 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3289) = mixedMoment B node3289 node3289Labels := rfl
  simpa [nodeValue3289, Sparse.eval] using hc.symm

theorem sound3290 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3290 node3290Labels = Sparse.eval nodeValue3290 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3290) = mixedMoment B node3290 node3290Labels := rfl
  simpa [nodeValue3290, Sparse.eval] using hc.symm

theorem sound3292 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3292 node3292Labels = Sparse.eval nodeValue3292 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3292) = mixedMoment B node3292 node3292Labels := rfl
  simpa [nodeValue3292, Sparse.eval] using hc.symm

theorem sound3299 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3299 node3299Labels = Sparse.eval nodeValue3299 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3299) = mixedMoment B node3299 node3299Labels := rfl
  simpa [nodeValue3299, Sparse.eval] using hc.symm

theorem sound3304 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3304 node3304Labels = Sparse.eval nodeValue3304 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3304) = mixedMoment B node3304 node3304Labels := rfl
  simpa [nodeValue3304, Sparse.eval] using hc.symm

theorem sound3307 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3307 node3307Labels = Sparse.eval nodeValue3307 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3307) = mixedMoment B node3307 node3307Labels := rfl
  simpa [nodeValue3307, Sparse.eval] using hc.symm

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

theorem zero3469 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3469 node3469Labels = 0 := by
  exact mixedMoment_order_one B hB node3469 node3469Labels 1
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

theorem sound3469 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3469 node3469Labels = Sparse.eval nodeValue3469 (mixedVector B) := by
  simpa only [nodeValue3469, Sparse.eval_nil] using zero3469 B _hB _hF

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

theorem sound3532 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3532 node3532Labels = Sparse.eval nodeValue3532 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3532) = mixedMoment B node3532 node3532Labels := rfl
  simpa [nodeValue3532, Sparse.eval] using hc.symm

theorem sound3546 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3546 node3546Labels = Sparse.eval nodeValue3546 (mixedVector B) := by
  simpa only [nodeValue3546, Sparse.eval_nil] using zero3546 B _hB _hF

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound8
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound567 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node567 node567Labels = Sparse.eval nodeValue567 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 567) = mixedMoment B node567 node567Labels := rfl
  simpa [nodeValue567, Sparse.eval] using hc.symm

theorem sound571 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node571 node571Labels = Sparse.eval nodeValue571 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 571) = mixedMoment B node571 node571Labels := rfl
  simpa [nodeValue571, Sparse.eval] using hc.symm

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

theorem sound4068 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4068 node4068Labels = Sparse.eval nodeValue4068 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4068) = mixedMoment B node4068 node4068Labels := rfl
  simpa [nodeValue4068, Sparse.eval] using hc.symm

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

theorem sound4087 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4087 node4087Labels = Sparse.eval nodeValue4087 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4087) = mixedMoment B node4087 node4087Labels := rfl
  simpa [nodeValue4087, Sparse.eval] using hc.symm

theorem sound4088 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4088 node4088Labels = Sparse.eval nodeValue4088 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4088) = mixedMoment B node4088 node4088Labels := rfl
  simpa [nodeValue4088, Sparse.eval] using hc.symm

theorem sound4090 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4090 node4090Labels = Sparse.eval nodeValue4090 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4090) = mixedMoment B node4090 node4090Labels := rfl
  simpa [nodeValue4090, Sparse.eval] using hc.symm

theorem sound4091 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4091 node4091Labels = Sparse.eval nodeValue4091 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4091) = mixedMoment B node4091 node4091Labels := rfl
  simpa [nodeValue4091, Sparse.eval] using hc.symm

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

theorem sound599 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node599 node599Labels = Sparse.eval nodeValue599 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 599) = mixedMoment B node599 node599Labels := rfl
  simpa [nodeValue599, Sparse.eval] using hc.symm

theorem sound625 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node625 node625Labels = Sparse.eval nodeValue625 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 625) = mixedMoment B node625 node625Labels := rfl
  simpa [nodeValue625, Sparse.eval] using hc.symm

theorem sound629 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node629 node629Labels = Sparse.eval nodeValue629 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 629) = mixedMoment B node629 node629Labels := rfl
  simpa [nodeValue629, Sparse.eval] using hc.symm

theorem sound637 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node637 node637Labels = Sparse.eval nodeValue637 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 637) = mixedMoment B node637 node637Labels := rfl
  simpa [nodeValue637, Sparse.eval] using hc.symm

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

theorem sound4149 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4149 node4149Labels = Sparse.eval nodeValue4149 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4149) = mixedMoment B node4149 node4149Labels := rfl
  simpa [nodeValue4149, Sparse.eval] using hc.symm

theorem sound4150 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4150 node4150Labels = Sparse.eval nodeValue4150 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4150) = mixedMoment B node4150 node4150Labels := rfl
  simpa [nodeValue4150, Sparse.eval] using hc.symm

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

theorem sound4169 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4169 node4169Labels = Sparse.eval nodeValue4169 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4169) = mixedMoment B node4169 node4169Labels := rfl
  simpa [nodeValue4169, Sparse.eval] using hc.symm

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

theorem sound4456 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4456 node4456Labels = Sparse.eval nodeValue4456 (mixedVector B) := by
  have h := singleton4456 B _hB
  rw [sound1039 B _hB _hF, sound1706 B _hB _hF] at h
  norm_num [nodeValue4456, nodeValue1039, nodeValue1706, Sparse.eval] at h ⊢
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

theorem sound4495 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4495 node4495Labels = Sparse.eval nodeValue4495 (mixedVector B) := by
  have h := singleton4495 B _hB
  rw [sound1079 B _hB _hF, sound1708 B _hB _hF] at h
  norm_num [nodeValue4495, nodeValue1079, nodeValue1708, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4497 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4497 node4497Labels = Sparse.eval nodeValue4497 (mixedVector B) := by
  simpa only [nodeValue4497, Sparse.eval_nil] using zero4497 B _hB _hF

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

theorem sound4544 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4544 node4544Labels = Sparse.eval nodeValue4544 (mixedVector B) := by
  have h := singleton4544 B _hB
  rw [sound1129 B _hB _hF, sound3263 B _hB _hF] at h
  norm_num [nodeValue4544, nodeValue1129, nodeValue3263, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4550 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4550 node4550Labels = Sparse.eval nodeValue4550 (mixedVector B) := by
  have h := singleton4550 B _hB
  rw [sound1135 B _hB _hF, sound3269 B _hB _hF] at h
  norm_num [nodeValue4550, nodeValue1135, nodeValue3269, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4589 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4589 node4589Labels = Sparse.eval nodeValue4589 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4589) = mixedMoment B node4589 node4589Labels := rfl
  simpa [nodeValue4589, Sparse.eval] using hc.symm

theorem sound4590 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4590 node4590Labels = Sparse.eval nodeValue4590 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4590) = mixedMoment B node4590 node4590Labels := rfl
  simpa [nodeValue4590, Sparse.eval] using hc.symm

theorem sound4599 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4599 node4599Labels = Sparse.eval nodeValue4599 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4599) = mixedMoment B node4599 node4599Labels := rfl
  simpa [nodeValue4599, Sparse.eval] using hc.symm

theorem sound4601 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4601 node4601Labels = Sparse.eval nodeValue4601 (mixedVector B) := by
  have h := singleton4601 B _hB
  rw [sound1235 B _hB _hF, sound3292 B _hB _hF] at h
  norm_num [nodeValue4601, nodeValue1235, nodeValue3292, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4606 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4606 node4606Labels = Sparse.eval nodeValue4606 (mixedVector B) := by
  have h := singleton4606 B _hB
  rw [sound1240 B _hB _hF, sound3299 B _hB _hF] at h
  norm_num [nodeValue4606, nodeValue1240, nodeValue3299, Sparse.eval] at h ⊢
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

theorem sound4616 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4616 node4616Labels = Sparse.eval nodeValue4616 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4616) = mixedMoment B node4616 node4616Labels := rfl
  simpa [nodeValue4616, Sparse.eval] using hc.symm

theorem sound4618 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4618 node4618Labels = Sparse.eval nodeValue4618 (mixedVector B) := by
  have h := singleton4618 B _hB
  rw [sound1293 B _hB _hF, sound3304 B _hB _hF] at h
  norm_num [nodeValue4618, nodeValue1293, nodeValue3304, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4622 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4622 node4622Labels = Sparse.eval nodeValue4622 (mixedVector B) := by
  have h := singleton4622 B _hB
  rw [sound1299_e B _hB _hF, sound3307 B _hB _hF] at h
  norm_num [nodeValue4622, nodeValue1299, nodeValue3307, Sparse.eval] at h ⊢
  linarith only [h]

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

theorem zero5100 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5100 node5100Labels = 0 := by
  exact mixedMoment_order_one B hB node5100 node5100Labels 1
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

theorem sound5100 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5100 node5100Labels = Sparse.eval nodeValue5100 (mixedVector B) := by
  simpa only [nodeValue5100, Sparse.eval_nil] using zero5100 B _hB _hF

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

theorem sound5257 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5257 node5257Labels = Sparse.eval nodeValue5257 (mixedVector B) := by
  have h := singleton5257 B _hB
  rw [sound2721 B _hB _hF, sound3532 B _hB _hF] at h
  norm_num [nodeValue5257, nodeValue2721, nodeValue3532, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5273 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5273 node5273Labels = Sparse.eval nodeValue5273 (mixedVector B) := by
  simpa only [nodeValue5273, Sparse.eval_nil] using zero5273 B _hB _hF

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources57
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sourceEq1854 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1854 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1854 + difference 0 1) (sourceB1854 + difference 1 0) sourceC1854) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4456) := by
    have ha : (tripleCharges (sourceA1854 + difference 0 1) (sourceB1854 + difference 1 0) sourceC1854) = raw26679 := by
      apply Matrix.ext; unfold tripleCharges sourceA1854 sourceB1854 sourceC1854 difference raw26679; decide +kernel
    rw [ha]
    exact (canonical26679 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1854 + difference 0 2) (sourceB1854 + difference 2 0) sourceC1854) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4495) := by
    have ha : (tripleCharges (sourceA1854 + difference 0 2) (sourceB1854 + difference 2 0) sourceC1854) = raw26680 := by
      apply Matrix.ext; unfold tripleCharges sourceA1854 sourceB1854 sourceC1854 difference raw26680; decide +kernel
    rw [ha]
    exact (canonical26680 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1854 + difference 0 3) (sourceB1854 + difference 3 0) sourceC1854) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4495) := by
    have ha : (tripleCharges (sourceA1854 + difference 0 3) (sourceB1854 + difference 3 0) sourceC1854) = raw26681 := by
      apply Matrix.ext; unfold tripleCharges sourceA1854 sourceB1854 sourceC1854 difference raw26681; decide +kernel
    rw [ha]
    exact (canonical26681 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1854 + difference 0 4) (sourceB1854 + difference 4 0) sourceC1854) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4497) := by
    have ha : (tripleCharges (sourceA1854 + difference 0 4) (sourceB1854 + difference 4 0) sourceC1854) = raw26581 := by
      apply Matrix.ext; unfold tripleCharges sourceA1854 sourceB1854 sourceC1854 difference raw26581; decide +kernel
    rw [ha]
    exact (canonical26581 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1854 + difference 0 5) (sourceB1854 + difference 5 0) sourceC1854) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4497) := by
    have ha : (tripleCharges (sourceA1854 + difference 0 5) (sourceB1854 + difference 5 0) sourceC1854) = raw26682 := by
      apply Matrix.ext; unfold tripleCharges sourceA1854 sourceB1854 sourceC1854 difference raw26682; decide +kernel
    rw [ha]
    exact (canonical26682 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1854 + difference 1 0) (sourceB1854 + difference 0 1) sourceC1854) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4456) := by
    have ha : (tripleCharges (sourceA1854 + difference 1 0) (sourceB1854 + difference 0 1) sourceC1854) = raw26683 := by
      apply Matrix.ext; unfold tripleCharges sourceA1854 sourceB1854 sourceC1854 difference raw26683; decide +kernel
    rw [ha]
    exact (canonical26683 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1854 + difference 1 2) (sourceB1854 + difference 2 1) sourceC1854) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4599) := by
    have ha : (tripleCharges (sourceA1854 + difference 1 2) (sourceB1854 + difference 2 1) sourceC1854) = raw26684 := by
      apply Matrix.ext; unfold tripleCharges sourceA1854 sourceB1854 sourceC1854 difference raw26684; decide +kernel
    rw [ha]
    exact (canonical26684 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1854 + difference 1 3) (sourceB1854 + difference 3 1) sourceC1854) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4599) := by
    have ha : (tripleCharges (sourceA1854 + difference 1 3) (sourceB1854 + difference 3 1) sourceC1854) = raw26685 := by
      apply Matrix.ext; unfold tripleCharges sourceA1854 sourceB1854 sourceC1854 difference raw26685; decide +kernel
    rw [ha]
    exact (canonical26685 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1854 + difference 1 4) (sourceB1854 + difference 4 1) sourceC1854) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4601) := by
    have ha : (tripleCharges (sourceA1854 + difference 1 4) (sourceB1854 + difference 4 1) sourceC1854) = raw26586 := by
      apply Matrix.ext; unfold tripleCharges sourceA1854 sourceB1854 sourceC1854 difference raw26586; decide +kernel
    rw [ha]
    exact (canonical26586 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1854 + difference 1 5) (sourceB1854 + difference 5 1) sourceC1854) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4601) := by
    have ha : (tripleCharges (sourceA1854 + difference 1 5) (sourceB1854 + difference 5 1) sourceC1854) = raw26686 := by
      apply Matrix.ext; unfold tripleCharges sourceA1854 sourceB1854 sourceC1854 difference raw26686; decide +kernel
    rw [ha]
    exact (canonical26686 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1854 + difference 2 0) (sourceB1854 + difference 0 2) sourceC1854) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4497) := by
    have ha : (tripleCharges (sourceA1854 + difference 2 0) (sourceB1854 + difference 0 2) sourceC1854) = raw26687 := by
      apply Matrix.ext; unfold tripleCharges sourceA1854 sourceB1854 sourceC1854 difference raw26687; decide +kernel
    rw [ha]
    exact (canonical26687 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1854 + difference 2 1) (sourceB1854 + difference 1 2) sourceC1854) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4601) := by
    have ha : (tripleCharges (sourceA1854 + difference 2 1) (sourceB1854 + difference 1 2) sourceC1854) = raw26688 := by
      apply Matrix.ext; unfold tripleCharges sourceA1854 sourceB1854 sourceC1854 difference raw26688; decide +kernel
    rw [ha]
    exact (canonical26688 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1854 + difference 2 3) (sourceB1854 + difference 3 2) sourceC1854) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4618) := by
    have ha : (tripleCharges (sourceA1854 + difference 2 3) (sourceB1854 + difference 3 2) sourceC1854) = raw26689 := by
      apply Matrix.ext; unfold tripleCharges sourceA1854 sourceB1854 sourceC1854 difference raw26689; decide +kernel
    rw [ha]
    exact (canonical26689 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1854 + difference 2 4) (sourceB1854 + difference 4 2) sourceC1854) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4622) := by
    have ha : (tripleCharges (sourceA1854 + difference 2 4) (sourceB1854 + difference 4 2) sourceC1854) = raw26591 := by
      apply Matrix.ext; unfold tripleCharges sourceA1854 sourceB1854 sourceC1854 difference raw26591; decide +kernel
    rw [ha]
    exact (canonical26591 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1854 + difference 2 5) (sourceB1854 + difference 5 2) sourceC1854) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4622) := by
    have ha : (tripleCharges (sourceA1854 + difference 2 5) (sourceB1854 + difference 5 2) sourceC1854) = raw26690 := by
      apply Matrix.ext; unfold tripleCharges sourceA1854 sourceB1854 sourceC1854 difference raw26690; decide +kernel
    rw [ha]
    exact (canonical26690 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1854 + difference 3 0) (sourceB1854 + difference 0 3) sourceC1854) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4497) := by
    have ha : (tripleCharges (sourceA1854 + difference 3 0) (sourceB1854 + difference 0 3) sourceC1854) = raw26691 := by
      apply Matrix.ext; unfold tripleCharges sourceA1854 sourceB1854 sourceC1854 difference raw26691; decide +kernel
    rw [ha]
    exact (canonical26691 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1854 + difference 3 1) (sourceB1854 + difference 1 3) sourceC1854) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4601) := by
    have ha : (tripleCharges (sourceA1854 + difference 3 1) (sourceB1854 + difference 1 3) sourceC1854) = raw26692 := by
      apply Matrix.ext; unfold tripleCharges sourceA1854 sourceB1854 sourceC1854 difference raw26692; decide +kernel
    rw [ha]
    exact (canonical26692 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1854 + difference 3 2) (sourceB1854 + difference 2 3) sourceC1854) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4618) := by
    have ha : (tripleCharges (sourceA1854 + difference 3 2) (sourceB1854 + difference 2 3) sourceC1854) = raw26693 := by
      apply Matrix.ext; unfold tripleCharges sourceA1854 sourceB1854 sourceC1854 difference raw26693; decide +kernel
    rw [ha]
    exact (canonical26693 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1854 + difference 3 4) (sourceB1854 + difference 4 3) sourceC1854) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4622) := by
    have ha : (tripleCharges (sourceA1854 + difference 3 4) (sourceB1854 + difference 4 3) sourceC1854) = raw26596 := by
      apply Matrix.ext; unfold tripleCharges sourceA1854 sourceB1854 sourceC1854 difference raw26596; decide +kernel
    rw [ha]
    exact (canonical26596 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1854 + difference 3 5) (sourceB1854 + difference 5 3) sourceC1854) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4622) := by
    have ha : (tripleCharges (sourceA1854 + difference 3 5) (sourceB1854 + difference 5 3) sourceC1854) = raw26694 := by
      apply Matrix.ext; unfold tripleCharges sourceA1854 sourceB1854 sourceC1854 difference raw26694; decide +kernel
    rw [ha]
    exact (canonical26694 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1854 + difference 4 0) (sourceB1854 + difference 0 4) sourceC1854) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4495) := by
    have ha : (tripleCharges (sourceA1854 + difference 4 0) (sourceB1854 + difference 0 4) sourceC1854) = raw26695 := by
      apply Matrix.ext; unfold tripleCharges sourceA1854 sourceB1854 sourceC1854 difference raw26695; decide +kernel
    rw [ha]
    exact (canonical26695 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1854 + difference 4 1) (sourceB1854 + difference 1 4) sourceC1854) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4599) := by
    have ha : (tripleCharges (sourceA1854 + difference 4 1) (sourceB1854 + difference 1 4) sourceC1854) = raw26696 := by
      apply Matrix.ext; unfold tripleCharges sourceA1854 sourceB1854 sourceC1854 difference raw26696; decide +kernel
    rw [ha]
    exact (canonical26696 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1854 + difference 4 2) (sourceB1854 + difference 2 4) sourceC1854) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4616) := by
    have ha : (tripleCharges (sourceA1854 + difference 4 2) (sourceB1854 + difference 2 4) sourceC1854) = raw26697 := by
      apply Matrix.ext; unfold tripleCharges sourceA1854 sourceB1854 sourceC1854 difference raw26697; decide +kernel
    rw [ha]
    exact (canonical26697 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1854 + difference 4 3) (sourceB1854 + difference 3 4) sourceC1854) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4616) := by
    have ha : (tripleCharges (sourceA1854 + difference 4 3) (sourceB1854 + difference 3 4) sourceC1854) = raw26698 := by
      apply Matrix.ext; unfold tripleCharges sourceA1854 sourceB1854 sourceC1854 difference raw26698; decide +kernel
    rw [ha]
    exact (canonical26698 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1854 + difference 4 5) (sourceB1854 + difference 5 4) sourceC1854) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4618) := by
    have ha : (tripleCharges (sourceA1854 + difference 4 5) (sourceB1854 + difference 5 4) sourceC1854) = raw26699 := by
      apply Matrix.ext; unfold tripleCharges sourceA1854 sourceB1854 sourceC1854 difference raw26699; decide +kernel
    rw [ha]
    exact (canonical26699 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1854 + difference 5 0) (sourceB1854 + difference 0 5) sourceC1854) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4495) := by
    have ha : (tripleCharges (sourceA1854 + difference 5 0) (sourceB1854 + difference 0 5) sourceC1854) = raw26597 := by
      apply Matrix.ext; unfold tripleCharges sourceA1854 sourceB1854 sourceC1854 difference raw26597; decide +kernel
    rw [ha]
    exact (canonical26597 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1854 + difference 5 1) (sourceB1854 + difference 1 5) sourceC1854) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4599) := by
    have ha : (tripleCharges (sourceA1854 + difference 5 1) (sourceB1854 + difference 1 5) sourceC1854) = raw26598 := by
      apply Matrix.ext; unfold tripleCharges sourceA1854 sourceB1854 sourceC1854 difference raw26598; decide +kernel
    rw [ha]
    exact (canonical26598 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1854 + difference 5 2) (sourceB1854 + difference 2 5) sourceC1854) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4616) := by
    have ha : (tripleCharges (sourceA1854 + difference 5 2) (sourceB1854 + difference 2 5) sourceC1854) = raw26599 := by
      apply Matrix.ext; unfold tripleCharges sourceA1854 sourceB1854 sourceC1854 difference raw26599; decide +kernel
    rw [ha]
    exact (canonical26599 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1854 + difference 5 3) (sourceB1854 + difference 3 5) sourceC1854) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4616) := by
    have ha : (tripleCharges (sourceA1854 + difference 5 3) (sourceB1854 + difference 3 5) sourceC1854) = raw26600 := by
      apply Matrix.ext; unfold tripleCharges sourceA1854 sourceB1854 sourceC1854 difference raw26600; decide +kernel
    rw [ha]
    exact (canonical26600 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1854 + difference 5 4) (sourceB1854 + difference 4 5) sourceC1854) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4618) := by
    have ha : (tripleCharges (sourceA1854 + difference 5 4) (sourceB1854 + difference 4 5) sourceC1854) = raw26700 := by
      apply Matrix.ext; unfold tripleCharges sourceA1854 sourceB1854 sourceC1854 difference raw26700; decide +kernel
    rw [ha]
    exact (canonical26700 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1854 sourceB1854 sourceC1854
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1854, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1855 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1855 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1855 + difference 0 0) (sourceB1855 + difference 0 0) sourceC1855) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1228) := by
    have ha : (tripleCharges (sourceA1855 + difference 0 0) (sourceB1855 + difference 0 0) sourceC1855) = raw26701 := by
      apply Matrix.ext; unfold tripleCharges sourceA1855 sourceB1855 sourceC1855 difference raw26701; decide +kernel
    rw [ha]
    exact (canonical26701 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1855 + difference 0 1) (sourceB1855 + difference 1 0) sourceC1855) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2503) := by
    have ha : (tripleCharges (sourceA1855 + difference 0 1) (sourceB1855 + difference 1 0) sourceC1855) = raw26702 := by
      apply Matrix.ext; unfold tripleCharges sourceA1855 sourceB1855 sourceC1855 difference raw26702; decide +kernel
    rw [ha]
    exact (canonical26702 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1855 + difference 0 2) (sourceB1855 + difference 2 0) sourceC1855) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2728) := by
    have ha : (tripleCharges (sourceA1855 + difference 0 2) (sourceB1855 + difference 2 0) sourceC1855) = raw26703 := by
      apply Matrix.ext; unfold tripleCharges sourceA1855 sourceB1855 sourceC1855 difference raw26703; decide +kernel
    rw [ha]
    exact (canonical26703 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1855 + difference 0 3) (sourceB1855 + difference 3 0) sourceC1855) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2718) := by
    have ha : (tripleCharges (sourceA1855 + difference 0 3) (sourceB1855 + difference 3 0) sourceC1855) = raw26704 := by
      apply Matrix.ext; unfold tripleCharges sourceA1855 sourceB1855 sourceC1855 difference raw26704; decide +kernel
    rw [ha]
    exact (canonical26704 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1855 + difference 0 4) (sourceB1855 + difference 4 0) sourceC1855) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2718) := by
    have ha : (tripleCharges (sourceA1855 + difference 0 4) (sourceB1855 + difference 4 0) sourceC1855) = raw26705 := by
      apply Matrix.ext; unfold tripleCharges sourceA1855 sourceB1855 sourceC1855 difference raw26705; decide +kernel
    rw [ha]
    exact (canonical26705 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1855 + difference 0 5) (sourceB1855 + difference 5 0) sourceC1855) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2703) := by
    have ha : (tripleCharges (sourceA1855 + difference 0 5) (sourceB1855 + difference 5 0) sourceC1855) = raw26706 := by
      apply Matrix.ext; unfold tripleCharges sourceA1855 sourceB1855 sourceC1855 difference raw26706; decide +kernel
    rw [ha]
    exact (canonical26706 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1855 + sourceB1855) sourceC1855) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4090) := by
    have ha : (doubleCharges (sourceA1855 + sourceB1855) sourceC1855) = raw26707 := by
      apply Matrix.ext; unfold doubleCharges sourceA1855 sourceB1855 sourceC1855 raw26707; decide +kernel
    rw [ha]
    exact (canonical26707 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1855 sourceB1855 sourceC1855
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1855, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources58
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sourceEq1856 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1856 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1856 + difference 0 1) (sourceB1856 + difference 1 0) sourceC1856) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5100) := by
    have ha : (tripleCharges (sourceA1856 + difference 0 1) (sourceB1856 + difference 1 0) sourceC1856) = raw26708 := by
      apply Matrix.ext; unfold tripleCharges sourceA1856 sourceB1856 sourceC1856 difference raw26708; decide +kernel
    rw [ha]
    exact (canonical26708 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1856 + difference 0 2) (sourceB1856 + difference 2 0) sourceC1856) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5257) := by
    have ha : (tripleCharges (sourceA1856 + difference 0 2) (sourceB1856 + difference 2 0) sourceC1856) = raw7310 := by
      apply Matrix.ext; unfold tripleCharges sourceA1856 sourceB1856 sourceC1856 difference raw7310; decide +kernel
    rw [ha]
    exact (canonical7310 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1856 + difference 0 3) (sourceB1856 + difference 3 0) sourceC1856) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5257) := by
    have ha : (tripleCharges (sourceA1856 + difference 0 3) (sourceB1856 + difference 3 0) sourceC1856) = raw7305 := by
      apply Matrix.ext; unfold tripleCharges sourceA1856 sourceB1856 sourceC1856 difference raw7305; decide +kernel
    rw [ha]
    exact (canonical7305 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1856 + difference 0 4) (sourceB1856 + difference 4 0) sourceC1856) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5257) := by
    have ha : (tripleCharges (sourceA1856 + difference 0 4) (sourceB1856 + difference 4 0) sourceC1856) = raw26709 := by
      apply Matrix.ext; unfold tripleCharges sourceA1856 sourceB1856 sourceC1856 difference raw26709; decide +kernel
    rw [ha]
    exact (canonical26709 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1856 + difference 0 5) (sourceB1856 + difference 5 0) sourceC1856) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5273) := by
    have ha : (tripleCharges (sourceA1856 + difference 0 5) (sourceB1856 + difference 5 0) sourceC1856) = raw26710 := by
      apply Matrix.ext; unfold tripleCharges sourceA1856 sourceB1856 sourceC1856 difference raw26710; decide +kernel
    rw [ha]
    exact (canonical26710 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1856 + difference 1 0) (sourceB1856 + difference 0 1) sourceC1856) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4169) := by
    have ha : (tripleCharges (sourceA1856 + difference 1 0) (sourceB1856 + difference 0 1) sourceC1856) = raw26711 := by
      apply Matrix.ext; unfold tripleCharges sourceA1856 sourceB1856 sourceC1856 difference raw26711; decide +kernel
    rw [ha]
    exact (canonical26711 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1856 + difference 1 2) (sourceB1856 + difference 2 1) sourceC1856) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4599) := by
    have ha : (tripleCharges (sourceA1856 + difference 1 2) (sourceB1856 + difference 2 1) sourceC1856) = raw26712 := by
      apply Matrix.ext; unfold tripleCharges sourceA1856 sourceB1856 sourceC1856 difference raw26712; decide +kernel
    rw [ha]
    exact (canonical26712 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1856 + difference 1 3) (sourceB1856 + difference 3 1) sourceC1856) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4599) := by
    have ha : (tripleCharges (sourceA1856 + difference 1 3) (sourceB1856 + difference 3 1) sourceC1856) = raw26713 := by
      apply Matrix.ext; unfold tripleCharges sourceA1856 sourceB1856 sourceC1856 difference raw26713; decide +kernel
    rw [ha]
    exact (canonical26713 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1856 + difference 1 4) (sourceB1856 + difference 4 1) sourceC1856) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4599) := by
    have ha : (tripleCharges (sourceA1856 + difference 1 4) (sourceB1856 + difference 4 1) sourceC1856) = raw26714 := by
      apply Matrix.ext; unfold tripleCharges sourceA1856 sourceB1856 sourceC1856 difference raw26714; decide +kernel
    rw [ha]
    exact (canonical26714 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1856 + difference 1 5) (sourceB1856 + difference 5 1) sourceC1856) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4618) := by
    have ha : (tripleCharges (sourceA1856 + difference 1 5) (sourceB1856 + difference 5 1) sourceC1856) = raw26715 := by
      apply Matrix.ext; unfold tripleCharges sourceA1856 sourceB1856 sourceC1856 difference raw26715; decide +kernel
    rw [ha]
    exact (canonical26715 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1856 + difference 2 0) (sourceB1856 + difference 0 2) sourceC1856) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4150) := by
    have ha : (tripleCharges (sourceA1856 + difference 2 0) (sourceB1856 + difference 0 2) sourceC1856) = raw26716 := by
      apply Matrix.ext; unfold tripleCharges sourceA1856 sourceB1856 sourceC1856 difference raw26716; decide +kernel
    rw [ha]
    exact (canonical26716 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1856 + difference 2 1) (sourceB1856 + difference 1 2) sourceC1856) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4544) := by
    have ha : (tripleCharges (sourceA1856 + difference 2 1) (sourceB1856 + difference 1 2) sourceC1856) = raw26717 := by
      apply Matrix.ext; unfold tripleCharges sourceA1856 sourceB1856 sourceC1856 difference raw26717; decide +kernel
    rw [ha]
    exact (canonical26717 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1856 + difference 2 3) (sourceB1856 + difference 3 2) sourceC1856) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4590) := by
    have ha : (tripleCharges (sourceA1856 + difference 2 3) (sourceB1856 + difference 3 2) sourceC1856) = raw26718 := by
      apply Matrix.ext; unfold tripleCharges sourceA1856 sourceB1856 sourceC1856 difference raw26718; decide +kernel
    rw [ha]
    exact (canonical26718 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1856 + difference 2 4) (sourceB1856 + difference 4 2) sourceC1856) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4590) := by
    have ha : (tripleCharges (sourceA1856 + difference 2 4) (sourceB1856 + difference 4 2) sourceC1856) = raw26719 := by
      apply Matrix.ext; unfold tripleCharges sourceA1856 sourceB1856 sourceC1856 difference raw26719; decide +kernel
    rw [ha]
    exact (canonical26719 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1856 + difference 2 5) (sourceB1856 + difference 5 2) sourceC1856) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4606) := by
    have ha : (tripleCharges (sourceA1856 + difference 2 5) (sourceB1856 + difference 5 2) sourceC1856) = raw26720 := by
      apply Matrix.ext; unfold tripleCharges sourceA1856 sourceB1856 sourceC1856 difference raw26720; decide +kernel
    rw [ha]
    exact (canonical26720 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1856 + difference 3 0) (sourceB1856 + difference 0 3) sourceC1856) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4150) := by
    have ha : (tripleCharges (sourceA1856 + difference 3 0) (sourceB1856 + difference 0 3) sourceC1856) = raw26721 := by
      apply Matrix.ext; unfold tripleCharges sourceA1856 sourceB1856 sourceC1856 difference raw26721; decide +kernel
    rw [ha]
    exact (canonical26721 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1856 + difference 3 1) (sourceB1856 + difference 1 3) sourceC1856) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4544) := by
    have ha : (tripleCharges (sourceA1856 + difference 3 1) (sourceB1856 + difference 1 3) sourceC1856) = raw26722 := by
      apply Matrix.ext; unfold tripleCharges sourceA1856 sourceB1856 sourceC1856 difference raw26722; decide +kernel
    rw [ha]
    exact (canonical26722 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1856 + difference 3 2) (sourceB1856 + difference 2 3) sourceC1856) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4590) := by
    have ha : (tripleCharges (sourceA1856 + difference 3 2) (sourceB1856 + difference 2 3) sourceC1856) = raw26723 := by
      apply Matrix.ext; unfold tripleCharges sourceA1856 sourceB1856 sourceC1856 difference raw26723; decide +kernel
    rw [ha]
    exact (canonical26723 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1856 + difference 3 4) (sourceB1856 + difference 4 3) sourceC1856) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4590) := by
    have ha : (tripleCharges (sourceA1856 + difference 3 4) (sourceB1856 + difference 4 3) sourceC1856) = raw26724 := by
      apply Matrix.ext; unfold tripleCharges sourceA1856 sourceB1856 sourceC1856 difference raw26724; decide +kernel
    rw [ha]
    exact (canonical26724 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1856 + difference 3 5) (sourceB1856 + difference 5 3) sourceC1856) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4606) := by
    have ha : (tripleCharges (sourceA1856 + difference 3 5) (sourceB1856 + difference 5 3) sourceC1856) = raw26725 := by
      apply Matrix.ext; unfold tripleCharges sourceA1856 sourceB1856 sourceC1856 difference raw26725; decide +kernel
    rw [ha]
    exact (canonical26725 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1856 + difference 4 0) (sourceB1856 + difference 0 4) sourceC1856) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4150) := by
    have ha : (tripleCharges (sourceA1856 + difference 4 0) (sourceB1856 + difference 0 4) sourceC1856) = raw26726 := by
      apply Matrix.ext; unfold tripleCharges sourceA1856 sourceB1856 sourceC1856 difference raw26726; decide +kernel
    rw [ha]
    exact (canonical26726 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1856 + difference 4 1) (sourceB1856 + difference 1 4) sourceC1856) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4544) := by
    have ha : (tripleCharges (sourceA1856 + difference 4 1) (sourceB1856 + difference 1 4) sourceC1856) = raw26727 := by
      apply Matrix.ext; unfold tripleCharges sourceA1856 sourceB1856 sourceC1856 difference raw26727; decide +kernel
    rw [ha]
    exact (canonical26727 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1856 + difference 4 2) (sourceB1856 + difference 2 4) sourceC1856) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4590) := by
    have ha : (tripleCharges (sourceA1856 + difference 4 2) (sourceB1856 + difference 2 4) sourceC1856) = raw26728 := by
      apply Matrix.ext; unfold tripleCharges sourceA1856 sourceB1856 sourceC1856 difference raw26728; decide +kernel
    rw [ha]
    exact (canonical26728 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1856 + difference 4 3) (sourceB1856 + difference 3 4) sourceC1856) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4590) := by
    have ha : (tripleCharges (sourceA1856 + difference 4 3) (sourceB1856 + difference 3 4) sourceC1856) = raw26729 := by
      apply Matrix.ext; unfold tripleCharges sourceA1856 sourceB1856 sourceC1856 difference raw26729; decide +kernel
    rw [ha]
    exact (canonical26729 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1856 + difference 4 5) (sourceB1856 + difference 5 4) sourceC1856) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4606) := by
    have ha : (tripleCharges (sourceA1856 + difference 4 5) (sourceB1856 + difference 5 4) sourceC1856) = raw26730 := by
      apply Matrix.ext; unfold tripleCharges sourceA1856 sourceB1856 sourceC1856 difference raw26730; decide +kernel
    rw [ha]
    exact (canonical26730 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1856 + difference 5 0) (sourceB1856 + difference 0 5) sourceC1856) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4149) := by
    have ha : (tripleCharges (sourceA1856 + difference 5 0) (sourceB1856 + difference 0 5) sourceC1856) = raw26731 := by
      apply Matrix.ext; unfold tripleCharges sourceA1856 sourceB1856 sourceC1856 difference raw26731; decide +kernel
    rw [ha]
    exact (canonical26731 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1856 + difference 5 1) (sourceB1856 + difference 1 5) sourceC1856) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4550) := by
    have ha : (tripleCharges (sourceA1856 + difference 5 1) (sourceB1856 + difference 1 5) sourceC1856) = raw26732 := by
      apply Matrix.ext; unfold tripleCharges sourceA1856 sourceB1856 sourceC1856 difference raw26732; decide +kernel
    rw [ha]
    exact (canonical26732 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1856 + difference 5 2) (sourceB1856 + difference 2 5) sourceC1856) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4589) := by
    have ha : (tripleCharges (sourceA1856 + difference 5 2) (sourceB1856 + difference 2 5) sourceC1856) = raw7306 := by
      apply Matrix.ext; unfold tripleCharges sourceA1856 sourceB1856 sourceC1856 difference raw7306; decide +kernel
    rw [ha]
    exact (canonical7306 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1856 + difference 5 3) (sourceB1856 + difference 3 5) sourceC1856) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4589) := by
    have ha : (tripleCharges (sourceA1856 + difference 5 3) (sourceB1856 + difference 3 5) sourceC1856) = raw7301 := by
      apply Matrix.ext; unfold tripleCharges sourceA1856 sourceB1856 sourceC1856 difference raw7301; decide +kernel
    rw [ha]
    exact (canonical7301 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1856 + difference 5 4) (sourceB1856 + difference 4 5) sourceC1856) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4589) := by
    have ha : (tripleCharges (sourceA1856 + difference 5 4) (sourceB1856 + difference 4 5) sourceC1856) = raw26733 := by
      apply Matrix.ext; unfold tripleCharges sourceA1856 sourceB1856 sourceC1856 difference raw26733; decide +kernel
    rw [ha]
    exact (canonical26733 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1856 sourceB1856 sourceC1856
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1856, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1858 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1858 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1858 + difference 0 1) (sourceB1858 + difference 1 0) sourceC1858) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3469) := by
    have ha : (tripleCharges (sourceA1858 + difference 0 1) (sourceB1858 + difference 1 0) sourceC1858) = raw26760 := by
      apply Matrix.ext; unfold tripleCharges sourceA1858 sourceB1858 sourceC1858 difference raw26760; decide +kernel
    rw [ha]
    exact (canonical26760 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1858 + difference 0 2) (sourceB1858 + difference 2 0) sourceC1858) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3532) := by
    have ha : (tripleCharges (sourceA1858 + difference 0 2) (sourceB1858 + difference 2 0) sourceC1858) = raw7370 := by
      apply Matrix.ext; unfold tripleCharges sourceA1858 sourceB1858 sourceC1858 difference raw7370; decide +kernel
    rw [ha]
    exact (canonical7370 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1858 + difference 0 3) (sourceB1858 + difference 3 0) sourceC1858) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3532) := by
    have ha : (tripleCharges (sourceA1858 + difference 0 3) (sourceB1858 + difference 3 0) sourceC1858) = raw7365 := by
      apply Matrix.ext; unfold tripleCharges sourceA1858 sourceB1858 sourceC1858 difference raw7365; decide +kernel
    rw [ha]
    exact (canonical7365 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1858 + difference 0 4) (sourceB1858 + difference 4 0) sourceC1858) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3532) := by
    have ha : (tripleCharges (sourceA1858 + difference 0 4) (sourceB1858 + difference 4 0) sourceC1858) = raw26761 := by
      apply Matrix.ext; unfold tripleCharges sourceA1858 sourceB1858 sourceC1858 difference raw26761; decide +kernel
    rw [ha]
    exact (canonical26761 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1858 + difference 0 5) (sourceB1858 + difference 5 0) sourceC1858) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3546) := by
    have ha : (tripleCharges (sourceA1858 + difference 0 5) (sourceB1858 + difference 5 0) sourceC1858) = raw26762 := by
      apply Matrix.ext; unfold tripleCharges sourceA1858 sourceB1858 sourceC1858 difference raw26762; decide +kernel
    rw [ha]
    exact (canonical26762 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1858 + difference 1 0) (sourceB1858 + difference 0 1) sourceC1858) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1502) := by
    have ha : (tripleCharges (sourceA1858 + difference 1 0) (sourceB1858 + difference 0 1) sourceC1858) = raw26763 := by
      apply Matrix.ext; unfold tripleCharges sourceA1858 sourceB1858 sourceC1858 difference raw26763; decide +kernel
    rw [ha]
    exact (canonical26763 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1858 + difference 1 2) (sourceB1858 + difference 2 1) sourceC1858) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3289) := by
    have ha : (tripleCharges (sourceA1858 + difference 1 2) (sourceB1858 + difference 2 1) sourceC1858) = raw26764 := by
      apply Matrix.ext; unfold tripleCharges sourceA1858 sourceB1858 sourceC1858 difference raw26764; decide +kernel
    rw [ha]
    exact (canonical26764 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1858 + difference 1 3) (sourceB1858 + difference 3 1) sourceC1858) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3289) := by
    have ha : (tripleCharges (sourceA1858 + difference 1 3) (sourceB1858 + difference 3 1) sourceC1858) = raw26765 := by
      apply Matrix.ext; unfold tripleCharges sourceA1858 sourceB1858 sourceC1858 difference raw26765; decide +kernel
    rw [ha]
    exact (canonical26765 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1858 + difference 1 4) (sourceB1858 + difference 4 1) sourceC1858) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3289) := by
    have ha : (tripleCharges (sourceA1858 + difference 1 4) (sourceB1858 + difference 4 1) sourceC1858) = raw26766 := by
      apply Matrix.ext; unfold tripleCharges sourceA1858 sourceB1858 sourceC1858 difference raw26766; decide +kernel
    rw [ha]
    exact (canonical26766 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1858 + difference 1 5) (sourceB1858 + difference 5 1) sourceC1858) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3304) := by
    have ha : (tripleCharges (sourceA1858 + difference 1 5) (sourceB1858 + difference 5 1) sourceC1858) = raw26767 := by
      apply Matrix.ext; unfold tripleCharges sourceA1858 sourceB1858 sourceC1858 difference raw26767; decide +kernel
    rw [ha]
    exact (canonical26767 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1858 + difference 2 0) (sourceB1858 + difference 0 2) sourceC1858) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1504) := by
    have ha : (tripleCharges (sourceA1858 + difference 2 0) (sourceB1858 + difference 0 2) sourceC1858) = raw26768 := by
      apply Matrix.ext; unfold tripleCharges sourceA1858 sourceB1858 sourceC1858 difference raw26768; decide +kernel
    rw [ha]
    exact (canonical26768 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1858 + difference 2 1) (sourceB1858 + difference 1 2) sourceC1858) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3263) := by
    have ha : (tripleCharges (sourceA1858 + difference 2 1) (sourceB1858 + difference 1 2) sourceC1858) = raw26769 := by
      apply Matrix.ext; unfold tripleCharges sourceA1858 sourceB1858 sourceC1858 difference raw26769; decide +kernel
    rw [ha]
    exact (canonical26769 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1858 + difference 2 3) (sourceB1858 + difference 3 2) sourceC1858) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3290) := by
    have ha : (tripleCharges (sourceA1858 + difference 2 3) (sourceB1858 + difference 3 2) sourceC1858) = raw26770 := by
      apply Matrix.ext; unfold tripleCharges sourceA1858 sourceB1858 sourceC1858 difference raw26770; decide +kernel
    rw [ha]
    exact (canonical26770 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1858 + difference 2 4) (sourceB1858 + difference 4 2) sourceC1858) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3290) := by
    have ha : (tripleCharges (sourceA1858 + difference 2 4) (sourceB1858 + difference 4 2) sourceC1858) = raw26771 := by
      apply Matrix.ext; unfold tripleCharges sourceA1858 sourceB1858 sourceC1858 difference raw26771; decide +kernel
    rw [ha]
    exact (canonical26771 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1858 + difference 2 5) (sourceB1858 + difference 5 2) sourceC1858) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3299) := by
    have ha : (tripleCharges (sourceA1858 + difference 2 5) (sourceB1858 + difference 5 2) sourceC1858) = raw26772 := by
      apply Matrix.ext; unfold tripleCharges sourceA1858 sourceB1858 sourceC1858 difference raw26772; decide +kernel
    rw [ha]
    exact (canonical26772 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1858 + difference 3 0) (sourceB1858 + difference 0 3) sourceC1858) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1504) := by
    have ha : (tripleCharges (sourceA1858 + difference 3 0) (sourceB1858 + difference 0 3) sourceC1858) = raw26773 := by
      apply Matrix.ext; unfold tripleCharges sourceA1858 sourceB1858 sourceC1858 difference raw26773; decide +kernel
    rw [ha]
    exact (canonical26773 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1858 + difference 3 1) (sourceB1858 + difference 1 3) sourceC1858) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3263) := by
    have ha : (tripleCharges (sourceA1858 + difference 3 1) (sourceB1858 + difference 1 3) sourceC1858) = raw26774 := by
      apply Matrix.ext; unfold tripleCharges sourceA1858 sourceB1858 sourceC1858 difference raw26774; decide +kernel
    rw [ha]
    exact (canonical26774 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1858 + difference 3 2) (sourceB1858 + difference 2 3) sourceC1858) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3290) := by
    have ha : (tripleCharges (sourceA1858 + difference 3 2) (sourceB1858 + difference 2 3) sourceC1858) = raw26775 := by
      apply Matrix.ext; unfold tripleCharges sourceA1858 sourceB1858 sourceC1858 difference raw26775; decide +kernel
    rw [ha]
    exact (canonical26775 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1858 + difference 3 4) (sourceB1858 + difference 4 3) sourceC1858) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3290) := by
    have ha : (tripleCharges (sourceA1858 + difference 3 4) (sourceB1858 + difference 4 3) sourceC1858) = raw26776 := by
      apply Matrix.ext; unfold tripleCharges sourceA1858 sourceB1858 sourceC1858 difference raw26776; decide +kernel
    rw [ha]
    exact (canonical26776 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1858 + difference 3 5) (sourceB1858 + difference 5 3) sourceC1858) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3299) := by
    have ha : (tripleCharges (sourceA1858 + difference 3 5) (sourceB1858 + difference 5 3) sourceC1858) = raw26777 := by
      apply Matrix.ext; unfold tripleCharges sourceA1858 sourceB1858 sourceC1858 difference raw26777; decide +kernel
    rw [ha]
    exact (canonical26777 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1858 + difference 4 0) (sourceB1858 + difference 0 4) sourceC1858) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1504) := by
    have ha : (tripleCharges (sourceA1858 + difference 4 0) (sourceB1858 + difference 0 4) sourceC1858) = raw26778 := by
      apply Matrix.ext; unfold tripleCharges sourceA1858 sourceB1858 sourceC1858 difference raw26778; decide +kernel
    rw [ha]
    exact (canonical26778 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1858 + difference 4 1) (sourceB1858 + difference 1 4) sourceC1858) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3263) := by
    have ha : (tripleCharges (sourceA1858 + difference 4 1) (sourceB1858 + difference 1 4) sourceC1858) = raw26779 := by
      apply Matrix.ext; unfold tripleCharges sourceA1858 sourceB1858 sourceC1858 difference raw26779; decide +kernel
    rw [ha]
    exact (canonical26779 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1858 + difference 4 2) (sourceB1858 + difference 2 4) sourceC1858) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3290) := by
    have ha : (tripleCharges (sourceA1858 + difference 4 2) (sourceB1858 + difference 2 4) sourceC1858) = raw26780 := by
      apply Matrix.ext; unfold tripleCharges sourceA1858 sourceB1858 sourceC1858 difference raw26780; decide +kernel
    rw [ha]
    exact (canonical26780 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1858 + difference 4 3) (sourceB1858 + difference 3 4) sourceC1858) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3290) := by
    have ha : (tripleCharges (sourceA1858 + difference 4 3) (sourceB1858 + difference 3 4) sourceC1858) = raw26781 := by
      apply Matrix.ext; unfold tripleCharges sourceA1858 sourceB1858 sourceC1858 difference raw26781; decide +kernel
    rw [ha]
    exact (canonical26781 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1858 + difference 4 5) (sourceB1858 + difference 5 4) sourceC1858) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3299) := by
    have ha : (tripleCharges (sourceA1858 + difference 4 5) (sourceB1858 + difference 5 4) sourceC1858) = raw26782 := by
      apply Matrix.ext; unfold tripleCharges sourceA1858 sourceB1858 sourceC1858 difference raw26782; decide +kernel
    rw [ha]
    exact (canonical26782 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1858 + difference 5 0) (sourceB1858 + difference 0 5) sourceC1858) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1501) := by
    have ha : (tripleCharges (sourceA1858 + difference 5 0) (sourceB1858 + difference 0 5) sourceC1858) = raw26783 := by
      apply Matrix.ext; unfold tripleCharges sourceA1858 sourceB1858 sourceC1858 difference raw26783; decide +kernel
    rw [ha]
    exact (canonical26783 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1858 + difference 5 1) (sourceB1858 + difference 1 5) sourceC1858) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3269) := by
    have ha : (tripleCharges (sourceA1858 + difference 5 1) (sourceB1858 + difference 1 5) sourceC1858) = raw26784 := by
      apply Matrix.ext; unfold tripleCharges sourceA1858 sourceB1858 sourceC1858 difference raw26784; decide +kernel
    rw [ha]
    exact (canonical26784 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1858 + difference 5 2) (sourceB1858 + difference 2 5) sourceC1858) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3288) := by
    have ha : (tripleCharges (sourceA1858 + difference 5 2) (sourceB1858 + difference 2 5) sourceC1858) = raw7366 := by
      apply Matrix.ext; unfold tripleCharges sourceA1858 sourceB1858 sourceC1858 difference raw7366; decide +kernel
    rw [ha]
    exact (canonical7366 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1858 + difference 5 3) (sourceB1858 + difference 3 5) sourceC1858) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3288) := by
    have ha : (tripleCharges (sourceA1858 + difference 5 3) (sourceB1858 + difference 3 5) sourceC1858) = raw7361 := by
      apply Matrix.ext; unfold tripleCharges sourceA1858 sourceB1858 sourceC1858 difference raw7361; decide +kernel
    rw [ha]
    exact (canonical7361 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1858 + difference 5 4) (sourceB1858 + difference 4 5) sourceC1858) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3288) := by
    have ha : (tripleCharges (sourceA1858 + difference 5 4) (sourceB1858 + difference 4 5) sourceC1858) = raw26785 := by
      apply Matrix.ext; unfold tripleCharges sourceA1858 sourceB1858 sourceC1858 difference raw26785; decide +kernel
    rw [ha]
    exact (canonical26785 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1858 sourceB1858 sourceC1858
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1858, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1859 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1859 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1859 + difference 0 0) (sourceB1859 + difference 0 0) sourceC1859) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1235) := by
    have ha : (tripleCharges (sourceA1859 + difference 0 0) (sourceB1859 + difference 0 0) sourceC1859) = raw26786 := by
      apply Matrix.ext; unfold tripleCharges sourceA1859 sourceB1859 sourceC1859 difference raw26786; decide +kernel
    rw [ha]
    exact (canonical26786 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1859 + difference 1 0) (sourceB1859 + difference 0 1) sourceC1859) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 637) := by
    have ha : (tripleCharges (sourceA1859 + difference 1 0) (sourceB1859 + difference 0 1) sourceC1859) = raw26787 := by
      apply Matrix.ext; unfold tripleCharges sourceA1859 sourceB1859 sourceC1859 difference raw26787; decide +kernel
    rw [ha]
    exact (canonical26787 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1859 + difference 2 0) (sourceB1859 + difference 0 2) sourceC1859) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 625) := by
    have ha : (tripleCharges (sourceA1859 + difference 2 0) (sourceB1859 + difference 0 2) sourceC1859) = raw26788 := by
      apply Matrix.ext; unfold tripleCharges sourceA1859 sourceB1859 sourceC1859 difference raw26788; decide +kernel
    rw [ha]
    exact (canonical26788 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1859 + difference 3 0) (sourceB1859 + difference 0 3) sourceC1859) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 625) := by
    have ha : (tripleCharges (sourceA1859 + difference 3 0) (sourceB1859 + difference 0 3) sourceC1859) = raw26789 := by
      apply Matrix.ext; unfold tripleCharges sourceA1859 sourceB1859 sourceC1859 difference raw26789; decide +kernel
    rw [ha]
    exact (canonical26789 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1859 + difference 4 0) (sourceB1859 + difference 0 4) sourceC1859) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 625) := by
    have ha : (tripleCharges (sourceA1859 + difference 4 0) (sourceB1859 + difference 0 4) sourceC1859) = raw26790 := by
      apply Matrix.ext; unfold tripleCharges sourceA1859 sourceB1859 sourceC1859 difference raw26790; decide +kernel
    rw [ha]
    exact (canonical26790 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1859 + difference 5 0) (sourceB1859 + difference 0 5) sourceC1859) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 629) := by
    have ha : (tripleCharges (sourceA1859 + difference 5 0) (sourceB1859 + difference 0 5) sourceC1859) = raw26791 := by
      apply Matrix.ext; unfold tripleCharges sourceA1859 sourceB1859 sourceC1859 difference raw26791; decide +kernel
    rw [ha]
    exact (canonical26791 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1859 + sourceB1859) sourceC1859) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA1859 + sourceB1859) sourceC1859) = raw7387 := by
      apply Matrix.ext; unfold doubleCharges sourceA1859 sourceB1859 sourceC1859 raw7387; decide +kernel
    rw [ha]
    exact (canonical7387 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1859 sourceB1859 sourceC1859
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1859, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1861 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1861 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1861 + difference 0 1) (sourceB1861 + difference 1 0) sourceC1861) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2880) := by
    have ha : (tripleCharges (sourceA1861 + difference 0 1) (sourceB1861 + difference 1 0) sourceC1861) = raw26822 := by
      apply Matrix.ext; unfold tripleCharges sourceA1861 sourceB1861 sourceC1861 difference raw26822; decide +kernel
    rw [ha]
    exact (canonical26822 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1861 + difference 0 2) (sourceB1861 + difference 2 0) sourceC1861) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3100) := by
    have ha : (tripleCharges (sourceA1861 + difference 0 2) (sourceB1861 + difference 2 0) sourceC1861) = raw26823 := by
      apply Matrix.ext; unfold tripleCharges sourceA1861 sourceB1861 sourceC1861 difference raw26823; decide +kernel
    rw [ha]
    exact (canonical26823 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1861 + difference 0 3) (sourceB1861 + difference 3 0) sourceC1861) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3100) := by
    have ha : (tripleCharges (sourceA1861 + difference 0 3) (sourceB1861 + difference 3 0) sourceC1861) = raw26824 := by
      apply Matrix.ext; unfold tripleCharges sourceA1861 sourceB1861 sourceC1861 difference raw26824; decide +kernel
    rw [ha]
    exact (canonical26824 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1861 + difference 0 4) (sourceB1861 + difference 4 0) sourceC1861) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3100) := by
    have ha : (tripleCharges (sourceA1861 + difference 0 4) (sourceB1861 + difference 4 0) sourceC1861) = raw26825 := by
      apply Matrix.ext; unfold tripleCharges sourceA1861 sourceB1861 sourceC1861 difference raw26825; decide +kernel
    rw [ha]
    exact (canonical26825 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1861 + difference 0 5) (sourceB1861 + difference 5 0) sourceC1861) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3076) := by
    have ha : (tripleCharges (sourceA1861 + difference 0 5) (sourceB1861 + difference 5 0) sourceC1861) = raw26826 := by
      apply Matrix.ext; unfold tripleCharges sourceA1861 sourceB1861 sourceC1861 difference raw26826; decide +kernel
    rw [ha]
    exact (canonical26826 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1861 + difference 1 0) (sourceB1861 + difference 0 1) sourceC1861) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 599) := by
    have ha : (tripleCharges (sourceA1861 + difference 1 0) (sourceB1861 + difference 0 1) sourceC1861) = raw26827 := by
      apply Matrix.ext; unfold tripleCharges sourceA1861 sourceB1861 sourceC1861 difference raw26827; decide +kernel
    rw [ha]
    exact (canonical26827 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1861 + difference 1 2) (sourceB1861 + difference 2 1) sourceC1861) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1299) := by
    have ha : (tripleCharges (sourceA1861 + difference 1 2) (sourceB1861 + difference 2 1) sourceC1861) = raw26828 := by
      apply Matrix.ext; unfold tripleCharges sourceA1861 sourceB1861 sourceC1861 difference raw26828; decide +kernel
    rw [ha]
    exact (canonical26828 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1861 + difference 1 3) (sourceB1861 + difference 3 1) sourceC1861) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1299) := by
    have ha : (tripleCharges (sourceA1861 + difference 1 3) (sourceB1861 + difference 3 1) sourceC1861) = raw26829 := by
      apply Matrix.ext; unfold tripleCharges sourceA1861 sourceB1861 sourceC1861 difference raw26829; decide +kernel
    rw [ha]
    exact (canonical26829 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1861 + difference 1 4) (sourceB1861 + difference 4 1) sourceC1861) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1299) := by
    have ha : (tripleCharges (sourceA1861 + difference 1 4) (sourceB1861 + difference 4 1) sourceC1861) = raw26830 := by
      apply Matrix.ext; unfold tripleCharges sourceA1861 sourceB1861 sourceC1861 difference raw26830; decide +kernel
    rw [ha]
    exact (canonical26830 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1861 + difference 1 5) (sourceB1861 + difference 5 1) sourceC1861) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1235) := by
    have ha : (tripleCharges (sourceA1861 + difference 1 5) (sourceB1861 + difference 5 1) sourceC1861) = raw26831 := by
      apply Matrix.ext; unfold tripleCharges sourceA1861 sourceB1861 sourceC1861 difference raw26831; decide +kernel
    rw [ha]
    exact (canonical26831 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1861 + difference 2 0) (sourceB1861 + difference 0 2) sourceC1861) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 567) := by
    have ha : (tripleCharges (sourceA1861 + difference 2 0) (sourceB1861 + difference 0 2) sourceC1861) = raw26832 := by
      apply Matrix.ext; unfold tripleCharges sourceA1861 sourceB1861 sourceC1861 difference raw26832; decide +kernel
    rw [ha]
    exact (canonical26832 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1861 + difference 2 1) (sourceB1861 + difference 1 2) sourceC1861) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1097) := by
    have ha : (tripleCharges (sourceA1861 + difference 2 1) (sourceB1861 + difference 1 2) sourceC1861) = raw26833 := by
      apply Matrix.ext; unfold tripleCharges sourceA1861 sourceB1861 sourceC1861 difference raw26833; decide +kernel
    rw [ha]
    exact (canonical26833 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1861 + difference 2 3) (sourceB1861 + difference 3 2) sourceC1861) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1236) := by
    have ha : (tripleCharges (sourceA1861 + difference 2 3) (sourceB1861 + difference 3 2) sourceC1861) = raw26834 := by
      apply Matrix.ext; unfold tripleCharges sourceA1861 sourceB1861 sourceC1861 difference raw26834; decide +kernel
    rw [ha]
    exact (canonical26834 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1861 + difference 2 4) (sourceB1861 + difference 4 2) sourceC1861) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1236) := by
    have ha : (tripleCharges (sourceA1861 + difference 2 4) (sourceB1861 + difference 4 2) sourceC1861) = raw26835 := by
      apply Matrix.ext; unfold tripleCharges sourceA1861 sourceB1861 sourceC1861 difference raw26835; decide +kernel
    rw [ha]
    exact (canonical26835 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1861 + difference 2 5) (sourceB1861 + difference 5 2) sourceC1861) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1200) := by
    have ha : (tripleCharges (sourceA1861 + difference 2 5) (sourceB1861 + difference 5 2) sourceC1861) = raw26836 := by
      apply Matrix.ext; unfold tripleCharges sourceA1861 sourceB1861 sourceC1861 difference raw26836; decide +kernel
    rw [ha]
    exact (canonical26836 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1861 + difference 3 0) (sourceB1861 + difference 0 3) sourceC1861) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 567) := by
    have ha : (tripleCharges (sourceA1861 + difference 3 0) (sourceB1861 + difference 0 3) sourceC1861) = raw26837 := by
      apply Matrix.ext; unfold tripleCharges sourceA1861 sourceB1861 sourceC1861 difference raw26837; decide +kernel
    rw [ha]
    exact (canonical26837 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1861 + difference 3 1) (sourceB1861 + difference 1 3) sourceC1861) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1097) := by
    have ha : (tripleCharges (sourceA1861 + difference 3 1) (sourceB1861 + difference 1 3) sourceC1861) = raw26838 := by
      apply Matrix.ext; unfold tripleCharges sourceA1861 sourceB1861 sourceC1861 difference raw26838; decide +kernel
    rw [ha]
    exact (canonical26838 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1861 + difference 3 2) (sourceB1861 + difference 2 3) sourceC1861) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1236) := by
    have ha : (tripleCharges (sourceA1861 + difference 3 2) (sourceB1861 + difference 2 3) sourceC1861) = raw26839 := by
      apply Matrix.ext; unfold tripleCharges sourceA1861 sourceB1861 sourceC1861 difference raw26839; decide +kernel
    rw [ha]
    exact (canonical26839 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1861 + difference 3 4) (sourceB1861 + difference 4 3) sourceC1861) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1236) := by
    have ha : (tripleCharges (sourceA1861 + difference 3 4) (sourceB1861 + difference 4 3) sourceC1861) = raw26840 := by
      apply Matrix.ext; unfold tripleCharges sourceA1861 sourceB1861 sourceC1861 difference raw26840; decide +kernel
    rw [ha]
    exact (canonical26840 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1861 + difference 3 5) (sourceB1861 + difference 5 3) sourceC1861) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1200) := by
    have ha : (tripleCharges (sourceA1861 + difference 3 5) (sourceB1861 + difference 5 3) sourceC1861) = raw26841 := by
      apply Matrix.ext; unfold tripleCharges sourceA1861 sourceB1861 sourceC1861 difference raw26841; decide +kernel
    rw [ha]
    exact (canonical26841 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1861 + difference 4 0) (sourceB1861 + difference 0 4) sourceC1861) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 567) := by
    have ha : (tripleCharges (sourceA1861 + difference 4 0) (sourceB1861 + difference 0 4) sourceC1861) = raw26842 := by
      apply Matrix.ext; unfold tripleCharges sourceA1861 sourceB1861 sourceC1861 difference raw26842; decide +kernel
    rw [ha]
    exact (canonical26842 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1861 + difference 4 1) (sourceB1861 + difference 1 4) sourceC1861) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1097) := by
    have ha : (tripleCharges (sourceA1861 + difference 4 1) (sourceB1861 + difference 1 4) sourceC1861) = raw26843 := by
      apply Matrix.ext; unfold tripleCharges sourceA1861 sourceB1861 sourceC1861 difference raw26843; decide +kernel
    rw [ha]
    exact (canonical26843 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1861 + difference 4 2) (sourceB1861 + difference 2 4) sourceC1861) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1236) := by
    have ha : (tripleCharges (sourceA1861 + difference 4 2) (sourceB1861 + difference 2 4) sourceC1861) = raw26844 := by
      apply Matrix.ext; unfold tripleCharges sourceA1861 sourceB1861 sourceC1861 difference raw26844; decide +kernel
    rw [ha]
    exact (canonical26844 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1861 + difference 4 3) (sourceB1861 + difference 3 4) sourceC1861) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1236) := by
    have ha : (tripleCharges (sourceA1861 + difference 4 3) (sourceB1861 + difference 3 4) sourceC1861) = raw26845 := by
      apply Matrix.ext; unfold tripleCharges sourceA1861 sourceB1861 sourceC1861 difference raw26845; decide +kernel
    rw [ha]
    exact (canonical26845 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1861 + difference 4 5) (sourceB1861 + difference 5 4) sourceC1861) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1200) := by
    have ha : (tripleCharges (sourceA1861 + difference 4 5) (sourceB1861 + difference 5 4) sourceC1861) = raw26846 := by
      apply Matrix.ext; unfold tripleCharges sourceA1861 sourceB1861 sourceC1861 difference raw26846; decide +kernel
    rw [ha]
    exact (canonical26846 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1861 + difference 5 0) (sourceB1861 + difference 0 5) sourceC1861) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 571) := by
    have ha : (tripleCharges (sourceA1861 + difference 5 0) (sourceB1861 + difference 0 5) sourceC1861) = raw26847 := by
      apply Matrix.ext; unfold tripleCharges sourceA1861 sourceB1861 sourceC1861 difference raw26847; decide +kernel
    rw [ha]
    exact (canonical26847 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1861 + difference 5 1) (sourceB1861 + difference 1 5) sourceC1861) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1100) := by
    have ha : (tripleCharges (sourceA1861 + difference 5 1) (sourceB1861 + difference 1 5) sourceC1861) = raw26848 := by
      apply Matrix.ext; unfold tripleCharges sourceA1861 sourceB1861 sourceC1861 difference raw26848; decide +kernel
    rw [ha]
    exact (canonical26848 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1861 + difference 5 2) (sourceB1861 + difference 2 5) sourceC1861) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1240) := by
    have ha : (tripleCharges (sourceA1861 + difference 5 2) (sourceB1861 + difference 2 5) sourceC1861) = raw26849 := by
      apply Matrix.ext; unfold tripleCharges sourceA1861 sourceB1861 sourceC1861 difference raw26849; decide +kernel
    rw [ha]
    exact (canonical26849 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1861 + difference 5 3) (sourceB1861 + difference 3 5) sourceC1861) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1240) := by
    have ha : (tripleCharges (sourceA1861 + difference 5 3) (sourceB1861 + difference 3 5) sourceC1861) = raw26850 := by
      apply Matrix.ext; unfold tripleCharges sourceA1861 sourceB1861 sourceC1861 difference raw26850; decide +kernel
    rw [ha]
    exact (canonical26850 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1861 + difference 5 4) (sourceB1861 + difference 4 5) sourceC1861) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1240) := by
    have ha : (tripleCharges (sourceA1861 + difference 5 4) (sourceB1861 + difference 4 5) sourceC1861) = raw26851 := by
      apply Matrix.ext; unfold tripleCharges sourceA1861 sourceB1861 sourceC1861 difference raw26851; decide +kernel
    rw [ha]
    exact (canonical26851 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1861 sourceB1861 sourceC1861
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1861, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1863 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1863 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1863 + difference 0 0) (sourceB1863 + difference 0 0) sourceC1863) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1183) := by
    have ha : (tripleCharges (sourceA1863 + difference 0 0) (sourceB1863 + difference 0 0) sourceC1863) = raw26878 := by
      apply Matrix.ext; unfold tripleCharges sourceA1863 sourceB1863 sourceC1863 difference raw26878; decide +kernel
    rw [ha]
    exact (canonical26878 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1863 + difference 0 1) (sourceB1863 + difference 1 0) sourceC1863) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2398) := by
    have ha : (tripleCharges (sourceA1863 + difference 0 1) (sourceB1863 + difference 1 0) sourceC1863) = raw26879 := by
      apply Matrix.ext; unfold tripleCharges sourceA1863 sourceB1863 sourceC1863 difference raw26879; decide +kernel
    rw [ha]
    exact (canonical26879 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1863 + difference 0 2) (sourceB1863 + difference 2 0) sourceC1863) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2676) := by
    have ha : (tripleCharges (sourceA1863 + difference 0 2) (sourceB1863 + difference 2 0) sourceC1863) = raw26880 := by
      apply Matrix.ext; unfold tripleCharges sourceA1863 sourceB1863 sourceC1863 difference raw26880; decide +kernel
    rw [ha]
    exact (canonical26880 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1863 + difference 0 3) (sourceB1863 + difference 3 0) sourceC1863) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2669) := by
    have ha : (tripleCharges (sourceA1863 + difference 0 3) (sourceB1863 + difference 3 0) sourceC1863) = raw26881 := by
      apply Matrix.ext; unfold tripleCharges sourceA1863 sourceB1863 sourceC1863 difference raw26881; decide +kernel
    rw [ha]
    exact (canonical26881 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1863 + difference 0 4) (sourceB1863 + difference 4 0) sourceC1863) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2669) := by
    have ha : (tripleCharges (sourceA1863 + difference 0 4) (sourceB1863 + difference 4 0) sourceC1863) = raw26882 := by
      apply Matrix.ext; unfold tripleCharges sourceA1863 sourceB1863 sourceC1863 difference raw26882; decide +kernel
    rw [ha]
    exact (canonical26882 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1863 + difference 0 5) (sourceB1863 + difference 5 0) sourceC1863) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2684) := by
    have ha : (tripleCharges (sourceA1863 + difference 0 5) (sourceB1863 + difference 5 0) sourceC1863) = raw26883 := by
      apply Matrix.ext; unfold tripleCharges sourceA1863 sourceB1863 sourceC1863 difference raw26883; decide +kernel
    rw [ha]
    exact (canonical26883 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1863 + sourceB1863) sourceC1863) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4088) := by
    have ha : (doubleCharges (sourceA1863 + sourceB1863) sourceC1863) = raw26884 := by
      apply Matrix.ext; unfold doubleCharges sourceA1863 sourceB1863 sourceC1863 raw26884; decide +kernel
    rw [ha]
    exact (canonical26884 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1863 sourceB1863 sourceC1863
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1863, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1864 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1864 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1864 + difference 0 0) (sourceB1864 + difference 0 0) sourceC1864) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1187) := by
    have ha : (tripleCharges (sourceA1864 + difference 0 0) (sourceB1864 + difference 0 0) sourceC1864) = raw26885 := by
      apply Matrix.ext; unfold tripleCharges sourceA1864 sourceB1864 sourceC1864 difference raw26885; decide +kernel
    rw [ha]
    exact (canonical26885 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1864 + difference 0 1) (sourceB1864 + difference 1 0) sourceC1864) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2402) := by
    have ha : (tripleCharges (sourceA1864 + difference 0 1) (sourceB1864 + difference 1 0) sourceC1864) = raw26886 := by
      apply Matrix.ext; unfold tripleCharges sourceA1864 sourceB1864 sourceC1864 difference raw26886; decide +kernel
    rw [ha]
    exact (canonical26886 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1864 + difference 0 2) (sourceB1864 + difference 2 0) sourceC1864) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2671) := by
    have ha : (tripleCharges (sourceA1864 + difference 0 2) (sourceB1864 + difference 2 0) sourceC1864) = raw26887 := by
      apply Matrix.ext; unfold tripleCharges sourceA1864 sourceB1864 sourceC1864 difference raw26887; decide +kernel
    rw [ha]
    exact (canonical26887 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1864 + difference 0 3) (sourceB1864 + difference 3 0) sourceC1864) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2671) := by
    have ha : (tripleCharges (sourceA1864 + difference 0 3) (sourceB1864 + difference 3 0) sourceC1864) = raw26888 := by
      apply Matrix.ext; unfold tripleCharges sourceA1864 sourceB1864 sourceC1864 difference raw26888; decide +kernel
    rw [ha]
    exact (canonical26888 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1864 + difference 0 4) (sourceB1864 + difference 4 0) sourceC1864) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2671) := by
    have ha : (tripleCharges (sourceA1864 + difference 0 4) (sourceB1864 + difference 4 0) sourceC1864) = raw26889 := by
      apply Matrix.ext; unfold tripleCharges sourceA1864 sourceB1864 sourceC1864 difference raw26889; decide +kernel
    rw [ha]
    exact (canonical26889 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1864 + difference 0 5) (sourceB1864 + difference 5 0) sourceC1864) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2671) := by
    have ha : (tripleCharges (sourceA1864 + difference 0 5) (sourceB1864 + difference 5 0) sourceC1864) = raw26890 := by
      apply Matrix.ext; unfold tripleCharges sourceA1864 sourceB1864 sourceC1864 difference raw26890; decide +kernel
    rw [ha]
    exact (canonical26890 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1864 + sourceB1864) sourceC1864) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4087) := by
    have ha : (doubleCharges (sourceA1864 + sourceB1864) sourceC1864) = raw26891 := by
      apply Matrix.ext; unfold doubleCharges sourceA1864 sourceB1864 sourceC1864 raw26891; decide +kernel
    rw [ha]
    exact (canonical26891 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1864 sourceB1864 sourceC1864
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1864, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1865 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1865 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1865 + difference 0 1) (sourceB1865 + difference 1 0) sourceC1865) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2402) := by
    have ha : (tripleCharges (sourceA1865 + difference 0 1) (sourceB1865 + difference 1 0) sourceC1865) = raw26886 := by
      apply Matrix.ext; unfold tripleCharges sourceA1865 sourceB1865 sourceC1865 difference raw26886; decide +kernel
    rw [ha]
    exact (canonical26886 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1865 + difference 1 1) (sourceB1865 + difference 1 1) sourceC1865) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1187) := by
    have ha : (tripleCharges (sourceA1865 + difference 1 1) (sourceB1865 + difference 1 1) sourceC1865) = raw26885 := by
      apply Matrix.ext; unfold tripleCharges sourceA1865 sourceB1865 sourceC1865 difference raw26885; decide +kernel
    rw [ha]
    exact (canonical26885 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1865 + difference 2 1) (sourceB1865 + difference 1 2) sourceC1865) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1100) := by
    have ha : (tripleCharges (sourceA1865 + difference 2 1) (sourceB1865 + difference 1 2) sourceC1865) = raw26892 := by
      apply Matrix.ext; unfold tripleCharges sourceA1865 sourceB1865 sourceC1865 difference raw26892; decide +kernel
    rw [ha]
    exact (canonical26892 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1865 + difference 3 1) (sourceB1865 + difference 1 3) sourceC1865) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1100) := by
    have ha : (tripleCharges (sourceA1865 + difference 3 1) (sourceB1865 + difference 1 3) sourceC1865) = raw26893 := by
      apply Matrix.ext; unfold tripleCharges sourceA1865 sourceB1865 sourceC1865 difference raw26893; decide +kernel
    rw [ha]
    exact (canonical26893 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1865 + difference 4 1) (sourceB1865 + difference 1 4) sourceC1865) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1100) := by
    have ha : (tripleCharges (sourceA1865 + difference 4 1) (sourceB1865 + difference 1 4) sourceC1865) = raw26894 := by
      apply Matrix.ext; unfold tripleCharges sourceA1865 sourceB1865 sourceC1865 difference raw26894; decide +kernel
    rw [ha]
    exact (canonical26894 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1865 + difference 5 1) (sourceB1865 + difference 1 5) sourceC1865) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1100) := by
    have ha : (tripleCharges (sourceA1865 + difference 5 1) (sourceB1865 + difference 1 5) sourceC1865) = raw26895 := by
      apply Matrix.ext; unfold tripleCharges sourceA1865 sourceB1865 sourceC1865 difference raw26895; decide +kernel
    rw [ha]
    exact (canonical26895 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1865 + sourceB1865) sourceC1865) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4087) := by
    have ha : (doubleCharges (sourceA1865 + sourceB1865) sourceC1865) = raw26891 := by
      apply Matrix.ext; unfold doubleCharges sourceA1865 sourceB1865 sourceC1865 raw26891; decide +kernel
    rw [ha]
    exact (canonical26891 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1865 sourceB1865 sourceC1865
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1865, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1867 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1867 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1867 + difference 0 0) (sourceB1867 + difference 0 0) sourceC1867) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1052) := by
    have ha : (tripleCharges (sourceA1867 + difference 0 0) (sourceB1867 + difference 0 0) sourceC1867) = raw26902 := by
      apply Matrix.ext; unfold tripleCharges sourceA1867 sourceB1867 sourceC1867 difference raw26902; decide +kernel
    rw [ha]
    exact (canonical26902 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1867 + difference 0 1) (sourceB1867 + difference 1 0) sourceC1867) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2127) := by
    have ha : (tripleCharges (sourceA1867 + difference 0 1) (sourceB1867 + difference 1 0) sourceC1867) = raw26903 := by
      apply Matrix.ext; unfold tripleCharges sourceA1867 sourceB1867 sourceC1867 difference raw26903; decide +kernel
    rw [ha]
    exact (canonical26903 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1867 + difference 0 2) (sourceB1867 + difference 2 0) sourceC1867) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2250) := by
    have ha : (tripleCharges (sourceA1867 + difference 0 2) (sourceB1867 + difference 2 0) sourceC1867) = raw26904 := by
      apply Matrix.ext; unfold tripleCharges sourceA1867 sourceB1867 sourceC1867 difference raw26904; decide +kernel
    rw [ha]
    exact (canonical26904 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1867 + difference 0 3) (sourceB1867 + difference 3 0) sourceC1867) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2250) := by
    have ha : (tripleCharges (sourceA1867 + difference 0 3) (sourceB1867 + difference 3 0) sourceC1867) = raw26905 := by
      apply Matrix.ext; unfold tripleCharges sourceA1867 sourceB1867 sourceC1867 difference raw26905; decide +kernel
    rw [ha]
    exact (canonical26905 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1867 + difference 0 4) (sourceB1867 + difference 4 0) sourceC1867) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2275) := by
    have ha : (tripleCharges (sourceA1867 + difference 0 4) (sourceB1867 + difference 4 0) sourceC1867) = raw26906 := by
      apply Matrix.ext; unfold tripleCharges sourceA1867 sourceB1867 sourceC1867 difference raw26906; decide +kernel
    rw [ha]
    exact (canonical26906 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1867 + difference 0 5) (sourceB1867 + difference 5 0) sourceC1867) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2214) := by
    have ha : (tripleCharges (sourceA1867 + difference 0 5) (sourceB1867 + difference 5 0) sourceC1867) = raw26907 := by
      apply Matrix.ext; unfold tripleCharges sourceA1867 sourceB1867 sourceC1867 difference raw26907; decide +kernel
    rw [ha]
    exact (canonical26907 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1867 + sourceB1867) sourceC1867) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4080) := by
    have ha : (doubleCharges (sourceA1867 + sourceB1867) sourceC1867) = raw26908 := by
      apply Matrix.ext; unfold doubleCharges sourceA1867 sourceB1867 sourceC1867 raw26908; decide +kernel
    rw [ha]
    exact (canonical26908 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1867 sourceB1867 sourceC1867
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1867, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1868 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1868 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1868 + difference 0 0) (sourceB1868 + difference 0 0) sourceC1868) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1032) := by
    have ha : (tripleCharges (sourceA1868 + difference 0 0) (sourceB1868 + difference 0 0) sourceC1868) = raw26909 := by
      apply Matrix.ext; unfold tripleCharges sourceA1868 sourceB1868 sourceC1868 difference raw26909; decide +kernel
    rw [ha]
    exact (canonical26909 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1868 + difference 0 1) (sourceB1868 + difference 1 0) sourceC1868) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2098) := by
    have ha : (tripleCharges (sourceA1868 + difference 0 1) (sourceB1868 + difference 1 0) sourceC1868) = raw26910 := by
      apply Matrix.ext; unfold tripleCharges sourceA1868 sourceB1868 sourceC1868 difference raw26910; decide +kernel
    rw [ha]
    exact (canonical26910 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1868 + difference 0 2) (sourceB1868 + difference 2 0) sourceC1868) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2250) := by
    have ha : (tripleCharges (sourceA1868 + difference 0 2) (sourceB1868 + difference 2 0) sourceC1868) = raw26911 := by
      apply Matrix.ext; unfold tripleCharges sourceA1868 sourceB1868 sourceC1868 difference raw26911; decide +kernel
    rw [ha]
    exact (canonical26911 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1868 + difference 0 3) (sourceB1868 + difference 3 0) sourceC1868) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2240) := by
    have ha : (tripleCharges (sourceA1868 + difference 0 3) (sourceB1868 + difference 3 0) sourceC1868) = raw26912 := by
      apply Matrix.ext; unfold tripleCharges sourceA1868 sourceB1868 sourceC1868 difference raw26912; decide +kernel
    rw [ha]
    exact (canonical26912 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1868 + difference 0 4) (sourceB1868 + difference 4 0) sourceC1868) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2260) := by
    have ha : (tripleCharges (sourceA1868 + difference 0 4) (sourceB1868 + difference 4 0) sourceC1868) = raw26913 := by
      apply Matrix.ext; unfold tripleCharges sourceA1868 sourceB1868 sourceC1868 difference raw26913; decide +kernel
    rw [ha]
    exact (canonical26913 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1868 + difference 0 5) (sourceB1868 + difference 5 0) sourceC1868) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2202) := by
    have ha : (tripleCharges (sourceA1868 + difference 0 5) (sourceB1868 + difference 5 0) sourceC1868) = raw26914 := by
      apply Matrix.ext; unfold tripleCharges sourceA1868 sourceB1868 sourceC1868 difference raw26914; decide +kernel
    rw [ha]
    exact (canonical26914 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1868 + sourceB1868) sourceC1868) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4080) := by
    have ha : (doubleCharges (sourceA1868 + sourceB1868) sourceC1868) = raw26915 := by
      apply Matrix.ext; unfold doubleCharges sourceA1868 sourceB1868 sourceC1868 raw26915; decide +kernel
    rw [ha]
    exact (canonical26915 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1868 sourceB1868 sourceC1868
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1868, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1869 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1869 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1869 + difference 0 0) (sourceB1869 + difference 0 0) sourceC1869) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1034) := by
    have ha : (tripleCharges (sourceA1869 + difference 0 0) (sourceB1869 + difference 0 0) sourceC1869) = raw24971 := by
      apply Matrix.ext; unfold tripleCharges sourceA1869 sourceB1869 sourceC1869 difference raw24971; decide +kernel
    rw [ha]
    exact (canonical24971 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1869 + difference 0 1) (sourceB1869 + difference 1 0) sourceC1869) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2100) := by
    have ha : (tripleCharges (sourceA1869 + difference 0 1) (sourceB1869 + difference 1 0) sourceC1869) = raw26916 := by
      apply Matrix.ext; unfold tripleCharges sourceA1869 sourceB1869 sourceC1869 difference raw26916; decide +kernel
    rw [ha]
    exact (canonical26916 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1869 + difference 0 2) (sourceB1869 + difference 2 0) sourceC1869) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2241) := by
    have ha : (tripleCharges (sourceA1869 + difference 0 2) (sourceB1869 + difference 2 0) sourceC1869) = raw24968 := by
      apply Matrix.ext; unfold tripleCharges sourceA1869 sourceB1869 sourceC1869 difference raw24968; decide +kernel
    rw [ha]
    exact (canonical24968 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1869 + difference 0 3) (sourceB1869 + difference 3 0) sourceC1869) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2241) := by
    have ha : (tripleCharges (sourceA1869 + difference 0 3) (sourceB1869 + difference 3 0) sourceC1869) = raw26917 := by
      apply Matrix.ext; unfold tripleCharges sourceA1869 sourceB1869 sourceC1869 difference raw26917; decide +kernel
    rw [ha]
    exact (canonical26917 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1869 + difference 0 4) (sourceB1869 + difference 4 0) sourceC1869) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2241) := by
    have ha : (tripleCharges (sourceA1869 + difference 0 4) (sourceB1869 + difference 4 0) sourceC1869) = raw26918 := by
      apply Matrix.ext; unfold tripleCharges sourceA1869 sourceB1869 sourceC1869 difference raw26918; decide +kernel
    rw [ha]
    exact (canonical26918 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1869 + difference 0 5) (sourceB1869 + difference 5 0) sourceC1869) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2204) := by
    have ha : (tripleCharges (sourceA1869 + difference 0 5) (sourceB1869 + difference 5 0) sourceC1869) = raw26919 := by
      apply Matrix.ext; unfold tripleCharges sourceA1869 sourceB1869 sourceC1869 difference raw26919; decide +kernel
    rw [ha]
    exact (canonical26919 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1869 + sourceB1869) sourceC1869) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4079) := by
    have ha : (doubleCharges (sourceA1869 + sourceB1869) sourceC1869) = raw24969 := by
      apply Matrix.ext; unfold doubleCharges sourceA1869 sourceB1869 sourceC1869 raw24969; decide +kernel
    rw [ha]
    exact (canonical24969 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1869 sourceB1869 sourceC1869
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1869, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1870 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1870 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1870 + difference 0 0) (sourceB1870 + difference 0 0) sourceC1870) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1644) := by
    have ha : (tripleCharges (sourceA1870 + difference 0 0) (sourceB1870 + difference 0 0) sourceC1870) = raw26920 := by
      apply Matrix.ext; unfold tripleCharges sourceA1870 sourceB1870 sourceC1870 difference raw26920; decide +kernel
    rw [ha]
    exact (canonical26920 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1870 + difference 1 0) (sourceB1870 + difference 0 1) sourceC1870) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 736) := by
    have ha : (tripleCharges (sourceA1870 + difference 1 0) (sourceB1870 + difference 0 1) sourceC1870) = raw26921 := by
      apply Matrix.ext; unfold tripleCharges sourceA1870 sourceB1870 sourceC1870 difference raw26921; decide +kernel
    rw [ha]
    exact (canonical26921 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1870 + difference 2 0) (sourceB1870 + difference 0 2) sourceC1870) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 732) := by
    have ha : (tripleCharges (sourceA1870 + difference 2 0) (sourceB1870 + difference 0 2) sourceC1870) = raw26922 := by
      apply Matrix.ext; unfold tripleCharges sourceA1870 sourceB1870 sourceC1870 difference raw26922; decide +kernel
    rw [ha]
    exact (canonical26922 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1870 + difference 3 0) (sourceB1870 + difference 0 3) sourceC1870) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 732) := by
    have ha : (tripleCharges (sourceA1870 + difference 3 0) (sourceB1870 + difference 0 3) sourceC1870) = raw26923 := by
      apply Matrix.ext; unfold tripleCharges sourceA1870 sourceB1870 sourceC1870 difference raw26923; decide +kernel
    rw [ha]
    exact (canonical26923 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1870 + difference 4 0) (sourceB1870 + difference 0 4) sourceC1870) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 732) := by
    have ha : (tripleCharges (sourceA1870 + difference 4 0) (sourceB1870 + difference 0 4) sourceC1870) = raw26924 := by
      apply Matrix.ext; unfold tripleCharges sourceA1870 sourceB1870 sourceC1870 difference raw26924; decide +kernel
    rw [ha]
    exact (canonical26924 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1870 + difference 5 0) (sourceB1870 + difference 0 5) sourceC1870) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 805) := by
    have ha : (tripleCharges (sourceA1870 + difference 5 0) (sourceB1870 + difference 0 5) sourceC1870) = raw26925 := by
      apply Matrix.ext; unfold tripleCharges sourceA1870 sourceB1870 sourceC1870 difference raw26925; decide +kernel
    rw [ha]
    exact (canonical26925 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1870 + sourceB1870) sourceC1870) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4068) := by
    have ha : (doubleCharges (sourceA1870 + sourceB1870) sourceC1870) = raw26370 := by
      apply Matrix.ext; unfold doubleCharges sourceA1870 sourceB1870 sourceC1870 raw26370; decide +kernel
    rw [ha]
    exact (canonical26370 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1870 sourceB1870 sourceC1870
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1870, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic98
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reindexCheck1569 : Integer.Sparse.reindex keyMap MixedData.row1569 = numericRow1569 := by decide +kernel

theorem numericCheck1569 (x : Master → ℝ) : Integer.Sparse.eval numericRow1569 x =
    (4320 : ℝ) * reducedSource1569 x := by
  norm_num [numericRow1569, reducedSource1569, Integer.Sparse.eval, Sparse.eval, nodeValue4456, nodeValue4495, nodeValue4497, nodeValue4599, nodeValue4601, nodeValue4616, nodeValue4618, nodeValue4622]
  ring

theorem reindexCheck1570 : Integer.Sparse.reindex keyMap MixedData.row1570 = numericRow1570 := by decide +kernel

theorem numericCheck1570 (x : Master → ℝ) : Integer.Sparse.eval numericRow1570 x =
    (1 : ℝ) * reducedSource1570 x := by
  norm_num [numericRow1570, reducedSource1570, Integer.Sparse.eval, Sparse.eval, nodeValue1228, nodeValue2503, nodeValue2703, nodeValue2718, nodeValue2728, nodeValue4090]

theorem reindexCheck1571 : Integer.Sparse.reindex keyMap MixedData.row1571 = numericRow1571 := by decide +kernel

theorem numericCheck1571 (x : Master → ℝ) : Integer.Sparse.eval numericRow1571 x =
    (4 : ℝ) * reducedSource1571 x := by
  norm_num [numericRow1571, reducedSource1571, Integer.Sparse.eval, Sparse.eval, nodeValue4149, nodeValue4150, nodeValue4169, nodeValue4544, nodeValue4550, nodeValue4589, nodeValue4590, nodeValue4599, nodeValue4606, nodeValue4618, nodeValue5100, nodeValue5257, nodeValue5273]
  ring

theorem reindexCheck1573 : Integer.Sparse.reindex keyMap MixedData.row1573 = numericRow1573 := by decide +kernel

theorem numericCheck1573 (x : Master → ℝ) : Integer.Sparse.eval numericRow1573 x =
    (1 : ℝ) * reducedSource1573 x := by
  norm_num [numericRow1573, reducedSource1573, Integer.Sparse.eval, Sparse.eval, nodeValue1501, nodeValue1502, nodeValue1504, nodeValue3263, nodeValue3269, nodeValue3288, nodeValue3289, nodeValue3290, nodeValue3299, nodeValue3304, nodeValue3469, nodeValue3532, nodeValue3546]

theorem reindexCheck1574 : Integer.Sparse.reindex keyMap MixedData.row1574 = numericRow1574 := by decide +kernel

theorem numericCheck1574 (x : Master → ℝ) : Integer.Sparse.eval numericRow1574 x =
    (1 : ℝ) * reducedSource1574 x := by
  norm_num [numericRow1574, reducedSource1574, Integer.Sparse.eval, Sparse.eval, nodeValue625, nodeValue629, nodeValue637, nodeValue1235, nodeValue4091]

theorem reindexCheck1576 : Integer.Sparse.reindex keyMap MixedData.row1576 = numericRow1576 := by decide +kernel

theorem numericCheck1576 (x : Master → ℝ) : Integer.Sparse.eval numericRow1576 x =
    (1440 : ℝ) * reducedSource1576 x := by
  norm_num [numericRow1576, reducedSource1576, Integer.Sparse.eval, Sparse.eval, nodeValue567, nodeValue571, nodeValue599, nodeValue1097, nodeValue1100, nodeValue1200, nodeValue1235, nodeValue1236, nodeValue1240, nodeValue1299, nodeValue2880, nodeValue3076, nodeValue3100]
  ring

theorem reindexCheck1577 : Integer.Sparse.reindex keyMap MixedData.row1577 = numericRow1577 := by decide +kernel

theorem numericCheck1577 (x : Master → ℝ) : Integer.Sparse.eval numericRow1577 x =
    (1 : ℝ) * reducedSource1577 x := by
  norm_num [numericRow1577, reducedSource1577, Integer.Sparse.eval, Sparse.eval, nodeValue1183, nodeValue2398, nodeValue2669, nodeValue2676, nodeValue2684, nodeValue4088]

theorem reindexCheck1578 : Integer.Sparse.reindex keyMap MixedData.row1578 = numericRow1578 := by decide +kernel

theorem numericCheck1578 (x : Master → ℝ) : Integer.Sparse.eval numericRow1578 x =
    (1 : ℝ) * reducedSource1578 x := by
  norm_num [numericRow1578, reducedSource1578, Integer.Sparse.eval, Sparse.eval, nodeValue1187, nodeValue2402, nodeValue2671, nodeValue4087]

theorem reindexCheck1579 : Integer.Sparse.reindex keyMap MixedData.row1579 = numericRow1579 := by decide +kernel

theorem numericCheck1579 (x : Master → ℝ) : Integer.Sparse.eval numericRow1579 x =
    (1 : ℝ) * reducedSource1579 x := by
  norm_num [numericRow1579, reducedSource1579, Integer.Sparse.eval, Sparse.eval, nodeValue1100, nodeValue1187, nodeValue2402, nodeValue4087]

theorem reindexCheck1580 : Integer.Sparse.reindex keyMap MixedData.row1580 = numericRow1580 := by decide +kernel

theorem numericCheck1580 (x : Master → ℝ) : Integer.Sparse.eval numericRow1580 x =
    (1 : ℝ) * reducedSource1580 x := by
  norm_num [numericRow1580, reducedSource1580, Integer.Sparse.eval, Sparse.eval, nodeValue1052, nodeValue2127, nodeValue2214, nodeValue2250, nodeValue2275, nodeValue4080]

theorem reindexCheck1581 : Integer.Sparse.reindex keyMap MixedData.row1581 = numericRow1581 := by decide +kernel

theorem numericCheck1581 (x : Master → ℝ) : Integer.Sparse.eval numericRow1581 x =
    (1 : ℝ) * reducedSource1581 x := by
  norm_num [numericRow1581, reducedSource1581, Integer.Sparse.eval, Sparse.eval, nodeValue1032, nodeValue2098, nodeValue2202, nodeValue2240, nodeValue2250, nodeValue2260, nodeValue4080]

theorem reindexCheck1582 : Integer.Sparse.reindex keyMap MixedData.row1582 = numericRow1582 := by decide +kernel

theorem numericCheck1582 (x : Master → ℝ) : Integer.Sparse.eval numericRow1582 x =
    (1 : ℝ) * reducedSource1582 x := by
  norm_num [numericRow1582, reducedSource1582, Integer.Sparse.eval, Sparse.eval, nodeValue1034, nodeValue2100, nodeValue2204, nodeValue2241, nodeValue4079]

theorem reindexCheck1583 : Integer.Sparse.reindex keyMap MixedData.row1583 = numericRow1583 := by decide +kernel

theorem numericCheck1583 (x : Master → ℝ) : Integer.Sparse.eval numericRow1583 x =
    (1 : ℝ) * reducedSource1583 x := by
  norm_num [numericRow1583, reducedSource1583, Integer.Sparse.eval, Sparse.eval, nodeValue732, nodeValue736, nodeValue805, nodeValue1644, nodeValue4068]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Rows98
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero1569 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1569 (mixedVector B) = 0 := by
  have h4456 : mixedVector B (Sum.inr 4456) = Sparse.eval nodeValue4456 (mixedVector B) := by
    change mixedMoment B node4456 node4456Labels = _
    exact sound4456 B hB hF
  have h4495 : mixedVector B (Sum.inr 4495) = Sparse.eval nodeValue4495 (mixedVector B) := by
    change mixedMoment B node4495 node4495Labels = _
    exact sound4495 B hB hF
  have h4497 : mixedVector B (Sum.inr 4497) = Sparse.eval nodeValue4497 (mixedVector B) := by
    change mixedMoment B node4497 node4497Labels = _
    exact sound4497 B hB hF
  have h4599 : mixedVector B (Sum.inr 4599) = Sparse.eval nodeValue4599 (mixedVector B) := by
    change mixedMoment B node4599 node4599Labels = _
    exact sound4599 B hB hF
  have h4601 : mixedVector B (Sum.inr 4601) = Sparse.eval nodeValue4601 (mixedVector B) := by
    change mixedMoment B node4601 node4601Labels = _
    exact sound4601 B hB hF
  have h4616 : mixedVector B (Sum.inr 4616) = Sparse.eval nodeValue4616 (mixedVector B) := by
    change mixedMoment B node4616 node4616Labels = _
    exact sound4616 B hB hF
  have h4618 : mixedVector B (Sum.inr 4618) = Sparse.eval nodeValue4618 (mixedVector B) := by
    change mixedMoment B node4618 node4618Labels = _
    exact sound4618 B hB hF
  have h4622 : mixedVector B (Sum.inr 4622) = Sparse.eval nodeValue4622 (mixedVector B) := by
    change mixedMoment B node4622 node4622Labels = _
    exact sound4622 B hB hF
  simpa only [sourceForm1854, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4456, h4495, h4497, h4599, h4601, h4616, h4618, h4622, reducedSource1569] using sourceEq1854 B hB

theorem rowSound1569 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1569 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1569, numericCheck1569, reducedZero1569 B hB hF, mul_zero]

theorem reducedZero1570 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1570 (mixedVector B) = 0 := by
  have h1228 : mixedVector B (Sum.inr 1228) = Sparse.eval nodeValue1228 (mixedVector B) := by
    change mixedMoment B node1228 node1228Labels = _
    exact sound1228 B hB hF
  have h2503 : mixedVector B (Sum.inr 2503) = Sparse.eval nodeValue2503 (mixedVector B) := by
    change mixedMoment B node2503 node2503Labels = _
    exact sound2503 B hB hF
  have h2703 : mixedVector B (Sum.inr 2703) = Sparse.eval nodeValue2703 (mixedVector B) := by
    change mixedMoment B node2703 node2703Labels = _
    exact sound2703 B hB hF
  have h2718 : mixedVector B (Sum.inr 2718) = Sparse.eval nodeValue2718 (mixedVector B) := by
    change mixedMoment B node2718 node2718Labels = _
    exact sound2718 B hB hF
  have h2728 : mixedVector B (Sum.inr 2728) = Sparse.eval nodeValue2728 (mixedVector B) := by
    change mixedMoment B node2728 node2728Labels = _
    exact sound2728 B hB hF
  have h4090 : mixedVector B (Sum.inr 4090) = Sparse.eval nodeValue4090 (mixedVector B) := by
    change mixedMoment B node4090 node4090Labels = _
    exact sound4090 B hB hF
  simpa only [sourceForm1855, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1228, h2503, h2703, h2718, h2728, h4090, reducedSource1570] using sourceEq1855 B hB

theorem rowSound1570 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1570 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1570, numericCheck1570, reducedZero1570 B hB hF, mul_zero]

theorem reducedZero1571 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1571 (mixedVector B) = 0 := by
  have h4149 : mixedVector B (Sum.inr 4149) = Sparse.eval nodeValue4149 (mixedVector B) := by
    change mixedMoment B node4149 node4149Labels = _
    exact sound4149 B hB hF
  have h4150 : mixedVector B (Sum.inr 4150) = Sparse.eval nodeValue4150 (mixedVector B) := by
    change mixedMoment B node4150 node4150Labels = _
    exact sound4150 B hB hF
  have h4169 : mixedVector B (Sum.inr 4169) = Sparse.eval nodeValue4169 (mixedVector B) := by
    change mixedMoment B node4169 node4169Labels = _
    exact sound4169 B hB hF
  have h4544 : mixedVector B (Sum.inr 4544) = Sparse.eval nodeValue4544 (mixedVector B) := by
    change mixedMoment B node4544 node4544Labels = _
    exact sound4544 B hB hF
  have h4550 : mixedVector B (Sum.inr 4550) = Sparse.eval nodeValue4550 (mixedVector B) := by
    change mixedMoment B node4550 node4550Labels = _
    exact sound4550 B hB hF
  have h4589 : mixedVector B (Sum.inr 4589) = Sparse.eval nodeValue4589 (mixedVector B) := by
    change mixedMoment B node4589 node4589Labels = _
    exact sound4589 B hB hF
  have h4590 : mixedVector B (Sum.inr 4590) = Sparse.eval nodeValue4590 (mixedVector B) := by
    change mixedMoment B node4590 node4590Labels = _
    exact sound4590 B hB hF
  have h4599 : mixedVector B (Sum.inr 4599) = Sparse.eval nodeValue4599 (mixedVector B) := by
    change mixedMoment B node4599 node4599Labels = _
    exact sound4599 B hB hF
  have h4606 : mixedVector B (Sum.inr 4606) = Sparse.eval nodeValue4606 (mixedVector B) := by
    change mixedMoment B node4606 node4606Labels = _
    exact sound4606 B hB hF
  have h4618 : mixedVector B (Sum.inr 4618) = Sparse.eval nodeValue4618 (mixedVector B) := by
    change mixedMoment B node4618 node4618Labels = _
    exact sound4618 B hB hF
  have h5100 : mixedVector B (Sum.inr 5100) = Sparse.eval nodeValue5100 (mixedVector B) := by
    change mixedMoment B node5100 node5100Labels = _
    exact sound5100 B hB hF
  have h5257 : mixedVector B (Sum.inr 5257) = Sparse.eval nodeValue5257 (mixedVector B) := by
    change mixedMoment B node5257 node5257Labels = _
    exact sound5257 B hB hF
  have h5273 : mixedVector B (Sum.inr 5273) = Sparse.eval nodeValue5273 (mixedVector B) := by
    change mixedMoment B node5273 node5273Labels = _
    exact sound5273 B hB hF
  simpa only [sourceForm1856, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4149, h4150, h4169, h4544, h4550, h4589, h4590, h4599, h4606, h4618, h5100, h5257, h5273, reducedSource1571] using sourceEq1856 B hB

theorem rowSound1571 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1571 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1571, numericCheck1571, reducedZero1571 B hB hF, mul_zero]

theorem reducedZero1573 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1573 (mixedVector B) = 0 := by
  have h1501 : mixedVector B (Sum.inr 1501) = Sparse.eval nodeValue1501 (mixedVector B) := by
    change mixedMoment B node1501 node1501Labels = _
    exact sound1501 B hB hF
  have h1502 : mixedVector B (Sum.inr 1502) = Sparse.eval nodeValue1502 (mixedVector B) := by
    change mixedMoment B node1502 node1502Labels = _
    exact sound1502 B hB hF
  have h1504 : mixedVector B (Sum.inr 1504) = Sparse.eval nodeValue1504 (mixedVector B) := by
    change mixedMoment B node1504 node1504Labels = _
    exact sound1504 B hB hF
  have h3263 : mixedVector B (Sum.inr 3263) = Sparse.eval nodeValue3263 (mixedVector B) := by
    change mixedMoment B node3263 node3263Labels = _
    exact sound3263 B hB hF
  have h3269 : mixedVector B (Sum.inr 3269) = Sparse.eval nodeValue3269 (mixedVector B) := by
    change mixedMoment B node3269 node3269Labels = _
    exact sound3269 B hB hF
  have h3288 : mixedVector B (Sum.inr 3288) = Sparse.eval nodeValue3288 (mixedVector B) := by
    change mixedMoment B node3288 node3288Labels = _
    exact sound3288 B hB hF
  have h3289 : mixedVector B (Sum.inr 3289) = Sparse.eval nodeValue3289 (mixedVector B) := by
    change mixedMoment B node3289 node3289Labels = _
    exact sound3289 B hB hF
  have h3290 : mixedVector B (Sum.inr 3290) = Sparse.eval nodeValue3290 (mixedVector B) := by
    change mixedMoment B node3290 node3290Labels = _
    exact sound3290 B hB hF
  have h3299 : mixedVector B (Sum.inr 3299) = Sparse.eval nodeValue3299 (mixedVector B) := by
    change mixedMoment B node3299 node3299Labels = _
    exact sound3299 B hB hF
  have h3304 : mixedVector B (Sum.inr 3304) = Sparse.eval nodeValue3304 (mixedVector B) := by
    change mixedMoment B node3304 node3304Labels = _
    exact sound3304 B hB hF
  have h3469 : mixedVector B (Sum.inr 3469) = Sparse.eval nodeValue3469 (mixedVector B) := by
    change mixedMoment B node3469 node3469Labels = _
    exact sound3469 B hB hF
  have h3532 : mixedVector B (Sum.inr 3532) = Sparse.eval nodeValue3532 (mixedVector B) := by
    change mixedMoment B node3532 node3532Labels = _
    exact sound3532 B hB hF
  have h3546 : mixedVector B (Sum.inr 3546) = Sparse.eval nodeValue3546 (mixedVector B) := by
    change mixedMoment B node3546 node3546Labels = _
    exact sound3546 B hB hF
  simpa only [sourceForm1858, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1501, h1502, h1504, h3263, h3269, h3288, h3289, h3290, h3299, h3304, h3469, h3532, h3546, reducedSource1573] using sourceEq1858 B hB

theorem rowSound1573 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1573 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1573, numericCheck1573, reducedZero1573 B hB hF, mul_zero]

theorem reducedZero1574 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1574 (mixedVector B) = 0 := by
  have h625 : mixedVector B (Sum.inr 625) = Sparse.eval nodeValue625 (mixedVector B) := by
    change mixedMoment B node625 node625Labels = _
    exact sound625 B hB hF
  have h629 : mixedVector B (Sum.inr 629) = Sparse.eval nodeValue629 (mixedVector B) := by
    change mixedMoment B node629 node629Labels = _
    exact sound629 B hB hF
  have h637 : mixedVector B (Sum.inr 637) = Sparse.eval nodeValue637 (mixedVector B) := by
    change mixedMoment B node637 node637Labels = _
    exact sound637 B hB hF
  have h1235 : mixedVector B (Sum.inr 1235) = Sparse.eval nodeValue1235 (mixedVector B) := by
    change mixedMoment B node1235 node1235Labels = _
    exact sound1235 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm1859, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h625, h629, h637, h1235, h4091, reducedSource1574] using sourceEq1859 B hB

theorem rowSound1574 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1574 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1574, numericCheck1574, reducedZero1574 B hB hF, mul_zero]

theorem reducedZero1576 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1576 (mixedVector B) = 0 := by
  have h567 : mixedVector B (Sum.inr 567) = Sparse.eval nodeValue567 (mixedVector B) := by
    change mixedMoment B node567 node567Labels = _
    exact sound567 B hB hF
  have h571 : mixedVector B (Sum.inr 571) = Sparse.eval nodeValue571 (mixedVector B) := by
    change mixedMoment B node571 node571Labels = _
    exact sound571 B hB hF
  have h599 : mixedVector B (Sum.inr 599) = Sparse.eval nodeValue599 (mixedVector B) := by
    change mixedMoment B node599 node599Labels = _
    exact sound599 B hB hF
  have h1097 : mixedVector B (Sum.inr 1097) = Sparse.eval nodeValue1097 (mixedVector B) := by
    change mixedMoment B node1097 node1097Labels = _
    exact sound1097 B hB hF
  have h1100 : mixedVector B (Sum.inr 1100) = Sparse.eval nodeValue1100 (mixedVector B) := by
    change mixedMoment B node1100 node1100Labels = _
    exact sound1100 B hB hF
  have h1200 : mixedVector B (Sum.inr 1200) = Sparse.eval nodeValue1200 (mixedVector B) := by
    change mixedMoment B node1200 node1200Labels = _
    exact sound1200 B hB hF
  have h1235 : mixedVector B (Sum.inr 1235) = Sparse.eval nodeValue1235 (mixedVector B) := by
    change mixedMoment B node1235 node1235Labels = _
    exact sound1235 B hB hF
  have h1236 : mixedVector B (Sum.inr 1236) = Sparse.eval nodeValue1236 (mixedVector B) := by
    change mixedMoment B node1236 node1236Labels = _
    exact sound1236 B hB hF
  have h1240 : mixedVector B (Sum.inr 1240) = Sparse.eval nodeValue1240 (mixedVector B) := by
    change mixedMoment B node1240 node1240Labels = _
    exact sound1240 B hB hF
  have h1299 : mixedVector B (Sum.inr 1299) = Sparse.eval nodeValue1299 (mixedVector B) := by
    change mixedMoment B node1299 node1299Labels = _
    exact sound1299_e B hB hF
  have h2880 : mixedVector B (Sum.inr 2880) = Sparse.eval nodeValue2880 (mixedVector B) := by
    change mixedMoment B node2880 node2880Labels = _
    exact sound2880 B hB hF
  have h3076 : mixedVector B (Sum.inr 3076) = Sparse.eval nodeValue3076 (mixedVector B) := by
    change mixedMoment B node3076 node3076Labels = _
    exact sound3076 B hB hF
  have h3100 : mixedVector B (Sum.inr 3100) = Sparse.eval nodeValue3100 (mixedVector B) := by
    change mixedMoment B node3100 node3100Labels = _
    exact sound3100_e B hB hF
  simpa only [sourceForm1861, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h567, h571, h599, h1097, h1100, h1200, h1235, h1236, h1240, h1299, h2880, h3076, h3100, reducedSource1576] using sourceEq1861 B hB

theorem rowSound1576 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1576 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1576, numericCheck1576, reducedZero1576 B hB hF, mul_zero]

theorem reducedZero1577 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1577 (mixedVector B) = 0 := by
  have h1183 : mixedVector B (Sum.inr 1183) = Sparse.eval nodeValue1183 (mixedVector B) := by
    change mixedMoment B node1183 node1183Labels = _
    exact sound1183 B hB hF
  have h2398 : mixedVector B (Sum.inr 2398) = Sparse.eval nodeValue2398 (mixedVector B) := by
    change mixedMoment B node2398 node2398Labels = _
    exact sound2398 B hB hF
  have h2669 : mixedVector B (Sum.inr 2669) = Sparse.eval nodeValue2669 (mixedVector B) := by
    change mixedMoment B node2669 node2669Labels = _
    exact sound2669 B hB hF
  have h2676 : mixedVector B (Sum.inr 2676) = Sparse.eval nodeValue2676 (mixedVector B) := by
    change mixedMoment B node2676 node2676Labels = _
    exact sound2676 B hB hF
  have h2684 : mixedVector B (Sum.inr 2684) = Sparse.eval nodeValue2684 (mixedVector B) := by
    change mixedMoment B node2684 node2684Labels = _
    exact sound2684 B hB hF
  have h4088 : mixedVector B (Sum.inr 4088) = Sparse.eval nodeValue4088 (mixedVector B) := by
    change mixedMoment B node4088 node4088Labels = _
    exact sound4088 B hB hF
  simpa only [sourceForm1863, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1183, h2398, h2669, h2676, h2684, h4088, reducedSource1577] using sourceEq1863 B hB

theorem rowSound1577 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1577 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1577, numericCheck1577, reducedZero1577 B hB hF, mul_zero]

theorem reducedZero1578 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1578 (mixedVector B) = 0 := by
  have h1187 : mixedVector B (Sum.inr 1187) = Sparse.eval nodeValue1187 (mixedVector B) := by
    change mixedMoment B node1187 node1187Labels = _
    exact sound1187 B hB hF
  have h2402 : mixedVector B (Sum.inr 2402) = Sparse.eval nodeValue2402 (mixedVector B) := by
    change mixedMoment B node2402 node2402Labels = _
    exact sound2402 B hB hF
  have h2671 : mixedVector B (Sum.inr 2671) = Sparse.eval nodeValue2671 (mixedVector B) := by
    change mixedMoment B node2671 node2671Labels = _
    exact sound2671 B hB hF
  have h4087 : mixedVector B (Sum.inr 4087) = Sparse.eval nodeValue4087 (mixedVector B) := by
    change mixedMoment B node4087 node4087Labels = _
    exact sound4087 B hB hF
  simpa only [sourceForm1864, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1187, h2402, h2671, h4087, reducedSource1578] using sourceEq1864 B hB

theorem rowSound1578 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1578 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1578, numericCheck1578, reducedZero1578 B hB hF, mul_zero]

theorem reducedZero1579 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1579 (mixedVector B) = 0 := by
  have h1100 : mixedVector B (Sum.inr 1100) = Sparse.eval nodeValue1100 (mixedVector B) := by
    change mixedMoment B node1100 node1100Labels = _
    exact sound1100 B hB hF
  have h1187 : mixedVector B (Sum.inr 1187) = Sparse.eval nodeValue1187 (mixedVector B) := by
    change mixedMoment B node1187 node1187Labels = _
    exact sound1187 B hB hF
  have h2402 : mixedVector B (Sum.inr 2402) = Sparse.eval nodeValue2402 (mixedVector B) := by
    change mixedMoment B node2402 node2402Labels = _
    exact sound2402 B hB hF
  have h4087 : mixedVector B (Sum.inr 4087) = Sparse.eval nodeValue4087 (mixedVector B) := by
    change mixedMoment B node4087 node4087Labels = _
    exact sound4087 B hB hF
  simpa only [sourceForm1865, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1100, h1187, h2402, h4087, reducedSource1579] using sourceEq1865 B hB

theorem rowSound1579 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1579 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1579, numericCheck1579, reducedZero1579 B hB hF, mul_zero]

theorem reducedZero1580 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1580 (mixedVector B) = 0 := by
  have h1052 : mixedVector B (Sum.inr 1052) = Sparse.eval nodeValue1052 (mixedVector B) := by
    change mixedMoment B node1052 node1052Labels = _
    exact sound1052 B hB hF
  have h2127 : mixedVector B (Sum.inr 2127) = Sparse.eval nodeValue2127 (mixedVector B) := by
    change mixedMoment B node2127 node2127Labels = _
    exact sound2127 B hB hF
  have h2214 : mixedVector B (Sum.inr 2214) = Sparse.eval nodeValue2214 (mixedVector B) := by
    change mixedMoment B node2214 node2214Labels = _
    exact sound2214 B hB hF
  have h2250 : mixedVector B (Sum.inr 2250) = Sparse.eval nodeValue2250 (mixedVector B) := by
    change mixedMoment B node2250 node2250Labels = _
    exact sound2250 B hB hF
  have h2275 : mixedVector B (Sum.inr 2275) = Sparse.eval nodeValue2275 (mixedVector B) := by
    change mixedMoment B node2275 node2275Labels = _
    exact sound2275 B hB hF
  have h4080 : mixedVector B (Sum.inr 4080) = Sparse.eval nodeValue4080 (mixedVector B) := by
    change mixedMoment B node4080 node4080Labels = _
    exact sound4080 B hB hF
  simpa only [sourceForm1867, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1052, h2127, h2214, h2250, h2275, h4080, reducedSource1580] using sourceEq1867 B hB

theorem rowSound1580 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1580 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1580, numericCheck1580, reducedZero1580 B hB hF, mul_zero]

theorem reducedZero1581 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1581 (mixedVector B) = 0 := by
  have h1032 : mixedVector B (Sum.inr 1032) = Sparse.eval nodeValue1032 (mixedVector B) := by
    change mixedMoment B node1032 node1032Labels = _
    exact sound1032 B hB hF
  have h2098 : mixedVector B (Sum.inr 2098) = Sparse.eval nodeValue2098 (mixedVector B) := by
    change mixedMoment B node2098 node2098Labels = _
    exact sound2098 B hB hF
  have h2202 : mixedVector B (Sum.inr 2202) = Sparse.eval nodeValue2202 (mixedVector B) := by
    change mixedMoment B node2202 node2202Labels = _
    exact sound2202 B hB hF
  have h2240 : mixedVector B (Sum.inr 2240) = Sparse.eval nodeValue2240 (mixedVector B) := by
    change mixedMoment B node2240 node2240Labels = _
    exact sound2240 B hB hF
  have h2250 : mixedVector B (Sum.inr 2250) = Sparse.eval nodeValue2250 (mixedVector B) := by
    change mixedMoment B node2250 node2250Labels = _
    exact sound2250 B hB hF
  have h2260 : mixedVector B (Sum.inr 2260) = Sparse.eval nodeValue2260 (mixedVector B) := by
    change mixedMoment B node2260 node2260Labels = _
    exact sound2260 B hB hF
  have h4080 : mixedVector B (Sum.inr 4080) = Sparse.eval nodeValue4080 (mixedVector B) := by
    change mixedMoment B node4080 node4080Labels = _
    exact sound4080 B hB hF
  simpa only [sourceForm1868, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1032, h2098, h2202, h2240, h2250, h2260, h4080, reducedSource1581] using sourceEq1868 B hB

theorem rowSound1581 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1581 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1581, numericCheck1581, reducedZero1581 B hB hF, mul_zero]

theorem reducedZero1582 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1582 (mixedVector B) = 0 := by
  have h1034 : mixedVector B (Sum.inr 1034) = Sparse.eval nodeValue1034 (mixedVector B) := by
    change mixedMoment B node1034 node1034Labels = _
    exact sound1034 B hB hF
  have h2100 : mixedVector B (Sum.inr 2100) = Sparse.eval nodeValue2100 (mixedVector B) := by
    change mixedMoment B node2100 node2100Labels = _
    exact sound2100 B hB hF
  have h2204 : mixedVector B (Sum.inr 2204) = Sparse.eval nodeValue2204 (mixedVector B) := by
    change mixedMoment B node2204 node2204Labels = _
    exact sound2204 B hB hF
  have h2241 : mixedVector B (Sum.inr 2241) = Sparse.eval nodeValue2241 (mixedVector B) := by
    change mixedMoment B node2241 node2241Labels = _
    exact sound2241 B hB hF
  have h4079 : mixedVector B (Sum.inr 4079) = Sparse.eval nodeValue4079 (mixedVector B) := by
    change mixedMoment B node4079 node4079Labels = _
    exact sound4079 B hB hF
  simpa only [sourceForm1869, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1034, h2100, h2204, h2241, h4079, reducedSource1582] using sourceEq1869 B hB

theorem rowSound1582 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1582 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1582, numericCheck1582, reducedZero1582 B hB hF, mul_zero]

theorem reducedZero1583 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1583 (mixedVector B) = 0 := by
  have h732 : mixedVector B (Sum.inr 732) = Sparse.eval nodeValue732 (mixedVector B) := by
    change mixedMoment B node732 node732Labels = _
    exact sound732 B hB hF
  have h736 : mixedVector B (Sum.inr 736) = Sparse.eval nodeValue736 (mixedVector B) := by
    change mixedMoment B node736 node736Labels = _
    exact sound736 B hB hF
  have h805 : mixedVector B (Sum.inr 805) = Sparse.eval nodeValue805 (mixedVector B) := by
    change mixedMoment B node805 node805Labels = _
    exact sound805 B hB hF
  have h1644 : mixedVector B (Sum.inr 1644) = Sparse.eval nodeValue1644 (mixedVector B) := by
    change mixedMoment B node1644 node1644Labels = _
    exact sound1644 B hB hF
  have h4068 : mixedVector B (Sum.inr 4068) = Sparse.eval nodeValue4068 (mixedVector B) := by
    change mixedMoment B node4068 node4068Labels = _
    exact sound4068 B hB hF
  simpa only [sourceForm1870, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h732, h736, h805, h1644, h4068, reducedSource1583] using sourceEq1870 B hB

theorem rowSound1583 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1583 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1583, numericCheck1583, reducedZero1583 B hB hF, mul_zero]

theorem sourceRowsAt1568 : MixedData.sourceRows (1568 : Fin 2425) =
    MixedData.row1568 := by decide +kernel

theorem sourceRowsAt1569 : MixedData.sourceRows (1569 : Fin 2425) =
    MixedData.row1569 := by decide +kernel

theorem sourceRowsAt1570 : MixedData.sourceRows (1570 : Fin 2425) =
    MixedData.row1570 := by decide +kernel

theorem sourceRowsAt1571 : MixedData.sourceRows (1571 : Fin 2425) =
    MixedData.row1571 := by decide +kernel

theorem sourceRowsAt1572 : MixedData.sourceRows (1572 : Fin 2425) =
    MixedData.row1572 := by decide +kernel

theorem sourceRowsAt1573 : MixedData.sourceRows (1573 : Fin 2425) =
    MixedData.row1573 := by decide +kernel

theorem sourceRowsAt1574 : MixedData.sourceRows (1574 : Fin 2425) =
    MixedData.row1574 := by decide +kernel

theorem sourceRowsAt1575 : MixedData.sourceRows (1575 : Fin 2425) =
    MixedData.row1575 := by decide +kernel

theorem sourceRowsAt1576 : MixedData.sourceRows (1576 : Fin 2425) =
    MixedData.row1576 := by decide +kernel

theorem sourceRowsAt1577 : MixedData.sourceRows (1577 : Fin 2425) =
    MixedData.row1577 := by decide +kernel

theorem sourceRowsAt1578 : MixedData.sourceRows (1578 : Fin 2425) =
    MixedData.row1578 := by decide +kernel

theorem sourceRowsAt1579 : MixedData.sourceRows (1579 : Fin 2425) =
    MixedData.row1579 := by decide +kernel

theorem sourceRowsAt1580 : MixedData.sourceRows (1580 : Fin 2425) =
    MixedData.row1580 := by decide +kernel

theorem sourceRowsAt1581 : MixedData.sourceRows (1581 : Fin 2425) =
    MixedData.row1581 := by decide +kernel

theorem sourceRowsAt1582 : MixedData.sourceRows (1582 : Fin 2425) =
    MixedData.row1582 := by decide +kernel

theorem sourceRowsAt1583 : MixedData.sourceRows (1583 : Fin 2425) =
    MixedData.row1583 := by decide +kernel

theorem chunkSound98_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) (k : Fin 2425)
    (hk : k.val / 16 = 98) :
    Integer.Sparse.eval (MixedData.sourceRows k) (numericVector B) = 0 := by
  have heq : k.val = 1568 ∨ k.val = 1569 ∨ k.val = 1570 ∨ k.val = 1571 ∨ k.val = 1572 ∨ k.val = 1573 ∨ k.val = 1574 ∨ k.val = 1575 ∨ k.val = 1576 ∨ k.val = 1577 ∨ k.val = 1578 ∨ k.val = 1579 ∨ k.val = 1580 ∨ k.val = 1581 ∨ k.val = 1582 ∨ k.val = 1583 := by omega
  rcases heq with h1568 | h1569 | h1570 | h1571 | h1572 | h1573 | h1574 | h1575 | h1576 | h1577 | h1578 | h1579 | h1580 | h1581 | h1582 | h1583
  · have he : k = (1568 : Fin 2425) := Fin.ext h1568
    subst k
    rw [sourceRowsAt1568]
    exact rowSound1568_e B hB hF
  · have he : k = (1569 : Fin 2425) := Fin.ext h1569
    subst k
    rw [sourceRowsAt1569]
    exact rowSound1569 B hB hF
  · have he : k = (1570 : Fin 2425) := Fin.ext h1570
    subst k
    rw [sourceRowsAt1570]
    exact rowSound1570 B hB hF
  · have he : k = (1571 : Fin 2425) := Fin.ext h1571
    subst k
    rw [sourceRowsAt1571]
    exact rowSound1571 B hB hF
  · have he : k = (1572 : Fin 2425) := Fin.ext h1572
    subst k
    rw [sourceRowsAt1572]
    exact rowSound1572_e B hB hF
  · have he : k = (1573 : Fin 2425) := Fin.ext h1573
    subst k
    rw [sourceRowsAt1573]
    exact rowSound1573 B hB hF
  · have he : k = (1574 : Fin 2425) := Fin.ext h1574
    subst k
    rw [sourceRowsAt1574]
    exact rowSound1574 B hB hF
  · have he : k = (1575 : Fin 2425) := Fin.ext h1575
    subst k
    rw [sourceRowsAt1575]
    exact rowSound1575_e B hB hF
  · have he : k = (1576 : Fin 2425) := Fin.ext h1576
    subst k
    rw [sourceRowsAt1576]
    exact rowSound1576 B hB hF
  · have he : k = (1577 : Fin 2425) := Fin.ext h1577
    subst k
    rw [sourceRowsAt1577]
    exact rowSound1577 B hB hF
  · have he : k = (1578 : Fin 2425) := Fin.ext h1578
    subst k
    rw [sourceRowsAt1578]
    exact rowSound1578 B hB hF
  · have he : k = (1579 : Fin 2425) := Fin.ext h1579
    subst k
    rw [sourceRowsAt1579]
    exact rowSound1579 B hB hF
  · have he : k = (1580 : Fin 2425) := Fin.ext h1580
    subst k
    rw [sourceRowsAt1580]
    exact rowSound1580 B hB hF
  · have he : k = (1581 : Fin 2425) := Fin.ext h1581
    subst k
    rw [sourceRowsAt1581]
    exact rowSound1581 B hB hF
  · have he : k = (1582 : Fin 2425) := Fin.ext h1582
    subst k
    rw [sourceRowsAt1582]
    exact rowSound1582 B hB hF
  · have he : k = (1583 : Fin 2425) := Fin.ext h1583
    subst k
    rw [sourceRowsAt1583]
    exact rowSound1583 B hB hF

end MUB6.Certificate.MixedSourceBridge

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedSourceBridge.chunkSound98_e_oai := @OAI.MUB6.Certificate.MixedSourceBridge.chunkSound98_e_oai
