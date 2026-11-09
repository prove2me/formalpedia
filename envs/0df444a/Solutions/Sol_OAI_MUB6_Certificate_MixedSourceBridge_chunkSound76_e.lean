-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedSourceBridge.chunkSound76_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T04:34:15.869048+00:00
-- url     : https://prove2.me/submissions/a150df52-9bb5-476d-a2dd-aede5c92cdda

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E077
import Definitions.Def_OAIQ106E086
import Definitions.Def_OAIQ106E088
import Definitions.Def_OAIQ106E089
import Definitions.Def_OAIQ106E096
import Definitions.Def_OAIQ106E188
import Definitions.Def_OAIQ106E189
import Definitions.Def_OAIQ106E098
import Definitions.Def_OAIQ106E116
import Definitions.Def_OAIQ106E118
import Definitions.Def_OAIQ106E119
import Definitions.Def_OAIQ106E120
import Definitions.Def_OAIQ106E124
import Definitions.Def_OAIQ106E140
import Definitions.Def_OAIQ106E147
import Definitions.Def_OAIQ106E170
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound1231_e

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

theorem mixedMoment_zero_first_factor {p n l : ℕ} (B : Fin 7 → Basis)
    (A : Matrix (Fin p) (Fin (n + 1)) ℤ) (label : Fin (n + 1) → Fin l)
    (hA : ∀ i, A i 0 = 0) :
    mixedMoment B A label = mixedMoment B (fun i j => A i j.succ) (fun j => label j.succ) := by
  apply average_congr
  intro r
  apply average_congr
  intro ρ
  apply average_congr
  intro τ
  unfold mixedIntegrand
  rw [Fin.prod_univ_succ]
  have hz : (fun i => A i 0) = 0 := funext hA
  rw [hz, rowFourier_zero, one_mul]

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

theorem delete_zero_factor {p n l : ℕ} (B : Fin 7 → Basis)
    (A : Matrix (Fin p) (Fin (n + 1)) ℤ) (label : Fin (n + 1) → Fin l)
    (σ : Equiv.Perm (Fin (n + 1))) (hz : ∀ i, A i (σ 0) = 0) :
    mixedMoment B A label =
      mixedMoment B (fun i j => A i (σ j.succ)) (fun j => label (σ j.succ)) := by
  rw [← mixedMoment_factor_permutation B A label σ]
  exact mixedMoment_zero_first_factor B _ _ hz

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

theorem canonical1284 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1284 raw1284Labels = mixedMoment B node4490 node4490Labels := by
  calc
    mixedMoment B raw1284 raw1284Labels = mixedMoment B raw1284step0 raw1284step0Labels := by
      have ha : raw1284step0 = (fun i j => raw1284 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1284step0 raw1284; decide +kernel
      have hl : raw1284step0Labels = raw1284Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1284 raw1284Labels permutation8 permutation4
    mixedMoment B raw1284step0 raw1284step0Labels = mixedMoment B raw1284step1 raw1284step1Labels := by
      have ha : raw1284step1 = raw1284step0 := by apply Matrix.ext; unfold raw1284step1 raw1284step0; decide +kernel
      have hl : raw1284step0Labels = labelEmbedding7 ∘ raw1284step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1284step0 raw1284step0Labels raw1284step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4490 node4490Labels := by rfl

theorem canonical1285 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1285 raw1285Labels = mixedMoment B node1074 node1074Labels := by
  calc
    mixedMoment B raw1285 raw1285Labels = mixedMoment B raw1285step0 raw1285step0Labels := by
      have ha : raw1285step0 = (fun i j => raw1285 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1285step0 raw1285; decide +kernel
      have hl : raw1285step0Labels = raw1285Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1285 raw1285Labels permutation8 permutation4
    _ = mixedMoment B node1074 node1074Labels := by rfl

theorem canonical1286 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1286 raw1286Labels = mixedMoment B node1650 node1650Labels := by
  calc
    mixedMoment B raw1286 raw1286Labels = mixedMoment B raw1286step0 raw1286step0Labels := by
      have ha : raw1286step0 = (fun i j => raw1286 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1286step0 raw1286; decide +kernel
      have hl : raw1286step0Labels = raw1286Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1286 raw1286Labels permutation8 permutation6
    mixedMoment B raw1286step0 raw1286step0Labels = mixedMoment B raw1286step1 raw1286step1Labels := by
      have ha : raw1286step1 = -raw1286step0 := by apply Matrix.ext; change ∀ i j, raw1286step1 i j = -(raw1286step0 i j); unfold raw1286step1 raw1286step0; decide +kernel
      have hl : raw1286step1Labels = raw1286step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1286step1 raw1286step1Labels = mixedMoment B raw1286step2 raw1286step2Labels := by
      have ha : raw1286step2 = raw1286step1 := by apply Matrix.ext; unfold raw1286step2 raw1286step1; decide +kernel
      have hl : raw1286step1Labels = labelEmbedding1 ∘ raw1286step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1286step1 raw1286step1Labels raw1286step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1650 node1650Labels := by rfl

theorem canonical1296 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1296 raw1296Labels = mixedMoment B node4496 node4496Labels := by
  calc
    mixedMoment B raw1296 raw1296Labels = mixedMoment B raw1296step0 raw1296step0Labels := by
      have ha : raw1296step0 = (fun i j => raw1296 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1296step0 raw1296; decide +kernel
      have hl : raw1296step0Labels = raw1296Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1296 raw1296Labels permutation8 permutation4
    mixedMoment B raw1296step0 raw1296step0Labels = mixedMoment B raw1296step1 raw1296step1Labels := by
      have ha : raw1296step1 = raw1296step0 := by apply Matrix.ext; unfold raw1296step1 raw1296step0; decide +kernel
      have hl : raw1296step0Labels = labelEmbedding7 ∘ raw1296step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1296step0 raw1296step0Labels raw1296step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4496 node4496Labels := by rfl

theorem canonical1297 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1297 raw1297Labels = mixedMoment B node1080 node1080Labels := by
  calc
    mixedMoment B raw1297 raw1297Labels = mixedMoment B raw1297step0 raw1297step0Labels := by
      have ha : raw1297step0 = (fun i j => raw1297 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1297step0 raw1297; decide +kernel
      have hl : raw1297step0Labels = raw1297Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1297 raw1297Labels permutation8 permutation4
    _ = mixedMoment B node1080 node1080Labels := by rfl

theorem canonical1298 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1298 raw1298Labels = mixedMoment B node1710 node1710Labels := by
  calc
    mixedMoment B raw1298 raw1298Labels = mixedMoment B raw1298step0 raw1298step0Labels := by
      have ha : raw1298step0 = (fun i j => raw1298 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1298step0 raw1298; decide +kernel
      have hl : raw1298step0Labels = raw1298Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1298 raw1298Labels permutation8 permutation6
    mixedMoment B raw1298step0 raw1298step0Labels = mixedMoment B raw1298step1 raw1298step1Labels := by
      have ha : raw1298step1 = -raw1298step0 := by apply Matrix.ext; change ∀ i j, raw1298step1 i j = -(raw1298step0 i j); unfold raw1298step1 raw1298step0; decide +kernel
      have hl : raw1298step1Labels = raw1298step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1298step1 raw1298step1Labels = mixedMoment B raw1298step2 raw1298step2Labels := by
      have ha : raw1298step2 = raw1298step1 := by apply Matrix.ext; unfold raw1298step2 raw1298step1; decide +kernel
      have hl : raw1298step1Labels = labelEmbedding1 ∘ raw1298step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1298step1 raw1298step1Labels raw1298step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1710 node1710Labels := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical168
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

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

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical169
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical21632 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21632 raw21632Labels = mixedMoment B node698 node698Labels := by
  calc
    mixedMoment B raw21632 raw21632Labels = mixedMoment B raw21632step0 raw21632step0Labels := by
      have ha : raw21632step0 = (fun i j => raw21632 (permutation212 i) (permutation4 j)) := by apply Matrix.ext; unfold raw21632step0 raw21632; decide +kernel
      have hl : raw21632step0Labels = raw21632Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21632 raw21632Labels permutation212 permutation4
    mixedMoment B raw21632step0 raw21632step0Labels = mixedMoment B raw21632step1 raw21632step1Labels := by
      have ha : raw21632step1 = -raw21632step0 := by apply Matrix.ext; change ∀ i j, raw21632step1 i j = -(raw21632step0 i j); unfold raw21632step1 raw21632step0; decide +kernel
      have hl : raw21632step1Labels = raw21632step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node698 node698Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical172
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical22065 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22065 raw22065Labels = mixedMoment B node1698 node1698Labels := by
  calc
    _ = mixedMoment B node1698 node1698Labels := by rfl

theorem canonical22066 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22066 raw22066Labels = mixedMoment B node783 node783Labels := by
  calc
    mixedMoment B raw22066 raw22066Labels = mixedMoment B raw22066step0 raw22066step0Labels := by
      have ha : raw22066step0 = (fun i j => raw22066 (permutation184 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22066step0 raw22066; decide +kernel
      have hl : raw22066step0Labels = raw22066Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22066 raw22066Labels permutation184 permutation2
    _ = mixedMoment B node783 node783Labels := by rfl

theorem canonical22067 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22067 raw22067Labels = mixedMoment B node783 node783Labels := by
  calc
    mixedMoment B raw22067 raw22067Labels = mixedMoment B raw22067step0 raw22067step0Labels := by
      have ha : raw22067step0 = (fun i j => raw22067 (permutation160 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22067step0 raw22067; decide +kernel
      have hl : raw22067step0Labels = raw22067Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22067 raw22067Labels permutation160 permutation2
    _ = mixedMoment B node783 node783Labels := by rfl

theorem canonical22068 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22068 raw22068Labels = mixedMoment B node783 node783Labels := by
  calc
    mixedMoment B raw22068 raw22068Labels = mixedMoment B raw22068step0 raw22068step0Labels := by
      have ha : raw22068step0 = (fun i j => raw22068 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22068step0 raw22068; decide +kernel
      have hl : raw22068step0Labels = raw22068Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22068 raw22068Labels permutation154 permutation2
    _ = mixedMoment B node783 node783Labels := by rfl

theorem canonical22069 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22069 raw22069Labels = mixedMoment B node778 node778Labels := by
  calc
    _ = mixedMoment B node778 node778Labels := by rfl

theorem canonical22070 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22070 raw22070Labels = mixedMoment B node776 node776Labels := by
  calc
    _ = mixedMoment B node776 node776Labels := by rfl

theorem canonical22071 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22071 raw22071Labels = mixedMoment B node4068 node4068Labels := by
  calc
    mixedMoment B raw22071 raw22071Labels = mixedMoment B raw22071step0 raw22071step0Labels := by
      have hz : ∀ j, raw22071 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw22071step0 = (fun i j => raw22071 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw22071step0 raw22071; decide +kernel
      have hl : raw22071step0Labels = raw22071Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22071 raw22071Labels permutation520 hz
    _ = mixedMoment B node4068 node4068Labels := by rfl

theorem canonical22079 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22079 raw22079Labels = mixedMoment B node787 node787Labels := by
  calc
    mixedMoment B raw22079 raw22079Labels = mixedMoment B raw22079step0 raw22079step0Labels := by
      have hz : ∀ j, raw22079 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22079step0 = (fun i j => raw22079 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22079step0 raw22079; decide +kernel
      have hl : raw22079step0Labels = raw22079Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22079 raw22079Labels permutation434 hz
    _ = mixedMoment B node787 node787Labels := by rfl

theorem canonical22080 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22080 raw22080Labels = mixedMoment B node1639 node1639Labels := by
  calc
    mixedMoment B raw22080 raw22080Labels = mixedMoment B raw22080step0 raw22080step0Labels := by
      have hz : ∀ j, raw22080 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22080step0 = (fun i j => raw22080 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22080step0 raw22080; decide +kernel
      have hl : raw22080step0Labels = raw22080Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22080 raw22080Labels permutation434 hz
    _ = mixedMoment B node1639 node1639Labels := by rfl

theorem canonical22081 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22081 raw22081Labels = mixedMoment B node1639 node1639Labels := by
  calc
    mixedMoment B raw22081 raw22081Labels = mixedMoment B raw22081step0 raw22081step0Labels := by
      have hz : ∀ j, raw22081 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22081step0 = (fun i j => raw22081 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22081step0 raw22081; decide +kernel
      have hl : raw22081step0Labels = raw22081Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22081 raw22081Labels permutation434 hz
    mixedMoment B raw22081step0 raw22081step0Labels = mixedMoment B raw22081step1 raw22081step1Labels := by
      have ha : raw22081step1 = (fun i j => raw22081step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22081step1 raw22081step0; decide +kernel
      have hl : raw22081step1Labels = raw22081step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22081step0 raw22081step0Labels permutation38 permutation2
    _ = mixedMoment B node1639 node1639Labels := by rfl

theorem canonical22082 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22082 raw22082Labels = mixedMoment B node1593 node1593Labels := by
  calc
    mixedMoment B raw22082 raw22082Labels = mixedMoment B raw22082step0 raw22082step0Labels := by
      have ha : raw22082step0 = (fun i j => raw22082 (permutation200 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22082step0 raw22082; decide +kernel
      have hl : raw22082step0Labels = raw22082Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22082 raw22082Labels permutation200 permutation2
    _ = mixedMoment B node1593 node1593Labels := by rfl

theorem canonical22083 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22083 raw22083Labels = mixedMoment B node1700 node1700Labels := by
  calc
    mixedMoment B raw22083 raw22083Labels = mixedMoment B raw22083step0 raw22083step0Labels := by
      have hz : ∀ j, raw22083 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22083step0 = (fun i j => raw22083 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22083step0 raw22083; decide +kernel
      have hl : raw22083step0Labels = raw22083Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22083 raw22083Labels permutation434 hz
    _ = mixedMoment B node1700 node1700Labels := by rfl

theorem canonical22084 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22084 raw22084Labels = mixedMoment B node1708 node1708Labels := by
  calc
    mixedMoment B raw22084 raw22084Labels = mixedMoment B raw22084step0 raw22084step0Labels := by
      have hz : ∀ j, raw22084 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22084step0 = (fun i j => raw22084 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22084step0 raw22084; decide +kernel
      have hl : raw22084step0Labels = raw22084Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22084 raw22084Labels permutation434 hz
    _ = mixedMoment B node1708 node1708Labels := by rfl

theorem canonical22085 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22085 raw22085Labels = mixedMoment B node4068 node4068Labels := by
  calc
    mixedMoment B raw22085 raw22085Labels = mixedMoment B raw22085step0 raw22085step0Labels := by
      have hz : ∀ j, raw22085 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22085step0 = (fun i j => raw22085 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22085step0 raw22085; decide +kernel
      have hl : raw22085step0Labels = raw22085Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22085 raw22085Labels permutation434 hz
    _ = mixedMoment B node4068 node4068Labels := by rfl

theorem canonical22086 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22086 raw22086Labels = mixedMoment B node542 node542Labels := by
  calc
    mixedMoment B raw22086 raw22086Labels = mixedMoment B raw22086step0 raw22086step0Labels := by
      have hz : ∀ j, raw22086 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22086step0 = (fun i j => raw22086 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22086step0 raw22086; decide +kernel
      have hl : raw22086step0Labels = raw22086Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22086 raw22086Labels permutation434 hz
    mixedMoment B raw22086step0 raw22086step0Labels = mixedMoment B raw22086step1 raw22086step1Labels := by
      have ha : raw22086step1 = (fun i j => raw22086step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22086step1 raw22086step0; decide +kernel
      have hl : raw22086step1Labels = raw22086step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22086step0 raw22086step0Labels permutation38 permutation2
    _ = mixedMoment B node542 node542Labels := by rfl

theorem canonical22087 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22087 raw22087Labels = mixedMoment B node737 node737Labels := by
  calc
    mixedMoment B raw22087 raw22087Labels = mixedMoment B raw22087step0 raw22087step0Labels := by
      have hz : ∀ j, raw22087 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22087step0 = (fun i j => raw22087 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22087step0 raw22087; decide +kernel
      have hl : raw22087step0Labels = raw22087Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22087 raw22087Labels permutation434 hz
    mixedMoment B raw22087step0 raw22087step0Labels = mixedMoment B raw22087step1 raw22087step1Labels := by
      have ha : raw22087step1 = (fun i j => raw22087step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22087step1 raw22087step0; decide +kernel
      have hl : raw22087step1Labels = raw22087step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22087step0 raw22087step0Labels permutation38 permutation2
    _ = mixedMoment B node737 node737Labels := by rfl

theorem canonical22088 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22088 raw22088Labels = mixedMoment B node702 node702Labels := by
  calc
    mixedMoment B raw22088 raw22088Labels = mixedMoment B raw22088step0 raw22088step0Labels := by
      have ha : raw22088step0 = (fun i j => raw22088 (permutation206 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22088step0 raw22088; decide +kernel
      have hl : raw22088step0Labels = raw22088Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22088 raw22088Labels permutation206 permutation2
    _ = mixedMoment B node702 node702Labels := by rfl

theorem canonical22089 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22089 raw22089Labels = mixedMoment B node787 node787Labels := by
  calc
    mixedMoment B raw22089 raw22089Labels = mixedMoment B raw22089step0 raw22089step0Labels := by
      have hz : ∀ j, raw22089 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22089step0 = (fun i j => raw22089 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22089step0 raw22089; decide +kernel
      have hl : raw22089step0Labels = raw22089Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22089 raw22089Labels permutation434 hz
    mixedMoment B raw22089step0 raw22089step0Labels = mixedMoment B raw22089step1 raw22089step1Labels := by
      have ha : raw22089step1 = (fun i j => raw22089step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22089step1 raw22089step0; decide +kernel
      have hl : raw22089step1Labels = raw22089step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22089step0 raw22089step0Labels permutation40 permutation2
    _ = mixedMoment B node787 node787Labels := by rfl

theorem canonical22090 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22090 raw22090Labels = mixedMoment B node810 node810Labels := by
  calc
    mixedMoment B raw22090 raw22090Labels = mixedMoment B raw22090step0 raw22090step0Labels := by
      have hz : ∀ j, raw22090 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22090step0 = (fun i j => raw22090 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22090step0 raw22090; decide +kernel
      have hl : raw22090step0Labels = raw22090Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22090 raw22090Labels permutation434 hz
    mixedMoment B raw22090step0 raw22090step0Labels = mixedMoment B raw22090step1 raw22090step1Labels := by
      have ha : raw22090step1 = (fun i j => raw22090step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22090step1 raw22090step0; decide +kernel
      have hl : raw22090step1Labels = raw22090step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22090step0 raw22090step0Labels permutation38 permutation2
    _ = mixedMoment B node810 node810Labels := by rfl

theorem canonical22091 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22091 raw22091Labels = mixedMoment B node810 node810Labels := by
  calc
    mixedMoment B raw22091 raw22091Labels = mixedMoment B raw22091step0 raw22091step0Labels := by
      have hz : ∀ j, raw22091 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22091step0 = (fun i j => raw22091 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22091step0 raw22091; decide +kernel
      have hl : raw22091step0Labels = raw22091Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22091 raw22091Labels permutation434 hz
    _ = mixedMoment B node810 node810Labels := by rfl

theorem canonical22092 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22092 raw22092Labels = mixedMoment B node783 node783Labels := by
  calc
    _ = mixedMoment B node783 node783Labels := by rfl

theorem canonical22093 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22093 raw22093Labels = mixedMoment B node790 node790Labels := by
  calc
    mixedMoment B raw22093 raw22093Labels = mixedMoment B raw22093step0 raw22093step0Labels := by
      have hz : ∀ j, raw22093 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22093step0 = (fun i j => raw22093 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22093step0 raw22093; decide +kernel
      have hl : raw22093step0Labels = raw22093Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22093 raw22093Labels permutation434 hz
    _ = mixedMoment B node790 node790Labels := by rfl

theorem canonical22096 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22096 raw22096Labels = mixedMoment B node804 node804Labels := by
  calc
    mixedMoment B raw22096 raw22096Labels = mixedMoment B raw22096step0 raw22096step0Labels := by
      have hz : ∀ j, raw22096 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22096step0 = (fun i j => raw22096 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22096step0 raw22096; decide +kernel
      have hl : raw22096step0Labels = raw22096Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22096 raw22096Labels permutation434 hz
    mixedMoment B raw22096step0 raw22096step0Labels = mixedMoment B raw22096step1 raw22096step1Labels := by
      have ha : raw22096step1 = (fun i j => raw22096step0 (permutation44 i) (permutation4 j)) := by apply Matrix.ext; unfold raw22096step1 raw22096step0; decide +kernel
      have hl : raw22096step1Labels = raw22096step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22096step0 raw22096step0Labels permutation44 permutation4
    mixedMoment B raw22096step1 raw22096step1Labels = mixedMoment B raw22096step2 raw22096step2Labels := by
      have ha : raw22096step2 = -raw22096step1 := by apply Matrix.ext; change ∀ i j, raw22096step2 i j = -(raw22096step1 i j); unfold raw22096step2 raw22096step1; decide +kernel
      have hl : raw22096step2Labels = raw22096step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node804 node804Labels := by rfl

theorem canonical22097 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22097 raw22097Labels = mixedMoment B node785 node785Labels := by
  calc
    mixedMoment B raw22097 raw22097Labels = mixedMoment B raw22097step0 raw22097step0Labels := by
      have hz : ∀ j, raw22097 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22097step0 = (fun i j => raw22097 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22097step0 raw22097; decide +kernel
      have hl : raw22097step0Labels = raw22097Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22097 raw22097Labels permutation434 hz
    _ = mixedMoment B node785 node785Labels := by rfl

theorem canonical22098 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22098 raw22098Labels = mixedMoment B node1637 node1637Labels := by
  calc
    mixedMoment B raw22098 raw22098Labels = mixedMoment B raw22098step0 raw22098step0Labels := by
      have hz : ∀ j, raw22098 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22098step0 = (fun i j => raw22098 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22098step0 raw22098; decide +kernel
      have hl : raw22098step0Labels = raw22098Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22098 raw22098Labels permutation434 hz
    _ = mixedMoment B node1637 node1637Labels := by rfl

theorem canonical22099 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22099 raw22099Labels = mixedMoment B node1637 node1637Labels := by
  calc
    mixedMoment B raw22099 raw22099Labels = mixedMoment B raw22099step0 raw22099step0Labels := by
      have hz : ∀ j, raw22099 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22099step0 = (fun i j => raw22099 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22099step0 raw22099; decide +kernel
      have hl : raw22099step0Labels = raw22099Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22099 raw22099Labels permutation434 hz
    mixedMoment B raw22099step0 raw22099step0Labels = mixedMoment B raw22099step1 raw22099step1Labels := by
      have ha : raw22099step1 = (fun i j => raw22099step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22099step1 raw22099step0; decide +kernel
      have hl : raw22099step1Labels = raw22099step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22099step0 raw22099step0Labels permutation38 permutation2
    _ = mixedMoment B node1637 node1637Labels := by rfl

theorem canonical22100 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22100 raw22100Labels = mixedMoment B node1592 node1592Labels := by
  calc
    mixedMoment B raw22100 raw22100Labels = mixedMoment B raw22100step0 raw22100step0Labels := by
      have ha : raw22100step0 = (fun i j => raw22100 (permutation200 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22100step0 raw22100; decide +kernel
      have hl : raw22100step0Labels = raw22100Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22100 raw22100Labels permutation200 permutation2
    _ = mixedMoment B node1592 node1592Labels := by rfl

theorem canonical22101 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22101 raw22101Labels = mixedMoment B node1710 node1710Labels := by
  calc
    mixedMoment B raw22101 raw22101Labels = mixedMoment B raw22101step0 raw22101step0Labels := by
      have hz : ∀ j, raw22101 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw22101step0 = (fun i j => raw22101 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw22101step0 raw22101; decide +kernel
      have hl : raw22101step0Labels = raw22101Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22101 raw22101Labels permutation520 hz
    mixedMoment B raw22101step0 raw22101step0Labels = mixedMoment B raw22101step1 raw22101step1Labels := by
      have hz : ∀ j, raw22101step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw22101step1 = (fun i j => raw22101step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw22101step1 raw22101step0; decide +kernel
      have hl : raw22101step1Labels = raw22101step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22101step0 raw22101step0Labels permutation104 hz
    _ = mixedMoment B node1710 node1710Labels := by rfl

theorem canonical22102 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22102 raw22102Labels = mixedMoment B node1707 node1707Labels := by
  calc
    mixedMoment B raw22102 raw22102Labels = mixedMoment B raw22102step0 raw22102step0Labels := by
      have hz : ∀ j, raw22102 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22102step0 = (fun i j => raw22102 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22102step0 raw22102; decide +kernel
      have hl : raw22102step0Labels = raw22102Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22102 raw22102Labels permutation434 hz
    _ = mixedMoment B node1707 node1707Labels := by rfl

theorem canonical22103 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22103 raw22103Labels = mixedMoment B node4069 node4069Labels := by
  calc
    mixedMoment B raw22103 raw22103Labels = mixedMoment B raw22103step0 raw22103step0Labels := by
      have hz : ∀ j, raw22103 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw22103step0 = (fun i j => raw22103 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw22103step0 raw22103; decide +kernel
      have hl : raw22103step0Labels = raw22103Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22103 raw22103Labels permutation520 hz
    mixedMoment B raw22103step0 raw22103step0Labels = mixedMoment B raw22103step1 raw22103step1Labels := by
      have hz : ∀ j, raw22103step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw22103step1 = (fun i j => raw22103step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw22103step1 raw22103step0; decide +kernel
      have hl : raw22103step1Labels = raw22103step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22103step0 raw22103step0Labels permutation104 hz
    _ = mixedMoment B node4069 node4069Labels := by rfl

theorem canonical22104 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22104 raw22104Labels = mixedMoment B node538 node538Labels := by
  calc
    mixedMoment B raw22104 raw22104Labels = mixedMoment B raw22104step0 raw22104step0Labels := by
      have hz : ∀ j, raw22104 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22104step0 = (fun i j => raw22104 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22104step0 raw22104; decide +kernel
      have hl : raw22104step0Labels = raw22104Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22104 raw22104Labels permutation434 hz
    mixedMoment B raw22104step0 raw22104step0Labels = mixedMoment B raw22104step1 raw22104step1Labels := by
      have ha : raw22104step1 = (fun i j => raw22104step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22104step1 raw22104step0; decide +kernel
      have hl : raw22104step1Labels = raw22104step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22104step0 raw22104step0Labels permutation40 permutation2
    _ = mixedMoment B node538 node538Labels := by rfl

theorem canonical22105 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22105 raw22105Labels = mixedMoment B node733 node733Labels := by
  calc
    mixedMoment B raw22105 raw22105Labels = mixedMoment B raw22105step0 raw22105step0Labels := by
      have hz : ∀ j, raw22105 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22105step0 = (fun i j => raw22105 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22105step0 raw22105; decide +kernel
      have hl : raw22105step0Labels = raw22105Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22105 raw22105Labels permutation434 hz
    mixedMoment B raw22105step0 raw22105step0Labels = mixedMoment B raw22105step1 raw22105step1Labels := by
      have ha : raw22105step1 = (fun i j => raw22105step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22105step1 raw22105step0; decide +kernel
      have hl : raw22105step1Labels = raw22105step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22105step0 raw22105step0Labels permutation40 permutation2
    _ = mixedMoment B node733 node733Labels := by rfl

theorem canonical22106 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22106 raw22106Labels = mixedMoment B node699 node699Labels := by
  calc
    mixedMoment B raw22106 raw22106Labels = mixedMoment B raw22106step0 raw22106step0Labels := by
      have ha : raw22106step0 = (fun i j => raw22106 (permutation208 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22106step0 raw22106; decide +kernel
      have hl : raw22106step0Labels = raw22106Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22106 raw22106Labels permutation208 permutation2
    _ = mixedMoment B node699 node699Labels := by rfl

theorem canonical22107 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22107 raw22107Labels = mixedMoment B node812 node812Labels := by
  calc
    mixedMoment B raw22107 raw22107Labels = mixedMoment B raw22107step0 raw22107step0Labels := by
      have hz : ∀ j, raw22107 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw22107step0 = (fun i j => raw22107 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw22107step0 raw22107; decide +kernel
      have hl : raw22107step0Labels = raw22107Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22107 raw22107Labels permutation520 hz
    mixedMoment B raw22107step0 raw22107step0Labels = mixedMoment B raw22107step1 raw22107step1Labels := by
      have hz : ∀ j, raw22107step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw22107step1 = (fun i j => raw22107step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw22107step1 raw22107step0; decide +kernel
      have hl : raw22107step1Labels = raw22107step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22107step0 raw22107step0Labels permutation104 hz
    mixedMoment B raw22107step1 raw22107step1Labels = mixedMoment B raw22107step2 raw22107step2Labels := by
      have ha : raw22107step2 = (fun i j => raw22107step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22107step2 raw22107step1; decide +kernel
      have hl : raw22107step2Labels = raw22107step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22107step1 raw22107step1Labels permutation10 permutation2
    _ = mixedMoment B node812 node812Labels := by rfl

theorem canonical22108 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22108 raw22108Labels = mixedMoment B node806 node806Labels := by
  calc
    mixedMoment B raw22108 raw22108Labels = mixedMoment B raw22108step0 raw22108step0Labels := by
      have hz : ∀ j, raw22108 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22108step0 = (fun i j => raw22108 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22108step0 raw22108; decide +kernel
      have hl : raw22108step0Labels = raw22108Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22108 raw22108Labels permutation434 hz
    mixedMoment B raw22108step0 raw22108step0Labels = mixedMoment B raw22108step1 raw22108step1Labels := by
      have ha : raw22108step1 = (fun i j => raw22108step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22108step1 raw22108step0; decide +kernel
      have hl : raw22108step1Labels = raw22108step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22108step0 raw22108step0Labels permutation40 permutation2
    _ = mixedMoment B node806 node806Labels := by rfl

theorem canonical22109 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22109 raw22109Labels = mixedMoment B node806 node806Labels := by
  calc
    mixedMoment B raw22109 raw22109Labels = mixedMoment B raw22109step0 raw22109step0Labels := by
      have hz : ∀ j, raw22109 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22109step0 = (fun i j => raw22109 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22109step0 raw22109; decide +kernel
      have hl : raw22109step0Labels = raw22109Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22109 raw22109Labels permutation434 hz
    mixedMoment B raw22109step0 raw22109step0Labels = mixedMoment B raw22109step1 raw22109step1Labels := by
      have ha : raw22109step1 = (fun i j => raw22109step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22109step1 raw22109step0; decide +kernel
      have hl : raw22109step1Labels = raw22109step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22109step0 raw22109step0Labels permutation34 permutation2
    _ = mixedMoment B node806 node806Labels := by rfl

theorem canonical22110 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22110 raw22110Labels = mixedMoment B node782 node782Labels := by
  calc
    _ = mixedMoment B node782 node782Labels := by rfl

theorem canonical22111 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22111 raw22111Labels = mixedMoment B node789 node789Labels := by
  calc
    mixedMoment B raw22111 raw22111Labels = mixedMoment B raw22111step0 raw22111step0Labels := by
      have hz : ∀ j, raw22111 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22111step0 = (fun i j => raw22111 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22111step0 raw22111; decide +kernel
      have hl : raw22111step0Labels = raw22111Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22111 raw22111Labels permutation434 hz
    _ = mixedMoment B node789 node789Labels := by rfl

theorem canonical22112 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22112 raw22112Labels = mixedMoment B node536 node536Labels := by
  calc
    mixedMoment B raw22112 raw22112Labels = mixedMoment B raw22112step0 raw22112step0Labels := by
      have hz : ∀ j, raw22112 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22112step0 = (fun i j => raw22112 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22112step0 raw22112; decide +kernel
      have hl : raw22112step0Labels = raw22112Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22112 raw22112Labels permutation434 hz
    mixedMoment B raw22112step0 raw22112step0Labels = mixedMoment B raw22112step1 raw22112step1Labels := by
      have ha : raw22112step1 = (fun i j => raw22112step0 (permutation44 i) (permutation4 j)) := by apply Matrix.ext; unfold raw22112step1 raw22112step0; decide +kernel
      have hl : raw22112step1Labels = raw22112step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22112step0 raw22112step0Labels permutation44 permutation4
    mixedMoment B raw22112step1 raw22112step1Labels = mixedMoment B raw22112step2 raw22112step2Labels := by
      have ha : raw22112step2 = -raw22112step1 := by apply Matrix.ext; change ∀ i j, raw22112step2 i j = -(raw22112step1 i j); unfold raw22112step2 raw22112step1; decide +kernel
      have hl : raw22112step2Labels = raw22112step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node536 node536Labels := by rfl

theorem canonical22113 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22113 raw22113Labels = mixedMoment B node809 node809Labels := by
  calc
    mixedMoment B raw22113 raw22113Labels = mixedMoment B raw22113step0 raw22113step0Labels := by
      have hz : ∀ j, raw22113 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22113step0 = (fun i j => raw22113 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22113step0 raw22113; decide +kernel
      have hl : raw22113step0Labels = raw22113Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22113 raw22113Labels permutation434 hz
    mixedMoment B raw22113step0 raw22113step0Labels = mixedMoment B raw22113step1 raw22113step1Labels := by
      have hz : ∀ j, raw22113step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw22113step1 = (fun i j => raw22113step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw22113step1 raw22113step0; decide +kernel
      have hl : raw22113step1Labels = raw22113step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22113step0 raw22113step0Labels permutation56 hz
    mixedMoment B raw22113step1 raw22113step1Labels = mixedMoment B raw22113step2 raw22113step2Labels := by
      have ha : raw22113step2 = (fun i j => raw22113step1 (permutation10 i) (permutation4 j)) := by apply Matrix.ext; unfold raw22113step2 raw22113step1; decide +kernel
      have hl : raw22113step2Labels = raw22113step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22113step1 raw22113step1Labels permutation10 permutation4
    mixedMoment B raw22113step2 raw22113step2Labels = mixedMoment B raw22113step3 raw22113step3Labels := by
      have ha : raw22113step3 = -raw22113step2 := by apply Matrix.ext; change ∀ i j, raw22113step3 i j = -(raw22113step2 i j); unfold raw22113step3 raw22113step2; decide +kernel
      have hl : raw22113step3Labels = raw22113step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node809 node809Labels := by rfl

theorem canonical22114 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22114 raw22114Labels = mixedMoment B node813 node813Labels := by
  calc
    mixedMoment B raw22114 raw22114Labels = mixedMoment B raw22114step0 raw22114step0Labels := by
      have hz : ∀ j, raw22114 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22114step0 = (fun i j => raw22114 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22114step0 raw22114; decide +kernel
      have hl : raw22114step0Labels = raw22114Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22114 raw22114Labels permutation434 hz
    mixedMoment B raw22114step0 raw22114step0Labels = mixedMoment B raw22114step1 raw22114step1Labels := by
      have hz : ∀ j, raw22114step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22114step1 = (fun i j => raw22114step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22114step1 raw22114step0; decide +kernel
      have hl : raw22114step1Labels = raw22114step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22114step0 raw22114step0Labels permutation80 hz
    _ = mixedMoment B node813 node813Labels := by rfl

theorem canonical22115 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22115 raw22115Labels = mixedMoment B node1651 node1651Labels := by
  calc
    mixedMoment B raw22115 raw22115Labels = mixedMoment B raw22115step0 raw22115step0Labels := by
      have hz : ∀ j, raw22115 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22115step0 = (fun i j => raw22115 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22115step0 raw22115; decide +kernel
      have hl : raw22115step0Labels = raw22115Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22115 raw22115Labels permutation434 hz
    mixedMoment B raw22115step0 raw22115step0Labels = mixedMoment B raw22115step1 raw22115step1Labels := by
      have hz : ∀ j, raw22115step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22115step1 = (fun i j => raw22115step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22115step1 raw22115step0; decide +kernel
      have hl : raw22115step1Labels = raw22115step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22115step0 raw22115step0Labels permutation80 hz
    _ = mixedMoment B node1651 node1651Labels := by rfl

theorem canonical22116 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22116 raw22116Labels = mixedMoment B node1603 node1603Labels := by
  calc
    mixedMoment B raw22116 raw22116Labels = mixedMoment B raw22116step0 raw22116step0Labels := by
      have hz : ∀ j, raw22116 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22116step0 = (fun i j => raw22116 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22116step0 raw22116; decide +kernel
      have hl : raw22116step0Labels = raw22116Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22116 raw22116Labels permutation434 hz
    mixedMoment B raw22116step0 raw22116step0Labels = mixedMoment B raw22116step1 raw22116step1Labels := by
      have ha : raw22116step1 = (fun i j => raw22116step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22116step1 raw22116step0; decide +kernel
      have hl : raw22116step1Labels = raw22116step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22116step0 raw22116step0Labels permutation38 permutation2
    _ = mixedMoment B node1603 node1603Labels := by rfl

theorem canonical22117 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22117 raw22117Labels = mixedMoment B node1603 node1603Labels := by
  calc
    mixedMoment B raw22117 raw22117Labels = mixedMoment B raw22117step0 raw22117step0Labels := by
      have hz : ∀ j, raw22117 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22117step0 = (fun i j => raw22117 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22117step0 raw22117; decide +kernel
      have hl : raw22117step0Labels = raw22117Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22117 raw22117Labels permutation346 hz
    mixedMoment B raw22117step0 raw22117step0Labels = mixedMoment B raw22117step1 raw22117step1Labels := by
      have ha : raw22117step1 = (fun i j => raw22117step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22117step1 raw22117step0; decide +kernel
      have hl : raw22117step1Labels = raw22117step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22117step0 raw22117step0Labels permutation38 permutation2
    _ = mixedMoment B node1603 node1603Labels := by rfl

theorem canonical22118 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22118 raw22118Labels = mixedMoment B node1716 node1716Labels := by
  calc
    mixedMoment B raw22118 raw22118Labels = mixedMoment B raw22118step0 raw22118step0Labels := by
      have hz : ∀ j, raw22118 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22118step0 = (fun i j => raw22118 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22118step0 raw22118; decide +kernel
      have hl : raw22118step0Labels = raw22118Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22118 raw22118Labels permutation434 hz
    mixedMoment B raw22118step0 raw22118step0Labels = mixedMoment B raw22118step1 raw22118step1Labels := by
      have hz : ∀ j, raw22118step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22118step1 = (fun i j => raw22118step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22118step1 raw22118step0; decide +kernel
      have hl : raw22118step1Labels = raw22118step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22118step0 raw22118step0Labels permutation80 hz
    _ = mixedMoment B node1716 node1716Labels := by rfl

theorem canonical22119 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22119 raw22119Labels = mixedMoment B node1728 node1728Labels := by
  calc
    mixedMoment B raw22119 raw22119Labels = mixedMoment B raw22119step0 raw22119step0Labels := by
      have hz : ∀ j, raw22119 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22119step0 = (fun i j => raw22119 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22119step0 raw22119; decide +kernel
      have hl : raw22119step0Labels = raw22119Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22119 raw22119Labels permutation434 hz
    mixedMoment B raw22119step0 raw22119step0Labels = mixedMoment B raw22119step1 raw22119step1Labels := by
      have hz : ∀ j, raw22119step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22119step1 = (fun i j => raw22119step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22119step1 raw22119step0; decide +kernel
      have hl : raw22119step1Labels = raw22119step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22119step0 raw22119step0Labels permutation80 hz
    _ = mixedMoment B node1728 node1728Labels := by rfl

theorem canonical22120 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22120 raw22120Labels = mixedMoment B node4069 node4069Labels := by
  calc
    mixedMoment B raw22120 raw22120Labels = mixedMoment B raw22120step0 raw22120step0Labels := by
      have hz : ∀ j, raw22120 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22120step0 = (fun i j => raw22120 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22120step0 raw22120; decide +kernel
      have hl : raw22120step0Labels = raw22120Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22120 raw22120Labels permutation434 hz
    mixedMoment B raw22120step0 raw22120step0Labels = mixedMoment B raw22120step1 raw22120step1Labels := by
      have hz : ∀ j, raw22120step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22120step1 = (fun i j => raw22120step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22120step1 raw22120step0; decide +kernel
      have hl : raw22120step1Labels = raw22120step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22120step0 raw22120step0Labels permutation80 hz
    mixedMoment B raw22120step1 raw22120step1Labels = mixedMoment B raw22120step2 raw22120step2Labels := by
      have ha : raw22120step2 = (fun i j => raw22120step1 (permutation9 i) (permutation0 j)) := by apply Matrix.ext; unfold raw22120step2 raw22120step1; decide +kernel
      have hl : raw22120step2Labels = raw22120step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22120step1 raw22120step1Labels permutation9 permutation0
    _ = mixedMoment B node4069 node4069Labels := by rfl

theorem canonical22121 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22121 raw22121Labels = mixedMoment B node548 node548Labels := by
  calc
    mixedMoment B raw22121 raw22121Labels = mixedMoment B raw22121step0 raw22121step0Labels := by
      have hz : ∀ j, raw22121 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22121step0 = (fun i j => raw22121 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22121step0 raw22121; decide +kernel
      have hl : raw22121step0Labels = raw22121Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22121 raw22121Labels permutation434 hz
    mixedMoment B raw22121step0 raw22121step0Labels = mixedMoment B raw22121step1 raw22121step1Labels := by
      have hz : ∀ j, raw22121step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22121step1 = (fun i j => raw22121step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22121step1 raw22121step0; decide +kernel
      have hl : raw22121step1Labels = raw22121step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22121step0 raw22121step0Labels permutation80 hz
    _ = mixedMoment B node548 node548Labels := by rfl

theorem canonical22122 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22122 raw22122Labels = mixedMoment B node743 node743Labels := by
  calc
    mixedMoment B raw22122 raw22122Labels = mixedMoment B raw22122step0 raw22122step0Labels := by
      have hz : ∀ j, raw22122 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22122step0 = (fun i j => raw22122 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22122step0 raw22122; decide +kernel
      have hl : raw22122step0Labels = raw22122Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22122 raw22122Labels permutation434 hz
    mixedMoment B raw22122step0 raw22122step0Labels = mixedMoment B raw22122step1 raw22122step1Labels := by
      have hz : ∀ j, raw22122step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22122step1 = (fun i j => raw22122step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22122step1 raw22122step0; decide +kernel
      have hl : raw22122step1Labels = raw22122step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22122step0 raw22122step0Labels permutation80 hz
    _ = mixedMoment B node743 node743Labels := by rfl

theorem canonical22123 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22123 raw22123Labels = mixedMoment B node708 node708Labels := by
  calc
    mixedMoment B raw22123 raw22123Labels = mixedMoment B raw22123step0 raw22123step0Labels := by
      have hz : ∀ j, raw22123 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22123step0 = (fun i j => raw22123 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22123step0 raw22123; decide +kernel
      have hl : raw22123step0Labels = raw22123Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22123 raw22123Labels permutation434 hz
    mixedMoment B raw22123step0 raw22123step0Labels = mixedMoment B raw22123step1 raw22123step1Labels := by
      have ha : raw22123step1 = (fun i j => raw22123step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22123step1 raw22123step0; decide +kernel
      have hl : raw22123step1Labels = raw22123step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22123step0 raw22123step0Labels permutation38 permutation2
    _ = mixedMoment B node708 node708Labels := by rfl

theorem canonical22124 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22124 raw22124Labels = mixedMoment B node708 node708Labels := by
  calc
    mixedMoment B raw22124 raw22124Labels = mixedMoment B raw22124step0 raw22124step0Labels := by
      have hz : ∀ j, raw22124 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22124step0 = (fun i j => raw22124 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22124step0 raw22124; decide +kernel
      have hl : raw22124step0Labels = raw22124Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22124 raw22124Labels permutation346 hz
    mixedMoment B raw22124step0 raw22124step0Labels = mixedMoment B raw22124step1 raw22124step1Labels := by
      have ha : raw22124step1 = (fun i j => raw22124step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22124step1 raw22124step0; decide +kernel
      have hl : raw22124step1Labels = raw22124step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22124step0 raw22124step0Labels permutation38 permutation2
    _ = mixedMoment B node708 node708Labels := by rfl

theorem canonical22125 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22125 raw22125Labels = mixedMoment B node816 node816Labels := by
  calc
    mixedMoment B raw22125 raw22125Labels = mixedMoment B raw22125step0 raw22125step0Labels := by
      have hz : ∀ j, raw22125 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22125step0 = (fun i j => raw22125 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22125step0 raw22125; decide +kernel
      have hl : raw22125step0Labels = raw22125Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22125 raw22125Labels permutation434 hz
    mixedMoment B raw22125step0 raw22125step0Labels = mixedMoment B raw22125step1 raw22125step1Labels := by
      have hz : ∀ j, raw22125step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22125step1 = (fun i j => raw22125step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22125step1 raw22125step0; decide +kernel
      have hl : raw22125step1Labels = raw22125step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22125step0 raw22125step0Labels permutation80 hz
    mixedMoment B raw22125step1 raw22125step1Labels = mixedMoment B raw22125step2 raw22125step2Labels := by
      have ha : raw22125step2 = (fun i j => raw22125step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22125step2 raw22125step1; decide +kernel
      have hl : raw22125step2Labels = raw22125step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22125step1 raw22125step1Labels permutation9 permutation2
    _ = mixedMoment B node816 node816Labels := by rfl

theorem canonical22126 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22126 raw22126Labels = mixedMoment B node856 node856Labels := by
  calc
    mixedMoment B raw22126 raw22126Labels = mixedMoment B raw22126step0 raw22126step0Labels := by
      have hz : ∀ j, raw22126 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22126step0 = (fun i j => raw22126 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22126step0 raw22126; decide +kernel
      have hl : raw22126step0Labels = raw22126Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22126 raw22126Labels permutation434 hz
    mixedMoment B raw22126step0 raw22126step0Labels = mixedMoment B raw22126step1 raw22126step1Labels := by
      have hz : ∀ j, raw22126step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22126step1 = (fun i j => raw22126step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22126step1 raw22126step0; decide +kernel
      have hl : raw22126step1Labels = raw22126step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22126step0 raw22126step0Labels permutation80 hz
    _ = mixedMoment B node856 node856Labels := by rfl

theorem canonical22127 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22127 raw22127Labels = mixedMoment B node807 node807Labels := by
  calc
    mixedMoment B raw22127 raw22127Labels = mixedMoment B raw22127step0 raw22127step0Labels := by
      have hz : ∀ j, raw22127 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22127step0 = (fun i j => raw22127 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22127step0 raw22127; decide +kernel
      have hl : raw22127step0Labels = raw22127Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22127 raw22127Labels permutation434 hz
    _ = mixedMoment B node807 node807Labels := by rfl

theorem canonical22128 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22128 raw22128Labels = mixedMoment B node807 node807Labels := by
  calc
    mixedMoment B raw22128 raw22128Labels = mixedMoment B raw22128step0 raw22128step0Labels := by
      have hz : ∀ j, raw22128 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22128step0 = (fun i j => raw22128 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22128step0 raw22128; decide +kernel
      have hl : raw22128step0Labels = raw22128Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22128 raw22128Labels permutation346 hz
    _ = mixedMoment B node807 node807Labels := by rfl

theorem canonical22131 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22131 raw22131Labels = mixedMoment B node4490 node4490Labels := by
  calc
    mixedMoment B raw22131 raw22131Labels = mixedMoment B raw22131step0 raw22131step0Labels := by
      have hz : ∀ j, raw22131 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22131step0 = (fun i j => raw22131 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22131step0 raw22131; decide +kernel
      have hl : raw22131step0Labels = raw22131Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22131 raw22131Labels permutation434 hz
    mixedMoment B raw22131step0 raw22131step0Labels = mixedMoment B raw22131step1 raw22131step1Labels := by
      have hz : ∀ j, raw22131step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22131step1 = (fun i j => raw22131step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22131step1 raw22131step0; decide +kernel
      have hl : raw22131step1Labels = raw22131step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22131step0 raw22131step0Labels permutation80 hz
    mixedMoment B raw22131step1 raw22131step1Labels = mixedMoment B raw22131step2 raw22131step2Labels := by
      have ha : raw22131step2 = (fun i j => raw22131step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw22131step2 raw22131step1; decide +kernel
      have hl : raw22131step2Labels = raw22131step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22131step1 raw22131step1Labels permutation8 permutation7
    mixedMoment B raw22131step2 raw22131step2Labels = mixedMoment B raw22131step3 raw22131step3Labels := by
      have ha : raw22131step3 = -raw22131step2 := by apply Matrix.ext; change ∀ i j, raw22131step3 i j = -(raw22131step2 i j); unfold raw22131step3 raw22131step2; decide +kernel
      have hl : raw22131step3Labels = raw22131step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw22131step3 raw22131step3Labels = mixedMoment B raw22131step4 raw22131step4Labels := by
      have ha : raw22131step4 = raw22131step3 := by apply Matrix.ext; unfold raw22131step4 raw22131step3; decide +kernel
      have hl : raw22131step3Labels = labelEmbedding10 ∘ raw22131step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22131step3 raw22131step3Labels raw22131step4Labels labelEmbedding10 hl
    _ = mixedMoment B node4490 node4490Labels := by rfl

theorem canonical22132 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22132 raw22132Labels = mixedMoment B node4418 node4418Labels := by
  calc
    mixedMoment B raw22132 raw22132Labels = mixedMoment B raw22132step0 raw22132step0Labels := by
      have hz : ∀ j, raw22132 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22132step0 = (fun i j => raw22132 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22132step0 raw22132; decide +kernel
      have hl : raw22132step0Labels = raw22132Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22132 raw22132Labels permutation434 hz
    mixedMoment B raw22132step0 raw22132step0Labels = mixedMoment B raw22132step1 raw22132step1Labels := by
      have ha : raw22132step1 = (fun i j => raw22132step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw22132step1 raw22132step0; decide +kernel
      have hl : raw22132step1Labels = raw22132step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22132step0 raw22132step0Labels permutation38 permutation7
    mixedMoment B raw22132step1 raw22132step1Labels = mixedMoment B raw22132step2 raw22132step2Labels := by
      have ha : raw22132step2 = -raw22132step1 := by apply Matrix.ext; change ∀ i j, raw22132step2 i j = -(raw22132step1 i j); unfold raw22132step2 raw22132step1; decide +kernel
      have hl : raw22132step2Labels = raw22132step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw22132step2 raw22132step2Labels = mixedMoment B raw22132step3 raw22132step3Labels := by
      have ha : raw22132step3 = raw22132step2 := by apply Matrix.ext; unfold raw22132step3 raw22132step2; decide +kernel
      have hl : raw22132step2Labels = labelEmbedding10 ∘ raw22132step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22132step2 raw22132step2Labels raw22132step3Labels labelEmbedding10 hl
    _ = mixedMoment B node4418 node4418Labels := by rfl

theorem canonical22133 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22133 raw22133Labels = mixedMoment B node4418 node4418Labels := by
  calc
    mixedMoment B raw22133 raw22133Labels = mixedMoment B raw22133step0 raw22133step0Labels := by
      have hz : ∀ j, raw22133 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22133step0 = (fun i j => raw22133 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22133step0 raw22133; decide +kernel
      have hl : raw22133step0Labels = raw22133Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22133 raw22133Labels permutation346 hz
    mixedMoment B raw22133step0 raw22133step0Labels = mixedMoment B raw22133step1 raw22133step1Labels := by
      have ha : raw22133step1 = (fun i j => raw22133step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw22133step1 raw22133step0; decide +kernel
      have hl : raw22133step1Labels = raw22133step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22133step0 raw22133step0Labels permutation38 permutation7
    mixedMoment B raw22133step1 raw22133step1Labels = mixedMoment B raw22133step2 raw22133step2Labels := by
      have ha : raw22133step2 = -raw22133step1 := by apply Matrix.ext; change ∀ i j, raw22133step2 i j = -(raw22133step1 i j); unfold raw22133step2 raw22133step1; decide +kernel
      have hl : raw22133step2Labels = raw22133step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw22133step2 raw22133step2Labels = mixedMoment B raw22133step3 raw22133step3Labels := by
      have ha : raw22133step3 = raw22133step2 := by apply Matrix.ext; unfold raw22133step3 raw22133step2; decide +kernel
      have hl : raw22133step2Labels = labelEmbedding10 ∘ raw22133step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22133step2 raw22133step2Labels raw22133step3Labels labelEmbedding10 hl
    _ = mixedMoment B node4418 node4418Labels := by rfl

theorem canonical22134 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22134 raw22134Labels = mixedMoment B node4496 node4496Labels := by
  calc
    mixedMoment B raw22134 raw22134Labels = mixedMoment B raw22134step0 raw22134step0Labels := by
      have hz : ∀ j, raw22134 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22134step0 = (fun i j => raw22134 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22134step0 raw22134; decide +kernel
      have hl : raw22134step0Labels = raw22134Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22134 raw22134Labels permutation434 hz
    mixedMoment B raw22134step0 raw22134step0Labels = mixedMoment B raw22134step1 raw22134step1Labels := by
      have hz : ∀ j, raw22134step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22134step1 = (fun i j => raw22134step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22134step1 raw22134step0; decide +kernel
      have hl : raw22134step1Labels = raw22134step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22134step0 raw22134step0Labels permutation80 hz
    mixedMoment B raw22134step1 raw22134step1Labels = mixedMoment B raw22134step2 raw22134step2Labels := by
      have ha : raw22134step2 = (fun i j => raw22134step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw22134step2 raw22134step1; decide +kernel
      have hl : raw22134step2Labels = raw22134step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22134step1 raw22134step1Labels permutation8 permutation7
    mixedMoment B raw22134step2 raw22134step2Labels = mixedMoment B raw22134step3 raw22134step3Labels := by
      have ha : raw22134step3 = -raw22134step2 := by apply Matrix.ext; change ∀ i j, raw22134step3 i j = -(raw22134step2 i j); unfold raw22134step3 raw22134step2; decide +kernel
      have hl : raw22134step3Labels = raw22134step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw22134step3 raw22134step3Labels = mixedMoment B raw22134step4 raw22134step4Labels := by
      have ha : raw22134step4 = raw22134step3 := by apply Matrix.ext; unfold raw22134step4 raw22134step3; decide +kernel
      have hl : raw22134step3Labels = labelEmbedding10 ∘ raw22134step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22134step3 raw22134step3Labels raw22134step4Labels labelEmbedding10 hl
    _ = mixedMoment B node4496 node4496Labels := by rfl

theorem canonical22135 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22135 raw22135Labels = mixedMoment B node4498 node4498Labels := by
  calc
    mixedMoment B raw22135 raw22135Labels = mixedMoment B raw22135step0 raw22135step0Labels := by
      have hz : ∀ j, raw22135 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22135step0 = (fun i j => raw22135 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22135step0 raw22135; decide +kernel
      have hl : raw22135step0Labels = raw22135Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22135 raw22135Labels permutation434 hz
    mixedMoment B raw22135step0 raw22135step0Labels = mixedMoment B raw22135step1 raw22135step1Labels := by
      have hz : ∀ j, raw22135step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22135step1 = (fun i j => raw22135step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22135step1 raw22135step0; decide +kernel
      have hl : raw22135step1Labels = raw22135step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22135step0 raw22135step0Labels permutation80 hz
    mixedMoment B raw22135step1 raw22135step1Labels = mixedMoment B raw22135step2 raw22135step2Labels := by
      have ha : raw22135step2 = (fun i j => raw22135step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw22135step2 raw22135step1; decide +kernel
      have hl : raw22135step2Labels = raw22135step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22135step1 raw22135step1Labels permutation8 permutation7
    mixedMoment B raw22135step2 raw22135step2Labels = mixedMoment B raw22135step3 raw22135step3Labels := by
      have ha : raw22135step3 = -raw22135step2 := by apply Matrix.ext; change ∀ i j, raw22135step3 i j = -(raw22135step2 i j); unfold raw22135step3 raw22135step2; decide +kernel
      have hl : raw22135step3Labels = raw22135step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw22135step3 raw22135step3Labels = mixedMoment B raw22135step4 raw22135step4Labels := by
      have ha : raw22135step4 = raw22135step3 := by apply Matrix.ext; unfold raw22135step4 raw22135step3; decide +kernel
      have hl : raw22135step3Labels = labelEmbedding10 ∘ raw22135step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22135step3 raw22135step3Labels raw22135step4Labels labelEmbedding10 hl
    _ = mixedMoment B node4498 node4498Labels := by rfl

theorem canonical22136 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22136 raw22136Labels = mixedMoment B node4127 node4127Labels := by
  calc
    mixedMoment B raw22136 raw22136Labels = mixedMoment B raw22136step0 raw22136step0Labels := by
      have hz : ∀ j, raw22136 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22136step0 = (fun i j => raw22136 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22136step0 raw22136; decide +kernel
      have hl : raw22136step0Labels = raw22136Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22136 raw22136Labels permutation434 hz
    mixedMoment B raw22136step0 raw22136step0Labels = mixedMoment B raw22136step1 raw22136step1Labels := by
      have hz : ∀ j, raw22136step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22136step1 = (fun i j => raw22136step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22136step1 raw22136step0; decide +kernel
      have hl : raw22136step1Labels = raw22136step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22136step0 raw22136step0Labels permutation80 hz
    _ = mixedMoment B node4127 node4127Labels := by rfl

theorem canonical22137 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22137 raw22137Labels = mixedMoment B node4218 node4218Labels := by
  calc
    mixedMoment B raw22137 raw22137Labels = mixedMoment B raw22137step0 raw22137step0Labels := by
      have hz : ∀ j, raw22137 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22137step0 = (fun i j => raw22137 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22137step0 raw22137; decide +kernel
      have hl : raw22137step0Labels = raw22137Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22137 raw22137Labels permutation434 hz
    mixedMoment B raw22137step0 raw22137step0Labels = mixedMoment B raw22137step1 raw22137step1Labels := by
      have ha : raw22137step1 = (fun i j => raw22137step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22137step1 raw22137step0; decide +kernel
      have hl : raw22137step1Labels = raw22137step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22137step0 raw22137step0Labels permutation38 permutation2
    _ = mixedMoment B node4218 node4218Labels := by rfl

theorem canonical22138 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22138 raw22138Labels = mixedMoment B node4218 node4218Labels := by
  calc
    mixedMoment B raw22138 raw22138Labels = mixedMoment B raw22138step0 raw22138step0Labels := by
      have hz : ∀ j, raw22138 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22138step0 = (fun i j => raw22138 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22138step0 raw22138; decide +kernel
      have hl : raw22138step0Labels = raw22138Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22138 raw22138Labels permutation346 hz
    mixedMoment B raw22138step0 raw22138step0Labels = mixedMoment B raw22138step1 raw22138step1Labels := by
      have ha : raw22138step1 = (fun i j => raw22138step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22138step1 raw22138step0; decide +kernel
      have hl : raw22138step1Labels = raw22138step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22138step0 raw22138step0Labels permutation38 permutation2
    _ = mixedMoment B node4218 node4218Labels := by rfl

theorem canonical22139 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22139 raw22139Labels = mixedMoment B node4269 node4269Labels := by
  calc
    mixedMoment B raw22139 raw22139Labels = mixedMoment B raw22139step0 raw22139step0Labels := by
      have hz : ∀ j, raw22139 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22139step0 = (fun i j => raw22139 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22139step0 raw22139; decide +kernel
      have hl : raw22139step0Labels = raw22139Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22139 raw22139Labels permutation434 hz
    mixedMoment B raw22139step0 raw22139step0Labels = mixedMoment B raw22139step1 raw22139step1Labels := by
      have hz : ∀ j, raw22139step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22139step1 = (fun i j => raw22139step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22139step1 raw22139step0; decide +kernel
      have hl : raw22139step1Labels = raw22139step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22139step0 raw22139step0Labels permutation80 hz
    mixedMoment B raw22139step1 raw22139step1Labels = mixedMoment B raw22139step2 raw22139step2Labels := by
      have ha : raw22139step2 = (fun i j => raw22139step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22139step2 raw22139step1; decide +kernel
      have hl : raw22139step2Labels = raw22139step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22139step1 raw22139step1Labels permutation10 permutation2
    _ = mixedMoment B node4269 node4269Labels := by rfl

theorem canonical22140 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22140 raw22140Labels = mixedMoment B node4069 node4069Labels := by
  calc
    mixedMoment B raw22140 raw22140Labels = mixedMoment B raw22140step0 raw22140step0Labels := by
      have hz : ∀ j, raw22140 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22140step0 = (fun i j => raw22140 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22140step0 raw22140; decide +kernel
      have hl : raw22140step0Labels = raw22140Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22140 raw22140Labels permutation434 hz
    mixedMoment B raw22140step0 raw22140step0Labels = mixedMoment B raw22140step1 raw22140step1Labels := by
      have hz : ∀ j, raw22140step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22140step1 = (fun i j => raw22140step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22140step1 raw22140step0; decide +kernel
      have hl : raw22140step1Labels = raw22140step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22140step0 raw22140step0Labels permutation80 hz
    mixedMoment B raw22140step1 raw22140step1Labels = mixedMoment B raw22140step2 raw22140step2Labels := by
      have hz : ∀ i, raw22140step1 i (permutation4 0) = 0 := by decide +kernel
      have ha : raw22140step2 = (fun i j => raw22140step1 i (permutation4 j.succ)) := by apply Matrix.ext; unfold raw22140step2 raw22140step1; decide +kernel
      have hl : raw22140step2Labels = (fun j => raw22140step1Labels (permutation4 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw22140step1 raw22140step1Labels permutation4 hz
    mixedMoment B raw22140step2 raw22140step2Labels = mixedMoment B raw22140step3 raw22140step3Labels := by
      have ha : raw22140step3 = raw22140step2 := by apply Matrix.ext; unfold raw22140step3 raw22140step2; decide +kernel
      have hl : raw22140step2Labels = labelEmbedding2 ∘ raw22140step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22140step2 raw22140step2Labels raw22140step3Labels labelEmbedding2 hl
    _ = mixedMoment B node4069 node4069Labels := by rfl

theorem canonical22141 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22141 raw22141Labels = mixedMoment B node4101 node4101Labels := by
  calc
    mixedMoment B raw22141 raw22141Labels = mixedMoment B raw22141step0 raw22141step0Labels := by
      have hz : ∀ j, raw22141 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22141step0 = (fun i j => raw22141 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22141step0 raw22141; decide +kernel
      have hl : raw22141step0Labels = raw22141Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22141 raw22141Labels permutation434 hz
    _ = mixedMoment B node4101 node4101Labels := by rfl

theorem canonical22142 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22142 raw22142Labels = mixedMoment B node4233 node4233Labels := by
  calc
    mixedMoment B raw22142 raw22142Labels = mixedMoment B raw22142step0 raw22142step0Labels := by
      have hz : ∀ j, raw22142 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22142step0 = (fun i j => raw22142 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22142step0 raw22142; decide +kernel
      have hl : raw22142step0Labels = raw22142Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22142 raw22142Labels permutation434 hz
    _ = mixedMoment B node4233 node4233Labels := by rfl

theorem canonical22143 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22143 raw22143Labels = mixedMoment B node4196 node4196Labels := by
  calc
    mixedMoment B raw22143 raw22143Labels = mixedMoment B raw22143step0 raw22143step0Labels := by
      have ha : raw22143step0 = (fun i j => raw22143 (permutation200 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22143step0 raw22143; decide +kernel
      have hl : raw22143step0Labels = raw22143Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22143 raw22143Labels permutation200 permutation2
    _ = mixedMoment B node4196 node4196Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical173
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical22144 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22144 raw22144Labels = mixedMoment B node4251 node4251Labels := by
  calc
    mixedMoment B raw22144 raw22144Labels = mixedMoment B raw22144step0 raw22144step0Labels := by
      have hz : ∀ j, raw22144 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22144step0 = (fun i j => raw22144 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22144step0 raw22144; decide +kernel
      have hl : raw22144step0Labels = raw22144Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22144 raw22144Labels permutation434 hz
    mixedMoment B raw22144step0 raw22144step0Labels = mixedMoment B raw22144step1 raw22144step1Labels := by
      have ha : raw22144step1 = (fun i j => raw22144step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22144step1 raw22144step0; decide +kernel
      have hl : raw22144step1Labels = raw22144step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22144step0 raw22144step0Labels permutation34 permutation2
    _ = mixedMoment B node4251 node4251Labels := by rfl

theorem canonical22145 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22145 raw22145Labels = mixedMoment B node4264 node4264Labels := by
  calc
    mixedMoment B raw22145 raw22145Labels = mixedMoment B raw22145step0 raw22145step0Labels := by
      have hz : ∀ j, raw22145 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22145step0 = (fun i j => raw22145 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22145step0 raw22145; decide +kernel
      have hl : raw22145step0Labels = raw22145Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22145 raw22145Labels permutation434 hz
    _ = mixedMoment B node4264 node4264Labels := by rfl

theorem canonical22146 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22146 raw22146Labels = mixedMoment B node4101 node4101Labels := by
  calc
    mixedMoment B raw22146 raw22146Labels = mixedMoment B raw22146step0 raw22146step0Labels := by
      have hz : ∀ j, raw22146 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22146step0 = (fun i j => raw22146 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22146step0 raw22146; decide +kernel
      have hl : raw22146step0Labels = raw22146Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22146 raw22146Labels permutation346 hz
    _ = mixedMoment B node4101 node4101Labels := by rfl

theorem canonical22147 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22147 raw22147Labels = mixedMoment B node4233 node4233Labels := by
  calc
    mixedMoment B raw22147 raw22147Labels = mixedMoment B raw22147step0 raw22147step0Labels := by
      have hz : ∀ j, raw22147 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22147step0 = (fun i j => raw22147 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22147step0 raw22147; decide +kernel
      have hl : raw22147step0Labels = raw22147Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22147 raw22147Labels permutation346 hz
    _ = mixedMoment B node4233 node4233Labels := by rfl

theorem canonical22148 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22148 raw22148Labels = mixedMoment B node4196 node4196Labels := by
  calc
    mixedMoment B raw22148 raw22148Labels = mixedMoment B raw22148step0 raw22148step0Labels := by
      have ha : raw22148step0 = (fun i j => raw22148 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22148step0 raw22148; decide +kernel
      have hl : raw22148step0Labels = raw22148Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22148 raw22148Labels permutation176 permutation2
    _ = mixedMoment B node4196 node4196Labels := by rfl

theorem canonical22149 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22149 raw22149Labels = mixedMoment B node4251 node4251Labels := by
  calc
    mixedMoment B raw22149 raw22149Labels = mixedMoment B raw22149step0 raw22149step0Labels := by
      have hz : ∀ j, raw22149 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22149step0 = (fun i j => raw22149 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22149step0 raw22149; decide +kernel
      have hl : raw22149step0Labels = raw22149Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22149 raw22149Labels permutation346 hz
    mixedMoment B raw22149step0 raw22149step0Labels = mixedMoment B raw22149step1 raw22149step1Labels := by
      have ha : raw22149step1 = (fun i j => raw22149step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22149step1 raw22149step0; decide +kernel
      have hl : raw22149step1Labels = raw22149step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22149step0 raw22149step0Labels permutation34 permutation2
    _ = mixedMoment B node4251 node4251Labels := by rfl

theorem canonical22150 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22150 raw22150Labels = mixedMoment B node4264 node4264Labels := by
  calc
    mixedMoment B raw22150 raw22150Labels = mixedMoment B raw22150step0 raw22150step0Labels := by
      have hz : ∀ j, raw22150 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22150step0 = (fun i j => raw22150 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22150step0 raw22150; decide +kernel
      have hl : raw22150step0Labels = raw22150Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22150 raw22150Labels permutation346 hz
    _ = mixedMoment B node4264 node4264Labels := by rfl

theorem canonical22151 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22151 raw22151Labels = mixedMoment B node4110 node4110Labels := by
  calc
    mixedMoment B raw22151 raw22151Labels = mixedMoment B raw22151step0 raw22151step0Labels := by
      have hz : ∀ j, raw22151 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22151step0 = (fun i j => raw22151 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22151step0 raw22151; decide +kernel
      have hl : raw22151step0Labels = raw22151Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22151 raw22151Labels permutation434 hz
    mixedMoment B raw22151step0 raw22151step0Labels = mixedMoment B raw22151step1 raw22151step1Labels := by
      have hz : ∀ j, raw22151step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22151step1 = (fun i j => raw22151step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22151step1 raw22151step0; decide +kernel
      have hl : raw22151step1Labels = raw22151step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22151step0 raw22151step0Labels permutation80 hz
    _ = mixedMoment B node4110 node4110Labels := by rfl

theorem canonical22152 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22152 raw22152Labels = mixedMoment B node4242 node4242Labels := by
  calc
    mixedMoment B raw22152 raw22152Labels = mixedMoment B raw22152step0 raw22152step0Labels := by
      have hz : ∀ j, raw22152 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22152step0 = (fun i j => raw22152 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22152step0 raw22152; decide +kernel
      have hl : raw22152step0Labels = raw22152Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22152 raw22152Labels permutation434 hz
    mixedMoment B raw22152step0 raw22152step0Labels = mixedMoment B raw22152step1 raw22152step1Labels := by
      have hz : ∀ j, raw22152step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22152step1 = (fun i j => raw22152step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22152step1 raw22152step0; decide +kernel
      have hl : raw22152step1Labels = raw22152step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22152step0 raw22152step0Labels permutation80 hz
    _ = mixedMoment B node4242 node4242Labels := by rfl

theorem canonical22153 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22153 raw22153Labels = mixedMoment B node4204 node4204Labels := by
  calc
    mixedMoment B raw22153 raw22153Labels = mixedMoment B raw22153step0 raw22153step0Labels := by
      have hz : ∀ j, raw22153 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22153step0 = (fun i j => raw22153 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22153step0 raw22153; decide +kernel
      have hl : raw22153step0Labels = raw22153Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22153 raw22153Labels permutation434 hz
    mixedMoment B raw22153step0 raw22153step0Labels = mixedMoment B raw22153step1 raw22153step1Labels := by
      have ha : raw22153step1 = (fun i j => raw22153step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22153step1 raw22153step0; decide +kernel
      have hl : raw22153step1Labels = raw22153step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22153step0 raw22153step0Labels permutation38 permutation2
    _ = mixedMoment B node4204 node4204Labels := by rfl

theorem canonical22154 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22154 raw22154Labels = mixedMoment B node4204 node4204Labels := by
  calc
    mixedMoment B raw22154 raw22154Labels = mixedMoment B raw22154step0 raw22154step0Labels := by
      have hz : ∀ j, raw22154 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22154step0 = (fun i j => raw22154 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22154step0 raw22154; decide +kernel
      have hl : raw22154step0Labels = raw22154Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22154 raw22154Labels permutation346 hz
    mixedMoment B raw22154step0 raw22154step0Labels = mixedMoment B raw22154step1 raw22154step1Labels := by
      have ha : raw22154step1 = (fun i j => raw22154step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22154step1 raw22154step0; decide +kernel
      have hl : raw22154step1Labels = raw22154step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22154step0 raw22154step0Labels permutation38 permutation2
    _ = mixedMoment B node4204 node4204Labels := by rfl

theorem canonical22155 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22155 raw22155Labels = mixedMoment B node4273 node4273Labels := by
  calc
    mixedMoment B raw22155 raw22155Labels = mixedMoment B raw22155step0 raw22155step0Labels := by
      have hz : ∀ j, raw22155 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22155step0 = (fun i j => raw22155 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22155step0 raw22155; decide +kernel
      have hl : raw22155step0Labels = raw22155Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22155 raw22155Labels permutation434 hz
    mixedMoment B raw22155step0 raw22155step0Labels = mixedMoment B raw22155step1 raw22155step1Labels := by
      have hz : ∀ j, raw22155step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22155step1 = (fun i j => raw22155step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22155step1 raw22155step0; decide +kernel
      have hl : raw22155step1Labels = raw22155step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22155step0 raw22155step0Labels permutation80 hz
    _ = mixedMoment B node4273 node4273Labels := by rfl

theorem canonical22156 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22156 raw22156Labels = mixedMoment B node4108 node4108Labels := by
  calc
    mixedMoment B raw22156 raw22156Labels = mixedMoment B raw22156step0 raw22156step0Labels := by
      have hz : ∀ j, raw22156 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22156step0 = (fun i j => raw22156 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22156step0 raw22156; decide +kernel
      have hl : raw22156step0Labels = raw22156Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22156 raw22156Labels permutation434 hz
    mixedMoment B raw22156step0 raw22156step0Labels = mixedMoment B raw22156step1 raw22156step1Labels := by
      have hz : ∀ j, raw22156step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22156step1 = (fun i j => raw22156step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22156step1 raw22156step0; decide +kernel
      have hl : raw22156step1Labels = raw22156step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22156step0 raw22156step0Labels permutation80 hz
    _ = mixedMoment B node4108 node4108Labels := by rfl

theorem canonical22157 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22157 raw22157Labels = mixedMoment B node4240 node4240Labels := by
  calc
    mixedMoment B raw22157 raw22157Labels = mixedMoment B raw22157step0 raw22157step0Labels := by
      have hz : ∀ j, raw22157 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22157step0 = (fun i j => raw22157 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22157step0 raw22157; decide +kernel
      have hl : raw22157step0Labels = raw22157Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22157 raw22157Labels permutation434 hz
    mixedMoment B raw22157step0 raw22157step0Labels = mixedMoment B raw22157step1 raw22157step1Labels := by
      have hz : ∀ j, raw22157step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22157step1 = (fun i j => raw22157step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22157step1 raw22157step0; decide +kernel
      have hl : raw22157step1Labels = raw22157step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22157step0 raw22157step0Labels permutation80 hz
    _ = mixedMoment B node4240 node4240Labels := by rfl

theorem canonical22158 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22158 raw22158Labels = mixedMoment B node4202 node4202Labels := by
  calc
    mixedMoment B raw22158 raw22158Labels = mixedMoment B raw22158step0 raw22158step0Labels := by
      have hz : ∀ j, raw22158 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22158step0 = (fun i j => raw22158 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22158step0 raw22158; decide +kernel
      have hl : raw22158step0Labels = raw22158Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22158 raw22158Labels permutation434 hz
    mixedMoment B raw22158step0 raw22158step0Labels = mixedMoment B raw22158step1 raw22158step1Labels := by
      have ha : raw22158step1 = (fun i j => raw22158step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22158step1 raw22158step0; decide +kernel
      have hl : raw22158step1Labels = raw22158step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22158step0 raw22158step0Labels permutation38 permutation2
    _ = mixedMoment B node4202 node4202Labels := by rfl

theorem canonical22159 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22159 raw22159Labels = mixedMoment B node4202 node4202Labels := by
  calc
    mixedMoment B raw22159 raw22159Labels = mixedMoment B raw22159step0 raw22159step0Labels := by
      have hz : ∀ j, raw22159 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22159step0 = (fun i j => raw22159 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22159step0 raw22159; decide +kernel
      have hl : raw22159step0Labels = raw22159Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22159 raw22159Labels permutation346 hz
    mixedMoment B raw22159step0 raw22159step0Labels = mixedMoment B raw22159step1 raw22159step1Labels := by
      have ha : raw22159step1 = (fun i j => raw22159step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22159step1 raw22159step0; decide +kernel
      have hl : raw22159step1Labels = raw22159step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22159step0 raw22159step0Labels permutation38 permutation2
    _ = mixedMoment B node4202 node4202Labels := by rfl

theorem canonical22160 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22160 raw22160Labels = mixedMoment B node4257 node4257Labels := by
  calc
    mixedMoment B raw22160 raw22160Labels = mixedMoment B raw22160step0 raw22160step0Labels := by
      have hz : ∀ j, raw22160 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22160step0 = (fun i j => raw22160 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22160step0 raw22160; decide +kernel
      have hl : raw22160step0Labels = raw22160Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22160 raw22160Labels permutation434 hz
    mixedMoment B raw22160step0 raw22160step0Labels = mixedMoment B raw22160step1 raw22160step1Labels := by
      have hz : ∀ j, raw22160step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22160step1 = (fun i j => raw22160step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22160step1 raw22160step0; decide +kernel
      have hl : raw22160step1Labels = raw22160step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22160step0 raw22160step0Labels permutation80 hz
    _ = mixedMoment B node4257 node4257Labels := by rfl

theorem canonical22161 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22161 raw22161Labels = mixedMoment B node1074 node1074Labels := by
  calc
    mixedMoment B raw22161 raw22161Labels = mixedMoment B raw22161step0 raw22161step0Labels := by
      have hz : ∀ j, raw22161 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22161step0 = (fun i j => raw22161 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22161step0 raw22161; decide +kernel
      have hl : raw22161step0Labels = raw22161Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22161 raw22161Labels permutation434 hz
    mixedMoment B raw22161step0 raw22161step0Labels = mixedMoment B raw22161step1 raw22161step1Labels := by
      have hz : ∀ j, raw22161step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22161step1 = (fun i j => raw22161step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22161step1 raw22161step0; decide +kernel
      have hl : raw22161step1Labels = raw22161step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22161step0 raw22161step0Labels permutation80 hz
    mixedMoment B raw22161step1 raw22161step1Labels = mixedMoment B raw22161step2 raw22161step2Labels := by
      have ha : raw22161step2 = (fun i j => raw22161step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw22161step2 raw22161step1; decide +kernel
      have hl : raw22161step2Labels = raw22161step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22161step1 raw22161step1Labels permutation8 permutation7
    mixedMoment B raw22161step2 raw22161step2Labels = mixedMoment B raw22161step3 raw22161step3Labels := by
      have ha : raw22161step3 = -raw22161step2 := by apply Matrix.ext; change ∀ i j, raw22161step3 i j = -(raw22161step2 i j); unfold raw22161step3 raw22161step2; decide +kernel
      have hl : raw22161step3Labels = raw22161step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw22161step3 raw22161step3Labels = mixedMoment B raw22161step4 raw22161step4Labels := by
      have ha : raw22161step4 = raw22161step3 := by apply Matrix.ext; unfold raw22161step4 raw22161step3; decide +kernel
      have hl : raw22161step3Labels = labelEmbedding1 ∘ raw22161step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22161step3 raw22161step3Labels raw22161step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1074 node1074Labels := by rfl

theorem canonical22162 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22162 raw22162Labels = mixedMoment B node999 node999Labels := by
  calc
    mixedMoment B raw22162 raw22162Labels = mixedMoment B raw22162step0 raw22162step0Labels := by
      have hz : ∀ j, raw22162 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22162step0 = (fun i j => raw22162 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22162step0 raw22162; decide +kernel
      have hl : raw22162step0Labels = raw22162Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22162 raw22162Labels permutation434 hz
    mixedMoment B raw22162step0 raw22162step0Labels = mixedMoment B raw22162step1 raw22162step1Labels := by
      have ha : raw22162step1 = (fun i j => raw22162step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw22162step1 raw22162step0; decide +kernel
      have hl : raw22162step1Labels = raw22162step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22162step0 raw22162step0Labels permutation38 permutation7
    mixedMoment B raw22162step1 raw22162step1Labels = mixedMoment B raw22162step2 raw22162step2Labels := by
      have ha : raw22162step2 = -raw22162step1 := by apply Matrix.ext; change ∀ i j, raw22162step2 i j = -(raw22162step1 i j); unfold raw22162step2 raw22162step1; decide +kernel
      have hl : raw22162step2Labels = raw22162step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw22162step2 raw22162step2Labels = mixedMoment B raw22162step3 raw22162step3Labels := by
      have ha : raw22162step3 = raw22162step2 := by apply Matrix.ext; unfold raw22162step3 raw22162step2; decide +kernel
      have hl : raw22162step2Labels = labelEmbedding1 ∘ raw22162step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22162step2 raw22162step2Labels raw22162step3Labels labelEmbedding1 hl
    _ = mixedMoment B node999 node999Labels := by rfl

theorem canonical22163 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22163 raw22163Labels = mixedMoment B node999 node999Labels := by
  calc
    mixedMoment B raw22163 raw22163Labels = mixedMoment B raw22163step0 raw22163step0Labels := by
      have hz : ∀ j, raw22163 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22163step0 = (fun i j => raw22163 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22163step0 raw22163; decide +kernel
      have hl : raw22163step0Labels = raw22163Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22163 raw22163Labels permutation346 hz
    mixedMoment B raw22163step0 raw22163step0Labels = mixedMoment B raw22163step1 raw22163step1Labels := by
      have ha : raw22163step1 = (fun i j => raw22163step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw22163step1 raw22163step0; decide +kernel
      have hl : raw22163step1Labels = raw22163step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22163step0 raw22163step0Labels permutation38 permutation7
    mixedMoment B raw22163step1 raw22163step1Labels = mixedMoment B raw22163step2 raw22163step2Labels := by
      have ha : raw22163step2 = -raw22163step1 := by apply Matrix.ext; change ∀ i j, raw22163step2 i j = -(raw22163step1 i j); unfold raw22163step2 raw22163step1; decide +kernel
      have hl : raw22163step2Labels = raw22163step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw22163step2 raw22163step2Labels = mixedMoment B raw22163step3 raw22163step3Labels := by
      have ha : raw22163step3 = raw22163step2 := by apply Matrix.ext; unfold raw22163step3 raw22163step2; decide +kernel
      have hl : raw22163step2Labels = labelEmbedding1 ∘ raw22163step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22163step2 raw22163step2Labels raw22163step3Labels labelEmbedding1 hl
    _ = mixedMoment B node999 node999Labels := by rfl

theorem canonical22164 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22164 raw22164Labels = mixedMoment B node1080 node1080Labels := by
  calc
    mixedMoment B raw22164 raw22164Labels = mixedMoment B raw22164step0 raw22164step0Labels := by
      have hz : ∀ j, raw22164 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22164step0 = (fun i j => raw22164 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22164step0 raw22164; decide +kernel
      have hl : raw22164step0Labels = raw22164Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22164 raw22164Labels permutation434 hz
    mixedMoment B raw22164step0 raw22164step0Labels = mixedMoment B raw22164step1 raw22164step1Labels := by
      have hz : ∀ j, raw22164step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22164step1 = (fun i j => raw22164step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22164step1 raw22164step0; decide +kernel
      have hl : raw22164step1Labels = raw22164step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22164step0 raw22164step0Labels permutation80 hz
    mixedMoment B raw22164step1 raw22164step1Labels = mixedMoment B raw22164step2 raw22164step2Labels := by
      have ha : raw22164step2 = (fun i j => raw22164step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw22164step2 raw22164step1; decide +kernel
      have hl : raw22164step2Labels = raw22164step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22164step1 raw22164step1Labels permutation8 permutation7
    mixedMoment B raw22164step2 raw22164step2Labels = mixedMoment B raw22164step3 raw22164step3Labels := by
      have ha : raw22164step3 = -raw22164step2 := by apply Matrix.ext; change ∀ i j, raw22164step3 i j = -(raw22164step2 i j); unfold raw22164step3 raw22164step2; decide +kernel
      have hl : raw22164step3Labels = raw22164step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw22164step3 raw22164step3Labels = mixedMoment B raw22164step4 raw22164step4Labels := by
      have ha : raw22164step4 = raw22164step3 := by apply Matrix.ext; unfold raw22164step4 raw22164step3; decide +kernel
      have hl : raw22164step3Labels = labelEmbedding1 ∘ raw22164step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22164step3 raw22164step3Labels raw22164step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1080 node1080Labels := by rfl

theorem canonical22165 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22165 raw22165Labels = mixedMoment B node1082 node1082Labels := by
  calc
    mixedMoment B raw22165 raw22165Labels = mixedMoment B raw22165step0 raw22165step0Labels := by
      have hz : ∀ j, raw22165 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22165step0 = (fun i j => raw22165 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22165step0 raw22165; decide +kernel
      have hl : raw22165step0Labels = raw22165Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22165 raw22165Labels permutation434 hz
    mixedMoment B raw22165step0 raw22165step0Labels = mixedMoment B raw22165step1 raw22165step1Labels := by
      have hz : ∀ j, raw22165step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22165step1 = (fun i j => raw22165step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22165step1 raw22165step0; decide +kernel
      have hl : raw22165step1Labels = raw22165step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22165step0 raw22165step0Labels permutation80 hz
    mixedMoment B raw22165step1 raw22165step1Labels = mixedMoment B raw22165step2 raw22165step2Labels := by
      have ha : raw22165step2 = (fun i j => raw22165step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw22165step2 raw22165step1; decide +kernel
      have hl : raw22165step2Labels = raw22165step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22165step1 raw22165step1Labels permutation8 permutation7
    mixedMoment B raw22165step2 raw22165step2Labels = mixedMoment B raw22165step3 raw22165step3Labels := by
      have ha : raw22165step3 = -raw22165step2 := by apply Matrix.ext; change ∀ i j, raw22165step3 i j = -(raw22165step2 i j); unfold raw22165step3 raw22165step2; decide +kernel
      have hl : raw22165step3Labels = raw22165step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw22165step3 raw22165step3Labels = mixedMoment B raw22165step4 raw22165step4Labels := by
      have ha : raw22165step4 = raw22165step3 := by apply Matrix.ext; unfold raw22165step4 raw22165step3; decide +kernel
      have hl : raw22165step3Labels = labelEmbedding1 ∘ raw22165step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22165step3 raw22165step3Labels raw22165step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1082 node1082Labels := by rfl

theorem canonical22166 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22166 raw22166Labels = mixedMoment B node688 node688Labels := by
  calc
    mixedMoment B raw22166 raw22166Labels = mixedMoment B raw22166step0 raw22166step0Labels := by
      have hz : ∀ j, raw22166 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22166step0 = (fun i j => raw22166 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22166step0 raw22166; decide +kernel
      have hl : raw22166step0Labels = raw22166Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22166 raw22166Labels permutation434 hz
    mixedMoment B raw22166step0 raw22166step0Labels = mixedMoment B raw22166step1 raw22166step1Labels := by
      have hz : ∀ j, raw22166step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22166step1 = (fun i j => raw22166step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22166step1 raw22166step0; decide +kernel
      have hl : raw22166step1Labels = raw22166step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22166step0 raw22166step0Labels permutation80 hz
    mixedMoment B raw22166step1 raw22166step1Labels = mixedMoment B raw22166step2 raw22166step2Labels := by
      have ha : raw22166step2 = (fun i j => raw22166step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw22166step2 raw22166step1; decide +kernel
      have hl : raw22166step2Labels = raw22166step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22166step1 raw22166step1Labels permutation8 permutation7
    mixedMoment B raw22166step2 raw22166step2Labels = mixedMoment B raw22166step3 raw22166step3Labels := by
      have ha : raw22166step3 = -raw22166step2 := by apply Matrix.ext; change ∀ i j, raw22166step3 i j = -(raw22166step2 i j); unfold raw22166step3 raw22166step2; decide +kernel
      have hl : raw22166step3Labels = raw22166step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw22166step3 raw22166step3Labels = mixedMoment B raw22166step4 raw22166step4Labels := by
      have ha : raw22166step4 = raw22166step3 := by apply Matrix.ext; unfold raw22166step4 raw22166step3; decide +kernel
      have hl : raw22166step3Labels = labelEmbedding1 ∘ raw22166step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22166step3 raw22166step3Labels raw22166step4Labels labelEmbedding1 hl
    _ = mixedMoment B node688 node688Labels := by rfl

theorem canonical22167 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22167 raw22167Labels = mixedMoment B node767 node767Labels := by
  calc
    mixedMoment B raw22167 raw22167Labels = mixedMoment B raw22167step0 raw22167step0Labels := by
      have hz : ∀ j, raw22167 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22167step0 = (fun i j => raw22167 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22167step0 raw22167; decide +kernel
      have hl : raw22167step0Labels = raw22167Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22167 raw22167Labels permutation434 hz
    mixedMoment B raw22167step0 raw22167step0Labels = mixedMoment B raw22167step1 raw22167step1Labels := by
      have ha : raw22167step1 = (fun i j => raw22167step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw22167step1 raw22167step0; decide +kernel
      have hl : raw22167step1Labels = raw22167step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22167step0 raw22167step0Labels permutation38 permutation7
    mixedMoment B raw22167step1 raw22167step1Labels = mixedMoment B raw22167step2 raw22167step2Labels := by
      have ha : raw22167step2 = -raw22167step1 := by apply Matrix.ext; change ∀ i j, raw22167step2 i j = -(raw22167step1 i j); unfold raw22167step2 raw22167step1; decide +kernel
      have hl : raw22167step2Labels = raw22167step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw22167step2 raw22167step2Labels = mixedMoment B raw22167step3 raw22167step3Labels := by
      have ha : raw22167step3 = raw22167step2 := by apply Matrix.ext; unfold raw22167step3 raw22167step2; decide +kernel
      have hl : raw22167step2Labels = labelEmbedding1 ∘ raw22167step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22167step2 raw22167step2Labels raw22167step3Labels labelEmbedding1 hl
    _ = mixedMoment B node767 node767Labels := by rfl

theorem canonical22168 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22168 raw22168Labels = mixedMoment B node767 node767Labels := by
  calc
    mixedMoment B raw22168 raw22168Labels = mixedMoment B raw22168step0 raw22168step0Labels := by
      have hz : ∀ j, raw22168 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22168step0 = (fun i j => raw22168 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22168step0 raw22168; decide +kernel
      have hl : raw22168step0Labels = raw22168Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22168 raw22168Labels permutation346 hz
    mixedMoment B raw22168step0 raw22168step0Labels = mixedMoment B raw22168step1 raw22168step1Labels := by
      have ha : raw22168step1 = (fun i j => raw22168step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw22168step1 raw22168step0; decide +kernel
      have hl : raw22168step1Labels = raw22168step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22168step0 raw22168step0Labels permutation38 permutation7
    mixedMoment B raw22168step1 raw22168step1Labels = mixedMoment B raw22168step2 raw22168step2Labels := by
      have ha : raw22168step2 = -raw22168step1 := by apply Matrix.ext; change ∀ i j, raw22168step2 i j = -(raw22168step1 i j); unfold raw22168step2 raw22168step1; decide +kernel
      have hl : raw22168step2Labels = raw22168step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw22168step2 raw22168step2Labels = mixedMoment B raw22168step3 raw22168step3Labels := by
      have ha : raw22168step3 = raw22168step2 := by apply Matrix.ext; unfold raw22168step3 raw22168step2; decide +kernel
      have hl : raw22168step2Labels = labelEmbedding1 ∘ raw22168step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22168step2 raw22168step2Labels raw22168step3Labels labelEmbedding1 hl
    _ = mixedMoment B node767 node767Labels := by rfl

theorem canonical22169 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22169 raw22169Labels = mixedMoment B node851 node851Labels := by
  calc
    mixedMoment B raw22169 raw22169Labels = mixedMoment B raw22169step0 raw22169step0Labels := by
      have hz : ∀ j, raw22169 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22169step0 = (fun i j => raw22169 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22169step0 raw22169; decide +kernel
      have hl : raw22169step0Labels = raw22169Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22169 raw22169Labels permutation434 hz
    mixedMoment B raw22169step0 raw22169step0Labels = mixedMoment B raw22169step1 raw22169step1Labels := by
      have hz : ∀ j, raw22169step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22169step1 = (fun i j => raw22169step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22169step1 raw22169step0; decide +kernel
      have hl : raw22169step1Labels = raw22169step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22169step0 raw22169step0Labels permutation80 hz
    mixedMoment B raw22169step1 raw22169step1Labels = mixedMoment B raw22169step2 raw22169step2Labels := by
      have ha : raw22169step2 = (fun i j => raw22169step1 (permutation10 i) (permutation7 j)) := by apply Matrix.ext; unfold raw22169step2 raw22169step1; decide +kernel
      have hl : raw22169step2Labels = raw22169step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22169step1 raw22169step1Labels permutation10 permutation7
    mixedMoment B raw22169step2 raw22169step2Labels = mixedMoment B raw22169step3 raw22169step3Labels := by
      have ha : raw22169step3 = -raw22169step2 := by apply Matrix.ext; change ∀ i j, raw22169step3 i j = -(raw22169step2 i j); unfold raw22169step3 raw22169step2; decide +kernel
      have hl : raw22169step3Labels = raw22169step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw22169step3 raw22169step3Labels = mixedMoment B raw22169step4 raw22169step4Labels := by
      have ha : raw22169step4 = raw22169step3 := by apply Matrix.ext; unfold raw22169step4 raw22169step3; decide +kernel
      have hl : raw22169step3Labels = labelEmbedding1 ∘ raw22169step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22169step3 raw22169step3Labels raw22169step4Labels labelEmbedding1 hl
    _ = mixedMoment B node851 node851Labels := by rfl

theorem canonical22170 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22170 raw22170Labels = mixedMoment B node4069 node4069Labels := by
  calc
    mixedMoment B raw22170 raw22170Labels = mixedMoment B raw22170step0 raw22170step0Labels := by
      have hz : ∀ j, raw22170 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22170step0 = (fun i j => raw22170 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22170step0 raw22170; decide +kernel
      have hl : raw22170step0Labels = raw22170Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22170 raw22170Labels permutation434 hz
    mixedMoment B raw22170step0 raw22170step0Labels = mixedMoment B raw22170step1 raw22170step1Labels := by
      have hz : ∀ j, raw22170step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22170step1 = (fun i j => raw22170step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22170step1 raw22170step0; decide +kernel
      have hl : raw22170step1Labels = raw22170step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22170step0 raw22170step0Labels permutation80 hz
    mixedMoment B raw22170step1 raw22170step1Labels = mixedMoment B raw22170step2 raw22170step2Labels := by
      have hz : ∀ i, raw22170step1 i (permutation4 0) = 0 := by decide +kernel
      have ha : raw22170step2 = (fun i j => raw22170step1 i (permutation4 j.succ)) := by apply Matrix.ext; unfold raw22170step2 raw22170step1; decide +kernel
      have hl : raw22170step2Labels = (fun j => raw22170step1Labels (permutation4 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw22170step1 raw22170step1Labels permutation4 hz
    _ = mixedMoment B node4069 node4069Labels := by rfl

theorem canonical22171 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22171 raw22171Labels = mixedMoment B node663 node663Labels := by
  calc
    mixedMoment B raw22171 raw22171Labels = mixedMoment B raw22171step0 raw22171step0Labels := by
      have hz : ∀ j, raw22171 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22171step0 = (fun i j => raw22171 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22171step0 raw22171; decide +kernel
      have hl : raw22171step0Labels = raw22171Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22171 raw22171Labels permutation434 hz
    mixedMoment B raw22171step0 raw22171step0Labels = mixedMoment B raw22171step1 raw22171step1Labels := by
      have ha : raw22171step1 = (fun i j => raw22171step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw22171step1 raw22171step0; decide +kernel
      have hl : raw22171step1Labels = raw22171step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22171step0 raw22171step0Labels permutation38 permutation7
    mixedMoment B raw22171step1 raw22171step1Labels = mixedMoment B raw22171step2 raw22171step2Labels := by
      have ha : raw22171step2 = -raw22171step1 := by apply Matrix.ext; change ∀ i j, raw22171step2 i j = -(raw22171step1 i j); unfold raw22171step2 raw22171step1; decide +kernel
      have hl : raw22171step2Labels = raw22171step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw22171step2 raw22171step2Labels = mixedMoment B raw22171step3 raw22171step3Labels := by
      have ha : raw22171step3 = raw22171step2 := by apply Matrix.ext; unfold raw22171step3 raw22171step2; decide +kernel
      have hl : raw22171step2Labels = labelEmbedding1 ∘ raw22171step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22171step2 raw22171step2Labels raw22171step3Labels labelEmbedding1 hl
    _ = mixedMoment B node663 node663Labels := by rfl

theorem canonical22172 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22172 raw22172Labels = mixedMoment B node799 node799Labels := by
  calc
    mixedMoment B raw22172 raw22172Labels = mixedMoment B raw22172step0 raw22172step0Labels := by
      have hz : ∀ j, raw22172 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22172step0 = (fun i j => raw22172 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22172step0 raw22172; decide +kernel
      have hl : raw22172step0Labels = raw22172Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22172 raw22172Labels permutation434 hz
    mixedMoment B raw22172step0 raw22172step0Labels = mixedMoment B raw22172step1 raw22172step1Labels := by
      have ha : raw22172step1 = (fun i j => raw22172step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw22172step1 raw22172step0; decide +kernel
      have hl : raw22172step1Labels = raw22172step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22172step0 raw22172step0Labels permutation38 permutation7
    mixedMoment B raw22172step1 raw22172step1Labels = mixedMoment B raw22172step2 raw22172step2Labels := by
      have ha : raw22172step2 = -raw22172step1 := by apply Matrix.ext; change ∀ i j, raw22172step2 i j = -(raw22172step1 i j); unfold raw22172step2 raw22172step1; decide +kernel
      have hl : raw22172step2Labels = raw22172step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw22172step2 raw22172step2Labels = mixedMoment B raw22172step3 raw22172step3Labels := by
      have ha : raw22172step3 = raw22172step2 := by apply Matrix.ext; unfold raw22172step3 raw22172step2; decide +kernel
      have hl : raw22172step2Labels = labelEmbedding1 ∘ raw22172step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22172step2 raw22172step2Labels raw22172step3Labels labelEmbedding1 hl
    _ = mixedMoment B node799 node799Labels := by rfl

theorem canonical22173 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22173 raw22173Labels = mixedMoment B node748 node748Labels := by
  calc
    mixedMoment B raw22173 raw22173Labels = mixedMoment B raw22173step0 raw22173step0Labels := by
      have ha : raw22173step0 = (fun i j => raw22173 (permutation206 i) (permutation7 j)) := by apply Matrix.ext; unfold raw22173step0 raw22173; decide +kernel
      have hl : raw22173step0Labels = raw22173Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22173 raw22173Labels permutation206 permutation7
    mixedMoment B raw22173step0 raw22173step0Labels = mixedMoment B raw22173step1 raw22173step1Labels := by
      have ha : raw22173step1 = -raw22173step0 := by apply Matrix.ext; change ∀ i j, raw22173step1 i j = -(raw22173step0 i j); unfold raw22173step1 raw22173step0; decide +kernel
      have hl : raw22173step1Labels = raw22173step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw22173step1 raw22173step1Labels = mixedMoment B raw22173step2 raw22173step2Labels := by
      have ha : raw22173step2 = raw22173step1 := by apply Matrix.ext; unfold raw22173step2 raw22173step1; decide +kernel
      have hl : raw22173step1Labels = labelEmbedding1 ∘ raw22173step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22173step1 raw22173step1Labels raw22173step2Labels labelEmbedding1 hl
    _ = mixedMoment B node748 node748Labels := by rfl

theorem canonical22174 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22174 raw22174Labels = mixedMoment B node804 node804Labels := by
  calc
    mixedMoment B raw22174 raw22174Labels = mixedMoment B raw22174step0 raw22174step0Labels := by
      have hz : ∀ j, raw22174 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22174step0 = (fun i j => raw22174 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22174step0 raw22174; decide +kernel
      have hl : raw22174step0Labels = raw22174Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22174 raw22174Labels permutation434 hz
    mixedMoment B raw22174step0 raw22174step0Labels = mixedMoment B raw22174step1 raw22174step1Labels := by
      have ha : raw22174step1 = (fun i j => raw22174step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw22174step1 raw22174step0; decide +kernel
      have hl : raw22174step1Labels = raw22174step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22174step0 raw22174step0Labels permutation38 permutation7
    mixedMoment B raw22174step1 raw22174step1Labels = mixedMoment B raw22174step2 raw22174step2Labels := by
      have ha : raw22174step2 = -raw22174step1 := by apply Matrix.ext; change ∀ i j, raw22174step2 i j = -(raw22174step1 i j); unfold raw22174step2 raw22174step1; decide +kernel
      have hl : raw22174step2Labels = raw22174step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw22174step2 raw22174step2Labels = mixedMoment B raw22174step3 raw22174step3Labels := by
      have ha : raw22174step3 = raw22174step2 := by apply Matrix.ext; unfold raw22174step3 raw22174step2; decide +kernel
      have hl : raw22174step2Labels = labelEmbedding1 ∘ raw22174step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22174step2 raw22174step2Labels raw22174step3Labels labelEmbedding1 hl
    _ = mixedMoment B node804 node804Labels := by rfl

theorem canonical22175 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22175 raw22175Labels = mixedMoment B node806 node806Labels := by
  calc
    mixedMoment B raw22175 raw22175Labels = mixedMoment B raw22175step0 raw22175step0Labels := by
      have hz : ∀ j, raw22175 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22175step0 = (fun i j => raw22175 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22175step0 raw22175; decide +kernel
      have hl : raw22175step0Labels = raw22175Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22175 raw22175Labels permutation434 hz
    mixedMoment B raw22175step0 raw22175step0Labels = mixedMoment B raw22175step1 raw22175step1Labels := by
      have ha : raw22175step1 = (fun i j => raw22175step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw22175step1 raw22175step0; decide +kernel
      have hl : raw22175step1Labels = raw22175step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22175step0 raw22175step0Labels permutation38 permutation7
    mixedMoment B raw22175step1 raw22175step1Labels = mixedMoment B raw22175step2 raw22175step2Labels := by
      have ha : raw22175step2 = -raw22175step1 := by apply Matrix.ext; change ∀ i j, raw22175step2 i j = -(raw22175step1 i j); unfold raw22175step2 raw22175step1; decide +kernel
      have hl : raw22175step2Labels = raw22175step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw22175step2 raw22175step2Labels = mixedMoment B raw22175step3 raw22175step3Labels := by
      have ha : raw22175step3 = raw22175step2 := by apply Matrix.ext; unfold raw22175step3 raw22175step2; decide +kernel
      have hl : raw22175step2Labels = labelEmbedding1 ∘ raw22175step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22175step2 raw22175step2Labels raw22175step3Labels labelEmbedding1 hl
    _ = mixedMoment B node806 node806Labels := by rfl

theorem canonical22176 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22176 raw22176Labels = mixedMoment B node663 node663Labels := by
  calc
    mixedMoment B raw22176 raw22176Labels = mixedMoment B raw22176step0 raw22176step0Labels := by
      have hz : ∀ j, raw22176 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22176step0 = (fun i j => raw22176 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22176step0 raw22176; decide +kernel
      have hl : raw22176step0Labels = raw22176Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22176 raw22176Labels permutation346 hz
    mixedMoment B raw22176step0 raw22176step0Labels = mixedMoment B raw22176step1 raw22176step1Labels := by
      have ha : raw22176step1 = (fun i j => raw22176step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw22176step1 raw22176step0; decide +kernel
      have hl : raw22176step1Labels = raw22176step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22176step0 raw22176step0Labels permutation38 permutation7
    mixedMoment B raw22176step1 raw22176step1Labels = mixedMoment B raw22176step2 raw22176step2Labels := by
      have ha : raw22176step2 = -raw22176step1 := by apply Matrix.ext; change ∀ i j, raw22176step2 i j = -(raw22176step1 i j); unfold raw22176step2 raw22176step1; decide +kernel
      have hl : raw22176step2Labels = raw22176step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw22176step2 raw22176step2Labels = mixedMoment B raw22176step3 raw22176step3Labels := by
      have ha : raw22176step3 = raw22176step2 := by apply Matrix.ext; unfold raw22176step3 raw22176step2; decide +kernel
      have hl : raw22176step2Labels = labelEmbedding1 ∘ raw22176step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22176step2 raw22176step2Labels raw22176step3Labels labelEmbedding1 hl
    _ = mixedMoment B node663 node663Labels := by rfl

theorem canonical22177 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22177 raw22177Labels = mixedMoment B node799 node799Labels := by
  calc
    mixedMoment B raw22177 raw22177Labels = mixedMoment B raw22177step0 raw22177step0Labels := by
      have hz : ∀ j, raw22177 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22177step0 = (fun i j => raw22177 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22177step0 raw22177; decide +kernel
      have hl : raw22177step0Labels = raw22177Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22177 raw22177Labels permutation346 hz
    mixedMoment B raw22177step0 raw22177step0Labels = mixedMoment B raw22177step1 raw22177step1Labels := by
      have ha : raw22177step1 = (fun i j => raw22177step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw22177step1 raw22177step0; decide +kernel
      have hl : raw22177step1Labels = raw22177step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22177step0 raw22177step0Labels permutation38 permutation7
    mixedMoment B raw22177step1 raw22177step1Labels = mixedMoment B raw22177step2 raw22177step2Labels := by
      have ha : raw22177step2 = -raw22177step1 := by apply Matrix.ext; change ∀ i j, raw22177step2 i j = -(raw22177step1 i j); unfold raw22177step2 raw22177step1; decide +kernel
      have hl : raw22177step2Labels = raw22177step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw22177step2 raw22177step2Labels = mixedMoment B raw22177step3 raw22177step3Labels := by
      have ha : raw22177step3 = raw22177step2 := by apply Matrix.ext; unfold raw22177step3 raw22177step2; decide +kernel
      have hl : raw22177step2Labels = labelEmbedding1 ∘ raw22177step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22177step2 raw22177step2Labels raw22177step3Labels labelEmbedding1 hl
    _ = mixedMoment B node799 node799Labels := by rfl

theorem canonical22178 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22178 raw22178Labels = mixedMoment B node748 node748Labels := by
  calc
    mixedMoment B raw22178 raw22178Labels = mixedMoment B raw22178step0 raw22178step0Labels := by
      have ha : raw22178step0 = (fun i j => raw22178 (permutation182 i) (permutation7 j)) := by apply Matrix.ext; unfold raw22178step0 raw22178; decide +kernel
      have hl : raw22178step0Labels = raw22178Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22178 raw22178Labels permutation182 permutation7
    mixedMoment B raw22178step0 raw22178step0Labels = mixedMoment B raw22178step1 raw22178step1Labels := by
      have ha : raw22178step1 = -raw22178step0 := by apply Matrix.ext; change ∀ i j, raw22178step1 i j = -(raw22178step0 i j); unfold raw22178step1 raw22178step0; decide +kernel
      have hl : raw22178step1Labels = raw22178step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw22178step1 raw22178step1Labels = mixedMoment B raw22178step2 raw22178step2Labels := by
      have ha : raw22178step2 = raw22178step1 := by apply Matrix.ext; unfold raw22178step2 raw22178step1; decide +kernel
      have hl : raw22178step1Labels = labelEmbedding1 ∘ raw22178step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22178step1 raw22178step1Labels raw22178step2Labels labelEmbedding1 hl
    _ = mixedMoment B node748 node748Labels := by rfl

theorem canonical22179 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22179 raw22179Labels = mixedMoment B node804 node804Labels := by
  calc
    mixedMoment B raw22179 raw22179Labels = mixedMoment B raw22179step0 raw22179step0Labels := by
      have hz : ∀ j, raw22179 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22179step0 = (fun i j => raw22179 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22179step0 raw22179; decide +kernel
      have hl : raw22179step0Labels = raw22179Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22179 raw22179Labels permutation346 hz
    mixedMoment B raw22179step0 raw22179step0Labels = mixedMoment B raw22179step1 raw22179step1Labels := by
      have ha : raw22179step1 = (fun i j => raw22179step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw22179step1 raw22179step0; decide +kernel
      have hl : raw22179step1Labels = raw22179step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22179step0 raw22179step0Labels permutation38 permutation7
    mixedMoment B raw22179step1 raw22179step1Labels = mixedMoment B raw22179step2 raw22179step2Labels := by
      have ha : raw22179step2 = -raw22179step1 := by apply Matrix.ext; change ∀ i j, raw22179step2 i j = -(raw22179step1 i j); unfold raw22179step2 raw22179step1; decide +kernel
      have hl : raw22179step2Labels = raw22179step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw22179step2 raw22179step2Labels = mixedMoment B raw22179step3 raw22179step3Labels := by
      have ha : raw22179step3 = raw22179step2 := by apply Matrix.ext; unfold raw22179step3 raw22179step2; decide +kernel
      have hl : raw22179step2Labels = labelEmbedding1 ∘ raw22179step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22179step2 raw22179step2Labels raw22179step3Labels labelEmbedding1 hl
    _ = mixedMoment B node804 node804Labels := by rfl

theorem canonical22180 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22180 raw22180Labels = mixedMoment B node806 node806Labels := by
  calc
    mixedMoment B raw22180 raw22180Labels = mixedMoment B raw22180step0 raw22180step0Labels := by
      have hz : ∀ j, raw22180 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22180step0 = (fun i j => raw22180 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22180step0 raw22180; decide +kernel
      have hl : raw22180step0Labels = raw22180Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22180 raw22180Labels permutation346 hz
    mixedMoment B raw22180step0 raw22180step0Labels = mixedMoment B raw22180step1 raw22180step1Labels := by
      have ha : raw22180step1 = (fun i j => raw22180step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw22180step1 raw22180step0; decide +kernel
      have hl : raw22180step1Labels = raw22180step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22180step0 raw22180step0Labels permutation38 permutation7
    mixedMoment B raw22180step1 raw22180step1Labels = mixedMoment B raw22180step2 raw22180step2Labels := by
      have ha : raw22180step2 = -raw22180step1 := by apply Matrix.ext; change ∀ i j, raw22180step2 i j = -(raw22180step1 i j); unfold raw22180step2 raw22180step1; decide +kernel
      have hl : raw22180step2Labels = raw22180step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw22180step2 raw22180step2Labels = mixedMoment B raw22180step3 raw22180step3Labels := by
      have ha : raw22180step3 = raw22180step2 := by apply Matrix.ext; unfold raw22180step3 raw22180step2; decide +kernel
      have hl : raw22180step2Labels = labelEmbedding1 ∘ raw22180step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22180step2 raw22180step2Labels raw22180step3Labels labelEmbedding1 hl
    _ = mixedMoment B node806 node806Labels := by rfl

theorem canonical22181 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22181 raw22181Labels = mixedMoment B node684 node684Labels := by
  calc
    mixedMoment B raw22181 raw22181Labels = mixedMoment B raw22181step0 raw22181step0Labels := by
      have hz : ∀ j, raw22181 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22181step0 = (fun i j => raw22181 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22181step0 raw22181; decide +kernel
      have hl : raw22181step0Labels = raw22181Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22181 raw22181Labels permutation434 hz
    mixedMoment B raw22181step0 raw22181step0Labels = mixedMoment B raw22181step1 raw22181step1Labels := by
      have hz : ∀ j, raw22181step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22181step1 = (fun i j => raw22181step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22181step1 raw22181step0; decide +kernel
      have hl : raw22181step1Labels = raw22181step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22181step0 raw22181step0Labels permutation80 hz
    mixedMoment B raw22181step1 raw22181step1Labels = mixedMoment B raw22181step2 raw22181step2Labels := by
      have ha : raw22181step2 = (fun i j => raw22181step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw22181step2 raw22181step1; decide +kernel
      have hl : raw22181step2Labels = raw22181step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22181step1 raw22181step1Labels permutation8 permutation7
    mixedMoment B raw22181step2 raw22181step2Labels = mixedMoment B raw22181step3 raw22181step3Labels := by
      have ha : raw22181step3 = -raw22181step2 := by apply Matrix.ext; change ∀ i j, raw22181step3 i j = -(raw22181step2 i j); unfold raw22181step3 raw22181step2; decide +kernel
      have hl : raw22181step3Labels = raw22181step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw22181step3 raw22181step3Labels = mixedMoment B raw22181step4 raw22181step4Labels := by
      have ha : raw22181step4 = raw22181step3 := by apply Matrix.ext; unfold raw22181step4 raw22181step3; decide +kernel
      have hl : raw22181step3Labels = labelEmbedding1 ∘ raw22181step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22181step3 raw22181step3Labels raw22181step4Labels labelEmbedding1 hl
    _ = mixedMoment B node684 node684Labels := by rfl

theorem canonical22182 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22182 raw22182Labels = mixedMoment B node843 node843Labels := by
  calc
    mixedMoment B raw22182 raw22182Labels = mixedMoment B raw22182step0 raw22182step0Labels := by
      have hz : ∀ j, raw22182 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22182step0 = (fun i j => raw22182 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22182step0 raw22182; decide +kernel
      have hl : raw22182step0Labels = raw22182Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22182 raw22182Labels permutation434 hz
    mixedMoment B raw22182step0 raw22182step0Labels = mixedMoment B raw22182step1 raw22182step1Labels := by
      have hz : ∀ j, raw22182step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22182step1 = (fun i j => raw22182step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22182step1 raw22182step0; decide +kernel
      have hl : raw22182step1Labels = raw22182step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22182step0 raw22182step0Labels permutation80 hz
    mixedMoment B raw22182step1 raw22182step1Labels = mixedMoment B raw22182step2 raw22182step2Labels := by
      have ha : raw22182step2 = (fun i j => raw22182step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw22182step2 raw22182step1; decide +kernel
      have hl : raw22182step2Labels = raw22182step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22182step1 raw22182step1Labels permutation8 permutation7
    mixedMoment B raw22182step2 raw22182step2Labels = mixedMoment B raw22182step3 raw22182step3Labels := by
      have ha : raw22182step3 = -raw22182step2 := by apply Matrix.ext; change ∀ i j, raw22182step3 i j = -(raw22182step2 i j); unfold raw22182step3 raw22182step2; decide +kernel
      have hl : raw22182step3Labels = raw22182step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw22182step3 raw22182step3Labels = mixedMoment B raw22182step4 raw22182step4Labels := by
      have ha : raw22182step4 = raw22182step3 := by apply Matrix.ext; unfold raw22182step4 raw22182step3; decide +kernel
      have hl : raw22182step3Labels = labelEmbedding1 ∘ raw22182step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22182step3 raw22182step3Labels raw22182step4Labels labelEmbedding1 hl
    _ = mixedMoment B node843 node843Labels := by rfl

theorem canonical22183 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22183 raw22183Labels = mixedMoment B node763 node763Labels := by
  calc
    mixedMoment B raw22183 raw22183Labels = mixedMoment B raw22183step0 raw22183step0Labels := by
      have hz : ∀ j, raw22183 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22183step0 = (fun i j => raw22183 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22183step0 raw22183; decide +kernel
      have hl : raw22183step0Labels = raw22183Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22183 raw22183Labels permutation434 hz
    mixedMoment B raw22183step0 raw22183step0Labels = mixedMoment B raw22183step1 raw22183step1Labels := by
      have ha : raw22183step1 = (fun i j => raw22183step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw22183step1 raw22183step0; decide +kernel
      have hl : raw22183step1Labels = raw22183step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22183step0 raw22183step0Labels permutation38 permutation7
    mixedMoment B raw22183step1 raw22183step1Labels = mixedMoment B raw22183step2 raw22183step2Labels := by
      have ha : raw22183step2 = -raw22183step1 := by apply Matrix.ext; change ∀ i j, raw22183step2 i j = -(raw22183step1 i j); unfold raw22183step2 raw22183step1; decide +kernel
      have hl : raw22183step2Labels = raw22183step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw22183step2 raw22183step2Labels = mixedMoment B raw22183step3 raw22183step3Labels := by
      have ha : raw22183step3 = raw22183step2 := by apply Matrix.ext; unfold raw22183step3 raw22183step2; decide +kernel
      have hl : raw22183step2Labels = labelEmbedding1 ∘ raw22183step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22183step2 raw22183step2Labels raw22183step3Labels labelEmbedding1 hl
    _ = mixedMoment B node763 node763Labels := by rfl

theorem canonical22184 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22184 raw22184Labels = mixedMoment B node763 node763Labels := by
  calc
    mixedMoment B raw22184 raw22184Labels = mixedMoment B raw22184step0 raw22184step0Labels := by
      have hz : ∀ j, raw22184 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22184step0 = (fun i j => raw22184 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22184step0 raw22184; decide +kernel
      have hl : raw22184step0Labels = raw22184Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22184 raw22184Labels permutation346 hz
    mixedMoment B raw22184step0 raw22184step0Labels = mixedMoment B raw22184step1 raw22184step1Labels := by
      have ha : raw22184step1 = (fun i j => raw22184step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw22184step1 raw22184step0; decide +kernel
      have hl : raw22184step1Labels = raw22184step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22184step0 raw22184step0Labels permutation38 permutation7
    mixedMoment B raw22184step1 raw22184step1Labels = mixedMoment B raw22184step2 raw22184step2Labels := by
      have ha : raw22184step2 = -raw22184step1 := by apply Matrix.ext; change ∀ i j, raw22184step2 i j = -(raw22184step1 i j); unfold raw22184step2 raw22184step1; decide +kernel
      have hl : raw22184step2Labels = raw22184step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw22184step2 raw22184step2Labels = mixedMoment B raw22184step3 raw22184step3Labels := by
      have ha : raw22184step3 = raw22184step2 := by apply Matrix.ext; unfold raw22184step3 raw22184step2; decide +kernel
      have hl : raw22184step2Labels = labelEmbedding1 ∘ raw22184step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22184step2 raw22184step2Labels raw22184step3Labels labelEmbedding1 hl
    _ = mixedMoment B node763 node763Labels := by rfl

theorem canonical22185 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22185 raw22185Labels = mixedMoment B node852 node852Labels := by
  calc
    mixedMoment B raw22185 raw22185Labels = mixedMoment B raw22185step0 raw22185step0Labels := by
      have hz : ∀ j, raw22185 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22185step0 = (fun i j => raw22185 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22185step0 raw22185; decide +kernel
      have hl : raw22185step0Labels = raw22185Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22185 raw22185Labels permutation434 hz
    mixedMoment B raw22185step0 raw22185step0Labels = mixedMoment B raw22185step1 raw22185step1Labels := by
      have hz : ∀ j, raw22185step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22185step1 = (fun i j => raw22185step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22185step1 raw22185step0; decide +kernel
      have hl : raw22185step1Labels = raw22185step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22185step0 raw22185step0Labels permutation80 hz
    mixedMoment B raw22185step1 raw22185step1Labels = mixedMoment B raw22185step2 raw22185step2Labels := by
      have ha : raw22185step2 = (fun i j => raw22185step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw22185step2 raw22185step1; decide +kernel
      have hl : raw22185step2Labels = raw22185step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22185step1 raw22185step1Labels permutation8 permutation7
    mixedMoment B raw22185step2 raw22185step2Labels = mixedMoment B raw22185step3 raw22185step3Labels := by
      have ha : raw22185step3 = -raw22185step2 := by apply Matrix.ext; change ∀ i j, raw22185step3 i j = -(raw22185step2 i j); unfold raw22185step3 raw22185step2; decide +kernel
      have hl : raw22185step3Labels = raw22185step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw22185step3 raw22185step3Labels = mixedMoment B raw22185step4 raw22185step4Labels := by
      have ha : raw22185step4 = raw22185step3 := by apply Matrix.ext; unfold raw22185step4 raw22185step3; decide +kernel
      have hl : raw22185step3Labels = labelEmbedding1 ∘ raw22185step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22185step3 raw22185step3Labels raw22185step4Labels labelEmbedding1 hl
    _ = mixedMoment B node852 node852Labels := by rfl

theorem canonical22186 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22186 raw22186Labels = mixedMoment B node683 node683Labels := by
  calc
    mixedMoment B raw22186 raw22186Labels = mixedMoment B raw22186step0 raw22186step0Labels := by
      have hz : ∀ j, raw22186 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22186step0 = (fun i j => raw22186 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22186step0 raw22186; decide +kernel
      have hl : raw22186step0Labels = raw22186Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22186 raw22186Labels permutation434 hz
    mixedMoment B raw22186step0 raw22186step0Labels = mixedMoment B raw22186step1 raw22186step1Labels := by
      have hz : ∀ j, raw22186step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22186step1 = (fun i j => raw22186step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22186step1 raw22186step0; decide +kernel
      have hl : raw22186step1Labels = raw22186step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22186step0 raw22186step0Labels permutation80 hz
    mixedMoment B raw22186step1 raw22186step1Labels = mixedMoment B raw22186step2 raw22186step2Labels := by
      have ha : raw22186step2 = (fun i j => raw22186step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw22186step2 raw22186step1; decide +kernel
      have hl : raw22186step2Labels = raw22186step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22186step1 raw22186step1Labels permutation8 permutation7
    mixedMoment B raw22186step2 raw22186step2Labels = mixedMoment B raw22186step3 raw22186step3Labels := by
      have ha : raw22186step3 = -raw22186step2 := by apply Matrix.ext; change ∀ i j, raw22186step3 i j = -(raw22186step2 i j); unfold raw22186step3 raw22186step2; decide +kernel
      have hl : raw22186step3Labels = raw22186step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw22186step3 raw22186step3Labels = mixedMoment B raw22186step4 raw22186step4Labels := by
      have ha : raw22186step4 = raw22186step3 := by apply Matrix.ext; unfold raw22186step4 raw22186step3; decide +kernel
      have hl : raw22186step3Labels = labelEmbedding1 ∘ raw22186step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22186step3 raw22186step3Labels raw22186step4Labels labelEmbedding1 hl
    _ = mixedMoment B node683 node683Labels := by rfl

theorem canonical22187 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22187 raw22187Labels = mixedMoment B node842 node842Labels := by
  calc
    mixedMoment B raw22187 raw22187Labels = mixedMoment B raw22187step0 raw22187step0Labels := by
      have hz : ∀ j, raw22187 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22187step0 = (fun i j => raw22187 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22187step0 raw22187; decide +kernel
      have hl : raw22187step0Labels = raw22187Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22187 raw22187Labels permutation434 hz
    mixedMoment B raw22187step0 raw22187step0Labels = mixedMoment B raw22187step1 raw22187step1Labels := by
      have hz : ∀ j, raw22187step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22187step1 = (fun i j => raw22187step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22187step1 raw22187step0; decide +kernel
      have hl : raw22187step1Labels = raw22187step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22187step0 raw22187step0Labels permutation80 hz
    mixedMoment B raw22187step1 raw22187step1Labels = mixedMoment B raw22187step2 raw22187step2Labels := by
      have ha : raw22187step2 = (fun i j => raw22187step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw22187step2 raw22187step1; decide +kernel
      have hl : raw22187step2Labels = raw22187step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22187step1 raw22187step1Labels permutation8 permutation7
    mixedMoment B raw22187step2 raw22187step2Labels = mixedMoment B raw22187step3 raw22187step3Labels := by
      have ha : raw22187step3 = -raw22187step2 := by apply Matrix.ext; change ∀ i j, raw22187step3 i j = -(raw22187step2 i j); unfold raw22187step3 raw22187step2; decide +kernel
      have hl : raw22187step3Labels = raw22187step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw22187step3 raw22187step3Labels = mixedMoment B raw22187step4 raw22187step4Labels := by
      have ha : raw22187step4 = raw22187step3 := by apply Matrix.ext; unfold raw22187step4 raw22187step3; decide +kernel
      have hl : raw22187step3Labels = labelEmbedding1 ∘ raw22187step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22187step3 raw22187step3Labels raw22187step4Labels labelEmbedding1 hl
    _ = mixedMoment B node842 node842Labels := by rfl

theorem canonical22188 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22188 raw22188Labels = mixedMoment B node762 node762Labels := by
  calc
    mixedMoment B raw22188 raw22188Labels = mixedMoment B raw22188step0 raw22188step0Labels := by
      have hz : ∀ j, raw22188 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22188step0 = (fun i j => raw22188 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22188step0 raw22188; decide +kernel
      have hl : raw22188step0Labels = raw22188Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22188 raw22188Labels permutation434 hz
    mixedMoment B raw22188step0 raw22188step0Labels = mixedMoment B raw22188step1 raw22188step1Labels := by
      have ha : raw22188step1 = (fun i j => raw22188step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw22188step1 raw22188step0; decide +kernel
      have hl : raw22188step1Labels = raw22188step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22188step0 raw22188step0Labels permutation38 permutation7
    mixedMoment B raw22188step1 raw22188step1Labels = mixedMoment B raw22188step2 raw22188step2Labels := by
      have ha : raw22188step2 = -raw22188step1 := by apply Matrix.ext; change ∀ i j, raw22188step2 i j = -(raw22188step1 i j); unfold raw22188step2 raw22188step1; decide +kernel
      have hl : raw22188step2Labels = raw22188step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw22188step2 raw22188step2Labels = mixedMoment B raw22188step3 raw22188step3Labels := by
      have ha : raw22188step3 = raw22188step2 := by apply Matrix.ext; unfold raw22188step3 raw22188step2; decide +kernel
      have hl : raw22188step2Labels = labelEmbedding1 ∘ raw22188step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22188step2 raw22188step2Labels raw22188step3Labels labelEmbedding1 hl
    _ = mixedMoment B node762 node762Labels := by rfl

theorem canonical22189 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22189 raw22189Labels = mixedMoment B node762 node762Labels := by
  calc
    mixedMoment B raw22189 raw22189Labels = mixedMoment B raw22189step0 raw22189step0Labels := by
      have hz : ∀ j, raw22189 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22189step0 = (fun i j => raw22189 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22189step0 raw22189; decide +kernel
      have hl : raw22189step0Labels = raw22189Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22189 raw22189Labels permutation346 hz
    mixedMoment B raw22189step0 raw22189step0Labels = mixedMoment B raw22189step1 raw22189step1Labels := by
      have ha : raw22189step1 = (fun i j => raw22189step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw22189step1 raw22189step0; decide +kernel
      have hl : raw22189step1Labels = raw22189step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22189step0 raw22189step0Labels permutation38 permutation7
    mixedMoment B raw22189step1 raw22189step1Labels = mixedMoment B raw22189step2 raw22189step2Labels := by
      have ha : raw22189step2 = -raw22189step1 := by apply Matrix.ext; change ∀ i j, raw22189step2 i j = -(raw22189step1 i j); unfold raw22189step2 raw22189step1; decide +kernel
      have hl : raw22189step2Labels = raw22189step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw22189step2 raw22189step2Labels = mixedMoment B raw22189step3 raw22189step3Labels := by
      have ha : raw22189step3 = raw22189step2 := by apply Matrix.ext; unfold raw22189step3 raw22189step2; decide +kernel
      have hl : raw22189step2Labels = labelEmbedding1 ∘ raw22189step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22189step2 raw22189step2Labels raw22189step3Labels labelEmbedding1 hl
    _ = mixedMoment B node762 node762Labels := by rfl

theorem canonical22190 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22190 raw22190Labels = mixedMoment B node849 node849Labels := by
  calc
    mixedMoment B raw22190 raw22190Labels = mixedMoment B raw22190step0 raw22190step0Labels := by
      have hz : ∀ j, raw22190 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22190step0 = (fun i j => raw22190 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22190step0 raw22190; decide +kernel
      have hl : raw22190step0Labels = raw22190Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22190 raw22190Labels permutation434 hz
    mixedMoment B raw22190step0 raw22190step0Labels = mixedMoment B raw22190step1 raw22190step1Labels := by
      have hz : ∀ j, raw22190step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22190step1 = (fun i j => raw22190step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22190step1 raw22190step0; decide +kernel
      have hl : raw22190step1Labels = raw22190step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22190step0 raw22190step0Labels permutation80 hz
    mixedMoment B raw22190step1 raw22190step1Labels = mixedMoment B raw22190step2 raw22190step2Labels := by
      have ha : raw22190step2 = (fun i j => raw22190step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw22190step2 raw22190step1; decide +kernel
      have hl : raw22190step2Labels = raw22190step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22190step1 raw22190step1Labels permutation8 permutation7
    mixedMoment B raw22190step2 raw22190step2Labels = mixedMoment B raw22190step3 raw22190step3Labels := by
      have ha : raw22190step3 = -raw22190step2 := by apply Matrix.ext; change ∀ i j, raw22190step3 i j = -(raw22190step2 i j); unfold raw22190step3 raw22190step2; decide +kernel
      have hl : raw22190step3Labels = raw22190step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw22190step3 raw22190step3Labels = mixedMoment B raw22190step4 raw22190step4Labels := by
      have ha : raw22190step4 = raw22190step3 := by apply Matrix.ext; unfold raw22190step4 raw22190step3; decide +kernel
      have hl : raw22190step3Labels = labelEmbedding1 ∘ raw22190step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22190step3 raw22190step3Labels raw22190step4Labels labelEmbedding1 hl
    _ = mixedMoment B node849 node849Labels := by rfl

theorem canonical22191 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22191 raw22191Labels = mixedMoment B node812 node812Labels := by
  calc
    mixedMoment B raw22191 raw22191Labels = mixedMoment B raw22191step0 raw22191step0Labels := by
      have hz : ∀ j, raw22191 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22191step0 = (fun i j => raw22191 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22191step0 raw22191; decide +kernel
      have hl : raw22191step0Labels = raw22191Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22191 raw22191Labels permutation434 hz
    mixedMoment B raw22191step0 raw22191step0Labels = mixedMoment B raw22191step1 raw22191step1Labels := by
      have hz : ∀ j, raw22191step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22191step1 = (fun i j => raw22191step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22191step1 raw22191step0; decide +kernel
      have hl : raw22191step1Labels = raw22191step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22191step0 raw22191step0Labels permutation80 hz
    _ = mixedMoment B node812 node812Labels := by rfl

theorem canonical22192 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22192 raw22192Labels = mixedMoment B node1650 node1650Labels := by
  calc
    mixedMoment B raw22192 raw22192Labels = mixedMoment B raw22192step0 raw22192step0Labels := by
      have hz : ∀ j, raw22192 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22192step0 = (fun i j => raw22192 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22192step0 raw22192; decide +kernel
      have hl : raw22192step0Labels = raw22192Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22192 raw22192Labels permutation434 hz
    mixedMoment B raw22192step0 raw22192step0Labels = mixedMoment B raw22192step1 raw22192step1Labels := by
      have hz : ∀ j, raw22192step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22192step1 = (fun i j => raw22192step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22192step1 raw22192step0; decide +kernel
      have hl : raw22192step1Labels = raw22192step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22192step0 raw22192step0Labels permutation80 hz
    _ = mixedMoment B node1650 node1650Labels := by rfl

theorem canonical22193 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22193 raw22193Labels = mixedMoment B node1602 node1602Labels := by
  calc
    mixedMoment B raw22193 raw22193Labels = mixedMoment B raw22193step0 raw22193step0Labels := by
      have hz : ∀ j, raw22193 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22193step0 = (fun i j => raw22193 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22193step0 raw22193; decide +kernel
      have hl : raw22193step0Labels = raw22193Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22193 raw22193Labels permutation434 hz
    mixedMoment B raw22193step0 raw22193step0Labels = mixedMoment B raw22193step1 raw22193step1Labels := by
      have ha : raw22193step1 = (fun i j => raw22193step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22193step1 raw22193step0; decide +kernel
      have hl : raw22193step1Labels = raw22193step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22193step0 raw22193step0Labels permutation38 permutation2
    _ = mixedMoment B node1602 node1602Labels := by rfl

theorem canonical22194 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22194 raw22194Labels = mixedMoment B node1602 node1602Labels := by
  calc
    mixedMoment B raw22194 raw22194Labels = mixedMoment B raw22194step0 raw22194step0Labels := by
      have hz : ∀ j, raw22194 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22194step0 = (fun i j => raw22194 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22194step0 raw22194; decide +kernel
      have hl : raw22194step0Labels = raw22194Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22194 raw22194Labels permutation346 hz
    mixedMoment B raw22194step0 raw22194step0Labels = mixedMoment B raw22194step1 raw22194step1Labels := by
      have ha : raw22194step1 = (fun i j => raw22194step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22194step1 raw22194step0; decide +kernel
      have hl : raw22194step1Labels = raw22194step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22194step0 raw22194step0Labels permutation38 permutation2
    _ = mixedMoment B node1602 node1602Labels := by rfl

theorem canonical22195 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22195 raw22195Labels = mixedMoment B node1710 node1710Labels := by
  calc
    mixedMoment B raw22195 raw22195Labels = mixedMoment B raw22195step0 raw22195step0Labels := by
      have hz : ∀ j, raw22195 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22195step0 = (fun i j => raw22195 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22195step0 raw22195; decide +kernel
      have hl : raw22195step0Labels = raw22195Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22195 raw22195Labels permutation434 hz
    mixedMoment B raw22195step0 raw22195step0Labels = mixedMoment B raw22195step1 raw22195step1Labels := by
      have hz : ∀ j, raw22195step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22195step1 = (fun i j => raw22195step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22195step1 raw22195step0; decide +kernel
      have hl : raw22195step1Labels = raw22195step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22195step0 raw22195step0Labels permutation80 hz
    _ = mixedMoment B node1710 node1710Labels := by rfl

theorem canonical22196 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22196 raw22196Labels = mixedMoment B node1727 node1727Labels := by
  calc
    mixedMoment B raw22196 raw22196Labels = mixedMoment B raw22196step0 raw22196step0Labels := by
      have hz : ∀ j, raw22196 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22196step0 = (fun i j => raw22196 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22196step0 raw22196; decide +kernel
      have hl : raw22196step0Labels = raw22196Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22196 raw22196Labels permutation434 hz
    mixedMoment B raw22196step0 raw22196step0Labels = mixedMoment B raw22196step1 raw22196step1Labels := by
      have hz : ∀ j, raw22196step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22196step1 = (fun i j => raw22196step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22196step1 raw22196step0; decide +kernel
      have hl : raw22196step1Labels = raw22196step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22196step0 raw22196step0Labels permutation80 hz
    _ = mixedMoment B node1727 node1727Labels := by rfl

theorem canonical22197 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22197 raw22197Labels = mixedMoment B node4069 node4069Labels := by
  calc
    mixedMoment B raw22197 raw22197Labels = mixedMoment B raw22197step0 raw22197step0Labels := by
      have hz : ∀ j, raw22197 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22197step0 = (fun i j => raw22197 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22197step0 raw22197; decide +kernel
      have hl : raw22197step0Labels = raw22197Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22197 raw22197Labels permutation434 hz
    mixedMoment B raw22197step0 raw22197step0Labels = mixedMoment B raw22197step1 raw22197step1Labels := by
      have hz : ∀ j, raw22197step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22197step1 = (fun i j => raw22197step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22197step1 raw22197step0; decide +kernel
      have hl : raw22197step1Labels = raw22197step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22197step0 raw22197step0Labels permutation80 hz
    _ = mixedMoment B node4069 node4069Labels := by rfl

theorem canonical22203 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22203 raw22203Labels = mixedMoment B node733 node733Labels := by
  calc
    mixedMoment B raw22203 raw22203Labels = mixedMoment B raw22203step0 raw22203step0Labels := by
      have hz : ∀ j, raw22203 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22203step0 = (fun i j => raw22203 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22203step0 raw22203; decide +kernel
      have hl : raw22203step0Labels = raw22203Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22203 raw22203Labels permutation434 hz
    _ = mixedMoment B node733 node733Labels := by rfl

theorem canonical22204 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22204 raw22204Labels = mixedMoment B node733 node733Labels := by
  calc
    mixedMoment B raw22204 raw22204Labels = mixedMoment B raw22204step0 raw22204step0Labels := by
      have hz : ∀ j, raw22204 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22204step0 = (fun i j => raw22204 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22204step0 raw22204; decide +kernel
      have hl : raw22204step0Labels = raw22204Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22204 raw22204Labels permutation346 hz
    _ = mixedMoment B node733 node733Labels := by rfl

theorem canonical22205 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22205 raw22205Labels = mixedMoment B node742 node742Labels := by
  calc
    mixedMoment B raw22205 raw22205Labels = mixedMoment B raw22205step0 raw22205step0Labels := by
      have hz : ∀ j, raw22205 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22205step0 = (fun i j => raw22205 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22205step0 raw22205; decide +kernel
      have hl : raw22205step0Labels = raw22205Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22205 raw22205Labels permutation434 hz
    mixedMoment B raw22205step0 raw22205step0Labels = mixedMoment B raw22205step1 raw22205step1Labels := by
      have hz : ∀ j, raw22205step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22205step1 = (fun i j => raw22205step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22205step1 raw22205step0; decide +kernel
      have hl : raw22205step1Labels = raw22205step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22205step0 raw22205step0Labels permutation80 hz
    _ = mixedMoment B node742 node742Labels := by rfl

theorem canonical22206 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22206 raw22206Labels = mixedMoment B node740 node740Labels := by
  calc
    mixedMoment B raw22206 raw22206Labels = mixedMoment B raw22206step0 raw22206step0Labels := by
      have hz : ∀ j, raw22206 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22206step0 = (fun i j => raw22206 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22206step0 raw22206; decide +kernel
      have hl : raw22206step0Labels = raw22206Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22206 raw22206Labels permutation434 hz
    mixedMoment B raw22206step0 raw22206step0Labels = mixedMoment B raw22206step1 raw22206step1Labels := by
      have hz : ∀ j, raw22206step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22206step1 = (fun i j => raw22206step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22206step1 raw22206step0; decide +kernel
      have hl : raw22206step1Labels = raw22206step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22206step0 raw22206step0Labels permutation80 hz
    _ = mixedMoment B node740 node740Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical5
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical675 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw675 raw675Labels = mixedMoment B node4101 node4101Labels := by
  calc
    mixedMoment B raw675 raw675Labels = mixedMoment B raw675step0 raw675step0Labels := by
      have ha : raw675step0 = (fun i j => raw675 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw675step0 raw675; decide +kernel
      have hl : raw675step0Labels = raw675Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw675 raw675Labels permutation32 permutation4
    mixedMoment B raw675step0 raw675step0Labels = mixedMoment B raw675step1 raw675step1Labels := by
      have ha : raw675step1 = raw675step0 := by apply Matrix.ext; unfold raw675step1 raw675step0; decide +kernel
      have hl : raw675step0Labels = labelEmbedding7 ∘ raw675step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw675step0 raw675step0Labels raw675step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4101 node4101Labels := by rfl

theorem canonical676 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw676 raw676Labels = mixedMoment B node538 node538Labels := by
  calc
    mixedMoment B raw676 raw676Labels = mixedMoment B raw676step0 raw676step0Labels := by
      have ha : raw676step0 = (fun i j => raw676 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw676step0 raw676; decide +kernel
      have hl : raw676step0Labels = raw676Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw676 raw676Labels permutation32 permutation4
    _ = mixedMoment B node538 node538Labels := by rfl

theorem canonical677 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw677 raw677Labels = mixedMoment B node663 node663Labels := by
  calc
    mixedMoment B raw677 raw677Labels = mixedMoment B raw677step0 raw677step0Labels := by
      have ha : raw677step0 = (fun i j => raw677 (permutation38 i) (permutation6 j)) := by apply Matrix.ext; unfold raw677step0 raw677; decide +kernel
      have hl : raw677step0Labels = raw677Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw677 raw677Labels permutation38 permutation6
    mixedMoment B raw677step0 raw677step0Labels = mixedMoment B raw677step1 raw677step1Labels := by
      have ha : raw677step1 = -raw677step0 := by apply Matrix.ext; change ∀ i j, raw677step1 i j = -(raw677step0 i j); unfold raw677step1 raw677step0; decide +kernel
      have hl : raw677step1Labels = raw677step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw677step1 raw677step1Labels = mixedMoment B raw677step2 raw677step2Labels := by
      have ha : raw677step2 = raw677step1 := by apply Matrix.ext; unfold raw677step2 raw677step1; decide +kernel
      have hl : raw677step1Labels = labelEmbedding1 ∘ raw677step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw677step1 raw677step1Labels raw677step2Labels labelEmbedding1 hl
    _ = mixedMoment B node663 node663Labels := by rfl

theorem canonical696 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw696 raw696Labels = mixedMoment B node4108 node4108Labels := by
  calc
    mixedMoment B raw696 raw696Labels = mixedMoment B raw696step0 raw696step0Labels := by
      have ha : raw696step0 = (fun i j => raw696 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw696step0 raw696; decide +kernel
      have hl : raw696step0Labels = raw696Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw696 raw696Labels permutation8 permutation4
    mixedMoment B raw696step0 raw696step0Labels = mixedMoment B raw696step1 raw696step1Labels := by
      have ha : raw696step1 = raw696step0 := by apply Matrix.ext; unfold raw696step1 raw696step0; decide +kernel
      have hl : raw696step0Labels = labelEmbedding7 ∘ raw696step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw696step0 raw696step0Labels raw696step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4108 node4108Labels := by rfl

theorem canonical697 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw697 raw697Labels = mixedMoment B node545 node545Labels := by
  calc
    mixedMoment B raw697 raw697Labels = mixedMoment B raw697step0 raw697step0Labels := by
      have ha : raw697step0 = (fun i j => raw697 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw697step0 raw697; decide +kernel
      have hl : raw697step0Labels = raw697Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw697 raw697Labels permutation8 permutation4
    _ = mixedMoment B node545 node545Labels := by rfl

theorem canonical698 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw698 raw698Labels = mixedMoment B node683 node683Labels := by
  calc
    mixedMoment B raw698 raw698Labels = mixedMoment B raw698step0 raw698step0Labels := by
      have ha : raw698step0 = (fun i j => raw698 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw698step0 raw698; decide +kernel
      have hl : raw698step0Labels = raw698Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw698 raw698Labels permutation8 permutation6
    mixedMoment B raw698step0 raw698step0Labels = mixedMoment B raw698step1 raw698step1Labels := by
      have ha : raw698step1 = -raw698step0 := by apply Matrix.ext; change ∀ i j, raw698step1 i j = -(raw698step0 i j); unfold raw698step1 raw698step0; decide +kernel
      have hl : raw698step1Labels = raw698step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw698step1 raw698step1Labels = mixedMoment B raw698step2 raw698step2Labels := by
      have ha : raw698step2 = raw698step1 := by apply Matrix.ext; unfold raw698step2 raw698step1; decide +kernel
      have hl : raw698step1Labels = labelEmbedding1 ∘ raw698step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw698step1 raw698step1Labels raw698step2Labels labelEmbedding1 hl
    _ = mixedMoment B node683 node683Labels := by rfl

theorem canonical702 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw702 raw702Labels = mixedMoment B node4110 node4110Labels := by
  calc
    mixedMoment B raw702 raw702Labels = mixedMoment B raw702step0 raw702step0Labels := by
      have ha : raw702step0 = (fun i j => raw702 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw702step0 raw702; decide +kernel
      have hl : raw702step0Labels = raw702Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw702 raw702Labels permutation8 permutation4
    mixedMoment B raw702step0 raw702step0Labels = mixedMoment B raw702step1 raw702step1Labels := by
      have ha : raw702step1 = raw702step0 := by apply Matrix.ext; unfold raw702step1 raw702step0; decide +kernel
      have hl : raw702step0Labels = labelEmbedding7 ∘ raw702step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw702step0 raw702step0Labels raw702step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4110 node4110Labels := by rfl

theorem canonical703 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw703 raw703Labels = mixedMoment B node547 node547Labels := by
  calc
    mixedMoment B raw703 raw703Labels = mixedMoment B raw703step0 raw703step0Labels := by
      have ha : raw703step0 = (fun i j => raw703 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw703step0 raw703; decide +kernel
      have hl : raw703step0Labels = raw703Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw703 raw703Labels permutation8 permutation4
    _ = mixedMoment B node547 node547Labels := by rfl

theorem canonical704 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw704 raw704Labels = mixedMoment B node684 node684Labels := by
  calc
    mixedMoment B raw704 raw704Labels = mixedMoment B raw704step0 raw704step0Labels := by
      have ha : raw704step0 = (fun i j => raw704 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw704step0 raw704; decide +kernel
      have hl : raw704step0Labels = raw704Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw704 raw704Labels permutation8 permutation6
    mixedMoment B raw704step0 raw704step0Labels = mixedMoment B raw704step1 raw704step1Labels := by
      have ha : raw704step1 = -raw704step0 := by apply Matrix.ext; change ∀ i j, raw704step1 i j = -(raw704step0 i j); unfold raw704step1 raw704step0; decide +kernel
      have hl : raw704step1Labels = raw704step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw704step1 raw704step1Labels = mixedMoment B raw704step2 raw704step2Labels := by
      have ha : raw704step2 = raw704step1 := by apply Matrix.ext; unfold raw704step2 raw704step1; decide +kernel
      have hl : raw704step1Labels = labelEmbedding1 ∘ raw704step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw704step1 raw704step1Labels raw704step2Labels labelEmbedding1 hl
    _ = mixedMoment B node684 node684Labels := by rfl

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

theorem canonical852 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw852 raw852Labels = mixedMoment B node4196 node4196Labels := by
  calc
    mixedMoment B raw852 raw852Labels = mixedMoment B raw852step0 raw852step0Labels := by
      have ha : raw852step0 = (fun i j => raw852 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw852step0 raw852; decide +kernel
      have hl : raw852step0Labels = raw852Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw852 raw852Labels permutation152 permutation4
    mixedMoment B raw852step0 raw852step0Labels = mixedMoment B raw852step1 raw852step1Labels := by
      have ha : raw852step1 = raw852step0 := by apply Matrix.ext; unfold raw852step1 raw852step0; decide +kernel
      have hl : raw852step0Labels = labelEmbedding7 ∘ raw852step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw852step0 raw852step0Labels raw852step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4196 node4196Labels := by rfl

theorem canonical853 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw853 raw853Labels = mixedMoment B node699 node699Labels := by
  calc
    mixedMoment B raw853 raw853Labels = mixedMoment B raw853step0 raw853step0Labels := by
      have ha : raw853step0 = (fun i j => raw853 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw853step0 raw853; decide +kernel
      have hl : raw853step0Labels = raw853Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw853 raw853Labels permutation152 permutation4
    _ = mixedMoment B node699 node699Labels := by rfl

theorem canonical854 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw854 raw854Labels = mixedMoment B node748 node748Labels := by
  calc
    mixedMoment B raw854 raw854Labels = mixedMoment B raw854step0 raw854step0Labels := by
      have ha : raw854step0 = (fun i j => raw854 (permutation158 i) (permutation6 j)) := by apply Matrix.ext; unfold raw854step0 raw854; decide +kernel
      have hl : raw854step0Labels = raw854Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw854 raw854Labels permutation158 permutation6
    mixedMoment B raw854step0 raw854step0Labels = mixedMoment B raw854step1 raw854step1Labels := by
      have ha : raw854step1 = -raw854step0 := by apply Matrix.ext; change ∀ i j, raw854step1 i j = -(raw854step0 i j); unfold raw854step1 raw854step0; decide +kernel
      have hl : raw854step1Labels = raw854step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw854step1 raw854step1Labels = mixedMoment B raw854step2 raw854step2Labels := by
      have ha : raw854step2 = raw854step1 := by apply Matrix.ext; unfold raw854step2 raw854step1; decide +kernel
      have hl : raw854step1Labels = labelEmbedding1 ∘ raw854step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw854step1 raw854step1Labels raw854step2Labels labelEmbedding1 hl
    _ = mixedMoment B node748 node748Labels := by rfl

theorem canonical870 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw870 raw870Labels = mixedMoment B node4202 node4202Labels := by
  calc
    mixedMoment B raw870 raw870Labels = mixedMoment B raw870step0 raw870step0Labels := by
      have ha : raw870step0 = (fun i j => raw870 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw870step0 raw870; decide +kernel
      have hl : raw870step0Labels = raw870Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw870 raw870Labels permutation32 permutation4
    mixedMoment B raw870step0 raw870step0Labels = mixedMoment B raw870step1 raw870step1Labels := by
      have ha : raw870step1 = raw870step0 := by apply Matrix.ext; unfold raw870step1 raw870step0; decide +kernel
      have hl : raw870step0Labels = labelEmbedding7 ∘ raw870step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw870step0 raw870step0Labels raw870step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4202 node4202Labels := by rfl

theorem canonical871 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw871 raw871Labels = mixedMoment B node705 node705Labels := by
  calc
    mixedMoment B raw871 raw871Labels = mixedMoment B raw871step0 raw871step0Labels := by
      have ha : raw871step0 = (fun i j => raw871 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw871step0 raw871; decide +kernel
      have hl : raw871step0Labels = raw871Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw871 raw871Labels permutation32 permutation4
    _ = mixedMoment B node705 node705Labels := by rfl

theorem canonical872 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw872 raw872Labels = mixedMoment B node762 node762Labels := by
  calc
    mixedMoment B raw872 raw872Labels = mixedMoment B raw872step0 raw872step0Labels := by
      have ha : raw872step0 = (fun i j => raw872 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw872step0 raw872; decide +kernel
      have hl : raw872step0Labels = raw872Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw872 raw872Labels permutation32 permutation6
    mixedMoment B raw872step0 raw872step0Labels = mixedMoment B raw872step1 raw872step1Labels := by
      have ha : raw872step1 = -raw872step0 := by apply Matrix.ext; change ∀ i j, raw872step1 i j = -(raw872step0 i j); unfold raw872step1 raw872step0; decide +kernel
      have hl : raw872step1Labels = raw872step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw872step1 raw872step1Labels = mixedMoment B raw872step2 raw872step2Labels := by
      have ha : raw872step2 = raw872step1 := by apply Matrix.ext; unfold raw872step2 raw872step1; decide +kernel
      have hl : raw872step1Labels = labelEmbedding1 ∘ raw872step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw872step1 raw872step1Labels raw872step2Labels labelEmbedding1 hl
    _ = mixedMoment B node762 node762Labels := by rfl

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

theorem canonical933 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw933 raw933Labels = mixedMoment B node4233 node4233Labels := by
  calc
    mixedMoment B raw933 raw933Labels = mixedMoment B raw933step0 raw933step0Labels := by
      have ha : raw933step0 = (fun i j => raw933 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw933step0 raw933; decide +kernel
      have hl : raw933step0Labels = raw933Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw933 raw933Labels permutation32 permutation4
    mixedMoment B raw933step0 raw933step0Labels = mixedMoment B raw933step1 raw933step1Labels := by
      have ha : raw933step1 = raw933step0 := by apply Matrix.ext; unfold raw933step1 raw933step0; decide +kernel
      have hl : raw933step0Labels = labelEmbedding7 ∘ raw933step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw933step0 raw933step0Labels raw933step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4233 node4233Labels := by rfl

theorem canonical934 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw934 raw934Labels = mixedMoment B node733 node733Labels := by
  calc
    mixedMoment B raw934 raw934Labels = mixedMoment B raw934step0 raw934step0Labels := by
      have ha : raw934step0 = (fun i j => raw934 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw934step0 raw934; decide +kernel
      have hl : raw934step0Labels = raw934Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw934 raw934Labels permutation32 permutation4
    _ = mixedMoment B node733 node733Labels := by rfl

theorem canonical935 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw935 raw935Labels = mixedMoment B node799 node799Labels := by
  calc
    mixedMoment B raw935 raw935Labels = mixedMoment B raw935step0 raw935step0Labels := by
      have ha : raw935step0 = (fun i j => raw935 (permutation38 i) (permutation6 j)) := by apply Matrix.ext; unfold raw935step0 raw935; decide +kernel
      have hl : raw935step0Labels = raw935Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw935 raw935Labels permutation38 permutation6
    mixedMoment B raw935step0 raw935step0Labels = mixedMoment B raw935step1 raw935step1Labels := by
      have ha : raw935step1 = -raw935step0 := by apply Matrix.ext; change ∀ i j, raw935step1 i j = -(raw935step0 i j); unfold raw935step1 raw935step0; decide +kernel
      have hl : raw935step1Labels = raw935step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw935step1 raw935step1Labels = mixedMoment B raw935step2 raw935step2Labels := by
      have ha : raw935step2 = raw935step1 := by apply Matrix.ext; unfold raw935step2 raw935step1; decide +kernel
      have hl : raw935step1Labels = labelEmbedding1 ∘ raw935step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw935step1 raw935step1Labels raw935step2Labels labelEmbedding1 hl
    _ = mixedMoment B node799 node799Labels := by rfl

theorem canonical954 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw954 raw954Labels = mixedMoment B node4240 node4240Labels := by
  calc
    mixedMoment B raw954 raw954Labels = mixedMoment B raw954step0 raw954step0Labels := by
      have ha : raw954step0 = (fun i j => raw954 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw954step0 raw954; decide +kernel
      have hl : raw954step0Labels = raw954Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw954 raw954Labels permutation8 permutation4
    mixedMoment B raw954step0 raw954step0Labels = mixedMoment B raw954step1 raw954step1Labels := by
      have ha : raw954step1 = raw954step0 := by apply Matrix.ext; unfold raw954step1 raw954step0; decide +kernel
      have hl : raw954step0Labels = labelEmbedding7 ∘ raw954step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw954step0 raw954step0Labels raw954step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4240 node4240Labels := by rfl

theorem canonical955 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw955 raw955Labels = mixedMoment B node740 node740Labels := by
  calc
    mixedMoment B raw955 raw955Labels = mixedMoment B raw955step0 raw955step0Labels := by
      have ha : raw955step0 = (fun i j => raw955 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw955step0 raw955; decide +kernel
      have hl : raw955step0Labels = raw955Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw955 raw955Labels permutation8 permutation4
    _ = mixedMoment B node740 node740Labels := by rfl

theorem canonical956 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw956 raw956Labels = mixedMoment B node842 node842Labels := by
  calc
    mixedMoment B raw956 raw956Labels = mixedMoment B raw956step0 raw956step0Labels := by
      have ha : raw956step0 = (fun i j => raw956 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw956step0 raw956; decide +kernel
      have hl : raw956step0Labels = raw956Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw956 raw956Labels permutation8 permutation6
    mixedMoment B raw956step0 raw956step0Labels = mixedMoment B raw956step1 raw956step1Labels := by
      have ha : raw956step1 = -raw956step0 := by apply Matrix.ext; change ∀ i j, raw956step1 i j = -(raw956step0 i j); unfold raw956step1 raw956step0; decide +kernel
      have hl : raw956step1Labels = raw956step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw956step1 raw956step1Labels = mixedMoment B raw956step2 raw956step2Labels := by
      have ha : raw956step2 = raw956step1 := by apply Matrix.ext; unfold raw956step2 raw956step1; decide +kernel
      have hl : raw956step1Labels = labelEmbedding1 ∘ raw956step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw956step1 raw956step1Labels raw956step2Labels labelEmbedding1 hl
    _ = mixedMoment B node842 node842Labels := by rfl

theorem canonical960 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw960 raw960Labels = mixedMoment B node4242 node4242Labels := by
  calc
    mixedMoment B raw960 raw960Labels = mixedMoment B raw960step0 raw960step0Labels := by
      have ha : raw960step0 = (fun i j => raw960 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw960step0 raw960; decide +kernel
      have hl : raw960step0Labels = raw960Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw960 raw960Labels permutation8 permutation4
    mixedMoment B raw960step0 raw960step0Labels = mixedMoment B raw960step1 raw960step1Labels := by
      have ha : raw960step1 = raw960step0 := by apply Matrix.ext; unfold raw960step1 raw960step0; decide +kernel
      have hl : raw960step0Labels = labelEmbedding7 ∘ raw960step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw960step0 raw960step0Labels raw960step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4242 node4242Labels := by rfl

theorem canonical961 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw961 raw961Labels = mixedMoment B node742 node742Labels := by
  calc
    mixedMoment B raw961 raw961Labels = mixedMoment B raw961step0 raw961step0Labels := by
      have ha : raw961step0 = (fun i j => raw961 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw961step0 raw961; decide +kernel
      have hl : raw961step0Labels = raw961Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw961 raw961Labels permutation8 permutation4
    _ = mixedMoment B node742 node742Labels := by rfl

theorem canonical962 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw962 raw962Labels = mixedMoment B node843 node843Labels := by
  calc
    mixedMoment B raw962 raw962Labels = mixedMoment B raw962step0 raw962step0Labels := by
      have ha : raw962step0 = (fun i j => raw962 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw962step0 raw962; decide +kernel
      have hl : raw962step0Labels = raw962Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw962 raw962Labels permutation8 permutation6
    mixedMoment B raw962step0 raw962step0Labels = mixedMoment B raw962step1 raw962step1Labels := by
      have ha : raw962step1 = -raw962step0 := by apply Matrix.ext; change ∀ i j, raw962step1 i j = -(raw962step0 i j); unfold raw962step1 raw962step0; decide +kernel
      have hl : raw962step1Labels = raw962step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw962step1 raw962step1Labels = mixedMoment B raw962step2 raw962step2Labels := by
      have ha : raw962step2 = raw962step1 := by apply Matrix.ext; unfold raw962step2 raw962step1; decide +kernel
      have hl : raw962step1Labels = labelEmbedding1 ∘ raw962step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw962step1 raw962step1Labels raw962step2Labels labelEmbedding1 hl
    _ = mixedMoment B node843 node843Labels := by rfl

theorem canonical972 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw972 raw972Labels = mixedMoment B node4251 node4251Labels := by
  calc
    mixedMoment B raw972 raw972Labels = mixedMoment B raw972step0 raw972step0Labels := by
      have ha : raw972step0 = (fun i j => raw972 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw972step0 raw972; decide +kernel
      have hl : raw972step0Labels = raw972Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw972 raw972Labels permutation32 permutation4
    mixedMoment B raw972step0 raw972step0Labels = mixedMoment B raw972step1 raw972step1Labels := by
      have ha : raw972step1 = raw972step0 := by apply Matrix.ext; unfold raw972step1 raw972step0; decide +kernel
      have hl : raw972step0Labels = labelEmbedding7 ∘ raw972step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw972step0 raw972step0Labels raw972step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4251 node4251Labels := by rfl

theorem canonical973 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw973 raw973Labels = mixedMoment B node785 node785Labels := by
  calc
    mixedMoment B raw973 raw973Labels = mixedMoment B raw973step0 raw973step0Labels := by
      have ha : raw973step0 = (fun i j => raw973 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw973step0 raw973; decide +kernel
      have hl : raw973step0Labels = raw973Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw973 raw973Labels permutation32 permutation4
    _ = mixedMoment B node785 node785Labels := by rfl

theorem canonical974 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw974 raw974Labels = mixedMoment B node804 node804Labels := by
  calc
    mixedMoment B raw974 raw974Labels = mixedMoment B raw974step0 raw974step0Labels := by
      have ha : raw974step0 = (fun i j => raw974 (permutation44 i) (permutation6 j)) := by apply Matrix.ext; unfold raw974step0 raw974; decide +kernel
      have hl : raw974step0Labels = raw974Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw974 raw974Labels permutation44 permutation6
    mixedMoment B raw974step0 raw974step0Labels = mixedMoment B raw974step1 raw974step1Labels := by
      have ha : raw974step1 = -raw974step0 := by apply Matrix.ext; change ∀ i j, raw974step1 i j = -(raw974step0 i j); unfold raw974step1 raw974step0; decide +kernel
      have hl : raw974step1Labels = raw974step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw974step1 raw974step1Labels = mixedMoment B raw974step2 raw974step2Labels := by
      have ha : raw974step2 = raw974step1 := by apply Matrix.ext; unfold raw974step2 raw974step1; decide +kernel
      have hl : raw974step1Labels = labelEmbedding1 ∘ raw974step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw974step1 raw974step1Labels raw974step2Labels labelEmbedding1 hl
    _ = mixedMoment B node804 node804Labels := by rfl

theorem canonical987 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw987 raw987Labels = mixedMoment B node4257 node4257Labels := by
  calc
    mixedMoment B raw987 raw987Labels = mixedMoment B raw987step0 raw987step0Labels := by
      have ha : raw987step0 = (fun i j => raw987 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw987step0 raw987; decide +kernel
      have hl : raw987step0Labels = raw987Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw987 raw987Labels permutation8 permutation4
    mixedMoment B raw987step0 raw987step0Labels = mixedMoment B raw987step1 raw987step1Labels := by
      have ha : raw987step1 = raw987step0 := by apply Matrix.ext; unfold raw987step1 raw987step0; decide +kernel
      have hl : raw987step0Labels = labelEmbedding7 ∘ raw987step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw987step0 raw987step0Labels raw987step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4257 node4257Labels := by rfl

theorem canonical988 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw988 raw988Labels = mixedMoment B node791 node791Labels := by
  calc
    mixedMoment B raw988 raw988Labels = mixedMoment B raw988step0 raw988step0Labels := by
      have ha : raw988step0 = (fun i j => raw988 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw988step0 raw988; decide +kernel
      have hl : raw988step0Labels = raw988Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw988 raw988Labels permutation8 permutation4
    _ = mixedMoment B node791 node791Labels := by rfl

theorem canonical989 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw989 raw989Labels = mixedMoment B node849 node849Labels := by
  calc
    mixedMoment B raw989 raw989Labels = mixedMoment B raw989step0 raw989step0Labels := by
      have ha : raw989step0 = (fun i j => raw989 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw989step0 raw989; decide +kernel
      have hl : raw989step0Labels = raw989Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw989 raw989Labels permutation8 permutation6
    mixedMoment B raw989step0 raw989step0Labels = mixedMoment B raw989step1 raw989step1Labels := by
      have ha : raw989step1 = -raw989step0 := by apply Matrix.ext; change ∀ i j, raw989step1 i j = -(raw989step0 i j); unfold raw989step1 raw989step0; decide +kernel
      have hl : raw989step1Labels = raw989step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw989step1 raw989step1Labels = mixedMoment B raw989step2 raw989step2Labels := by
      have ha : raw989step2 = raw989step1 := by apply Matrix.ext; unfold raw989step2 raw989step1; decide +kernel
      have hl : raw989step1Labels = labelEmbedding1 ∘ raw989step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw989step1 raw989step1Labels raw989step2Labels labelEmbedding1 hl
    _ = mixedMoment B node849 node849Labels := by rfl

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

theorem canonical1227 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1227 raw1227Labels = mixedMoment B node4418 node4418Labels := by
  calc
    mixedMoment B raw1227 raw1227Labels = mixedMoment B raw1227step0 raw1227step0Labels := by
      have ha : raw1227step0 = (fun i j => raw1227 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1227step0 raw1227; decide +kernel
      have hl : raw1227step0Labels = raw1227Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1227 raw1227Labels permutation32 permutation4
    mixedMoment B raw1227step0 raw1227step0Labels = mixedMoment B raw1227step1 raw1227step1Labels := by
      have ha : raw1227step1 = raw1227step0 := by apply Matrix.ext; unfold raw1227step1 raw1227step0; decide +kernel
      have hl : raw1227step0Labels = labelEmbedding7 ∘ raw1227step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1227step0 raw1227step0Labels raw1227step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4418 node4418Labels := by rfl

theorem canonical1228 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1228 raw1228Labels = mixedMoment B node999 node999Labels := by
  calc
    mixedMoment B raw1228 raw1228Labels = mixedMoment B raw1228step0 raw1228step0Labels := by
      have ha : raw1228step0 = (fun i j => raw1228 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1228step0 raw1228; decide +kernel
      have hl : raw1228step0Labels = raw1228Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1228 raw1228Labels permutation32 permutation4
    _ = mixedMoment B node999 node999Labels := by rfl

theorem canonical1229 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1229 raw1229Labels = mixedMoment B node1602 node1602Labels := by
  calc
    mixedMoment B raw1229 raw1229Labels = mixedMoment B raw1229step0 raw1229step0Labels := by
      have ha : raw1229step0 = (fun i j => raw1229 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1229step0 raw1229; decide +kernel
      have hl : raw1229step0Labels = raw1229Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1229 raw1229Labels permutation32 permutation6
    mixedMoment B raw1229step0 raw1229step0Labels = mixedMoment B raw1229step1 raw1229step1Labels := by
      have ha : raw1229step1 = -raw1229step0 := by apply Matrix.ext; change ∀ i j, raw1229step1 i j = -(raw1229step0 i j); unfold raw1229step1 raw1229step0; decide +kernel
      have hl : raw1229step1Labels = raw1229step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1229step1 raw1229step1Labels = mixedMoment B raw1229step2 raw1229step2Labels := by
      have ha : raw1229step2 = raw1229step1 := by apply Matrix.ext; unfold raw1229step2 raw1229step1; decide +kernel
      have hl : raw1229step1Labels = labelEmbedding1 ∘ raw1229step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1229step1 raw1229step1Labels raw1229step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1602 node1602Labels := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons64
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singleton4101 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4101 node4101Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node538 node538Labels + mixedMoment B node663 node663Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw675 singletonSmall4101
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4101) = raw675Labels := by decide +kernel
  rw [hl, canonical675 B hB] at h
  have hc0 : mixedMoment B raw675 (Fin.cases (0 : Fin 2) singletonSmall4101) =
      mixedMoment B node538 node538Labels := by
    have ha : raw675 = raw676 := by apply Matrix.ext; unfold raw675 raw676; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4101 = raw676Labels := by decide +kernel
    rw [ha, hj, canonical676 B hB]
  have hc1 : mixedMoment B raw675 (Fin.cases (1 : Fin 2) singletonSmall4101) =
      mixedMoment B node663 node663Labels := by
    have ha : raw675 = raw677 := by apply Matrix.ext; unfold raw675 raw677; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4101 = raw677Labels := by decide +kernel
    rw [ha, hj, canonical677 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4108 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4108 node4108Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node545 node545Labels + mixedMoment B node683 node683Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw696 singletonSmall4108
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4108) = raw696Labels := by decide +kernel
  rw [hl, canonical696 B hB] at h
  have hc0 : mixedMoment B raw696 (Fin.cases (0 : Fin 2) singletonSmall4108) =
      mixedMoment B node545 node545Labels := by
    have ha : raw696 = raw697 := by apply Matrix.ext; unfold raw696 raw697; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4108 = raw697Labels := by decide +kernel
    rw [ha, hj, canonical697 B hB]
  have hc1 : mixedMoment B raw696 (Fin.cases (1 : Fin 2) singletonSmall4108) =
      mixedMoment B node683 node683Labels := by
    have ha : raw696 = raw698 := by apply Matrix.ext; unfold raw696 raw698; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4108 = raw698Labels := by decide +kernel
    rw [ha, hj, canonical698 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4110 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4110 node4110Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node547 node547Labels + mixedMoment B node684 node684Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw702 singletonSmall4110
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4110) = raw702Labels := by decide +kernel
  rw [hl, canonical702 B hB] at h
  have hc0 : mixedMoment B raw702 (Fin.cases (0 : Fin 2) singletonSmall4110) =
      mixedMoment B node547 node547Labels := by
    have ha : raw702 = raw703 := by apply Matrix.ext; unfold raw702 raw703; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4110 = raw703Labels := by decide +kernel
    rw [ha, hj, canonical703 B hB]
  have hc1 : mixedMoment B raw702 (Fin.cases (1 : Fin 2) singletonSmall4110) =
      mixedMoment B node684 node684Labels := by
    have ha : raw702 = raw704 := by apply Matrix.ext; unfold raw702 raw704; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4110 = raw704Labels := by decide +kernel
    rw [ha, hj, canonical704 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

end MUB6.Certificate.MixedSemantics

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

theorem singleton4196 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4196 node4196Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node699 node699Labels + mixedMoment B node748 node748Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw852 singletonSmall4196
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4196) = raw852Labels := by decide +kernel
  rw [hl, canonical852 B hB] at h
  have hc0 : mixedMoment B raw852 (Fin.cases (0 : Fin 2) singletonSmall4196) =
      mixedMoment B node699 node699Labels := by
    have ha : raw852 = raw853 := by apply Matrix.ext; unfold raw852 raw853; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4196 = raw853Labels := by decide +kernel
    rw [ha, hj, canonical853 B hB]
  have hc1 : mixedMoment B raw852 (Fin.cases (1 : Fin 2) singletonSmall4196) =
      mixedMoment B node748 node748Labels := by
    have ha : raw852 = raw854 := by apply Matrix.ext; unfold raw852 raw854; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4196 = raw854Labels := by decide +kernel
    rw [ha, hj, canonical854 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4202 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4202 node4202Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node705 node705Labels + mixedMoment B node762 node762Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw870 singletonSmall4202
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4202) = raw870Labels := by decide +kernel
  rw [hl, canonical870 B hB] at h
  have hc0 : mixedMoment B raw870 (Fin.cases (0 : Fin 2) singletonSmall4202) =
      mixedMoment B node705 node705Labels := by
    have ha : raw870 = raw871 := by apply Matrix.ext; unfold raw870 raw871; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4202 = raw871Labels := by decide +kernel
    rw [ha, hj, canonical871 B hB]
  have hc1 : mixedMoment B raw870 (Fin.cases (1 : Fin 2) singletonSmall4202) =
      mixedMoment B node762 node762Labels := by
    have ha : raw870 = raw872 := by apply Matrix.ext; unfold raw870 raw872; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4202 = raw872Labels := by decide +kernel
    rw [ha, hj, canonical872 B hB]
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

theorem singleton4233 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4233 node4233Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node733 node733Labels + mixedMoment B node799 node799Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw933 singletonSmall4233
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4233) = raw933Labels := by decide +kernel
  rw [hl, canonical933 B hB] at h
  have hc0 : mixedMoment B raw933 (Fin.cases (0 : Fin 2) singletonSmall4233) =
      mixedMoment B node733 node733Labels := by
    have ha : raw933 = raw934 := by apply Matrix.ext; unfold raw933 raw934; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4233 = raw934Labels := by decide +kernel
    rw [ha, hj, canonical934 B hB]
  have hc1 : mixedMoment B raw933 (Fin.cases (1 : Fin 2) singletonSmall4233) =
      mixedMoment B node799 node799Labels := by
    have ha : raw933 = raw935 := by apply Matrix.ext; unfold raw933 raw935; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4233 = raw935Labels := by decide +kernel
    rw [ha, hj, canonical935 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4240 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4240 node4240Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node740 node740Labels + mixedMoment B node842 node842Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw954 singletonSmall4240
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4240) = raw954Labels := by decide +kernel
  rw [hl, canonical954 B hB] at h
  have hc0 : mixedMoment B raw954 (Fin.cases (0 : Fin 2) singletonSmall4240) =
      mixedMoment B node740 node740Labels := by
    have ha : raw954 = raw955 := by apply Matrix.ext; unfold raw954 raw955; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4240 = raw955Labels := by decide +kernel
    rw [ha, hj, canonical955 B hB]
  have hc1 : mixedMoment B raw954 (Fin.cases (1 : Fin 2) singletonSmall4240) =
      mixedMoment B node842 node842Labels := by
    have ha : raw954 = raw956 := by apply Matrix.ext; unfold raw954 raw956; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4240 = raw956Labels := by decide +kernel
    rw [ha, hj, canonical956 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4242 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4242 node4242Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node742 node742Labels + mixedMoment B node843 node843Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw960 singletonSmall4242
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4242) = raw960Labels := by decide +kernel
  rw [hl, canonical960 B hB] at h
  have hc0 : mixedMoment B raw960 (Fin.cases (0 : Fin 2) singletonSmall4242) =
      mixedMoment B node742 node742Labels := by
    have ha : raw960 = raw961 := by apply Matrix.ext; unfold raw960 raw961; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4242 = raw961Labels := by decide +kernel
    rw [ha, hj, canonical961 B hB]
  have hc1 : mixedMoment B raw960 (Fin.cases (1 : Fin 2) singletonSmall4242) =
      mixedMoment B node843 node843Labels := by
    have ha : raw960 = raw962 := by apply Matrix.ext; unfold raw960 raw962; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4242 = raw962Labels := by decide +kernel
    rw [ha, hj, canonical962 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4251 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4251 node4251Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node785 node785Labels + mixedMoment B node804 node804Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw972 singletonSmall4251
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4251) = raw972Labels := by decide +kernel
  rw [hl, canonical972 B hB] at h
  have hc0 : mixedMoment B raw972 (Fin.cases (0 : Fin 2) singletonSmall4251) =
      mixedMoment B node785 node785Labels := by
    have ha : raw972 = raw973 := by apply Matrix.ext; unfold raw972 raw973; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4251 = raw973Labels := by decide +kernel
    rw [ha, hj, canonical973 B hB]
  have hc1 : mixedMoment B raw972 (Fin.cases (1 : Fin 2) singletonSmall4251) =
      mixedMoment B node804 node804Labels := by
    have ha : raw972 = raw974 := by apply Matrix.ext; unfold raw972 raw974; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4251 = raw974Labels := by decide +kernel
    rw [ha, hj, canonical974 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4257 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4257 node4257Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node791 node791Labels + mixedMoment B node849 node849Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw987 singletonSmall4257
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4257) = raw987Labels := by decide +kernel
  rw [hl, canonical987 B hB] at h
  have hc0 : mixedMoment B raw987 (Fin.cases (0 : Fin 2) singletonSmall4257) =
      mixedMoment B node791 node791Labels := by
    have ha : raw987 = raw988 := by apply Matrix.ext; unfold raw987 raw988; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4257 = raw988Labels := by decide +kernel
    rw [ha, hj, canonical988 B hB]
  have hc1 : mixedMoment B raw987 (Fin.cases (1 : Fin 2) singletonSmall4257) =
      mixedMoment B node849 node849Labels := by
    have ha : raw987 = raw989 := by apply Matrix.ext; unfold raw987 raw989; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4257 = raw989Labels := by decide +kernel
    rw [ha, hj, canonical989 B hB]
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

theorem singleton4418 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4418 node4418Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node999 node999Labels + mixedMoment B node1602 node1602Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1227 singletonSmall4418
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4418) = raw1227Labels := by decide +kernel
  rw [hl, canonical1227 B hB] at h
  have hc0 : mixedMoment B raw1227 (Fin.cases (0 : Fin 2) singletonSmall4418) =
      mixedMoment B node999 node999Labels := by
    have ha : raw1227 = raw1228 := by apply Matrix.ext; unfold raw1227 raw1228; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4418 = raw1228Labels := by decide +kernel
    rw [ha, hj, canonical1228 B hB]
  have hc1 : mixedMoment B raw1227 (Fin.cases (1 : Fin 2) singletonSmall4418) =
      mixedMoment B node1602 node1602Labels := by
    have ha : raw1227 = raw1229 := by apply Matrix.ext; unfold raw1227 raw1229; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4418 = raw1229Labels := by decide +kernel
    rw [ha, hj, canonical1229 B hB]
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

theorem singleton4490 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4490 node4490Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1074 node1074Labels + mixedMoment B node1650 node1650Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1284 singletonSmall4490
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4490) = raw1284Labels := by decide +kernel
  rw [hl, canonical1284 B hB] at h
  have hc0 : mixedMoment B raw1284 (Fin.cases (0 : Fin 2) singletonSmall4490) =
      mixedMoment B node1074 node1074Labels := by
    have ha : raw1284 = raw1285 := by apply Matrix.ext; unfold raw1284 raw1285; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4490 = raw1285Labels := by decide +kernel
    rw [ha, hj, canonical1285 B hB]
  have hc1 : mixedMoment B raw1284 (Fin.cases (1 : Fin 2) singletonSmall4490) =
      mixedMoment B node1650 node1650Labels := by
    have ha : raw1284 = raw1286 := by apply Matrix.ext; unfold raw1284 raw1286; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4490 = raw1286Labels := by decide +kernel
    rw [ha, hj, canonical1286 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4496 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4496 node4496Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1080 node1080Labels + mixedMoment B node1710 node1710Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1296 singletonSmall4496
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4496) = raw1296Labels := by decide +kernel
  rw [hl, canonical1296 B hB] at h
  have hc0 : mixedMoment B raw1296 (Fin.cases (0 : Fin 2) singletonSmall4496) =
      mixedMoment B node1080 node1080Labels := by
    have ha : raw1296 = raw1297 := by apply Matrix.ext; unfold raw1296 raw1297; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4496 = raw1297Labels := by decide +kernel
    rw [ha, hj, canonical1297 B hB]
  have hc1 : mixedMoment B raw1296 (Fin.cases (1 : Fin 2) singletonSmall4496) =
      mixedMoment B node1710 node1710Labels := by
    have ha : raw1296 = raw1298 := by apply Matrix.ext; unfold raw1296 raw1298; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4496 = raw1298Labels := by decide +kernel
    rw [ha, hj, canonical1298 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros10
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero688 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node688 node688Labels = 0 := by
  exact mixedMoment_order_one B hB node688 node688Labels 1
    (by decide +kernel) (by decide +kernel)

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound10
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound663 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node663 node663Labels = Sparse.eval nodeValue663 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 663) = mixedMoment B node663 node663Labels := rfl
  simpa [nodeValue663, Sparse.eval] using hc.symm

theorem sound683 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node683 node683Labels = Sparse.eval nodeValue683 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 683) = mixedMoment B node683 node683Labels := rfl
  simpa [nodeValue683, Sparse.eval] using hc.symm

theorem sound684 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node684 node684Labels = Sparse.eval nodeValue684 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 684) = mixedMoment B node684 node684Labels := rfl
  simpa [nodeValue684, Sparse.eval] using hc.symm

theorem sound688 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node688 node688Labels = Sparse.eval nodeValue688 (mixedVector B) := by
  simpa only [nodeValue688, Sparse.eval_nil] using zero688 B _hB _hF

theorem sound698 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node698 node698Labels = Sparse.eval nodeValue698 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 698) = mixedMoment B node698 node698Labels := rfl
  simpa [nodeValue698, Sparse.eval] using hc.symm

theorem sound699 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node699 node699Labels = Sparse.eval nodeValue699 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 699) = mixedMoment B node699 node699Labels := rfl
  simpa [nodeValue699, Sparse.eval] using hc.symm

theorem sound702 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node702 node702Labels = Sparse.eval nodeValue702 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 702) = mixedMoment B node702 node702Labels := rfl
  simpa [nodeValue702, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros11
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero767 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node767 node767Labels = 0 := by
  exact mixedMoment_order_one B hB node767 node767Labels 1
    (by decide +kernel) (by decide +kernel)

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

theorem sound705 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node705 node705Labels = Sparse.eval nodeValue705 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 705) = mixedMoment B node705 node705Labels := rfl
  simpa [nodeValue705, Sparse.eval] using hc.symm

theorem sound707 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node707 node707Labels = Sparse.eval nodeValue707 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 707) = mixedMoment B node707 node707Labels := rfl
  simpa [nodeValue707, Sparse.eval] using hc.symm

theorem sound708 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node708 node708Labels = Sparse.eval nodeValue708 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 708) = mixedMoment B node708 node708Labels := rfl
  simpa [nodeValue708, Sparse.eval] using hc.symm

theorem sound731 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node731 node731Labels = Sparse.eval nodeValue731 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 731) = mixedMoment B node731 node731Labels := rfl
  simpa [nodeValue731, Sparse.eval] using hc.symm

theorem sound733 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node733 node733Labels = Sparse.eval nodeValue733 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 733) = mixedMoment B node733 node733Labels := rfl
  simpa [nodeValue733, Sparse.eval] using hc.symm

theorem sound737 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node737 node737Labels = Sparse.eval nodeValue737 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 737) = mixedMoment B node737 node737Labels := rfl
  simpa [nodeValue737, Sparse.eval] using hc.symm

theorem sound740 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node740 node740Labels = Sparse.eval nodeValue740 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 740) = mixedMoment B node740 node740Labels := rfl
  simpa [nodeValue740, Sparse.eval] using hc.symm

theorem sound742 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node742 node742Labels = Sparse.eval nodeValue742 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 742) = mixedMoment B node742 node742Labels := rfl
  simpa [nodeValue742, Sparse.eval] using hc.symm

theorem sound743 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node743 node743Labels = Sparse.eval nodeValue743 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 743) = mixedMoment B node743 node743Labels := rfl
  simpa [nodeValue743, Sparse.eval] using hc.symm

theorem sound748 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node748 node748Labels = Sparse.eval nodeValue748 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 748) = mixedMoment B node748 node748Labels := rfl
  simpa [nodeValue748, Sparse.eval] using hc.symm

theorem sound762 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node762 node762Labels = Sparse.eval nodeValue762 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 762) = mixedMoment B node762 node762Labels := rfl
  simpa [nodeValue762, Sparse.eval] using hc.symm

theorem sound763 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node763 node763Labels = Sparse.eval nodeValue763 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 763) = mixedMoment B node763 node763Labels := rfl
  simpa [nodeValue763, Sparse.eval] using hc.symm

theorem sound767 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node767 node767Labels = Sparse.eval nodeValue767 (mixedVector B) := by
  simpa only [nodeValue767, Sparse.eval_nil] using zero767 B _hB _hF

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

theorem zero806 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node806 node806Labels = 0 := by
  exact mixedMoment_order_one B hB node806 node806Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero809 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node809 node809Labels = 0 := by
  exact mixedMoment_order_one B hB node809 node809Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero810 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node810 node810Labels = 0 := by
  exact mixedMoment_order_one B hB node810 node810Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero812 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node812 node812Labels = 0 := by
  exact mixedMoment_order_one B hB node812 node812Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero816 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node816 node816Labels = 0 := by
  exact mixedMoment_order_one B hB node816 node816Labels 1
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

theorem sound776 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node776 node776Labels = Sparse.eval nodeValue776 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 776) = mixedMoment B node776 node776Labels := rfl
  simpa [nodeValue776, Sparse.eval] using hc.symm

theorem sound778 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node778 node778Labels = Sparse.eval nodeValue778 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 778) = mixedMoment B node778 node778Labels := rfl
  simpa [nodeValue778, Sparse.eval] using hc.symm

theorem sound782 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node782 node782Labels = Sparse.eval nodeValue782 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 782) = mixedMoment B node782 node782Labels := rfl
  simpa [nodeValue782, Sparse.eval] using hc.symm

theorem sound783 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node783 node783Labels = Sparse.eval nodeValue783 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 783) = mixedMoment B node783 node783Labels := rfl
  simpa [nodeValue783, Sparse.eval] using hc.symm

theorem sound785 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node785 node785Labels = Sparse.eval nodeValue785 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 785) = mixedMoment B node785 node785Labels := rfl
  simpa [nodeValue785, Sparse.eval] using hc.symm

theorem sound787 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node787 node787Labels = Sparse.eval nodeValue787 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 787) = mixedMoment B node787 node787Labels := rfl
  simpa [nodeValue787, Sparse.eval] using hc.symm

theorem sound789 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node789 node789Labels = Sparse.eval nodeValue789 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 789) = mixedMoment B node789 node789Labels := rfl
  simpa [nodeValue789, Sparse.eval] using hc.symm

theorem sound790 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node790 node790Labels = Sparse.eval nodeValue790 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 790) = mixedMoment B node790 node790Labels := rfl
  simpa [nodeValue790, Sparse.eval] using hc.symm

theorem sound791 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node791 node791Labels = Sparse.eval nodeValue791 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 791) = mixedMoment B node791 node791Labels := rfl
  simpa [nodeValue791, Sparse.eval] using hc.symm

theorem sound799 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node799 node799Labels = Sparse.eval nodeValue799 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 799) = mixedMoment B node799 node799Labels := rfl
  simpa [nodeValue799, Sparse.eval] using hc.symm

theorem sound804 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node804 node804Labels = Sparse.eval nodeValue804 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 804) = mixedMoment B node804 node804Labels := rfl
  simpa [nodeValue804, Sparse.eval] using hc.symm

theorem sound806 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node806 node806Labels = Sparse.eval nodeValue806 (mixedVector B) := by
  simpa only [nodeValue806, Sparse.eval_nil] using zero806 B _hB _hF

theorem sound807 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node807 node807Labels = Sparse.eval nodeValue807 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 807) = mixedMoment B node807 node807Labels := rfl
  simpa [nodeValue807, Sparse.eval] using hc.symm

theorem sound809 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node809 node809Labels = Sparse.eval nodeValue809 (mixedVector B) := by
  simpa only [nodeValue809, Sparse.eval_nil] using zero809 B _hB _hF

theorem sound810 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node810 node810Labels = Sparse.eval nodeValue810 (mixedVector B) := by
  simpa only [nodeValue810, Sparse.eval_nil] using zero810 B _hB _hF

theorem sound812 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node812 node812Labels = Sparse.eval nodeValue812 (mixedVector B) := by
  simpa only [nodeValue812, Sparse.eval_nil] using zero812 B _hB _hF

theorem sound813 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node813 node813Labels = Sparse.eval nodeValue813 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 813) = mixedMoment B node813 node813Labels := rfl
  simpa [nodeValue813, Sparse.eval] using hc.symm

theorem sound816 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node816 node816Labels = Sparse.eval nodeValue816 (mixedVector B) := by
  simpa only [nodeValue816, Sparse.eval_nil] using zero816 B _hB _hF

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

theorem zero852 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node852 node852Labels = 0 := by
  exact mixedMoment_order_one B hB node852 node852Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero856 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node856 node856Labels = 0 := by
  exact mixedMoment_order_one B hB node856 node856Labels 1
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

theorem sound842 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node842 node842Labels = Sparse.eval nodeValue842 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 842) = mixedMoment B node842 node842Labels := rfl
  simpa [nodeValue842, Sparse.eval] using hc.symm

theorem sound843 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node843 node843Labels = Sparse.eval nodeValue843 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 843) = mixedMoment B node843 node843Labels := rfl
  simpa [nodeValue843, Sparse.eval] using hc.symm

theorem sound849 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node849 node849Labels = Sparse.eval nodeValue849 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 849) = mixedMoment B node849 node849Labels := rfl
  simpa [nodeValue849, Sparse.eval] using hc.symm

theorem sound851 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node851 node851Labels = Sparse.eval nodeValue851 (mixedVector B) := by
  simpa only [nodeValue851, Sparse.eval_nil] using zero851 B _hB _hF

theorem sound852 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node852 node852Labels = Sparse.eval nodeValue852 (mixedVector B) := by
  simpa only [nodeValue852, Sparse.eval_nil] using zero852 B _hB _hF

theorem sound856 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node856 node856Labels = Sparse.eval nodeValue856 (mixedVector B) := by
  simpa only [nodeValue856, Sparse.eval_nil] using zero856 B _hB _hF

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

theorem sound999 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node999 node999Labels = Sparse.eval nodeValue999 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 999) = mixedMoment B node999 node999Labels := rfl
  simpa [nodeValue999, Sparse.eval] using hc.symm

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

theorem sound1074 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1074 node1074Labels = Sparse.eval nodeValue1074 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1074) = mixedMoment B node1074 node1074Labels := rfl
  simpa [nodeValue1074, Sparse.eval] using hc.symm

theorem sound1080 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1080 node1080Labels = Sparse.eval nodeValue1080 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1080) = mixedMoment B node1080 node1080Labels := rfl
  simpa [nodeValue1080, Sparse.eval] using hc.symm

theorem sound1082 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1082 node1082Labels = Sparse.eval nodeValue1082 (mixedVector B) := by
  simpa only [nodeValue1082, Sparse.eval_nil] using zero1082 B _hB _hF

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros24
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero1592 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node1592 node1592Labels = 0 := by
  exact mixedMoment_alpha B hF node1592 node1592Labels 1 permutation434
    (by decide +kernel)

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound24
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound1592 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1592 node1592Labels = Sparse.eval nodeValue1592 (mixedVector B) := by
  simpa only [nodeValue1592, Sparse.eval_nil] using zero1592 B _hB _hF

theorem sound1593 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1593 node1593Labels = Sparse.eval nodeValue1593 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1593) = mixedMoment B node1593 node1593Labels := rfl
  simpa [nodeValue1593, Sparse.eval] using hc.symm

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

theorem sound1602 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1602 node1602Labels = Sparse.eval nodeValue1602 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1602) = mixedMoment B node1602 node1602Labels := rfl
  simpa [nodeValue1602, Sparse.eval] using hc.symm

theorem sound1603 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1603 node1603Labels = Sparse.eval nodeValue1603 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1603) = mixedMoment B node1603 node1603Labels := rfl
  simpa [nodeValue1603, Sparse.eval] using hc.symm

theorem sound1637 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1637 node1637Labels = Sparse.eval nodeValue1637 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1637) = mixedMoment B node1637 node1637Labels := rfl
  simpa [nodeValue1637, Sparse.eval] using hc.symm

theorem sound1639 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1639 node1639Labels = Sparse.eval nodeValue1639 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1639) = mixedMoment B node1639 node1639Labels := rfl
  simpa [nodeValue1639, Sparse.eval] using hc.symm

theorem sound1650 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1650 node1650Labels = Sparse.eval nodeValue1650 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1650) = mixedMoment B node1650 node1650Labels := rfl
  simpa [nodeValue1650, Sparse.eval] using hc.symm

theorem sound1651 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1651 node1651Labels = Sparse.eval nodeValue1651 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1651) = mixedMoment B node1651 node1651Labels := rfl
  simpa [nodeValue1651, Sparse.eval] using hc.symm

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

theorem zero1698 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node1698 node1698Labels = 0 := by
  exact mixedMoment_alpha B hF node1698 node1698Labels 1 permutation434
    (by decide +kernel)

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

theorem sound1698 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1698 node1698Labels = Sparse.eval nodeValue1698 (mixedVector B) := by
  simpa only [nodeValue1698, Sparse.eval_nil] using zero1698 B _hB _hF

theorem sound1700 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1700 node1700Labels = Sparse.eval nodeValue1700 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1700) = mixedMoment B node1700 node1700Labels := rfl
  simpa [nodeValue1700, Sparse.eval] using hc.symm

theorem sound1707 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1707 node1707Labels = Sparse.eval nodeValue1707 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1707) = mixedMoment B node1707 node1707Labels := rfl
  simpa [nodeValue1707, Sparse.eval] using hc.symm

theorem sound1708 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1708 node1708Labels = Sparse.eval nodeValue1708 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1708) = mixedMoment B node1708 node1708Labels := rfl
  simpa [nodeValue1708, Sparse.eval] using hc.symm

theorem sound1710 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1710 node1710Labels = Sparse.eval nodeValue1710 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1710) = mixedMoment B node1710 node1710Labels := rfl
  simpa [nodeValue1710, Sparse.eval] using hc.symm

theorem sound1716 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1716 node1716Labels = Sparse.eval nodeValue1716 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1716) = mixedMoment B node1716 node1716Labels := rfl
  simpa [nodeValue1716, Sparse.eval] using hc.symm

theorem sound1727 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1727 node1727Labels = Sparse.eval nodeValue1727 (mixedVector B) := by
  simpa only [nodeValue1727, Sparse.eval_nil] using zero1727 B _hB _hF

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

theorem sound1728 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1728 node1728Labels = Sparse.eval nodeValue1728 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1728) = mixedMoment B node1728 node1728Labels := rfl
  simpa [nodeValue1728, Sparse.eval] using hc.symm

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

theorem sound536 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node536 node536Labels = Sparse.eval nodeValue536 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 536) = mixedMoment B node536 node536Labels := rfl
  simpa [nodeValue536, Sparse.eval] using hc.symm

theorem sound538 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node538 node538Labels = Sparse.eval nodeValue538 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 538) = mixedMoment B node538 node538Labels := rfl
  simpa [nodeValue538, Sparse.eval] using hc.symm

theorem sound542 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node542 node542Labels = Sparse.eval nodeValue542 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 542) = mixedMoment B node542 node542Labels := rfl
  simpa [nodeValue542, Sparse.eval] using hc.symm

theorem sound545 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node545 node545Labels = Sparse.eval nodeValue545 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 545) = mixedMoment B node545 node545Labels := rfl
  simpa [nodeValue545, Sparse.eval] using hc.symm

theorem sound547 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node547 node547Labels = Sparse.eval nodeValue547 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 547) = mixedMoment B node547 node547Labels := rfl
  simpa [nodeValue547, Sparse.eval] using hc.symm

theorem sound548 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node548 node548Labels = Sparse.eval nodeValue548 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 548) = mixedMoment B node548 node548Labels := rfl
  simpa [nodeValue548, Sparse.eval] using hc.symm

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

theorem sound4069 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4069 node4069Labels = Sparse.eval nodeValue4069 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4069) = mixedMoment B node4069 node4069Labels := rfl
  simpa [nodeValue4069, Sparse.eval] using hc.symm

theorem sound4070 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4070 node4070Labels = Sparse.eval nodeValue4070 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4070) = mixedMoment B node4070 node4070Labels := rfl
  simpa [nodeValue4070, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros64
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero4127 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4127 node4127Labels = 0 := by
  exact mixedMoment_order_one B hB node4127 node4127Labels 1
    (by decide +kernel) (by decide +kernel)

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

theorem sound4101 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4101 node4101Labels = Sparse.eval nodeValue4101 (mixedVector B) := by
  have h := singleton4101 B _hB
  rw [sound538 B _hB _hF, sound663 B _hB _hF] at h
  norm_num [nodeValue4101, nodeValue538, nodeValue663, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4108 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4108 node4108Labels = Sparse.eval nodeValue4108 (mixedVector B) := by
  have h := singleton4108 B _hB
  rw [sound545 B _hB _hF, sound683 B _hB _hF] at h
  norm_num [nodeValue4108, nodeValue545, nodeValue683, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4110 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4110 node4110Labels = Sparse.eval nodeValue4110 (mixedVector B) := by
  have h := singleton4110 B _hB
  rw [sound547 B _hB _hF, sound684 B _hB _hF] at h
  norm_num [nodeValue4110, nodeValue547, nodeValue684, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4127 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4127 node4127Labels = Sparse.eval nodeValue4127 (mixedVector B) := by
  simpa only [nodeValue4127, Sparse.eval_nil] using zero4127 B _hB _hF

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros65
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero4218 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4218 node4218Labels = 0 := by
  exact mixedMoment_order_one B hB node4218 node4218Labels 1
    (by decide +kernel) (by decide +kernel)

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

theorem sound4196 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4196 node4196Labels = Sparse.eval nodeValue4196 (mixedVector B) := by
  have h := singleton4196 B _hB
  rw [sound699 B _hB _hF, sound748 B _hB _hF] at h
  norm_num [nodeValue4196, nodeValue699, nodeValue748, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4202 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4202 node4202Labels = Sparse.eval nodeValue4202 (mixedVector B) := by
  have h := singleton4202 B _hB
  rw [sound705 B _hB _hF, sound762 B _hB _hF] at h
  norm_num [nodeValue4202, nodeValue705, nodeValue762, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4204 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4204 node4204Labels = Sparse.eval nodeValue4204 (mixedVector B) := by
  have h := singleton4204 B _hB
  rw [sound707 B _hB _hF, sound763 B _hB _hF] at h
  norm_num [nodeValue4204, nodeValue707, nodeValue763, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4218 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4218 node4218Labels = Sparse.eval nodeValue4218 (mixedVector B) := by
  simpa only [nodeValue4218, Sparse.eval_nil] using zero4218 B _hB _hF

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros66
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero4264 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4264 node4264Labels = 0 := by
  exact mixedMoment_order_one B hB node4264 node4264Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero4269 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4269 node4269Labels = 0 := by
  exact mixedMoment_order_one B hB node4269 node4269Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero4273 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4273 node4273Labels = 0 := by
  exact mixedMoment_order_one B hB node4273 node4273Labels 1
    (by decide +kernel) (by decide +kernel)

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

theorem sound4233 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4233 node4233Labels = Sparse.eval nodeValue4233 (mixedVector B) := by
  have h := singleton4233 B _hB
  rw [sound733 B _hB _hF, sound799 B _hB _hF] at h
  norm_num [nodeValue4233, nodeValue733, nodeValue799, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4240 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4240 node4240Labels = Sparse.eval nodeValue4240 (mixedVector B) := by
  have h := singleton4240 B _hB
  rw [sound740 B _hB _hF, sound842 B _hB _hF] at h
  norm_num [nodeValue4240, nodeValue740, nodeValue842, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4242 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4242 node4242Labels = Sparse.eval nodeValue4242 (mixedVector B) := by
  have h := singleton4242 B _hB
  rw [sound742 B _hB _hF, sound843 B _hB _hF] at h
  norm_num [nodeValue4242, nodeValue742, nodeValue843, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4251 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4251 node4251Labels = Sparse.eval nodeValue4251 (mixedVector B) := by
  have h := singleton4251 B _hB
  rw [sound785 B _hB _hF, sound804 B _hB _hF] at h
  norm_num [nodeValue4251, nodeValue785, nodeValue804, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4257 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4257 node4257Labels = Sparse.eval nodeValue4257 (mixedVector B) := by
  have h := singleton4257 B _hB
  rw [sound791 B _hB _hF, sound849 B _hB _hF] at h
  norm_num [nodeValue4257, nodeValue791, nodeValue849, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4264 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4264 node4264Labels = Sparse.eval nodeValue4264 (mixedVector B) := by
  simpa only [nodeValue4264, Sparse.eval_nil] using zero4264 B _hB _hF

theorem sound4269 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4269 node4269Labels = Sparse.eval nodeValue4269 (mixedVector B) := by
  simpa only [nodeValue4269, Sparse.eval_nil] using zero4269 B _hB _hF

theorem sound4273 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4273 node4273Labels = Sparse.eval nodeValue4273 (mixedVector B) := by
  simpa only [nodeValue4273, Sparse.eval_nil] using zero4273 B _hB _hF

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

theorem sound4418 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4418 node4418Labels = Sparse.eval nodeValue4418 (mixedVector B) := by
  have h := singleton4418 B _hB
  rw [sound999 B _hB _hF, sound1602 B _hB _hF] at h
  norm_num [nodeValue4418, nodeValue999, nodeValue1602, Sparse.eval] at h ⊢
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

theorem sound4490 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4490 node4490Labels = Sparse.eval nodeValue4490 (mixedVector B) := by
  have h := singleton4490 B _hB
  rw [sound1074 B _hB _hF, sound1650 B _hB _hF] at h
  norm_num [nodeValue4490, nodeValue1074, nodeValue1650, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4496 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4496 node4496Labels = Sparse.eval nodeValue4496 (mixedVector B) := by
  have h := singleton4496 B _hB
  rw [sound1080 B _hB _hF, sound1710 B _hB _hF] at h
  norm_num [nodeValue4496, nodeValue1080, nodeValue1710, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4498 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4498 node4498Labels = Sparse.eval nodeValue4498 (mixedVector B) := by
  simpa only [nodeValue4498, Sparse.eval_nil] using zero4498 B _hB _hF

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources44
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sourceEq1415 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1415 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1415 + difference 0 5) (sourceB1415 + difference 5 0) sourceC1415) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1698) := by
    have ha : (tripleCharges (sourceA1415 + difference 0 5) (sourceB1415 + difference 5 0) sourceC1415) = raw22065 := by
      apply Matrix.ext; unfold tripleCharges sourceA1415 sourceB1415 sourceC1415 difference raw22065; decide +kernel
    rw [ha]
    exact (canonical22065 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1415 + difference 1 5) (sourceB1415 + difference 5 1) sourceC1415) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 783) := by
    have ha : (tripleCharges (sourceA1415 + difference 1 5) (sourceB1415 + difference 5 1) sourceC1415) = raw22066 := by
      apply Matrix.ext; unfold tripleCharges sourceA1415 sourceB1415 sourceC1415 difference raw22066; decide +kernel
    rw [ha]
    exact (canonical22066 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1415 + difference 2 5) (sourceB1415 + difference 5 2) sourceC1415) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 783) := by
    have ha : (tripleCharges (sourceA1415 + difference 2 5) (sourceB1415 + difference 5 2) sourceC1415) = raw22067 := by
      apply Matrix.ext; unfold tripleCharges sourceA1415 sourceB1415 sourceC1415 difference raw22067; decide +kernel
    rw [ha]
    exact (canonical22067 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1415 + difference 3 5) (sourceB1415 + difference 5 3) sourceC1415) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 783) := by
    have ha : (tripleCharges (sourceA1415 + difference 3 5) (sourceB1415 + difference 5 3) sourceC1415) = raw22068 := by
      apply Matrix.ext; unfold tripleCharges sourceA1415 sourceB1415 sourceC1415 difference raw22068; decide +kernel
    rw [ha]
    exact (canonical22068 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1415 + difference 4 5) (sourceB1415 + difference 5 4) sourceC1415) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 778) := by
    have ha : (tripleCharges (sourceA1415 + difference 4 5) (sourceB1415 + difference 5 4) sourceC1415) = raw22069 := by
      apply Matrix.ext; unfold tripleCharges sourceA1415 sourceB1415 sourceC1415 difference raw22069; decide +kernel
    rw [ha]
    exact (canonical22069 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1415 + difference 5 5) (sourceB1415 + difference 5 5) sourceC1415) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 776) := by
    have ha : (tripleCharges (sourceA1415 + difference 5 5) (sourceB1415 + difference 5 5) sourceC1415) = raw22070 := by
      apply Matrix.ext; unfold tripleCharges sourceA1415 sourceB1415 sourceC1415 difference raw22070; decide +kernel
    rw [ha]
    exact (canonical22070 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1415 + sourceB1415) sourceC1415) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4068) := by
    have ha : (doubleCharges (sourceA1415 + sourceB1415) sourceC1415) = raw22071 := by
      apply Matrix.ext; unfold doubleCharges sourceA1415 sourceB1415 sourceC1415 raw22071; decide +kernel
    rw [ha]
    exact (canonical22071 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1415 sourceB1415 sourceC1415
    (0 : Fin 2) 1 (5 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1415, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1417 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1417 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1417 + difference 0 0) (sourceB1417 + difference 0 0) sourceC1417) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 787) := by
    have ha : (tripleCharges (sourceA1417 + difference 0 0) (sourceB1417 + difference 0 0) sourceC1417) = raw22079 := by
      apply Matrix.ext; unfold tripleCharges sourceA1417 sourceB1417 sourceC1417 difference raw22079; decide +kernel
    rw [ha]
    exact (canonical22079 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1417 + difference 0 1) (sourceB1417 + difference 1 0) sourceC1417) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1639) := by
    have ha : (tripleCharges (sourceA1417 + difference 0 1) (sourceB1417 + difference 1 0) sourceC1417) = raw22080 := by
      apply Matrix.ext; unfold tripleCharges sourceA1417 sourceB1417 sourceC1417 difference raw22080; decide +kernel
    rw [ha]
    exact (canonical22080 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1417 + difference 0 2) (sourceB1417 + difference 2 0) sourceC1417) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1639) := by
    have ha : (tripleCharges (sourceA1417 + difference 0 2) (sourceB1417 + difference 2 0) sourceC1417) = raw22081 := by
      apply Matrix.ext; unfold tripleCharges sourceA1417 sourceB1417 sourceC1417 difference raw22081; decide +kernel
    rw [ha]
    exact (canonical22081 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1417 + difference 0 3) (sourceB1417 + difference 3 0) sourceC1417) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1593) := by
    have ha : (tripleCharges (sourceA1417 + difference 0 3) (sourceB1417 + difference 3 0) sourceC1417) = raw22082 := by
      apply Matrix.ext; unfold tripleCharges sourceA1417 sourceB1417 sourceC1417 difference raw22082; decide +kernel
    rw [ha]
    exact (canonical22082 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1417 + difference 0 4) (sourceB1417 + difference 4 0) sourceC1417) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1700) := by
    have ha : (tripleCharges (sourceA1417 + difference 0 4) (sourceB1417 + difference 4 0) sourceC1417) = raw22083 := by
      apply Matrix.ext; unfold tripleCharges sourceA1417 sourceB1417 sourceC1417 difference raw22083; decide +kernel
    rw [ha]
    exact (canonical22083 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1417 + difference 0 5) (sourceB1417 + difference 5 0) sourceC1417) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1708) := by
    have ha : (tripleCharges (sourceA1417 + difference 0 5) (sourceB1417 + difference 5 0) sourceC1417) = raw22084 := by
      apply Matrix.ext; unfold tripleCharges sourceA1417 sourceB1417 sourceC1417 difference raw22084; decide +kernel
    rw [ha]
    exact (canonical22084 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1417 + sourceB1417) sourceC1417) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4068) := by
    have ha : (doubleCharges (sourceA1417 + sourceB1417) sourceC1417) = raw22085 := by
      apply Matrix.ext; unfold doubleCharges sourceA1417 sourceB1417 sourceC1417 raw22085; decide +kernel
    rw [ha]
    exact (canonical22085 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1417 sourceB1417 sourceC1417
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1417, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1418 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1418 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1418 + difference 1 0) (sourceB1418 + difference 0 1) sourceC1418) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 542) := by
    have ha : (tripleCharges (sourceA1418 + difference 1 0) (sourceB1418 + difference 0 1) sourceC1418) = raw22086 := by
      apply Matrix.ext; unfold tripleCharges sourceA1418 sourceB1418 sourceC1418 difference raw22086; decide +kernel
    rw [ha]
    exact (canonical22086 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1418 + difference 1 1) (sourceB1418 + difference 1 1) sourceC1418) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 787) := by
    have ha : (tripleCharges (sourceA1418 + difference 1 1) (sourceB1418 + difference 1 1) sourceC1418) = raw22079 := by
      apply Matrix.ext; unfold tripleCharges sourceA1418 sourceB1418 sourceC1418 difference raw22079; decide +kernel
    rw [ha]
    exact (canonical22079 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1418 + difference 1 2) (sourceB1418 + difference 2 1) sourceC1418) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 737) := by
    have ha : (tripleCharges (sourceA1418 + difference 1 2) (sourceB1418 + difference 2 1) sourceC1418) = raw22087 := by
      apply Matrix.ext; unfold tripleCharges sourceA1418 sourceB1418 sourceC1418 difference raw22087; decide +kernel
    rw [ha]
    exact (canonical22087 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1418 + difference 1 3) (sourceB1418 + difference 3 1) sourceC1418) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 702) := by
    have ha : (tripleCharges (sourceA1418 + difference 1 3) (sourceB1418 + difference 3 1) sourceC1418) = raw22088 := by
      apply Matrix.ext; unfold tripleCharges sourceA1418 sourceB1418 sourceC1418 difference raw22088; decide +kernel
    rw [ha]
    exact (canonical22088 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1418 + difference 1 4) (sourceB1418 + difference 4 1) sourceC1418) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 787) := by
    have ha : (tripleCharges (sourceA1418 + difference 1 4) (sourceB1418 + difference 4 1) sourceC1418) = raw22089 := by
      apply Matrix.ext; unfold tripleCharges sourceA1418 sourceB1418 sourceC1418 difference raw22089; decide +kernel
    rw [ha]
    exact (canonical22089 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1418 + difference 1 5) (sourceB1418 + difference 5 1) sourceC1418) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 810) := by
    have ha : (tripleCharges (sourceA1418 + difference 1 5) (sourceB1418 + difference 5 1) sourceC1418) = raw22090 := by
      apply Matrix.ext; unfold tripleCharges sourceA1418 sourceB1418 sourceC1418 difference raw22090; decide +kernel
    rw [ha]
    exact (canonical22090 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1418 + sourceB1418) sourceC1418) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4068) := by
    have ha : (doubleCharges (sourceA1418 + sourceB1418) sourceC1418) = raw22085 := by
      apply Matrix.ext; unfold doubleCharges sourceA1418 sourceB1418 sourceC1418 raw22085; decide +kernel
    rw [ha]
    exact (canonical22085 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1418 sourceB1418 sourceC1418
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1418, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1419 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1419 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1419 + difference 0 5) (sourceB1419 + difference 5 0) sourceC1419) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1708) := by
    have ha : (tripleCharges (sourceA1419 + difference 0 5) (sourceB1419 + difference 5 0) sourceC1419) = raw22084 := by
      apply Matrix.ext; unfold tripleCharges sourceA1419 sourceB1419 sourceC1419 difference raw22084; decide +kernel
    rw [ha]
    exact (canonical22084 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1419 + difference 1 5) (sourceB1419 + difference 5 1) sourceC1419) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 810) := by
    have ha : (tripleCharges (sourceA1419 + difference 1 5) (sourceB1419 + difference 5 1) sourceC1419) = raw22090 := by
      apply Matrix.ext; unfold tripleCharges sourceA1419 sourceB1419 sourceC1419 difference raw22090; decide +kernel
    rw [ha]
    exact (canonical22090 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1419 + difference 2 5) (sourceB1419 + difference 5 2) sourceC1419) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 810) := by
    have ha : (tripleCharges (sourceA1419 + difference 2 5) (sourceB1419 + difference 5 2) sourceC1419) = raw22091 := by
      apply Matrix.ext; unfold tripleCharges sourceA1419 sourceB1419 sourceC1419 difference raw22091; decide +kernel
    rw [ha]
    exact (canonical22091 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1419 + difference 3 5) (sourceB1419 + difference 5 3) sourceC1419) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 783) := by
    have ha : (tripleCharges (sourceA1419 + difference 3 5) (sourceB1419 + difference 5 3) sourceC1419) = raw22092 := by
      apply Matrix.ext; unfold tripleCharges sourceA1419 sourceB1419 sourceC1419 difference raw22092; decide +kernel
    rw [ha]
    exact (canonical22092 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1419 + difference 4 5) (sourceB1419 + difference 5 4) sourceC1419) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 790) := by
    have ha : (tripleCharges (sourceA1419 + difference 4 5) (sourceB1419 + difference 5 4) sourceC1419) = raw22093 := by
      apply Matrix.ext; unfold tripleCharges sourceA1419 sourceB1419 sourceC1419 difference raw22093; decide +kernel
    rw [ha]
    exact (canonical22093 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1419 + difference 5 5) (sourceB1419 + difference 5 5) sourceC1419) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 787) := by
    have ha : (tripleCharges (sourceA1419 + difference 5 5) (sourceB1419 + difference 5 5) sourceC1419) = raw22079 := by
      apply Matrix.ext; unfold tripleCharges sourceA1419 sourceB1419 sourceC1419 difference raw22079; decide +kernel
    rw [ha]
    exact (canonical22079 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1419 + sourceB1419) sourceC1419) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4068) := by
    have ha : (doubleCharges (sourceA1419 + sourceB1419) sourceC1419) = raw22085 := by
      apply Matrix.ext; unfold doubleCharges sourceA1419 sourceB1419 sourceC1419 raw22085; decide +kernel
    rw [ha]
    exact (canonical22085 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1419 sourceB1419 sourceC1419
    (0 : Fin 2) 1 (5 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1419, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1421 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1421 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1421 + difference 0 0) (sourceB1421 + difference 0 0) sourceC1421) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 785) := by
    have ha : (tripleCharges (sourceA1421 + difference 0 0) (sourceB1421 + difference 0 0) sourceC1421) = raw22097 := by
      apply Matrix.ext; unfold tripleCharges sourceA1421 sourceB1421 sourceC1421 difference raw22097; decide +kernel
    rw [ha]
    exact (canonical22097 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1421 + difference 0 1) (sourceB1421 + difference 1 0) sourceC1421) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1637) := by
    have ha : (tripleCharges (sourceA1421 + difference 0 1) (sourceB1421 + difference 1 0) sourceC1421) = raw22098 := by
      apply Matrix.ext; unfold tripleCharges sourceA1421 sourceB1421 sourceC1421 difference raw22098; decide +kernel
    rw [ha]
    exact (canonical22098 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1421 + difference 0 2) (sourceB1421 + difference 2 0) sourceC1421) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1637) := by
    have ha : (tripleCharges (sourceA1421 + difference 0 2) (sourceB1421 + difference 2 0) sourceC1421) = raw22099 := by
      apply Matrix.ext; unfold tripleCharges sourceA1421 sourceB1421 sourceC1421 difference raw22099; decide +kernel
    rw [ha]
    exact (canonical22099 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1421 + difference 0 3) (sourceB1421 + difference 3 0) sourceC1421) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1592) := by
    have ha : (tripleCharges (sourceA1421 + difference 0 3) (sourceB1421 + difference 3 0) sourceC1421) = raw22100 := by
      apply Matrix.ext; unfold tripleCharges sourceA1421 sourceB1421 sourceC1421 difference raw22100; decide +kernel
    rw [ha]
    exact (canonical22100 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1421 + difference 0 4) (sourceB1421 + difference 4 0) sourceC1421) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1710) := by
    have ha : (tripleCharges (sourceA1421 + difference 0 4) (sourceB1421 + difference 4 0) sourceC1421) = raw22101 := by
      apply Matrix.ext; unfold tripleCharges sourceA1421 sourceB1421 sourceC1421 difference raw22101; decide +kernel
    rw [ha]
    exact (canonical22101 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1421 + difference 0 5) (sourceB1421 + difference 5 0) sourceC1421) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1707) := by
    have ha : (tripleCharges (sourceA1421 + difference 0 5) (sourceB1421 + difference 5 0) sourceC1421) = raw22102 := by
      apply Matrix.ext; unfold tripleCharges sourceA1421 sourceB1421 sourceC1421 difference raw22102; decide +kernel
    rw [ha]
    exact (canonical22102 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1421 + sourceB1421) sourceC1421) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4069) := by
    have ha : (doubleCharges (sourceA1421 + sourceB1421) sourceC1421) = raw22103 := by
      apply Matrix.ext; unfold doubleCharges sourceA1421 sourceB1421 sourceC1421 raw22103; decide +kernel
    rw [ha]
    exact (canonical22103 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1421 sourceB1421 sourceC1421
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1421, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1422 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1422 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1422 + difference 1 0) (sourceB1422 + difference 0 1) sourceC1422) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 538) := by
    have ha : (tripleCharges (sourceA1422 + difference 1 0) (sourceB1422 + difference 0 1) sourceC1422) = raw22104 := by
      apply Matrix.ext; unfold tripleCharges sourceA1422 sourceB1422 sourceC1422 difference raw22104; decide +kernel
    rw [ha]
    exact (canonical22104 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1422 + difference 1 1) (sourceB1422 + difference 1 1) sourceC1422) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 785) := by
    have ha : (tripleCharges (sourceA1422 + difference 1 1) (sourceB1422 + difference 1 1) sourceC1422) = raw22097 := by
      apply Matrix.ext; unfold tripleCharges sourceA1422 sourceB1422 sourceC1422 difference raw22097; decide +kernel
    rw [ha]
    exact (canonical22097 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1422 + difference 1 2) (sourceB1422 + difference 2 1) sourceC1422) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 733) := by
    have ha : (tripleCharges (sourceA1422 + difference 1 2) (sourceB1422 + difference 2 1) sourceC1422) = raw22105 := by
      apply Matrix.ext; unfold tripleCharges sourceA1422 sourceB1422 sourceC1422 difference raw22105; decide +kernel
    rw [ha]
    exact (canonical22105 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1422 + difference 1 3) (sourceB1422 + difference 3 1) sourceC1422) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 699) := by
    have ha : (tripleCharges (sourceA1422 + difference 1 3) (sourceB1422 + difference 3 1) sourceC1422) = raw22106 := by
      apply Matrix.ext; unfold tripleCharges sourceA1422 sourceB1422 sourceC1422 difference raw22106; decide +kernel
    rw [ha]
    exact (canonical22106 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1422 + difference 1 4) (sourceB1422 + difference 4 1) sourceC1422) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 812) := by
    have ha : (tripleCharges (sourceA1422 + difference 1 4) (sourceB1422 + difference 4 1) sourceC1422) = raw22107 := by
      apply Matrix.ext; unfold tripleCharges sourceA1422 sourceB1422 sourceC1422 difference raw22107; decide +kernel
    rw [ha]
    exact (canonical22107 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1422 + difference 1 5) (sourceB1422 + difference 5 1) sourceC1422) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 806) := by
    have ha : (tripleCharges (sourceA1422 + difference 1 5) (sourceB1422 + difference 5 1) sourceC1422) = raw22108 := by
      apply Matrix.ext; unfold tripleCharges sourceA1422 sourceB1422 sourceC1422 difference raw22108; decide +kernel
    rw [ha]
    exact (canonical22108 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1422 + sourceB1422) sourceC1422) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4069) := by
    have ha : (doubleCharges (sourceA1422 + sourceB1422) sourceC1422) = raw22103 := by
      apply Matrix.ext; unfold doubleCharges sourceA1422 sourceB1422 sourceC1422 raw22103; decide +kernel
    rw [ha]
    exact (canonical22103 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1422 sourceB1422 sourceC1422
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1422, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1423 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1423 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1423 + difference 0 5) (sourceB1423 + difference 5 0) sourceC1423) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1707) := by
    have ha : (tripleCharges (sourceA1423 + difference 0 5) (sourceB1423 + difference 5 0) sourceC1423) = raw22102 := by
      apply Matrix.ext; unfold tripleCharges sourceA1423 sourceB1423 sourceC1423 difference raw22102; decide +kernel
    rw [ha]
    exact (canonical22102 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1423 + difference 1 5) (sourceB1423 + difference 5 1) sourceC1423) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 806) := by
    have ha : (tripleCharges (sourceA1423 + difference 1 5) (sourceB1423 + difference 5 1) sourceC1423) = raw22108 := by
      apply Matrix.ext; unfold tripleCharges sourceA1423 sourceB1423 sourceC1423 difference raw22108; decide +kernel
    rw [ha]
    exact (canonical22108 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1423 + difference 2 5) (sourceB1423 + difference 5 2) sourceC1423) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 806) := by
    have ha : (tripleCharges (sourceA1423 + difference 2 5) (sourceB1423 + difference 5 2) sourceC1423) = raw22109 := by
      apply Matrix.ext; unfold tripleCharges sourceA1423 sourceB1423 sourceC1423 difference raw22109; decide +kernel
    rw [ha]
    exact (canonical22109 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1423 + difference 3 5) (sourceB1423 + difference 5 3) sourceC1423) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 782) := by
    have ha : (tripleCharges (sourceA1423 + difference 3 5) (sourceB1423 + difference 5 3) sourceC1423) = raw22110 := by
      apply Matrix.ext; unfold tripleCharges sourceA1423 sourceB1423 sourceC1423 difference raw22110; decide +kernel
    rw [ha]
    exact (canonical22110 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1423 + difference 4 5) (sourceB1423 + difference 5 4) sourceC1423) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 789) := by
    have ha : (tripleCharges (sourceA1423 + difference 4 5) (sourceB1423 + difference 5 4) sourceC1423) = raw22111 := by
      apply Matrix.ext; unfold tripleCharges sourceA1423 sourceB1423 sourceC1423 difference raw22111; decide +kernel
    rw [ha]
    exact (canonical22111 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1423 + difference 5 5) (sourceB1423 + difference 5 5) sourceC1423) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 785) := by
    have ha : (tripleCharges (sourceA1423 + difference 5 5) (sourceB1423 + difference 5 5) sourceC1423) = raw22097 := by
      apply Matrix.ext; unfold tripleCharges sourceA1423 sourceB1423 sourceC1423 difference raw22097; decide +kernel
    rw [ha]
    exact (canonical22097 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1423 + sourceB1423) sourceC1423) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4069) := by
    have ha : (doubleCharges (sourceA1423 + sourceB1423) sourceC1423) = raw22103 := by
      apply Matrix.ext; unfold doubleCharges sourceA1423 sourceB1423 sourceC1423 raw22103; decide +kernel
    rw [ha]
    exact (canonical22103 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1423 sourceB1423 sourceC1423
    (0 : Fin 2) 1 (5 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1423, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1424 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1424 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1424 + difference 5 0) (sourceB1424 + difference 0 5) sourceC1424) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 536) := by
    have ha : (tripleCharges (sourceA1424 + difference 5 0) (sourceB1424 + difference 0 5) sourceC1424) = raw22112 := by
      apply Matrix.ext; unfold tripleCharges sourceA1424 sourceB1424 sourceC1424 difference raw22112; decide +kernel
    rw [ha]
    exact (canonical22112 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1424 + difference 5 1) (sourceB1424 + difference 1 5) sourceC1424) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 809) := by
    have ha : (tripleCharges (sourceA1424 + difference 5 1) (sourceB1424 + difference 1 5) sourceC1424) = raw22113 := by
      apply Matrix.ext; unfold tripleCharges sourceA1424 sourceB1424 sourceC1424 difference raw22113; decide +kernel
    rw [ha]
    exact (canonical22113 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1424 + difference 5 2) (sourceB1424 + difference 2 5) sourceC1424) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 809) := by
    have ha : (tripleCharges (sourceA1424 + difference 5 2) (sourceB1424 + difference 2 5) sourceC1424) = raw21578 := by
      apply Matrix.ext; unfold tripleCharges sourceA1424 sourceB1424 sourceC1424 difference raw21578; decide +kernel
    rw [ha]
    exact (canonical21578 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1424 + difference 5 3) (sourceB1424 + difference 3 5) sourceC1424) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 698) := by
    have ha : (tripleCharges (sourceA1424 + difference 5 3) (sourceB1424 + difference 3 5) sourceC1424) = raw21632 := by
      apply Matrix.ext; unfold tripleCharges sourceA1424 sourceB1424 sourceC1424 difference raw21632; decide +kernel
    rw [ha]
    exact (canonical21632 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1424 + difference 5 4) (sourceB1424 + difference 4 5) sourceC1424) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 731) := by
    have ha : (tripleCharges (sourceA1424 + difference 5 4) (sourceB1424 + difference 4 5) sourceC1424) = raw21576 := by
      apply Matrix.ext; unfold tripleCharges sourceA1424 sourceB1424 sourceC1424 difference raw21576; decide +kernel
    rw [ha]
    exact (canonical21576 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1424 + difference 5 5) (sourceB1424 + difference 5 5) sourceC1424) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 804) := by
    have ha : (tripleCharges (sourceA1424 + difference 5 5) (sourceB1424 + difference 5 5) sourceC1424) = raw22096 := by
      apply Matrix.ext; unfold tripleCharges sourceA1424 sourceB1424 sourceC1424 difference raw22096; decide +kernel
    rw [ha]
    exact (canonical22096 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1424 + sourceB1424) sourceC1424) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4070) := by
    have ha : (doubleCharges (sourceA1424 + sourceB1424) sourceC1424) = raw20099 := by
      apply Matrix.ext; unfold doubleCharges sourceA1424 sourceB1424 sourceC1424 raw20099; decide +kernel
    rw [ha]
    exact (canonical20099 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1424 sourceB1424 sourceC1424
    (0 : Fin 2) 1 (5 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1424, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1425 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1425 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1425 + difference 0 0) (sourceB1425 + difference 0 0) sourceC1425) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 813) := by
    have ha : (tripleCharges (sourceA1425 + difference 0 0) (sourceB1425 + difference 0 0) sourceC1425) = raw22114 := by
      apply Matrix.ext; unfold tripleCharges sourceA1425 sourceB1425 sourceC1425 difference raw22114; decide +kernel
    rw [ha]
    exact (canonical22114 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1425 + difference 0 1) (sourceB1425 + difference 1 0) sourceC1425) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1651) := by
    have ha : (tripleCharges (sourceA1425 + difference 0 1) (sourceB1425 + difference 1 0) sourceC1425) = raw22115 := by
      apply Matrix.ext; unfold tripleCharges sourceA1425 sourceB1425 sourceC1425 difference raw22115; decide +kernel
    rw [ha]
    exact (canonical22115 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1425 + difference 0 2) (sourceB1425 + difference 2 0) sourceC1425) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1603) := by
    have ha : (tripleCharges (sourceA1425 + difference 0 2) (sourceB1425 + difference 2 0) sourceC1425) = raw22116 := by
      apply Matrix.ext; unfold tripleCharges sourceA1425 sourceB1425 sourceC1425 difference raw22116; decide +kernel
    rw [ha]
    exact (canonical22116 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1425 + difference 0 3) (sourceB1425 + difference 3 0) sourceC1425) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1603) := by
    have ha : (tripleCharges (sourceA1425 + difference 0 3) (sourceB1425 + difference 3 0) sourceC1425) = raw22117 := by
      apply Matrix.ext; unfold tripleCharges sourceA1425 sourceB1425 sourceC1425 difference raw22117; decide +kernel
    rw [ha]
    exact (canonical22117 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1425 + difference 0 4) (sourceB1425 + difference 4 0) sourceC1425) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1716) := by
    have ha : (tripleCharges (sourceA1425 + difference 0 4) (sourceB1425 + difference 4 0) sourceC1425) = raw22118 := by
      apply Matrix.ext; unfold tripleCharges sourceA1425 sourceB1425 sourceC1425 difference raw22118; decide +kernel
    rw [ha]
    exact (canonical22118 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1425 + difference 0 5) (sourceB1425 + difference 5 0) sourceC1425) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1728) := by
    have ha : (tripleCharges (sourceA1425 + difference 0 5) (sourceB1425 + difference 5 0) sourceC1425) = raw22119 := by
      apply Matrix.ext; unfold tripleCharges sourceA1425 sourceB1425 sourceC1425 difference raw22119; decide +kernel
    rw [ha]
    exact (canonical22119 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1425 + sourceB1425) sourceC1425) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4069) := by
    have ha : (doubleCharges (sourceA1425 + sourceB1425) sourceC1425) = raw22120 := by
      apply Matrix.ext; unfold doubleCharges sourceA1425 sourceB1425 sourceC1425 raw22120; decide +kernel
    rw [ha]
    exact (canonical22120 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1425 sourceB1425 sourceC1425
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1425, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1426 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1426 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1426 + difference 4 0) (sourceB1426 + difference 0 4) sourceC1426) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 548) := by
    have ha : (tripleCharges (sourceA1426 + difference 4 0) (sourceB1426 + difference 0 4) sourceC1426) = raw22121 := by
      apply Matrix.ext; unfold tripleCharges sourceA1426 sourceB1426 sourceC1426 difference raw22121; decide +kernel
    rw [ha]
    exact (canonical22121 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1426 + difference 4 1) (sourceB1426 + difference 1 4) sourceC1426) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 743) := by
    have ha : (tripleCharges (sourceA1426 + difference 4 1) (sourceB1426 + difference 1 4) sourceC1426) = raw22122 := by
      apply Matrix.ext; unfold tripleCharges sourceA1426 sourceB1426 sourceC1426 difference raw22122; decide +kernel
    rw [ha]
    exact (canonical22122 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1426 + difference 4 2) (sourceB1426 + difference 2 4) sourceC1426) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 708) := by
    have ha : (tripleCharges (sourceA1426 + difference 4 2) (sourceB1426 + difference 2 4) sourceC1426) = raw22123 := by
      apply Matrix.ext; unfold tripleCharges sourceA1426 sourceB1426 sourceC1426 difference raw22123; decide +kernel
    rw [ha]
    exact (canonical22123 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1426 + difference 4 3) (sourceB1426 + difference 3 4) sourceC1426) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 708) := by
    have ha : (tripleCharges (sourceA1426 + difference 4 3) (sourceB1426 + difference 3 4) sourceC1426) = raw22124 := by
      apply Matrix.ext; unfold tripleCharges sourceA1426 sourceB1426 sourceC1426 difference raw22124; decide +kernel
    rw [ha]
    exact (canonical22124 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1426 + difference 4 4) (sourceB1426 + difference 4 4) sourceC1426) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 813) := by
    have ha : (tripleCharges (sourceA1426 + difference 4 4) (sourceB1426 + difference 4 4) sourceC1426) = raw22114 := by
      apply Matrix.ext; unfold tripleCharges sourceA1426 sourceB1426 sourceC1426 difference raw22114; decide +kernel
    rw [ha]
    exact (canonical22114 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1426 + difference 4 5) (sourceB1426 + difference 5 4) sourceC1426) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 816) := by
    have ha : (tripleCharges (sourceA1426 + difference 4 5) (sourceB1426 + difference 5 4) sourceC1426) = raw22125 := by
      apply Matrix.ext; unfold tripleCharges sourceA1426 sourceB1426 sourceC1426 difference raw22125; decide +kernel
    rw [ha]
    exact (canonical22125 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1426 + sourceB1426) sourceC1426) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4069) := by
    have ha : (doubleCharges (sourceA1426 + sourceB1426) sourceC1426) = raw22120 := by
      apply Matrix.ext; unfold doubleCharges sourceA1426 sourceB1426 sourceC1426 raw22120; decide +kernel
    rw [ha]
    exact (canonical22120 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1426 sourceB1426 sourceC1426
    (0 : Fin 2) 1 (4 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1426, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1427 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1427 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1427 + difference 0 5) (sourceB1427 + difference 5 0) sourceC1427) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1728) := by
    have ha : (tripleCharges (sourceA1427 + difference 0 5) (sourceB1427 + difference 5 0) sourceC1427) = raw22119 := by
      apply Matrix.ext; unfold tripleCharges sourceA1427 sourceB1427 sourceC1427 difference raw22119; decide +kernel
    rw [ha]
    exact (canonical22119 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1427 + difference 1 5) (sourceB1427 + difference 5 1) sourceC1427) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 856) := by
    have ha : (tripleCharges (sourceA1427 + difference 1 5) (sourceB1427 + difference 5 1) sourceC1427) = raw22126 := by
      apply Matrix.ext; unfold tripleCharges sourceA1427 sourceB1427 sourceC1427 difference raw22126; decide +kernel
    rw [ha]
    exact (canonical22126 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1427 + difference 2 5) (sourceB1427 + difference 5 2) sourceC1427) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 807) := by
    have ha : (tripleCharges (sourceA1427 + difference 2 5) (sourceB1427 + difference 5 2) sourceC1427) = raw22127 := by
      apply Matrix.ext; unfold tripleCharges sourceA1427 sourceB1427 sourceC1427 difference raw22127; decide +kernel
    rw [ha]
    exact (canonical22127 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1427 + difference 3 5) (sourceB1427 + difference 5 3) sourceC1427) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 807) := by
    have ha : (tripleCharges (sourceA1427 + difference 3 5) (sourceB1427 + difference 5 3) sourceC1427) = raw22128 := by
      apply Matrix.ext; unfold tripleCharges sourceA1427 sourceB1427 sourceC1427 difference raw22128; decide +kernel
    rw [ha]
    exact (canonical22128 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1427 + difference 4 5) (sourceB1427 + difference 5 4) sourceC1427) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 816) := by
    have ha : (tripleCharges (sourceA1427 + difference 4 5) (sourceB1427 + difference 5 4) sourceC1427) = raw22125 := by
      apply Matrix.ext; unfold tripleCharges sourceA1427 sourceB1427 sourceC1427 difference raw22125; decide +kernel
    rw [ha]
    exact (canonical22125 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1427 + difference 5 5) (sourceB1427 + difference 5 5) sourceC1427) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 813) := by
    have ha : (tripleCharges (sourceA1427 + difference 5 5) (sourceB1427 + difference 5 5) sourceC1427) = raw22114 := by
      apply Matrix.ext; unfold tripleCharges sourceA1427 sourceB1427 sourceC1427 difference raw22114; decide +kernel
    rw [ha]
    exact (canonical22114 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1427 + sourceB1427) sourceC1427) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4069) := by
    have ha : (doubleCharges (sourceA1427 + sourceB1427) sourceC1427) = raw22120 := by
      apply Matrix.ext; unfold doubleCharges sourceA1427 sourceB1427 sourceC1427 raw22120; decide +kernel
    rw [ha]
    exact (canonical22120 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1427 sourceB1427 sourceC1427
    (0 : Fin 2) 1 (5 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1427, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1429 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1429 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1429 + difference 0 1) (sourceB1429 + difference 1 0) sourceC1429) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4490) := by
    have ha : (tripleCharges (sourceA1429 + difference 0 1) (sourceB1429 + difference 1 0) sourceC1429) = raw22131 := by
      apply Matrix.ext; unfold tripleCharges sourceA1429 sourceB1429 sourceC1429 difference raw22131; decide +kernel
    rw [ha]
    exact (canonical22131 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1429 + difference 0 2) (sourceB1429 + difference 2 0) sourceC1429) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4418) := by
    have ha : (tripleCharges (sourceA1429 + difference 0 2) (sourceB1429 + difference 2 0) sourceC1429) = raw22132 := by
      apply Matrix.ext; unfold tripleCharges sourceA1429 sourceB1429 sourceC1429 difference raw22132; decide +kernel
    rw [ha]
    exact (canonical22132 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1429 + difference 0 3) (sourceB1429 + difference 3 0) sourceC1429) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4418) := by
    have ha : (tripleCharges (sourceA1429 + difference 0 3) (sourceB1429 + difference 3 0) sourceC1429) = raw22133 := by
      apply Matrix.ext; unfold tripleCharges sourceA1429 sourceB1429 sourceC1429 difference raw22133; decide +kernel
    rw [ha]
    exact (canonical22133 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1429 + difference 0 4) (sourceB1429 + difference 4 0) sourceC1429) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4496) := by
    have ha : (tripleCharges (sourceA1429 + difference 0 4) (sourceB1429 + difference 4 0) sourceC1429) = raw22134 := by
      apply Matrix.ext; unfold tripleCharges sourceA1429 sourceB1429 sourceC1429 difference raw22134; decide +kernel
    rw [ha]
    exact (canonical22134 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1429 + difference 0 5) (sourceB1429 + difference 5 0) sourceC1429) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4498) := by
    have ha : (tripleCharges (sourceA1429 + difference 0 5) (sourceB1429 + difference 5 0) sourceC1429) = raw22135 := by
      apply Matrix.ext; unfold tripleCharges sourceA1429 sourceB1429 sourceC1429 difference raw22135; decide +kernel
    rw [ha]
    exact (canonical22135 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1429 + difference 1 0) (sourceB1429 + difference 0 1) sourceC1429) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4127) := by
    have ha : (tripleCharges (sourceA1429 + difference 1 0) (sourceB1429 + difference 0 1) sourceC1429) = raw22136 := by
      apply Matrix.ext; unfold tripleCharges sourceA1429 sourceB1429 sourceC1429 difference raw22136; decide +kernel
    rw [ha]
    exact (canonical22136 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1429 + difference 1 2) (sourceB1429 + difference 2 1) sourceC1429) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4218) := by
    have ha : (tripleCharges (sourceA1429 + difference 1 2) (sourceB1429 + difference 2 1) sourceC1429) = raw22137 := by
      apply Matrix.ext; unfold tripleCharges sourceA1429 sourceB1429 sourceC1429 difference raw22137; decide +kernel
    rw [ha]
    exact (canonical22137 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1429 + difference 1 3) (sourceB1429 + difference 3 1) sourceC1429) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4218) := by
    have ha : (tripleCharges (sourceA1429 + difference 1 3) (sourceB1429 + difference 3 1) sourceC1429) = raw22138 := by
      apply Matrix.ext; unfold tripleCharges sourceA1429 sourceB1429 sourceC1429 difference raw22138; decide +kernel
    rw [ha]
    exact (canonical22138 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1429 + difference 1 4) (sourceB1429 + difference 4 1) sourceC1429) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4269) := by
    have ha : (tripleCharges (sourceA1429 + difference 1 4) (sourceB1429 + difference 4 1) sourceC1429) = raw22139 := by
      apply Matrix.ext; unfold tripleCharges sourceA1429 sourceB1429 sourceC1429 difference raw22139; decide +kernel
    rw [ha]
    exact (canonical22139 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1429 + difference 1 5) (sourceB1429 + difference 5 1) sourceC1429) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4069) := by
    have ha : (tripleCharges (sourceA1429 + difference 1 5) (sourceB1429 + difference 5 1) sourceC1429) = raw22140 := by
      apply Matrix.ext; unfold tripleCharges sourceA1429 sourceB1429 sourceC1429 difference raw22140; decide +kernel
    rw [ha]
    exact (canonical22140 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1429 + difference 2 0) (sourceB1429 + difference 0 2) sourceC1429) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4101) := by
    have ha : (tripleCharges (sourceA1429 + difference 2 0) (sourceB1429 + difference 0 2) sourceC1429) = raw22141 := by
      apply Matrix.ext; unfold tripleCharges sourceA1429 sourceB1429 sourceC1429 difference raw22141; decide +kernel
    rw [ha]
    exact (canonical22141 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1429 + difference 2 1) (sourceB1429 + difference 1 2) sourceC1429) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4233) := by
    have ha : (tripleCharges (sourceA1429 + difference 2 1) (sourceB1429 + difference 1 2) sourceC1429) = raw22142 := by
      apply Matrix.ext; unfold tripleCharges sourceA1429 sourceB1429 sourceC1429 difference raw22142; decide +kernel
    rw [ha]
    exact (canonical22142 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1429 + difference 2 3) (sourceB1429 + difference 3 2) sourceC1429) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4196) := by
    have ha : (tripleCharges (sourceA1429 + difference 2 3) (sourceB1429 + difference 3 2) sourceC1429) = raw22143 := by
      apply Matrix.ext; unfold tripleCharges sourceA1429 sourceB1429 sourceC1429 difference raw22143; decide +kernel
    rw [ha]
    exact (canonical22143 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1429 + difference 2 4) (sourceB1429 + difference 4 2) sourceC1429) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4251) := by
    have ha : (tripleCharges (sourceA1429 + difference 2 4) (sourceB1429 + difference 4 2) sourceC1429) = raw22144 := by
      apply Matrix.ext; unfold tripleCharges sourceA1429 sourceB1429 sourceC1429 difference raw22144; decide +kernel
    rw [ha]
    exact (canonical22144 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1429 + difference 2 5) (sourceB1429 + difference 5 2) sourceC1429) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4264) := by
    have ha : (tripleCharges (sourceA1429 + difference 2 5) (sourceB1429 + difference 5 2) sourceC1429) = raw22145 := by
      apply Matrix.ext; unfold tripleCharges sourceA1429 sourceB1429 sourceC1429 difference raw22145; decide +kernel
    rw [ha]
    exact (canonical22145 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1429 + difference 3 0) (sourceB1429 + difference 0 3) sourceC1429) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4101) := by
    have ha : (tripleCharges (sourceA1429 + difference 3 0) (sourceB1429 + difference 0 3) sourceC1429) = raw22146 := by
      apply Matrix.ext; unfold tripleCharges sourceA1429 sourceB1429 sourceC1429 difference raw22146; decide +kernel
    rw [ha]
    exact (canonical22146 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1429 + difference 3 1) (sourceB1429 + difference 1 3) sourceC1429) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4233) := by
    have ha : (tripleCharges (sourceA1429 + difference 3 1) (sourceB1429 + difference 1 3) sourceC1429) = raw22147 := by
      apply Matrix.ext; unfold tripleCharges sourceA1429 sourceB1429 sourceC1429 difference raw22147; decide +kernel
    rw [ha]
    exact (canonical22147 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1429 + difference 3 2) (sourceB1429 + difference 2 3) sourceC1429) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4196) := by
    have ha : (tripleCharges (sourceA1429 + difference 3 2) (sourceB1429 + difference 2 3) sourceC1429) = raw22148 := by
      apply Matrix.ext; unfold tripleCharges sourceA1429 sourceB1429 sourceC1429 difference raw22148; decide +kernel
    rw [ha]
    exact (canonical22148 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1429 + difference 3 4) (sourceB1429 + difference 4 3) sourceC1429) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4251) := by
    have ha : (tripleCharges (sourceA1429 + difference 3 4) (sourceB1429 + difference 4 3) sourceC1429) = raw22149 := by
      apply Matrix.ext; unfold tripleCharges sourceA1429 sourceB1429 sourceC1429 difference raw22149; decide +kernel
    rw [ha]
    exact (canonical22149 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1429 + difference 3 5) (sourceB1429 + difference 5 3) sourceC1429) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4264) := by
    have ha : (tripleCharges (sourceA1429 + difference 3 5) (sourceB1429 + difference 5 3) sourceC1429) = raw22150 := by
      apply Matrix.ext; unfold tripleCharges sourceA1429 sourceB1429 sourceC1429 difference raw22150; decide +kernel
    rw [ha]
    exact (canonical22150 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1429 + difference 4 0) (sourceB1429 + difference 0 4) sourceC1429) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4110) := by
    have ha : (tripleCharges (sourceA1429 + difference 4 0) (sourceB1429 + difference 0 4) sourceC1429) = raw22151 := by
      apply Matrix.ext; unfold tripleCharges sourceA1429 sourceB1429 sourceC1429 difference raw22151; decide +kernel
    rw [ha]
    exact (canonical22151 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1429 + difference 4 1) (sourceB1429 + difference 1 4) sourceC1429) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4242) := by
    have ha : (tripleCharges (sourceA1429 + difference 4 1) (sourceB1429 + difference 1 4) sourceC1429) = raw22152 := by
      apply Matrix.ext; unfold tripleCharges sourceA1429 sourceB1429 sourceC1429 difference raw22152; decide +kernel
    rw [ha]
    exact (canonical22152 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1429 + difference 4 2) (sourceB1429 + difference 2 4) sourceC1429) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4204) := by
    have ha : (tripleCharges (sourceA1429 + difference 4 2) (sourceB1429 + difference 2 4) sourceC1429) = raw22153 := by
      apply Matrix.ext; unfold tripleCharges sourceA1429 sourceB1429 sourceC1429 difference raw22153; decide +kernel
    rw [ha]
    exact (canonical22153 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1429 + difference 4 3) (sourceB1429 + difference 3 4) sourceC1429) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4204) := by
    have ha : (tripleCharges (sourceA1429 + difference 4 3) (sourceB1429 + difference 3 4) sourceC1429) = raw22154 := by
      apply Matrix.ext; unfold tripleCharges sourceA1429 sourceB1429 sourceC1429 difference raw22154; decide +kernel
    rw [ha]
    exact (canonical22154 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1429 + difference 4 5) (sourceB1429 + difference 5 4) sourceC1429) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4273) := by
    have ha : (tripleCharges (sourceA1429 + difference 4 5) (sourceB1429 + difference 5 4) sourceC1429) = raw22155 := by
      apply Matrix.ext; unfold tripleCharges sourceA1429 sourceB1429 sourceC1429 difference raw22155; decide +kernel
    rw [ha]
    exact (canonical22155 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1429 + difference 5 0) (sourceB1429 + difference 0 5) sourceC1429) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4108) := by
    have ha : (tripleCharges (sourceA1429 + difference 5 0) (sourceB1429 + difference 0 5) sourceC1429) = raw22156 := by
      apply Matrix.ext; unfold tripleCharges sourceA1429 sourceB1429 sourceC1429 difference raw22156; decide +kernel
    rw [ha]
    exact (canonical22156 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1429 + difference 5 1) (sourceB1429 + difference 1 5) sourceC1429) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4240) := by
    have ha : (tripleCharges (sourceA1429 + difference 5 1) (sourceB1429 + difference 1 5) sourceC1429) = raw22157 := by
      apply Matrix.ext; unfold tripleCharges sourceA1429 sourceB1429 sourceC1429 difference raw22157; decide +kernel
    rw [ha]
    exact (canonical22157 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1429 + difference 5 2) (sourceB1429 + difference 2 5) sourceC1429) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4202) := by
    have ha : (tripleCharges (sourceA1429 + difference 5 2) (sourceB1429 + difference 2 5) sourceC1429) = raw22158 := by
      apply Matrix.ext; unfold tripleCharges sourceA1429 sourceB1429 sourceC1429 difference raw22158; decide +kernel
    rw [ha]
    exact (canonical22158 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1429 + difference 5 3) (sourceB1429 + difference 3 5) sourceC1429) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4202) := by
    have ha : (tripleCharges (sourceA1429 + difference 5 3) (sourceB1429 + difference 3 5) sourceC1429) = raw22159 := by
      apply Matrix.ext; unfold tripleCharges sourceA1429 sourceB1429 sourceC1429 difference raw22159; decide +kernel
    rw [ha]
    exact (canonical22159 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1429 + difference 5 4) (sourceB1429 + difference 4 5) sourceC1429) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4257) := by
    have ha : (tripleCharges (sourceA1429 + difference 5 4) (sourceB1429 + difference 4 5) sourceC1429) = raw22160 := by
      apply Matrix.ext; unfold tripleCharges sourceA1429 sourceB1429 sourceC1429 difference raw22160; decide +kernel
    rw [ha]
    exact (canonical22160 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1429 sourceB1429 sourceC1429
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1429, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1430 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1430 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1430 + difference 0 1) (sourceB1430 + difference 1 0) sourceC1430) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1074) := by
    have ha : (tripleCharges (sourceA1430 + difference 0 1) (sourceB1430 + difference 1 0) sourceC1430) = raw22161 := by
      apply Matrix.ext; unfold tripleCharges sourceA1430 sourceB1430 sourceC1430 difference raw22161; decide +kernel
    rw [ha]
    exact (canonical22161 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1430 + difference 0 2) (sourceB1430 + difference 2 0) sourceC1430) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 999) := by
    have ha : (tripleCharges (sourceA1430 + difference 0 2) (sourceB1430 + difference 2 0) sourceC1430) = raw22162 := by
      apply Matrix.ext; unfold tripleCharges sourceA1430 sourceB1430 sourceC1430 difference raw22162; decide +kernel
    rw [ha]
    exact (canonical22162 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1430 + difference 0 3) (sourceB1430 + difference 3 0) sourceC1430) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 999) := by
    have ha : (tripleCharges (sourceA1430 + difference 0 3) (sourceB1430 + difference 3 0) sourceC1430) = raw22163 := by
      apply Matrix.ext; unfold tripleCharges sourceA1430 sourceB1430 sourceC1430 difference raw22163; decide +kernel
    rw [ha]
    exact (canonical22163 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1430 + difference 0 4) (sourceB1430 + difference 4 0) sourceC1430) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1080) := by
    have ha : (tripleCharges (sourceA1430 + difference 0 4) (sourceB1430 + difference 4 0) sourceC1430) = raw22164 := by
      apply Matrix.ext; unfold tripleCharges sourceA1430 sourceB1430 sourceC1430 difference raw22164; decide +kernel
    rw [ha]
    exact (canonical22164 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1430 + difference 0 5) (sourceB1430 + difference 5 0) sourceC1430) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1082) := by
    have ha : (tripleCharges (sourceA1430 + difference 0 5) (sourceB1430 + difference 5 0) sourceC1430) = raw22165 := by
      apply Matrix.ext; unfold tripleCharges sourceA1430 sourceB1430 sourceC1430 difference raw22165; decide +kernel
    rw [ha]
    exact (canonical22165 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1430 + difference 1 0) (sourceB1430 + difference 0 1) sourceC1430) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 688) := by
    have ha : (tripleCharges (sourceA1430 + difference 1 0) (sourceB1430 + difference 0 1) sourceC1430) = raw22166 := by
      apply Matrix.ext; unfold tripleCharges sourceA1430 sourceB1430 sourceC1430 difference raw22166; decide +kernel
    rw [ha]
    exact (canonical22166 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1430 + difference 1 2) (sourceB1430 + difference 2 1) sourceC1430) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 767) := by
    have ha : (tripleCharges (sourceA1430 + difference 1 2) (sourceB1430 + difference 2 1) sourceC1430) = raw22167 := by
      apply Matrix.ext; unfold tripleCharges sourceA1430 sourceB1430 sourceC1430 difference raw22167; decide +kernel
    rw [ha]
    exact (canonical22167 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1430 + difference 1 3) (sourceB1430 + difference 3 1) sourceC1430) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 767) := by
    have ha : (tripleCharges (sourceA1430 + difference 1 3) (sourceB1430 + difference 3 1) sourceC1430) = raw22168 := by
      apply Matrix.ext; unfold tripleCharges sourceA1430 sourceB1430 sourceC1430 difference raw22168; decide +kernel
    rw [ha]
    exact (canonical22168 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1430 + difference 1 4) (sourceB1430 + difference 4 1) sourceC1430) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 851) := by
    have ha : (tripleCharges (sourceA1430 + difference 1 4) (sourceB1430 + difference 4 1) sourceC1430) = raw22169 := by
      apply Matrix.ext; unfold tripleCharges sourceA1430 sourceB1430 sourceC1430 difference raw22169; decide +kernel
    rw [ha]
    exact (canonical22169 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1430 + difference 1 5) (sourceB1430 + difference 5 1) sourceC1430) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4069) := by
    have ha : (tripleCharges (sourceA1430 + difference 1 5) (sourceB1430 + difference 5 1) sourceC1430) = raw22170 := by
      apply Matrix.ext; unfold tripleCharges sourceA1430 sourceB1430 sourceC1430 difference raw22170; decide +kernel
    rw [ha]
    exact (canonical22170 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1430 + difference 2 0) (sourceB1430 + difference 0 2) sourceC1430) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 663) := by
    have ha : (tripleCharges (sourceA1430 + difference 2 0) (sourceB1430 + difference 0 2) sourceC1430) = raw22171 := by
      apply Matrix.ext; unfold tripleCharges sourceA1430 sourceB1430 sourceC1430 difference raw22171; decide +kernel
    rw [ha]
    exact (canonical22171 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1430 + difference 2 1) (sourceB1430 + difference 1 2) sourceC1430) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 799) := by
    have ha : (tripleCharges (sourceA1430 + difference 2 1) (sourceB1430 + difference 1 2) sourceC1430) = raw22172 := by
      apply Matrix.ext; unfold tripleCharges sourceA1430 sourceB1430 sourceC1430 difference raw22172; decide +kernel
    rw [ha]
    exact (canonical22172 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1430 + difference 2 3) (sourceB1430 + difference 3 2) sourceC1430) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 748) := by
    have ha : (tripleCharges (sourceA1430 + difference 2 3) (sourceB1430 + difference 3 2) sourceC1430) = raw22173 := by
      apply Matrix.ext; unfold tripleCharges sourceA1430 sourceB1430 sourceC1430 difference raw22173; decide +kernel
    rw [ha]
    exact (canonical22173 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1430 + difference 2 4) (sourceB1430 + difference 4 2) sourceC1430) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 804) := by
    have ha : (tripleCharges (sourceA1430 + difference 2 4) (sourceB1430 + difference 4 2) sourceC1430) = raw22174 := by
      apply Matrix.ext; unfold tripleCharges sourceA1430 sourceB1430 sourceC1430 difference raw22174; decide +kernel
    rw [ha]
    exact (canonical22174 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1430 + difference 2 5) (sourceB1430 + difference 5 2) sourceC1430) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 806) := by
    have ha : (tripleCharges (sourceA1430 + difference 2 5) (sourceB1430 + difference 5 2) sourceC1430) = raw22175 := by
      apply Matrix.ext; unfold tripleCharges sourceA1430 sourceB1430 sourceC1430 difference raw22175; decide +kernel
    rw [ha]
    exact (canonical22175 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1430 + difference 3 0) (sourceB1430 + difference 0 3) sourceC1430) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 663) := by
    have ha : (tripleCharges (sourceA1430 + difference 3 0) (sourceB1430 + difference 0 3) sourceC1430) = raw22176 := by
      apply Matrix.ext; unfold tripleCharges sourceA1430 sourceB1430 sourceC1430 difference raw22176; decide +kernel
    rw [ha]
    exact (canonical22176 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1430 + difference 3 1) (sourceB1430 + difference 1 3) sourceC1430) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 799) := by
    have ha : (tripleCharges (sourceA1430 + difference 3 1) (sourceB1430 + difference 1 3) sourceC1430) = raw22177 := by
      apply Matrix.ext; unfold tripleCharges sourceA1430 sourceB1430 sourceC1430 difference raw22177; decide +kernel
    rw [ha]
    exact (canonical22177 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1430 + difference 3 2) (sourceB1430 + difference 2 3) sourceC1430) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 748) := by
    have ha : (tripleCharges (sourceA1430 + difference 3 2) (sourceB1430 + difference 2 3) sourceC1430) = raw22178 := by
      apply Matrix.ext; unfold tripleCharges sourceA1430 sourceB1430 sourceC1430 difference raw22178; decide +kernel
    rw [ha]
    exact (canonical22178 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1430 + difference 3 4) (sourceB1430 + difference 4 3) sourceC1430) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 804) := by
    have ha : (tripleCharges (sourceA1430 + difference 3 4) (sourceB1430 + difference 4 3) sourceC1430) = raw22179 := by
      apply Matrix.ext; unfold tripleCharges sourceA1430 sourceB1430 sourceC1430 difference raw22179; decide +kernel
    rw [ha]
    exact (canonical22179 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1430 + difference 3 5) (sourceB1430 + difference 5 3) sourceC1430) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 806) := by
    have ha : (tripleCharges (sourceA1430 + difference 3 5) (sourceB1430 + difference 5 3) sourceC1430) = raw22180 := by
      apply Matrix.ext; unfold tripleCharges sourceA1430 sourceB1430 sourceC1430 difference raw22180; decide +kernel
    rw [ha]
    exact (canonical22180 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1430 + difference 4 0) (sourceB1430 + difference 0 4) sourceC1430) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 684) := by
    have ha : (tripleCharges (sourceA1430 + difference 4 0) (sourceB1430 + difference 0 4) sourceC1430) = raw22181 := by
      apply Matrix.ext; unfold tripleCharges sourceA1430 sourceB1430 sourceC1430 difference raw22181; decide +kernel
    rw [ha]
    exact (canonical22181 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1430 + difference 4 1) (sourceB1430 + difference 1 4) sourceC1430) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 843) := by
    have ha : (tripleCharges (sourceA1430 + difference 4 1) (sourceB1430 + difference 1 4) sourceC1430) = raw22182 := by
      apply Matrix.ext; unfold tripleCharges sourceA1430 sourceB1430 sourceC1430 difference raw22182; decide +kernel
    rw [ha]
    exact (canonical22182 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1430 + difference 4 2) (sourceB1430 + difference 2 4) sourceC1430) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 763) := by
    have ha : (tripleCharges (sourceA1430 + difference 4 2) (sourceB1430 + difference 2 4) sourceC1430) = raw22183 := by
      apply Matrix.ext; unfold tripleCharges sourceA1430 sourceB1430 sourceC1430 difference raw22183; decide +kernel
    rw [ha]
    exact (canonical22183 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1430 + difference 4 3) (sourceB1430 + difference 3 4) sourceC1430) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 763) := by
    have ha : (tripleCharges (sourceA1430 + difference 4 3) (sourceB1430 + difference 3 4) sourceC1430) = raw22184 := by
      apply Matrix.ext; unfold tripleCharges sourceA1430 sourceB1430 sourceC1430 difference raw22184; decide +kernel
    rw [ha]
    exact (canonical22184 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1430 + difference 4 5) (sourceB1430 + difference 5 4) sourceC1430) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 852) := by
    have ha : (tripleCharges (sourceA1430 + difference 4 5) (sourceB1430 + difference 5 4) sourceC1430) = raw22185 := by
      apply Matrix.ext; unfold tripleCharges sourceA1430 sourceB1430 sourceC1430 difference raw22185; decide +kernel
    rw [ha]
    exact (canonical22185 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1430 + difference 5 0) (sourceB1430 + difference 0 5) sourceC1430) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 683) := by
    have ha : (tripleCharges (sourceA1430 + difference 5 0) (sourceB1430 + difference 0 5) sourceC1430) = raw22186 := by
      apply Matrix.ext; unfold tripleCharges sourceA1430 sourceB1430 sourceC1430 difference raw22186; decide +kernel
    rw [ha]
    exact (canonical22186 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1430 + difference 5 1) (sourceB1430 + difference 1 5) sourceC1430) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 842) := by
    have ha : (tripleCharges (sourceA1430 + difference 5 1) (sourceB1430 + difference 1 5) sourceC1430) = raw22187 := by
      apply Matrix.ext; unfold tripleCharges sourceA1430 sourceB1430 sourceC1430 difference raw22187; decide +kernel
    rw [ha]
    exact (canonical22187 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1430 + difference 5 2) (sourceB1430 + difference 2 5) sourceC1430) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 762) := by
    have ha : (tripleCharges (sourceA1430 + difference 5 2) (sourceB1430 + difference 2 5) sourceC1430) = raw22188 := by
      apply Matrix.ext; unfold tripleCharges sourceA1430 sourceB1430 sourceC1430 difference raw22188; decide +kernel
    rw [ha]
    exact (canonical22188 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1430 + difference 5 3) (sourceB1430 + difference 3 5) sourceC1430) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 762) := by
    have ha : (tripleCharges (sourceA1430 + difference 5 3) (sourceB1430 + difference 3 5) sourceC1430) = raw22189 := by
      apply Matrix.ext; unfold tripleCharges sourceA1430 sourceB1430 sourceC1430 difference raw22189; decide +kernel
    rw [ha]
    exact (canonical22189 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1430 + difference 5 4) (sourceB1430 + difference 4 5) sourceC1430) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 849) := by
    have ha : (tripleCharges (sourceA1430 + difference 5 4) (sourceB1430 + difference 4 5) sourceC1430) = raw22190 := by
      apply Matrix.ext; unfold tripleCharges sourceA1430 sourceB1430 sourceC1430 difference raw22190; decide +kernel
    rw [ha]
    exact (canonical22190 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1430 sourceB1430 sourceC1430
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1430, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1431 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1431 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1431 + difference 0 0) (sourceB1431 + difference 0 0) sourceC1431) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 812) := by
    have ha : (tripleCharges (sourceA1431 + difference 0 0) (sourceB1431 + difference 0 0) sourceC1431) = raw22191 := by
      apply Matrix.ext; unfold tripleCharges sourceA1431 sourceB1431 sourceC1431 difference raw22191; decide +kernel
    rw [ha]
    exact (canonical22191 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1431 + difference 0 1) (sourceB1431 + difference 1 0) sourceC1431) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1650) := by
    have ha : (tripleCharges (sourceA1431 + difference 0 1) (sourceB1431 + difference 1 0) sourceC1431) = raw22192 := by
      apply Matrix.ext; unfold tripleCharges sourceA1431 sourceB1431 sourceC1431 difference raw22192; decide +kernel
    rw [ha]
    exact (canonical22192 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1431 + difference 0 2) (sourceB1431 + difference 2 0) sourceC1431) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1602) := by
    have ha : (tripleCharges (sourceA1431 + difference 0 2) (sourceB1431 + difference 2 0) sourceC1431) = raw22193 := by
      apply Matrix.ext; unfold tripleCharges sourceA1431 sourceB1431 sourceC1431 difference raw22193; decide +kernel
    rw [ha]
    exact (canonical22193 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1431 + difference 0 3) (sourceB1431 + difference 3 0) sourceC1431) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1602) := by
    have ha : (tripleCharges (sourceA1431 + difference 0 3) (sourceB1431 + difference 3 0) sourceC1431) = raw22194 := by
      apply Matrix.ext; unfold tripleCharges sourceA1431 sourceB1431 sourceC1431 difference raw22194; decide +kernel
    rw [ha]
    exact (canonical22194 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1431 + difference 0 4) (sourceB1431 + difference 4 0) sourceC1431) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1710) := by
    have ha : (tripleCharges (sourceA1431 + difference 0 4) (sourceB1431 + difference 4 0) sourceC1431) = raw22195 := by
      apply Matrix.ext; unfold tripleCharges sourceA1431 sourceB1431 sourceC1431 difference raw22195; decide +kernel
    rw [ha]
    exact (canonical22195 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1431 + difference 0 5) (sourceB1431 + difference 5 0) sourceC1431) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1727) := by
    have ha : (tripleCharges (sourceA1431 + difference 0 5) (sourceB1431 + difference 5 0) sourceC1431) = raw22196 := by
      apply Matrix.ext; unfold tripleCharges sourceA1431 sourceB1431 sourceC1431 difference raw22196; decide +kernel
    rw [ha]
    exact (canonical22196 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1431 + sourceB1431) sourceC1431) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4069) := by
    have ha : (doubleCharges (sourceA1431 + sourceB1431) sourceC1431) = raw22197 := by
      apply Matrix.ext; unfold doubleCharges sourceA1431 sourceB1431 sourceC1431 raw22197; decide +kernel
    rw [ha]
    exact (canonical22197 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1431 sourceB1431 sourceC1431
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1431, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1433 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1433 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1433 + difference 0 1) (sourceB1433 + difference 1 0) sourceC1433) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1650) := by
    have ha : (tripleCharges (sourceA1433 + difference 0 1) (sourceB1433 + difference 1 0) sourceC1433) = raw22192 := by
      apply Matrix.ext; unfold tripleCharges sourceA1433 sourceB1433 sourceC1433 difference raw22192; decide +kernel
    rw [ha]
    exact (canonical22192 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1433 + difference 1 1) (sourceB1433 + difference 1 1) sourceC1433) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 812) := by
    have ha : (tripleCharges (sourceA1433 + difference 1 1) (sourceB1433 + difference 1 1) sourceC1433) = raw22191 := by
      apply Matrix.ext; unfold tripleCharges sourceA1433 sourceB1433 sourceC1433 difference raw22191; decide +kernel
    rw [ha]
    exact (canonical22191 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1433 + difference 2 1) (sourceB1433 + difference 1 2) sourceC1433) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 733) := by
    have ha : (tripleCharges (sourceA1433 + difference 2 1) (sourceB1433 + difference 1 2) sourceC1433) = raw22203 := by
      apply Matrix.ext; unfold tripleCharges sourceA1433 sourceB1433 sourceC1433 difference raw22203; decide +kernel
    rw [ha]
    exact (canonical22203 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1433 + difference 3 1) (sourceB1433 + difference 1 3) sourceC1433) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 733) := by
    have ha : (tripleCharges (sourceA1433 + difference 3 1) (sourceB1433 + difference 1 3) sourceC1433) = raw22204 := by
      apply Matrix.ext; unfold tripleCharges sourceA1433 sourceB1433 sourceC1433 difference raw22204; decide +kernel
    rw [ha]
    exact (canonical22204 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1433 + difference 4 1) (sourceB1433 + difference 1 4) sourceC1433) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 742) := by
    have ha : (tripleCharges (sourceA1433 + difference 4 1) (sourceB1433 + difference 1 4) sourceC1433) = raw22205 := by
      apply Matrix.ext; unfold tripleCharges sourceA1433 sourceB1433 sourceC1433 difference raw22205; decide +kernel
    rw [ha]
    exact (canonical22205 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1433 + difference 5 1) (sourceB1433 + difference 1 5) sourceC1433) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 740) := by
    have ha : (tripleCharges (sourceA1433 + difference 5 1) (sourceB1433 + difference 1 5) sourceC1433) = raw22206 := by
      apply Matrix.ext; unfold tripleCharges sourceA1433 sourceB1433 sourceC1433 difference raw22206; decide +kernel
    rw [ha]
    exact (canonical22206 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1433 + sourceB1433) sourceC1433) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4069) := by
    have ha : (doubleCharges (sourceA1433 + sourceB1433) sourceC1433) = raw22197 := by
      apply Matrix.ext; unfold doubleCharges sourceA1433 sourceB1433 sourceC1433 raw22197; decide +kernel
    rw [ha]
    exact (canonical22197 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1433 sourceB1433 sourceC1433
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1433, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic76
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reindexCheck1216 : Integer.Sparse.reindex keyMap MixedData.row1216 = numericRow1216 := by decide +kernel

theorem numericCheck1216 (x : Master → ℝ) : Integer.Sparse.eval numericRow1216 x =
    (1 : ℝ) * reducedSource1216 x := by
  norm_num [numericRow1216, reducedSource1216, Integer.Sparse.eval, Sparse.eval, nodeValue776, nodeValue778, nodeValue783, nodeValue1698, nodeValue4068]

theorem reindexCheck1217 : Integer.Sparse.reindex keyMap MixedData.row1217 = numericRow1217 := by decide +kernel

theorem numericCheck1217 (x : Master → ℝ) : Integer.Sparse.eval numericRow1217 x =
    (1 : ℝ) * reducedSource1217 x := by
  norm_num [numericRow1217, reducedSource1217, Integer.Sparse.eval, Sparse.eval, nodeValue787, nodeValue1593, nodeValue1639, nodeValue1700, nodeValue1708, nodeValue4068]

theorem reindexCheck1218 : Integer.Sparse.reindex keyMap MixedData.row1218 = numericRow1218 := by decide +kernel

theorem numericCheck1218 (x : Master → ℝ) : Integer.Sparse.eval numericRow1218 x =
    (1 : ℝ) * reducedSource1218 x := by
  norm_num [numericRow1218, reducedSource1218, Integer.Sparse.eval, Sparse.eval, nodeValue542, nodeValue702, nodeValue737, nodeValue787, nodeValue810, nodeValue4068]

theorem reindexCheck1219 : Integer.Sparse.reindex keyMap MixedData.row1219 = numericRow1219 := by decide +kernel

theorem numericCheck1219 (x : Master → ℝ) : Integer.Sparse.eval numericRow1219 x =
    (1 : ℝ) * reducedSource1219 x := by
  norm_num [numericRow1219, reducedSource1219, Integer.Sparse.eval, Sparse.eval, nodeValue783, nodeValue787, nodeValue790, nodeValue810, nodeValue1708, nodeValue4068]

theorem reindexCheck1220 : Integer.Sparse.reindex keyMap MixedData.row1220 = numericRow1220 := by decide +kernel

theorem numericCheck1220 (x : Master → ℝ) : Integer.Sparse.eval numericRow1220 x =
    (1 : ℝ) * reducedSource1220 x := by
  norm_num [numericRow1220, reducedSource1220, Integer.Sparse.eval, Sparse.eval, nodeValue785, nodeValue1592, nodeValue1637, nodeValue1707, nodeValue1710, nodeValue4069]

theorem reindexCheck1221 : Integer.Sparse.reindex keyMap MixedData.row1221 = numericRow1221 := by decide +kernel

theorem numericCheck1221 (x : Master → ℝ) : Integer.Sparse.eval numericRow1221 x =
    (1 : ℝ) * reducedSource1221 x := by
  norm_num [numericRow1221, reducedSource1221, Integer.Sparse.eval, Sparse.eval, nodeValue538, nodeValue699, nodeValue733, nodeValue785, nodeValue806, nodeValue812, nodeValue4069]

theorem reindexCheck1222 : Integer.Sparse.reindex keyMap MixedData.row1222 = numericRow1222 := by decide +kernel

theorem numericCheck1222 (x : Master → ℝ) : Integer.Sparse.eval numericRow1222 x =
    (1 : ℝ) * reducedSource1222 x := by
  norm_num [numericRow1222, reducedSource1222, Integer.Sparse.eval, Sparse.eval, nodeValue782, nodeValue785, nodeValue789, nodeValue806, nodeValue1707, nodeValue4069]

theorem reindexCheck1223 : Integer.Sparse.reindex keyMap MixedData.row1223 = numericRow1223 := by decide +kernel

theorem numericCheck1223 (x : Master → ℝ) : Integer.Sparse.eval numericRow1223 x =
    (1 : ℝ) * reducedSource1223 x := by
  norm_num [numericRow1223, reducedSource1223, Integer.Sparse.eval, Sparse.eval, nodeValue536, nodeValue698, nodeValue731, nodeValue804, nodeValue809, nodeValue4070]

theorem reindexCheck1224 : Integer.Sparse.reindex keyMap MixedData.row1224 = numericRow1224 := by decide +kernel

theorem numericCheck1224 (x : Master → ℝ) : Integer.Sparse.eval numericRow1224 x =
    (1 : ℝ) * reducedSource1224 x := by
  norm_num [numericRow1224, reducedSource1224, Integer.Sparse.eval, Sparse.eval, nodeValue813, nodeValue1603, nodeValue1651, nodeValue1716, nodeValue1728, nodeValue4069]

theorem reindexCheck1225 : Integer.Sparse.reindex keyMap MixedData.row1225 = numericRow1225 := by decide +kernel

theorem numericCheck1225 (x : Master → ℝ) : Integer.Sparse.eval numericRow1225 x =
    (1 : ℝ) * reducedSource1225 x := by
  norm_num [numericRow1225, reducedSource1225, Integer.Sparse.eval, Sparse.eval, nodeValue548, nodeValue708, nodeValue743, nodeValue813, nodeValue816, nodeValue4069]

theorem reindexCheck1226 : Integer.Sparse.reindex keyMap MixedData.row1226 = numericRow1226 := by decide +kernel

theorem numericCheck1226 (x : Master → ℝ) : Integer.Sparse.eval numericRow1226 x =
    (1 : ℝ) * reducedSource1226 x := by
  norm_num [numericRow1226, reducedSource1226, Integer.Sparse.eval, Sparse.eval, nodeValue807, nodeValue813, nodeValue816, nodeValue856, nodeValue1728, nodeValue4069]

theorem reindexCheck1227 : Integer.Sparse.reindex keyMap MixedData.row1227 = numericRow1227 := by decide +kernel

theorem numericCheck1227 (x : Master → ℝ) : Integer.Sparse.eval numericRow1227 x =
    (4 : ℝ) * reducedSource1227 x := by
  norm_num [numericRow1227, reducedSource1227, Integer.Sparse.eval, Sparse.eval, nodeValue4069, nodeValue4101, nodeValue4108, nodeValue4110, nodeValue4127, nodeValue4196, nodeValue4202, nodeValue4204, nodeValue4218, nodeValue4233, nodeValue4240, nodeValue4242, nodeValue4251, nodeValue4257, nodeValue4264, nodeValue4269, nodeValue4273, nodeValue4418, nodeValue4490, nodeValue4496, nodeValue4498]
  ring

theorem reindexCheck1228 : Integer.Sparse.reindex keyMap MixedData.row1228 = numericRow1228 := by decide +kernel

theorem numericCheck1228 (x : Master → ℝ) : Integer.Sparse.eval numericRow1228 x =
    (1 : ℝ) * reducedSource1228 x := by
  norm_num [numericRow1228, reducedSource1228, Integer.Sparse.eval, Sparse.eval, nodeValue663, nodeValue683, nodeValue684, nodeValue688, nodeValue748, nodeValue762, nodeValue763, nodeValue767, nodeValue799, nodeValue804, nodeValue806, nodeValue842, nodeValue843, nodeValue849, nodeValue851, nodeValue852, nodeValue999, nodeValue1074, nodeValue1080, nodeValue1082, nodeValue4069]

theorem reindexCheck1229 : Integer.Sparse.reindex keyMap MixedData.row1229 = numericRow1229 := by decide +kernel

theorem numericCheck1229 (x : Master → ℝ) : Integer.Sparse.eval numericRow1229 x =
    (1 : ℝ) * reducedSource1229 x := by
  norm_num [numericRow1229, reducedSource1229, Integer.Sparse.eval, Sparse.eval, nodeValue812, nodeValue1602, nodeValue1650, nodeValue1710, nodeValue1727, nodeValue4069]

theorem reindexCheck1230 : Integer.Sparse.reindex keyMap MixedData.row1230 = numericRow1230 := by decide +kernel

theorem numericCheck1230 (x : Master → ℝ) : Integer.Sparse.eval numericRow1230 x =
    (1 : ℝ) * reducedSource1230 x := by
  norm_num [numericRow1230, reducedSource1230, Integer.Sparse.eval, Sparse.eval, nodeValue733, nodeValue740, nodeValue742, nodeValue812, nodeValue1650, nodeValue4069]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Rows76
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero1216 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1216 (mixedVector B) = 0 := by
  have h776 : mixedVector B (Sum.inr 776) = Sparse.eval nodeValue776 (mixedVector B) := by
    change mixedMoment B node776 node776Labels = _
    exact sound776 B hB hF
  have h778 : mixedVector B (Sum.inr 778) = Sparse.eval nodeValue778 (mixedVector B) := by
    change mixedMoment B node778 node778Labels = _
    exact sound778 B hB hF
  have h783 : mixedVector B (Sum.inr 783) = Sparse.eval nodeValue783 (mixedVector B) := by
    change mixedMoment B node783 node783Labels = _
    exact sound783 B hB hF
  have h1698 : mixedVector B (Sum.inr 1698) = Sparse.eval nodeValue1698 (mixedVector B) := by
    change mixedMoment B node1698 node1698Labels = _
    exact sound1698 B hB hF
  have h4068 : mixedVector B (Sum.inr 4068) = Sparse.eval nodeValue4068 (mixedVector B) := by
    change mixedMoment B node4068 node4068Labels = _
    exact sound4068 B hB hF
  simpa only [sourceForm1415, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h776, h778, h783, h1698, h4068, reducedSource1216] using sourceEq1415 B hB

theorem rowSound1216 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1216 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1216, numericCheck1216, reducedZero1216 B hB hF, mul_zero]

theorem reducedZero1217 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1217 (mixedVector B) = 0 := by
  have h787 : mixedVector B (Sum.inr 787) = Sparse.eval nodeValue787 (mixedVector B) := by
    change mixedMoment B node787 node787Labels = _
    exact sound787 B hB hF
  have h1593 : mixedVector B (Sum.inr 1593) = Sparse.eval nodeValue1593 (mixedVector B) := by
    change mixedMoment B node1593 node1593Labels = _
    exact sound1593 B hB hF
  have h1639 : mixedVector B (Sum.inr 1639) = Sparse.eval nodeValue1639 (mixedVector B) := by
    change mixedMoment B node1639 node1639Labels = _
    exact sound1639 B hB hF
  have h1700 : mixedVector B (Sum.inr 1700) = Sparse.eval nodeValue1700 (mixedVector B) := by
    change mixedMoment B node1700 node1700Labels = _
    exact sound1700 B hB hF
  have h1708 : mixedVector B (Sum.inr 1708) = Sparse.eval nodeValue1708 (mixedVector B) := by
    change mixedMoment B node1708 node1708Labels = _
    exact sound1708 B hB hF
  have h4068 : mixedVector B (Sum.inr 4068) = Sparse.eval nodeValue4068 (mixedVector B) := by
    change mixedMoment B node4068 node4068Labels = _
    exact sound4068 B hB hF
  simpa only [sourceForm1417, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h787, h1593, h1639, h1700, h1708, h4068, reducedSource1217] using sourceEq1417 B hB

theorem rowSound1217 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1217 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1217, numericCheck1217, reducedZero1217 B hB hF, mul_zero]

theorem reducedZero1218 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1218 (mixedVector B) = 0 := by
  have h542 : mixedVector B (Sum.inr 542) = Sparse.eval nodeValue542 (mixedVector B) := by
    change mixedMoment B node542 node542Labels = _
    exact sound542 B hB hF
  have h702 : mixedVector B (Sum.inr 702) = Sparse.eval nodeValue702 (mixedVector B) := by
    change mixedMoment B node702 node702Labels = _
    exact sound702 B hB hF
  have h737 : mixedVector B (Sum.inr 737) = Sparse.eval nodeValue737 (mixedVector B) := by
    change mixedMoment B node737 node737Labels = _
    exact sound737 B hB hF
  have h787 : mixedVector B (Sum.inr 787) = Sparse.eval nodeValue787 (mixedVector B) := by
    change mixedMoment B node787 node787Labels = _
    exact sound787 B hB hF
  have h810 : mixedVector B (Sum.inr 810) = Sparse.eval nodeValue810 (mixedVector B) := by
    change mixedMoment B node810 node810Labels = _
    exact sound810 B hB hF
  have h4068 : mixedVector B (Sum.inr 4068) = Sparse.eval nodeValue4068 (mixedVector B) := by
    change mixedMoment B node4068 node4068Labels = _
    exact sound4068 B hB hF
  simpa only [sourceForm1418, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h542, h702, h737, h787, h810, h4068, reducedSource1218] using sourceEq1418 B hB

theorem rowSound1218 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1218 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1218, numericCheck1218, reducedZero1218 B hB hF, mul_zero]

theorem reducedZero1219 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1219 (mixedVector B) = 0 := by
  have h783 : mixedVector B (Sum.inr 783) = Sparse.eval nodeValue783 (mixedVector B) := by
    change mixedMoment B node783 node783Labels = _
    exact sound783 B hB hF
  have h787 : mixedVector B (Sum.inr 787) = Sparse.eval nodeValue787 (mixedVector B) := by
    change mixedMoment B node787 node787Labels = _
    exact sound787 B hB hF
  have h790 : mixedVector B (Sum.inr 790) = Sparse.eval nodeValue790 (mixedVector B) := by
    change mixedMoment B node790 node790Labels = _
    exact sound790 B hB hF
  have h810 : mixedVector B (Sum.inr 810) = Sparse.eval nodeValue810 (mixedVector B) := by
    change mixedMoment B node810 node810Labels = _
    exact sound810 B hB hF
  have h1708 : mixedVector B (Sum.inr 1708) = Sparse.eval nodeValue1708 (mixedVector B) := by
    change mixedMoment B node1708 node1708Labels = _
    exact sound1708 B hB hF
  have h4068 : mixedVector B (Sum.inr 4068) = Sparse.eval nodeValue4068 (mixedVector B) := by
    change mixedMoment B node4068 node4068Labels = _
    exact sound4068 B hB hF
  simpa only [sourceForm1419, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h783, h787, h790, h810, h1708, h4068, reducedSource1219] using sourceEq1419 B hB

theorem rowSound1219 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1219 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1219, numericCheck1219, reducedZero1219 B hB hF, mul_zero]

theorem reducedZero1220 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1220 (mixedVector B) = 0 := by
  have h785 : mixedVector B (Sum.inr 785) = Sparse.eval nodeValue785 (mixedVector B) := by
    change mixedMoment B node785 node785Labels = _
    exact sound785 B hB hF
  have h1592 : mixedVector B (Sum.inr 1592) = Sparse.eval nodeValue1592 (mixedVector B) := by
    change mixedMoment B node1592 node1592Labels = _
    exact sound1592 B hB hF
  have h1637 : mixedVector B (Sum.inr 1637) = Sparse.eval nodeValue1637 (mixedVector B) := by
    change mixedMoment B node1637 node1637Labels = _
    exact sound1637 B hB hF
  have h1707 : mixedVector B (Sum.inr 1707) = Sparse.eval nodeValue1707 (mixedVector B) := by
    change mixedMoment B node1707 node1707Labels = _
    exact sound1707 B hB hF
  have h1710 : mixedVector B (Sum.inr 1710) = Sparse.eval nodeValue1710 (mixedVector B) := by
    change mixedMoment B node1710 node1710Labels = _
    exact sound1710 B hB hF
  have h4069 : mixedVector B (Sum.inr 4069) = Sparse.eval nodeValue4069 (mixedVector B) := by
    change mixedMoment B node4069 node4069Labels = _
    exact sound4069 B hB hF
  simpa only [sourceForm1421, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h785, h1592, h1637, h1707, h1710, h4069, reducedSource1220] using sourceEq1421 B hB

theorem rowSound1220 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1220 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1220, numericCheck1220, reducedZero1220 B hB hF, mul_zero]

theorem reducedZero1221 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1221 (mixedVector B) = 0 := by
  have h538 : mixedVector B (Sum.inr 538) = Sparse.eval nodeValue538 (mixedVector B) := by
    change mixedMoment B node538 node538Labels = _
    exact sound538 B hB hF
  have h699 : mixedVector B (Sum.inr 699) = Sparse.eval nodeValue699 (mixedVector B) := by
    change mixedMoment B node699 node699Labels = _
    exact sound699 B hB hF
  have h733 : mixedVector B (Sum.inr 733) = Sparse.eval nodeValue733 (mixedVector B) := by
    change mixedMoment B node733 node733Labels = _
    exact sound733 B hB hF
  have h785 : mixedVector B (Sum.inr 785) = Sparse.eval nodeValue785 (mixedVector B) := by
    change mixedMoment B node785 node785Labels = _
    exact sound785 B hB hF
  have h806 : mixedVector B (Sum.inr 806) = Sparse.eval nodeValue806 (mixedVector B) := by
    change mixedMoment B node806 node806Labels = _
    exact sound806 B hB hF
  have h812 : mixedVector B (Sum.inr 812) = Sparse.eval nodeValue812 (mixedVector B) := by
    change mixedMoment B node812 node812Labels = _
    exact sound812 B hB hF
  have h4069 : mixedVector B (Sum.inr 4069) = Sparse.eval nodeValue4069 (mixedVector B) := by
    change mixedMoment B node4069 node4069Labels = _
    exact sound4069 B hB hF
  simpa only [sourceForm1422, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h538, h699, h733, h785, h806, h812, h4069, reducedSource1221] using sourceEq1422 B hB

theorem rowSound1221 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1221 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1221, numericCheck1221, reducedZero1221 B hB hF, mul_zero]

theorem reducedZero1222 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1222 (mixedVector B) = 0 := by
  have h782 : mixedVector B (Sum.inr 782) = Sparse.eval nodeValue782 (mixedVector B) := by
    change mixedMoment B node782 node782Labels = _
    exact sound782 B hB hF
  have h785 : mixedVector B (Sum.inr 785) = Sparse.eval nodeValue785 (mixedVector B) := by
    change mixedMoment B node785 node785Labels = _
    exact sound785 B hB hF
  have h789 : mixedVector B (Sum.inr 789) = Sparse.eval nodeValue789 (mixedVector B) := by
    change mixedMoment B node789 node789Labels = _
    exact sound789 B hB hF
  have h806 : mixedVector B (Sum.inr 806) = Sparse.eval nodeValue806 (mixedVector B) := by
    change mixedMoment B node806 node806Labels = _
    exact sound806 B hB hF
  have h1707 : mixedVector B (Sum.inr 1707) = Sparse.eval nodeValue1707 (mixedVector B) := by
    change mixedMoment B node1707 node1707Labels = _
    exact sound1707 B hB hF
  have h4069 : mixedVector B (Sum.inr 4069) = Sparse.eval nodeValue4069 (mixedVector B) := by
    change mixedMoment B node4069 node4069Labels = _
    exact sound4069 B hB hF
  simpa only [sourceForm1423, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h782, h785, h789, h806, h1707, h4069, reducedSource1222] using sourceEq1423 B hB

theorem rowSound1222 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1222 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1222, numericCheck1222, reducedZero1222 B hB hF, mul_zero]

theorem reducedZero1223 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1223 (mixedVector B) = 0 := by
  have h536 : mixedVector B (Sum.inr 536) = Sparse.eval nodeValue536 (mixedVector B) := by
    change mixedMoment B node536 node536Labels = _
    exact sound536 B hB hF
  have h698 : mixedVector B (Sum.inr 698) = Sparse.eval nodeValue698 (mixedVector B) := by
    change mixedMoment B node698 node698Labels = _
    exact sound698 B hB hF
  have h731 : mixedVector B (Sum.inr 731) = Sparse.eval nodeValue731 (mixedVector B) := by
    change mixedMoment B node731 node731Labels = _
    exact sound731 B hB hF
  have h804 : mixedVector B (Sum.inr 804) = Sparse.eval nodeValue804 (mixedVector B) := by
    change mixedMoment B node804 node804Labels = _
    exact sound804 B hB hF
  have h809 : mixedVector B (Sum.inr 809) = Sparse.eval nodeValue809 (mixedVector B) := by
    change mixedMoment B node809 node809Labels = _
    exact sound809 B hB hF
  have h4070 : mixedVector B (Sum.inr 4070) = Sparse.eval nodeValue4070 (mixedVector B) := by
    change mixedMoment B node4070 node4070Labels = _
    exact sound4070 B hB hF
  simpa only [sourceForm1424, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h536, h698, h731, h804, h809, h4070, reducedSource1223] using sourceEq1424 B hB

theorem rowSound1223 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1223 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1223, numericCheck1223, reducedZero1223 B hB hF, mul_zero]

theorem reducedZero1224 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1224 (mixedVector B) = 0 := by
  have h813 : mixedVector B (Sum.inr 813) = Sparse.eval nodeValue813 (mixedVector B) := by
    change mixedMoment B node813 node813Labels = _
    exact sound813 B hB hF
  have h1603 : mixedVector B (Sum.inr 1603) = Sparse.eval nodeValue1603 (mixedVector B) := by
    change mixedMoment B node1603 node1603Labels = _
    exact sound1603 B hB hF
  have h1651 : mixedVector B (Sum.inr 1651) = Sparse.eval nodeValue1651 (mixedVector B) := by
    change mixedMoment B node1651 node1651Labels = _
    exact sound1651 B hB hF
  have h1716 : mixedVector B (Sum.inr 1716) = Sparse.eval nodeValue1716 (mixedVector B) := by
    change mixedMoment B node1716 node1716Labels = _
    exact sound1716 B hB hF
  have h1728 : mixedVector B (Sum.inr 1728) = Sparse.eval nodeValue1728 (mixedVector B) := by
    change mixedMoment B node1728 node1728Labels = _
    exact sound1728 B hB hF
  have h4069 : mixedVector B (Sum.inr 4069) = Sparse.eval nodeValue4069 (mixedVector B) := by
    change mixedMoment B node4069 node4069Labels = _
    exact sound4069 B hB hF
  simpa only [sourceForm1425, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h813, h1603, h1651, h1716, h1728, h4069, reducedSource1224] using sourceEq1425 B hB

theorem rowSound1224 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1224 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1224, numericCheck1224, reducedZero1224 B hB hF, mul_zero]

theorem reducedZero1225 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1225 (mixedVector B) = 0 := by
  have h548 : mixedVector B (Sum.inr 548) = Sparse.eval nodeValue548 (mixedVector B) := by
    change mixedMoment B node548 node548Labels = _
    exact sound548 B hB hF
  have h708 : mixedVector B (Sum.inr 708) = Sparse.eval nodeValue708 (mixedVector B) := by
    change mixedMoment B node708 node708Labels = _
    exact sound708 B hB hF
  have h743 : mixedVector B (Sum.inr 743) = Sparse.eval nodeValue743 (mixedVector B) := by
    change mixedMoment B node743 node743Labels = _
    exact sound743 B hB hF
  have h813 : mixedVector B (Sum.inr 813) = Sparse.eval nodeValue813 (mixedVector B) := by
    change mixedMoment B node813 node813Labels = _
    exact sound813 B hB hF
  have h816 : mixedVector B (Sum.inr 816) = Sparse.eval nodeValue816 (mixedVector B) := by
    change mixedMoment B node816 node816Labels = _
    exact sound816 B hB hF
  have h4069 : mixedVector B (Sum.inr 4069) = Sparse.eval nodeValue4069 (mixedVector B) := by
    change mixedMoment B node4069 node4069Labels = _
    exact sound4069 B hB hF
  simpa only [sourceForm1426, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h548, h708, h743, h813, h816, h4069, reducedSource1225] using sourceEq1426 B hB

theorem rowSound1225 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1225 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1225, numericCheck1225, reducedZero1225 B hB hF, mul_zero]

theorem reducedZero1226 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1226 (mixedVector B) = 0 := by
  have h807 : mixedVector B (Sum.inr 807) = Sparse.eval nodeValue807 (mixedVector B) := by
    change mixedMoment B node807 node807Labels = _
    exact sound807 B hB hF
  have h813 : mixedVector B (Sum.inr 813) = Sparse.eval nodeValue813 (mixedVector B) := by
    change mixedMoment B node813 node813Labels = _
    exact sound813 B hB hF
  have h816 : mixedVector B (Sum.inr 816) = Sparse.eval nodeValue816 (mixedVector B) := by
    change mixedMoment B node816 node816Labels = _
    exact sound816 B hB hF
  have h856 : mixedVector B (Sum.inr 856) = Sparse.eval nodeValue856 (mixedVector B) := by
    change mixedMoment B node856 node856Labels = _
    exact sound856 B hB hF
  have h1728 : mixedVector B (Sum.inr 1728) = Sparse.eval nodeValue1728 (mixedVector B) := by
    change mixedMoment B node1728 node1728Labels = _
    exact sound1728 B hB hF
  have h4069 : mixedVector B (Sum.inr 4069) = Sparse.eval nodeValue4069 (mixedVector B) := by
    change mixedMoment B node4069 node4069Labels = _
    exact sound4069 B hB hF
  simpa only [sourceForm1427, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h807, h813, h816, h856, h1728, h4069, reducedSource1226] using sourceEq1427 B hB

theorem rowSound1226 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1226 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1226, numericCheck1226, reducedZero1226 B hB hF, mul_zero]

theorem reducedZero1227 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1227 (mixedVector B) = 0 := by
  have h4069 : mixedVector B (Sum.inr 4069) = Sparse.eval nodeValue4069 (mixedVector B) := by
    change mixedMoment B node4069 node4069Labels = _
    exact sound4069 B hB hF
  have h4101 : mixedVector B (Sum.inr 4101) = Sparse.eval nodeValue4101 (mixedVector B) := by
    change mixedMoment B node4101 node4101Labels = _
    exact sound4101 B hB hF
  have h4108 : mixedVector B (Sum.inr 4108) = Sparse.eval nodeValue4108 (mixedVector B) := by
    change mixedMoment B node4108 node4108Labels = _
    exact sound4108 B hB hF
  have h4110 : mixedVector B (Sum.inr 4110) = Sparse.eval nodeValue4110 (mixedVector B) := by
    change mixedMoment B node4110 node4110Labels = _
    exact sound4110 B hB hF
  have h4127 : mixedVector B (Sum.inr 4127) = Sparse.eval nodeValue4127 (mixedVector B) := by
    change mixedMoment B node4127 node4127Labels = _
    exact sound4127 B hB hF
  have h4196 : mixedVector B (Sum.inr 4196) = Sparse.eval nodeValue4196 (mixedVector B) := by
    change mixedMoment B node4196 node4196Labels = _
    exact sound4196 B hB hF
  have h4202 : mixedVector B (Sum.inr 4202) = Sparse.eval nodeValue4202 (mixedVector B) := by
    change mixedMoment B node4202 node4202Labels = _
    exact sound4202 B hB hF
  have h4204 : mixedVector B (Sum.inr 4204) = Sparse.eval nodeValue4204 (mixedVector B) := by
    change mixedMoment B node4204 node4204Labels = _
    exact sound4204 B hB hF
  have h4218 : mixedVector B (Sum.inr 4218) = Sparse.eval nodeValue4218 (mixedVector B) := by
    change mixedMoment B node4218 node4218Labels = _
    exact sound4218 B hB hF
  have h4233 : mixedVector B (Sum.inr 4233) = Sparse.eval nodeValue4233 (mixedVector B) := by
    change mixedMoment B node4233 node4233Labels = _
    exact sound4233 B hB hF
  have h4240 : mixedVector B (Sum.inr 4240) = Sparse.eval nodeValue4240 (mixedVector B) := by
    change mixedMoment B node4240 node4240Labels = _
    exact sound4240 B hB hF
  have h4242 : mixedVector B (Sum.inr 4242) = Sparse.eval nodeValue4242 (mixedVector B) := by
    change mixedMoment B node4242 node4242Labels = _
    exact sound4242 B hB hF
  have h4251 : mixedVector B (Sum.inr 4251) = Sparse.eval nodeValue4251 (mixedVector B) := by
    change mixedMoment B node4251 node4251Labels = _
    exact sound4251 B hB hF
  have h4257 : mixedVector B (Sum.inr 4257) = Sparse.eval nodeValue4257 (mixedVector B) := by
    change mixedMoment B node4257 node4257Labels = _
    exact sound4257 B hB hF
  have h4264 : mixedVector B (Sum.inr 4264) = Sparse.eval nodeValue4264 (mixedVector B) := by
    change mixedMoment B node4264 node4264Labels = _
    exact sound4264 B hB hF
  have h4269 : mixedVector B (Sum.inr 4269) = Sparse.eval nodeValue4269 (mixedVector B) := by
    change mixedMoment B node4269 node4269Labels = _
    exact sound4269 B hB hF
  have h4273 : mixedVector B (Sum.inr 4273) = Sparse.eval nodeValue4273 (mixedVector B) := by
    change mixedMoment B node4273 node4273Labels = _
    exact sound4273 B hB hF
  have h4418 : mixedVector B (Sum.inr 4418) = Sparse.eval nodeValue4418 (mixedVector B) := by
    change mixedMoment B node4418 node4418Labels = _
    exact sound4418 B hB hF
  have h4490 : mixedVector B (Sum.inr 4490) = Sparse.eval nodeValue4490 (mixedVector B) := by
    change mixedMoment B node4490 node4490Labels = _
    exact sound4490 B hB hF
  have h4496 : mixedVector B (Sum.inr 4496) = Sparse.eval nodeValue4496 (mixedVector B) := by
    change mixedMoment B node4496 node4496Labels = _
    exact sound4496 B hB hF
  have h4498 : mixedVector B (Sum.inr 4498) = Sparse.eval nodeValue4498 (mixedVector B) := by
    change mixedMoment B node4498 node4498Labels = _
    exact sound4498 B hB hF
  simpa only [sourceForm1429, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4069, h4101, h4108, h4110, h4127, h4196, h4202, h4204, h4218, h4233, h4240, h4242, h4251, h4257, h4264, h4269, h4273, h4418, h4490, h4496, h4498, reducedSource1227] using sourceEq1429 B hB

theorem rowSound1227 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1227 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1227, numericCheck1227, reducedZero1227 B hB hF, mul_zero]

theorem reducedZero1228 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1228 (mixedVector B) = 0 := by
  have h663 : mixedVector B (Sum.inr 663) = Sparse.eval nodeValue663 (mixedVector B) := by
    change mixedMoment B node663 node663Labels = _
    exact sound663 B hB hF
  have h683 : mixedVector B (Sum.inr 683) = Sparse.eval nodeValue683 (mixedVector B) := by
    change mixedMoment B node683 node683Labels = _
    exact sound683 B hB hF
  have h684 : mixedVector B (Sum.inr 684) = Sparse.eval nodeValue684 (mixedVector B) := by
    change mixedMoment B node684 node684Labels = _
    exact sound684 B hB hF
  have h688 : mixedVector B (Sum.inr 688) = Sparse.eval nodeValue688 (mixedVector B) := by
    change mixedMoment B node688 node688Labels = _
    exact sound688 B hB hF
  have h748 : mixedVector B (Sum.inr 748) = Sparse.eval nodeValue748 (mixedVector B) := by
    change mixedMoment B node748 node748Labels = _
    exact sound748 B hB hF
  have h762 : mixedVector B (Sum.inr 762) = Sparse.eval nodeValue762 (mixedVector B) := by
    change mixedMoment B node762 node762Labels = _
    exact sound762 B hB hF
  have h763 : mixedVector B (Sum.inr 763) = Sparse.eval nodeValue763 (mixedVector B) := by
    change mixedMoment B node763 node763Labels = _
    exact sound763 B hB hF
  have h767 : mixedVector B (Sum.inr 767) = Sparse.eval nodeValue767 (mixedVector B) := by
    change mixedMoment B node767 node767Labels = _
    exact sound767 B hB hF
  have h799 : mixedVector B (Sum.inr 799) = Sparse.eval nodeValue799 (mixedVector B) := by
    change mixedMoment B node799 node799Labels = _
    exact sound799 B hB hF
  have h804 : mixedVector B (Sum.inr 804) = Sparse.eval nodeValue804 (mixedVector B) := by
    change mixedMoment B node804 node804Labels = _
    exact sound804 B hB hF
  have h806 : mixedVector B (Sum.inr 806) = Sparse.eval nodeValue806 (mixedVector B) := by
    change mixedMoment B node806 node806Labels = _
    exact sound806 B hB hF
  have h842 : mixedVector B (Sum.inr 842) = Sparse.eval nodeValue842 (mixedVector B) := by
    change mixedMoment B node842 node842Labels = _
    exact sound842 B hB hF
  have h843 : mixedVector B (Sum.inr 843) = Sparse.eval nodeValue843 (mixedVector B) := by
    change mixedMoment B node843 node843Labels = _
    exact sound843 B hB hF
  have h849 : mixedVector B (Sum.inr 849) = Sparse.eval nodeValue849 (mixedVector B) := by
    change mixedMoment B node849 node849Labels = _
    exact sound849 B hB hF
  have h851 : mixedVector B (Sum.inr 851) = Sparse.eval nodeValue851 (mixedVector B) := by
    change mixedMoment B node851 node851Labels = _
    exact sound851 B hB hF
  have h852 : mixedVector B (Sum.inr 852) = Sparse.eval nodeValue852 (mixedVector B) := by
    change mixedMoment B node852 node852Labels = _
    exact sound852 B hB hF
  have h999 : mixedVector B (Sum.inr 999) = Sparse.eval nodeValue999 (mixedVector B) := by
    change mixedMoment B node999 node999Labels = _
    exact sound999 B hB hF
  have h1074 : mixedVector B (Sum.inr 1074) = Sparse.eval nodeValue1074 (mixedVector B) := by
    change mixedMoment B node1074 node1074Labels = _
    exact sound1074 B hB hF
  have h1080 : mixedVector B (Sum.inr 1080) = Sparse.eval nodeValue1080 (mixedVector B) := by
    change mixedMoment B node1080 node1080Labels = _
    exact sound1080 B hB hF
  have h1082 : mixedVector B (Sum.inr 1082) = Sparse.eval nodeValue1082 (mixedVector B) := by
    change mixedMoment B node1082 node1082Labels = _
    exact sound1082 B hB hF
  have h4069 : mixedVector B (Sum.inr 4069) = Sparse.eval nodeValue4069 (mixedVector B) := by
    change mixedMoment B node4069 node4069Labels = _
    exact sound4069 B hB hF
  simpa only [sourceForm1430, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h663, h683, h684, h688, h748, h762, h763, h767, h799, h804, h806, h842, h843, h849, h851, h852, h999, h1074, h1080, h1082, h4069, reducedSource1228] using sourceEq1430 B hB

theorem rowSound1228 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1228 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1228, numericCheck1228, reducedZero1228 B hB hF, mul_zero]

theorem reducedZero1229 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1229 (mixedVector B) = 0 := by
  have h812 : mixedVector B (Sum.inr 812) = Sparse.eval nodeValue812 (mixedVector B) := by
    change mixedMoment B node812 node812Labels = _
    exact sound812 B hB hF
  have h1602 : mixedVector B (Sum.inr 1602) = Sparse.eval nodeValue1602 (mixedVector B) := by
    change mixedMoment B node1602 node1602Labels = _
    exact sound1602 B hB hF
  have h1650 : mixedVector B (Sum.inr 1650) = Sparse.eval nodeValue1650 (mixedVector B) := by
    change mixedMoment B node1650 node1650Labels = _
    exact sound1650 B hB hF
  have h1710 : mixedVector B (Sum.inr 1710) = Sparse.eval nodeValue1710 (mixedVector B) := by
    change mixedMoment B node1710 node1710Labels = _
    exact sound1710 B hB hF
  have h1727 : mixedVector B (Sum.inr 1727) = Sparse.eval nodeValue1727 (mixedVector B) := by
    change mixedMoment B node1727 node1727Labels = _
    exact sound1727 B hB hF
  have h4069 : mixedVector B (Sum.inr 4069) = Sparse.eval nodeValue4069 (mixedVector B) := by
    change mixedMoment B node4069 node4069Labels = _
    exact sound4069 B hB hF
  simpa only [sourceForm1431, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h812, h1602, h1650, h1710, h1727, h4069, reducedSource1229] using sourceEq1431 B hB

theorem rowSound1229 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1229 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1229, numericCheck1229, reducedZero1229 B hB hF, mul_zero]

theorem reducedZero1230 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1230 (mixedVector B) = 0 := by
  have h733 : mixedVector B (Sum.inr 733) = Sparse.eval nodeValue733 (mixedVector B) := by
    change mixedMoment B node733 node733Labels = _
    exact sound733 B hB hF
  have h740 : mixedVector B (Sum.inr 740) = Sparse.eval nodeValue740 (mixedVector B) := by
    change mixedMoment B node740 node740Labels = _
    exact sound740 B hB hF
  have h742 : mixedVector B (Sum.inr 742) = Sparse.eval nodeValue742 (mixedVector B) := by
    change mixedMoment B node742 node742Labels = _
    exact sound742 B hB hF
  have h812 : mixedVector B (Sum.inr 812) = Sparse.eval nodeValue812 (mixedVector B) := by
    change mixedMoment B node812 node812Labels = _
    exact sound812 B hB hF
  have h1650 : mixedVector B (Sum.inr 1650) = Sparse.eval nodeValue1650 (mixedVector B) := by
    change mixedMoment B node1650 node1650Labels = _
    exact sound1650 B hB hF
  have h4069 : mixedVector B (Sum.inr 4069) = Sparse.eval nodeValue4069 (mixedVector B) := by
    change mixedMoment B node4069 node4069Labels = _
    exact sound4069 B hB hF
  simpa only [sourceForm1433, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h733, h740, h742, h812, h1650, h4069, reducedSource1230] using sourceEq1433 B hB

theorem rowSound1230 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1230 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1230, numericCheck1230, reducedZero1230 B hB hF, mul_zero]

theorem sourceRowsAt1216 : MixedData.sourceRows (1216 : Fin 2425) =
    MixedData.row1216 := by decide +kernel

theorem sourceRowsAt1217 : MixedData.sourceRows (1217 : Fin 2425) =
    MixedData.row1217 := by decide +kernel

theorem sourceRowsAt1218 : MixedData.sourceRows (1218 : Fin 2425) =
    MixedData.row1218 := by decide +kernel

theorem sourceRowsAt1219 : MixedData.sourceRows (1219 : Fin 2425) =
    MixedData.row1219 := by decide +kernel

theorem sourceRowsAt1220 : MixedData.sourceRows (1220 : Fin 2425) =
    MixedData.row1220 := by decide +kernel

theorem sourceRowsAt1221 : MixedData.sourceRows (1221 : Fin 2425) =
    MixedData.row1221 := by decide +kernel

theorem sourceRowsAt1222 : MixedData.sourceRows (1222 : Fin 2425) =
    MixedData.row1222 := by decide +kernel

theorem sourceRowsAt1223 : MixedData.sourceRows (1223 : Fin 2425) =
    MixedData.row1223 := by decide +kernel

theorem sourceRowsAt1224 : MixedData.sourceRows (1224 : Fin 2425) =
    MixedData.row1224 := by decide +kernel

theorem sourceRowsAt1225 : MixedData.sourceRows (1225 : Fin 2425) =
    MixedData.row1225 := by decide +kernel

theorem sourceRowsAt1226 : MixedData.sourceRows (1226 : Fin 2425) =
    MixedData.row1226 := by decide +kernel

theorem sourceRowsAt1227 : MixedData.sourceRows (1227 : Fin 2425) =
    MixedData.row1227 := by decide +kernel

theorem sourceRowsAt1228 : MixedData.sourceRows (1228 : Fin 2425) =
    MixedData.row1228 := by decide +kernel

theorem sourceRowsAt1229 : MixedData.sourceRows (1229 : Fin 2425) =
    MixedData.row1229 := by decide +kernel

theorem sourceRowsAt1230 : MixedData.sourceRows (1230 : Fin 2425) =
    MixedData.row1230 := by decide +kernel

theorem sourceRowsAt1231 : MixedData.sourceRows (1231 : Fin 2425) =
    MixedData.row1231 := by decide +kernel

theorem chunkSound76_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) (k : Fin 2425)
    (hk : k.val / 16 = 76) :
    Integer.Sparse.eval (MixedData.sourceRows k) (numericVector B) = 0 := by
  have heq : k.val = 1216 ∨ k.val = 1217 ∨ k.val = 1218 ∨ k.val = 1219 ∨ k.val = 1220 ∨ k.val = 1221 ∨ k.val = 1222 ∨ k.val = 1223 ∨ k.val = 1224 ∨ k.val = 1225 ∨ k.val = 1226 ∨ k.val = 1227 ∨ k.val = 1228 ∨ k.val = 1229 ∨ k.val = 1230 ∨ k.val = 1231 := by omega
  rcases heq with h1216 | h1217 | h1218 | h1219 | h1220 | h1221 | h1222 | h1223 | h1224 | h1225 | h1226 | h1227 | h1228 | h1229 | h1230 | h1231
  · have he : k = (1216 : Fin 2425) := Fin.ext h1216
    subst k
    rw [sourceRowsAt1216]
    exact rowSound1216 B hB hF
  · have he : k = (1217 : Fin 2425) := Fin.ext h1217
    subst k
    rw [sourceRowsAt1217]
    exact rowSound1217 B hB hF
  · have he : k = (1218 : Fin 2425) := Fin.ext h1218
    subst k
    rw [sourceRowsAt1218]
    exact rowSound1218 B hB hF
  · have he : k = (1219 : Fin 2425) := Fin.ext h1219
    subst k
    rw [sourceRowsAt1219]
    exact rowSound1219 B hB hF
  · have he : k = (1220 : Fin 2425) := Fin.ext h1220
    subst k
    rw [sourceRowsAt1220]
    exact rowSound1220 B hB hF
  · have he : k = (1221 : Fin 2425) := Fin.ext h1221
    subst k
    rw [sourceRowsAt1221]
    exact rowSound1221 B hB hF
  · have he : k = (1222 : Fin 2425) := Fin.ext h1222
    subst k
    rw [sourceRowsAt1222]
    exact rowSound1222 B hB hF
  · have he : k = (1223 : Fin 2425) := Fin.ext h1223
    subst k
    rw [sourceRowsAt1223]
    exact rowSound1223 B hB hF
  · have he : k = (1224 : Fin 2425) := Fin.ext h1224
    subst k
    rw [sourceRowsAt1224]
    exact rowSound1224 B hB hF
  · have he : k = (1225 : Fin 2425) := Fin.ext h1225
    subst k
    rw [sourceRowsAt1225]
    exact rowSound1225 B hB hF
  · have he : k = (1226 : Fin 2425) := Fin.ext h1226
    subst k
    rw [sourceRowsAt1226]
    exact rowSound1226 B hB hF
  · have he : k = (1227 : Fin 2425) := Fin.ext h1227
    subst k
    rw [sourceRowsAt1227]
    exact rowSound1227 B hB hF
  · have he : k = (1228 : Fin 2425) := Fin.ext h1228
    subst k
    rw [sourceRowsAt1228]
    exact rowSound1228 B hB hF
  · have he : k = (1229 : Fin 2425) := Fin.ext h1229
    subst k
    rw [sourceRowsAt1229]
    exact rowSound1229 B hB hF
  · have he : k = (1230 : Fin 2425) := Fin.ext h1230
    subst k
    rw [sourceRowsAt1230]
    exact rowSound1230 B hB hF
  · have he : k = (1231 : Fin 2425) := Fin.ext h1231
    subst k
    rw [sourceRowsAt1231]
    exact rowSound1231_e B hB hF

end MUB6.Certificate.MixedSourceBridge

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedSourceBridge.chunkSound76_e_oai := @OAI.MUB6.Certificate.MixedSourceBridge.chunkSound76_e_oai
