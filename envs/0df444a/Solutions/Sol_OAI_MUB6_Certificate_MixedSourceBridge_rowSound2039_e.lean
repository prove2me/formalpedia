-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedSourceBridge.rowSound2039_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-08T23:12:52.179752+00:00
-- url     : https://prove2.me/submissions/209b360f-6de3-4b8e-8418-d514601e8321

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E070
import Definitions.Def_OAIQ106E086
import Definitions.Def_OAIQ106E092
import Definitions.Def_OAIQ106E095
import Definitions.Def_OAIQ106E097
import Definitions.Def_OAIQ106E188
import Definitions.Def_OAIQ106E192
import Definitions.Def_OAIQ106E193
import Definitions.Def_OAIQ106E100
import Definitions.Def_OAIQ106E194
import Definitions.Def_OAIQ106E195
import Definitions.Def_OAIQ106E108
import Definitions.Def_OAIQ106E119
import Definitions.Def_OAIQ106E121
import Definitions.Def_OAIQ106E126
import Definitions.Def_OAIQ106E140
import Definitions.Def_OAIQ106E147
import Definitions.Def_OAIQ106E170

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical128
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical16442 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16442 raw16442Labels = mixedMoment B node5428 node5428Labels := by
  calc
    mixedMoment B raw16442 raw16442Labels = mixedMoment B raw16442step0 raw16442step0Labels := by
      have hz : ∀ j, raw16442 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16442step0 = (fun i j => raw16442 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16442step0 raw16442; decide +kernel
      have hl : raw16442step0Labels = raw16442Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16442 raw16442Labels permutation346 hz
    mixedMoment B raw16442step0 raw16442step0Labels = mixedMoment B raw16442step1 raw16442step1Labels := by
      have ha : raw16442step1 = (fun i j => raw16442step0 (permutation56 i) (permutation2 j)) := by apply Matrix.ext; unfold raw16442step1 raw16442step0; decide +kernel
      have hl : raw16442step1Labels = raw16442step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16442step0 raw16442step0Labels permutation56 permutation2
    _ = mixedMoment B node5428 node5428Labels := by rfl

theorem canonical16453 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16453 raw16453Labels = mixedMoment B node5379 node5379Labels := by
  calc
    mixedMoment B raw16453 raw16453Labels = mixedMoment B raw16453step0 raw16453step0Labels := by
      have ha : raw16453step0 = (fun i j => raw16453 (permutation271 i) (permutation2 j)) := by apply Matrix.ext; unfold raw16453step0 raw16453; decide +kernel
      have hl : raw16453step0Labels = raw16453Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16453 raw16453Labels permutation271 permutation2
    _ = mixedMoment B node5379 node5379Labels := by rfl

theorem canonical16458 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16458 raw16458Labels = mixedMoment B node5385 node5385Labels := by
  calc
    mixedMoment B raw16458 raw16458Labels = mixedMoment B raw16458step0 raw16458step0Labels := by
      have hz : ∀ j, raw16458 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16458step0 = (fun i j => raw16458 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16458step0 raw16458; decide +kernel
      have hl : raw16458step0Labels = raw16458Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16458 raw16458Labels permutation346 hz
    mixedMoment B raw16458step0 raw16458step0Labels = mixedMoment B raw16458step1 raw16458step1Labels := by
      have ha : raw16458step1 = (fun i j => raw16458step0 (permutation56 i) (permutation2 j)) := by apply Matrix.ext; unfold raw16458step1 raw16458step0; decide +kernel
      have hl : raw16458step1Labels = raw16458step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16458step0 raw16458step0Labels permutation56 permutation2
    _ = mixedMoment B node5385 node5385Labels := by rfl

theorem canonical16462 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16462 raw16462Labels = mixedMoment B node4856 node4856Labels := by
  calc
    mixedMoment B raw16462 raw16462Labels = mixedMoment B raw16462step0 raw16462step0Labels := by
      have hz : ∀ j, raw16462 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16462step0 = (fun i j => raw16462 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16462step0 raw16462; decide +kernel
      have hl : raw16462step0Labels = raw16462Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16462 raw16462Labels permutation346 hz
    mixedMoment B raw16462step0 raw16462step0Labels = mixedMoment B raw16462step1 raw16462step1Labels := by
      have ha : raw16462step1 = (fun i j => raw16462step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16462step1 raw16462step0; decide +kernel
      have hl : raw16462step1Labels = raw16462step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16462step0 raw16462step0Labels permutation32 permutation3
    mixedMoment B raw16462step1 raw16462step1Labels = mixedMoment B raw16462step2 raw16462step2Labels := by
      have ha : raw16462step2 = raw16462step1 := by apply Matrix.ext; unfold raw16462step2 raw16462step1; decide +kernel
      have hl : raw16462step1Labels = labelEmbedding6 ∘ raw16462step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16462step1 raw16462step1Labels raw16462step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4856 node4856Labels := by rfl

theorem canonical16464 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16464 raw16464Labels = mixedMoment B node5353 node5353Labels := by
  calc
    mixedMoment B raw16464 raw16464Labels = mixedMoment B raw16464step0 raw16464step0Labels := by
      have ha : raw16464step0 = (fun i j => raw16464 (permutation589 i) (permutation2 j)) := by apply Matrix.ext; unfold raw16464step0 raw16464; decide +kernel
      have hl : raw16464step0Labels = raw16464Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16464 raw16464Labels permutation589 permutation2
    mixedMoment B raw16464step0 raw16464step0Labels = mixedMoment B raw16464step1 raw16464step1Labels := by
      have ha : raw16464step1 = -raw16464step0 := by apply Matrix.ext; change ∀ i j, raw16464step1 i j = -(raw16464step0 i j); unfold raw16464step1 raw16464step0; decide +kernel
      have hl : raw16464step1Labels = raw16464step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5353 node5353Labels := by rfl

theorem canonical16465 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16465 raw16465Labels = mixedMoment B node5370 node5370Labels := by
  calc
    mixedMoment B raw16465 raw16465Labels = mixedMoment B raw16465step0 raw16465step0Labels := by
      have hz : ∀ j, raw16465 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16465step0 = (fun i j => raw16465 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16465step0 raw16465; decide +kernel
      have hl : raw16465step0Labels = raw16465Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16465 raw16465Labels permutation346 hz
    mixedMoment B raw16465step0 raw16465step0Labels = mixedMoment B raw16465step1 raw16465step1Labels := by
      have ha : raw16465step1 = (fun i j => raw16465step0 (permutation127 i) (permutation2 j)) := by apply Matrix.ext; unfold raw16465step1 raw16465step0; decide +kernel
      have hl : raw16465step1Labels = raw16465step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16465step0 raw16465step0Labels permutation127 permutation2
    mixedMoment B raw16465step1 raw16465step1Labels = mixedMoment B raw16465step2 raw16465step2Labels := by
      have ha : raw16465step2 = -raw16465step1 := by apply Matrix.ext; change ∀ i j, raw16465step2 i j = -(raw16465step1 i j); unfold raw16465step2 raw16465step1; decide +kernel
      have hl : raw16465step2Labels = raw16465step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5370 node5370Labels := by rfl

theorem canonical16466 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16466 raw16466Labels = mixedMoment B node5411 node5411Labels := by
  calc
    mixedMoment B raw16466 raw16466Labels = mixedMoment B raw16466step0 raw16466step0Labels := by
      have hz : ∀ j, raw16466 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16466step0 = (fun i j => raw16466 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16466step0 raw16466; decide +kernel
      have hl : raw16466step0Labels = raw16466Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16466 raw16466Labels permutation346 hz
    mixedMoment B raw16466step0 raw16466step0Labels = mixedMoment B raw16466step1 raw16466step1Labels := by
      have ha : raw16466step1 = (fun i j => raw16466step0 (permutation127 i) (permutation2 j)) := by apply Matrix.ext; unfold raw16466step1 raw16466step0; decide +kernel
      have hl : raw16466step1Labels = raw16466step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16466step0 raw16466step0Labels permutation127 permutation2
    mixedMoment B raw16466step1 raw16466step1Labels = mixedMoment B raw16466step2 raw16466step2Labels := by
      have ha : raw16466step2 = -raw16466step1 := by apply Matrix.ext; change ∀ i j, raw16466step2 i j = -(raw16466step1 i j); unfold raw16466step2 raw16466step1; decide +kernel
      have hl : raw16466step2Labels = raw16466step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5411 node5411Labels := by rfl

theorem canonical16468 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16468 raw16468Labels = mixedMoment B node5188 node5188Labels := by
  calc
    mixedMoment B raw16468 raw16468Labels = mixedMoment B raw16468step0 raw16468step0Labels := by
      have hz : ∀ j, raw16468 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16468step0 = (fun i j => raw16468 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16468step0 raw16468; decide +kernel
      have hl : raw16468step0Labels = raw16468Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16468 raw16468Labels permutation346 hz
    mixedMoment B raw16468step0 raw16468step0Labels = mixedMoment B raw16468step1 raw16468step1Labels := by
      have ha : raw16468step1 = (fun i j => raw16468step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16468step1 raw16468step0; decide +kernel
      have hl : raw16468step1Labels = raw16468step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16468step0 raw16468step0Labels permutation151 permutation3
    mixedMoment B raw16468step1 raw16468step1Labels = mixedMoment B raw16468step2 raw16468step2Labels := by
      have ha : raw16468step2 = -raw16468step1 := by apply Matrix.ext; change ∀ i j, raw16468step2 i j = -(raw16468step1 i j); unfold raw16468step2 raw16468step1; decide +kernel
      have hl : raw16468step2Labels = raw16468step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16468step2 raw16468step2Labels = mixedMoment B raw16468step3 raw16468step3Labels := by
      have ha : raw16468step3 = raw16468step2 := by apply Matrix.ext; unfold raw16468step3 raw16468step2; decide +kernel
      have hl : raw16468step2Labels = labelEmbedding6 ∘ raw16468step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16468step2 raw16468step2Labels raw16468step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5188 node5188Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical15
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical1920 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1920 raw1920Labels = mixedMoment B node4949 node4949Labels := by
  calc
    mixedMoment B raw1920 raw1920Labels = mixedMoment B raw1920step0 raw1920step0Labels := by
      have ha : raw1920step0 = (fun i j => raw1920 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1920step0 raw1920; decide +kernel
      have hl : raw1920step0Labels = raw1920Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1920 raw1920Labels permutation32 permutation4
    mixedMoment B raw1920step0 raw1920step0Labels = mixedMoment B raw1920step1 raw1920step1Labels := by
      have ha : raw1920step1 = raw1920step0 := by apply Matrix.ext; unfold raw1920step1 raw1920step0; decide +kernel
      have hl : raw1920step0Labels = labelEmbedding7 ∘ raw1920step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1920step0 raw1920step0Labels raw1920step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4949 node4949Labels := by rfl

theorem canonical1921 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1921 raw1921Labels = mixedMoment B node2341 node2341Labels := by
  calc
    mixedMoment B raw1921 raw1921Labels = mixedMoment B raw1921step0 raw1921step0Labels := by
      have ha : raw1921step0 = (fun i j => raw1921 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1921step0 raw1921; decide +kernel
      have hl : raw1921step0Labels = raw1921Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1921 raw1921Labels permutation32 permutation4
    _ = mixedMoment B node2341 node2341Labels := by rfl

theorem canonical1922 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1922 raw1922Labels = mixedMoment B node3417 node3417Labels := by
  calc
    mixedMoment B raw1922 raw1922Labels = mixedMoment B raw1922step0 raw1922step0Labels := by
      have ha : raw1922step0 = (fun i j => raw1922 (permutation34 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1922step0 raw1922; decide +kernel
      have hl : raw1922step0Labels = raw1922Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1922 raw1922Labels permutation34 permutation6
    mixedMoment B raw1922step0 raw1922step0Labels = mixedMoment B raw1922step1 raw1922step1Labels := by
      have ha : raw1922step1 = -raw1922step0 := by apply Matrix.ext; change ∀ i j, raw1922step1 i j = -(raw1922step0 i j); unfold raw1922step1 raw1922step0; decide +kernel
      have hl : raw1922step1Labels = raw1922step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1922step1 raw1922step1Labels = mixedMoment B raw1922step2 raw1922step2Labels := by
      have ha : raw1922step2 = raw1922step1 := by apply Matrix.ext; unfold raw1922step2 raw1922step1; decide +kernel
      have hl : raw1922step1Labels = labelEmbedding1 ∘ raw1922step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1922step1 raw1922step1Labels raw1922step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3417 node3417Labels := by rfl

theorem canonical1959 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1959 raw1959Labels = mixedMoment B node4973 node4973Labels := by
  calc
    mixedMoment B raw1959 raw1959Labels = mixedMoment B raw1959step0 raw1959step0Labels := by
      have ha : raw1959step0 = (fun i j => raw1959 (permutation32 i) (permutation5 j)) := by apply Matrix.ext; unfold raw1959step0 raw1959; decide +kernel
      have hl : raw1959step0Labels = raw1959Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1959 raw1959Labels permutation32 permutation5
    mixedMoment B raw1959step0 raw1959step0Labels = mixedMoment B raw1959step1 raw1959step1Labels := by
      have ha : raw1959step1 = raw1959step0 := by apply Matrix.ext; unfold raw1959step1 raw1959step0; decide +kernel
      have hl : raw1959step0Labels = labelEmbedding8 ∘ raw1959step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1959step0 raw1959step0Labels raw1959step1Labels labelEmbedding8 hl
    _ = mixedMoment B node4973 node4973Labels := by rfl

theorem canonical1960 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1960 raw1960Labels = mixedMoment B node2817 node2817Labels := by
  calc
    mixedMoment B raw1960 raw1960Labels = mixedMoment B raw1960step0 raw1960step0Labels := by
      have ha : raw1960step0 = (fun i j => raw1960 (permutation33 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1960step0 raw1960; decide +kernel
      have hl : raw1960step0Labels = raw1960Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1960 raw1960Labels permutation33 permutation4
    _ = mixedMoment B node2817 node2817Labels := by rfl

theorem canonical1961 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1961 raw1961Labels = mixedMoment B node3591 node3591Labels := by
  calc
    mixedMoment B raw1961 raw1961Labels = mixedMoment B raw1961step0 raw1961step0Labels := by
      have ha : raw1961step0 = (fun i j => raw1961 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw1961step0 raw1961; decide +kernel
      have hl : raw1961step0Labels = raw1961Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1961 raw1961Labels permutation32 permutation3
    mixedMoment B raw1961step0 raw1961step0Labels = mixedMoment B raw1961step1 raw1961step1Labels := by
      have ha : raw1961step1 = -raw1961step0 := by apply Matrix.ext; change ∀ i j, raw1961step1 i j = -(raw1961step0 i j); unfold raw1961step1 raw1961step0; decide +kernel
      have hl : raw1961step1Labels = raw1961step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1961step1 raw1961step1Labels = mixedMoment B raw1961step2 raw1961step2Labels := by
      have ha : raw1961step2 = raw1961step1 := by apply Matrix.ext; unfold raw1961step2 raw1961step1; decide +kernel
      have hl : raw1961step1Labels = labelEmbedding1 ∘ raw1961step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1961step1 raw1961step1Labels raw1961step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3591 node3591Labels := by rfl

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

theorem canonical2169 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2169 raw2169Labels = mixedMoment B node5141 node5141Labels := by
  calc
    mixedMoment B raw2169 raw2169Labels = mixedMoment B raw2169step0 raw2169step0Labels := by
      have ha : raw2169step0 = (fun i j => raw2169 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2169step0 raw2169; decide +kernel
      have hl : raw2169step0Labels = raw2169Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2169 raw2169Labels permutation32 permutation4
    mixedMoment B raw2169step0 raw2169step0Labels = mixedMoment B raw2169step1 raw2169step1Labels := by
      have ha : raw2169step1 = raw2169step0 := by apply Matrix.ext; unfold raw2169step1 raw2169step0; decide +kernel
      have hl : raw2169step0Labels = labelEmbedding7 ∘ raw2169step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2169step0 raw2169step0Labels raw2169step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5141 node5141Labels := by rfl

theorem canonical2170 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2170 raw2170Labels = mixedMoment B node2561 node2561Labels := by
  calc
    mixedMoment B raw2170 raw2170Labels = mixedMoment B raw2170step0 raw2170step0Labels := by
      have ha : raw2170step0 = (fun i j => raw2170 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2170step0 raw2170; decide +kernel
      have hl : raw2170step0Labels = raw2170Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2170 raw2170Labels permutation32 permutation4
    _ = mixedMoment B node2561 node2561Labels := by rfl

theorem canonical2171 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2171 raw2171Labels = mixedMoment B node3522 node3522Labels := by
  calc
    mixedMoment B raw2171 raw2171Labels = mixedMoment B raw2171step0 raw2171step0Labels := by
      have ha : raw2171step0 = (fun i j => raw2171 (permutation38 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2171step0 raw2171; decide +kernel
      have hl : raw2171step0Labels = raw2171Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2171 raw2171Labels permutation38 permutation6
    mixedMoment B raw2171step0 raw2171step0Labels = mixedMoment B raw2171step1 raw2171step1Labels := by
      have ha : raw2171step1 = -raw2171step0 := by apply Matrix.ext; change ∀ i j, raw2171step1 i j = -(raw2171step0 i j); unfold raw2171step1 raw2171step0; decide +kernel
      have hl : raw2171step1Labels = raw2171step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2171step1 raw2171step1Labels = mixedMoment B raw2171step2 raw2171step2Labels := by
      have ha : raw2171step2 = raw2171step1 := by apply Matrix.ext; unfold raw2171step2 raw2171step1; decide +kernel
      have hl : raw2171step1Labels = labelEmbedding1 ∘ raw2171step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2171step1 raw2171step1Labels raw2171step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3522 node3522Labels := by rfl

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

theorem canonical2373 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2373 raw2373Labels = mixedMoment B node5336 node5336Labels := by
  calc
    mixedMoment B raw2373 raw2373Labels = mixedMoment B raw2373step0 raw2373step0Labels := by
      have ha : raw2373step0 = (fun i j => raw2373 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2373step0 raw2373; decide +kernel
      have hl : raw2373step0Labels = raw2373Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2373 raw2373Labels permutation152 permutation4
    mixedMoment B raw2373step0 raw2373step0Labels = mixedMoment B raw2373step1 raw2373step1Labels := by
      have ha : raw2373step1 = raw2373step0 := by apply Matrix.ext; unfold raw2373step1 raw2373step0; decide +kernel
      have hl : raw2373step0Labels = labelEmbedding7 ∘ raw2373step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2373step0 raw2373step0Labels raw2373step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5336 node5336Labels := by rfl

theorem canonical2374 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2374 raw2374Labels = mixedMoment B node3671 node3671Labels := by
  calc
    mixedMoment B raw2374 raw2374Labels = mixedMoment B raw2374step0 raw2374step0Labels := by
      have ha : raw2374step0 = (fun i j => raw2374 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2374step0 raw2374; decide +kernel
      have hl : raw2374step0Labels = raw2374Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2374 raw2374Labels permutation152 permutation4
    _ = mixedMoment B node3671 node3671Labels := by rfl

theorem canonical2375 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2375 raw2375Labels = mixedMoment B node3754 node3754Labels := by
  calc
    mixedMoment B raw2375 raw2375Labels = mixedMoment B raw2375step0 raw2375step0Labels := by
      have ha : raw2375step0 = (fun i j => raw2375 (permutation154 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2375step0 raw2375; decide +kernel
      have hl : raw2375step0Labels = raw2375Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2375 raw2375Labels permutation154 permutation6
    mixedMoment B raw2375step0 raw2375step0Labels = mixedMoment B raw2375step1 raw2375step1Labels := by
      have ha : raw2375step1 = -raw2375step0 := by apply Matrix.ext; change ∀ i j, raw2375step1 i j = -(raw2375step0 i j); unfold raw2375step1 raw2375step0; decide +kernel
      have hl : raw2375step1Labels = raw2375step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2375step1 raw2375step1Labels = mixedMoment B raw2375step2 raw2375step2Labels := by
      have ha : raw2375step2 = raw2375step1 := by apply Matrix.ext; unfold raw2375step2 raw2375step1; decide +kernel
      have hl : raw2375step1Labels = labelEmbedding1 ∘ raw2375step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2375step1 raw2375step1Labels raw2375step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3754 node3754Labels := by rfl

theorem canonical2391 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2391 raw2391Labels = mixedMoment B node5351 node5351Labels := by
  calc
    mixedMoment B raw2391 raw2391Labels = mixedMoment B raw2391step0 raw2391step0Labels := by
      have ha : raw2391step0 = (fun i j => raw2391 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2391step0 raw2391; decide +kernel
      have hl : raw2391step0Labels = raw2391Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2391 raw2391Labels permutation152 permutation4
    mixedMoment B raw2391step0 raw2391step0Labels = mixedMoment B raw2391step1 raw2391step1Labels := by
      have ha : raw2391step1 = raw2391step0 := by apply Matrix.ext; unfold raw2391step1 raw2391step0; decide +kernel
      have hl : raw2391step0Labels = labelEmbedding7 ∘ raw2391step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2391step0 raw2391step0Labels raw2391step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5351 node5351Labels := by rfl

theorem canonical2392 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2392 raw2392Labels = mixedMoment B node3689 node3689Labels := by
  calc
    mixedMoment B raw2392 raw2392Labels = mixedMoment B raw2392step0 raw2392step0Labels := by
      have ha : raw2392step0 = (fun i j => raw2392 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2392step0 raw2392; decide +kernel
      have hl : raw2392step0Labels = raw2392Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2392 raw2392Labels permutation152 permutation4
    _ = mixedMoment B node3689 node3689Labels := by rfl

theorem canonical2393 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2393 raw2393Labels = mixedMoment B node3757 node3757Labels := by
  calc
    mixedMoment B raw2393 raw2393Labels = mixedMoment B raw2393step0 raw2393step0Labels := by
      have ha : raw2393step0 = (fun i j => raw2393 (permutation160 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2393step0 raw2393; decide +kernel
      have hl : raw2393step0Labels = raw2393Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2393 raw2393Labels permutation160 permutation6
    mixedMoment B raw2393step0 raw2393step0Labels = mixedMoment B raw2393step1 raw2393step1Labels := by
      have ha : raw2393step1 = -raw2393step0 := by apply Matrix.ext; change ∀ i j, raw2393step1 i j = -(raw2393step0 i j); unfold raw2393step1 raw2393step0; decide +kernel
      have hl : raw2393step1Labels = raw2393step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2393step1 raw2393step1Labels = mixedMoment B raw2393step2 raw2393step2Labels := by
      have ha : raw2393step2 = raw2393step1 := by apply Matrix.ext; unfold raw2393step2 raw2393step1; decide +kernel
      have hl : raw2393step1Labels = labelEmbedding1 ∘ raw2393step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2393step1 raw2393step1Labels raw2393step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3757 node3757Labels := by rfl

theorem canonical2418 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2418 raw2418Labels = mixedMoment B node5370 node5370Labels := by
  calc
    mixedMoment B raw2418 raw2418Labels = mixedMoment B raw2418step0 raw2418step0Labels := by
      have ha : raw2418step0 = (fun i j => raw2418 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2418step0 raw2418; decide +kernel
      have hl : raw2418step0Labels = raw2418Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2418 raw2418Labels permutation32 permutation4
    mixedMoment B raw2418step0 raw2418step0Labels = mixedMoment B raw2418step1 raw2418step1Labels := by
      have ha : raw2418step1 = raw2418step0 := by apply Matrix.ext; unfold raw2418step1 raw2418step0; decide +kernel
      have hl : raw2418step0Labels = labelEmbedding7 ∘ raw2418step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2418step0 raw2418step0Labels raw2418step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5370 node5370Labels := by rfl

theorem canonical2419 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2419 raw2419Labels = mixedMoment B node3706 node3706Labels := by
  calc
    mixedMoment B raw2419 raw2419Labels = mixedMoment B raw2419step0 raw2419step0Labels := by
      have ha : raw2419step0 = (fun i j => raw2419 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2419step0 raw2419; decide +kernel
      have hl : raw2419step0Labels = raw2419Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2419 raw2419Labels permutation32 permutation4
    _ = mixedMoment B node3706 node3706Labels := by rfl

theorem canonical2420 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2420 raw2420Labels = mixedMoment B node3771 node3771Labels := by
  calc
    mixedMoment B raw2420 raw2420Labels = mixedMoment B raw2420step0 raw2420step0Labels := by
      have ha : raw2420step0 = (fun i j => raw2420 (permutation36 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2420step0 raw2420; decide +kernel
      have hl : raw2420step0Labels = raw2420Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2420 raw2420Labels permutation36 permutation6
    mixedMoment B raw2420step0 raw2420step0Labels = mixedMoment B raw2420step1 raw2420step1Labels := by
      have ha : raw2420step1 = -raw2420step0 := by apply Matrix.ext; change ∀ i j, raw2420step1 i j = -(raw2420step0 i j); unfold raw2420step1 raw2420step0; decide +kernel
      have hl : raw2420step1Labels = raw2420step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2420step1 raw2420step1Labels = mixedMoment B raw2420step2 raw2420step2Labels := by
      have ha : raw2420step2 = raw2420step1 := by apply Matrix.ext; unfold raw2420step2 raw2420step1; decide +kernel
      have hl : raw2420step1Labels = labelEmbedding1 ∘ raw2420step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2420step1 raw2420step1Labels raw2420step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3771 node3771Labels := by rfl

theorem canonical2430 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2430 raw2430Labels = mixedMoment B node5378 node5378Labels := by
  calc
    mixedMoment B raw2430 raw2430Labels = mixedMoment B raw2430step0 raw2430step0Labels := by
      have ha : raw2430step0 = (fun i j => raw2430 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2430step0 raw2430; decide +kernel
      have hl : raw2430step0Labels = raw2430Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2430 raw2430Labels permutation152 permutation4
    mixedMoment B raw2430step0 raw2430step0Labels = mixedMoment B raw2430step1 raw2430step1Labels := by
      have ha : raw2430step1 = raw2430step0 := by apply Matrix.ext; unfold raw2430step1 raw2430step0; decide +kernel
      have hl : raw2430step0Labels = labelEmbedding7 ∘ raw2430step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2430step0 raw2430step0Labels raw2430step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5378 node5378Labels := by rfl

theorem canonical2431 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2431 raw2431Labels = mixedMoment B node3719 node3719Labels := by
  calc
    mixedMoment B raw2431 raw2431Labels = mixedMoment B raw2431step0 raw2431step0Labels := by
      have ha : raw2431step0 = (fun i j => raw2431 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2431step0 raw2431; decide +kernel
      have hl : raw2431step0Labels = raw2431Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2431 raw2431Labels permutation152 permutation4
    _ = mixedMoment B node3719 node3719Labels := by rfl

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

theorem canonical2432 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2432 raw2432Labels = mixedMoment B node3795 node3795Labels := by
  calc
    mixedMoment B raw2432 raw2432Labels = mixedMoment B raw2432step0 raw2432step0Labels := by
      have ha : raw2432step0 = (fun i j => raw2432 (permutation686 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2432step0 raw2432; decide +kernel
      have hl : raw2432step0Labels = raw2432Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2432 raw2432Labels permutation686 permutation6
    mixedMoment B raw2432step0 raw2432step0Labels = mixedMoment B raw2432step1 raw2432step1Labels := by
      have ha : raw2432step1 = raw2432step0 := by apply Matrix.ext; unfold raw2432step1 raw2432step0; decide +kernel
      have hl : raw2432step0Labels = labelEmbedding1 ∘ raw2432step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2432step0 raw2432step0Labels raw2432step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3795 node3795Labels := by rfl

theorem canonical2439 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2439 raw2439Labels = mixedMoment B node5384 node5384Labels := by
  calc
    mixedMoment B raw2439 raw2439Labels = mixedMoment B raw2439step0 raw2439step0Labels := by
      have ha : raw2439step0 = (fun i j => raw2439 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2439step0 raw2439; decide +kernel
      have hl : raw2439step0Labels = raw2439Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2439 raw2439Labels permutation32 permutation4
    mixedMoment B raw2439step0 raw2439step0Labels = mixedMoment B raw2439step1 raw2439step1Labels := by
      have ha : raw2439step1 = raw2439step0 := by apply Matrix.ext; unfold raw2439step1 raw2439step0; decide +kernel
      have hl : raw2439step0Labels = labelEmbedding7 ∘ raw2439step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2439step0 raw2439step0Labels raw2439step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5384 node5384Labels := by rfl

theorem canonical2440 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2440 raw2440Labels = mixedMoment B node3732 node3732Labels := by
  calc
    mixedMoment B raw2440 raw2440Labels = mixedMoment B raw2440step0 raw2440step0Labels := by
      have ha : raw2440step0 = (fun i j => raw2440 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2440step0 raw2440; decide +kernel
      have hl : raw2440step0Labels = raw2440Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2440 raw2440Labels permutation32 permutation4
    _ = mixedMoment B node3732 node3732Labels := by rfl

theorem canonical2441 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2441 raw2441Labels = mixedMoment B node3811 node3811Labels := by
  calc
    mixedMoment B raw2441 raw2441Labels = mixedMoment B raw2441step0 raw2441step0Labels := by
      have ha : raw2441step0 = (fun i j => raw2441 (permutation149 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2441step0 raw2441; decide +kernel
      have hl : raw2441step0Labels = raw2441Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2441 raw2441Labels permutation149 permutation6
    mixedMoment B raw2441step0 raw2441step0Labels = mixedMoment B raw2441step1 raw2441step1Labels := by
      have ha : raw2441step1 = raw2441step0 := by apply Matrix.ext; unfold raw2441step1 raw2441step0; decide +kernel
      have hl : raw2441step0Labels = labelEmbedding1 ∘ raw2441step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2441step0 raw2441step0Labels raw2441step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3811 node3811Labels := by rfl

theorem canonical2490 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2490 raw2490Labels = mixedMoment B node5411 node5411Labels := by
  calc
    mixedMoment B raw2490 raw2490Labels = mixedMoment B raw2490step0 raw2490step0Labels := by
      have ha : raw2490step0 = (fun i j => raw2490 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2490step0 raw2490; decide +kernel
      have hl : raw2490step0Labels = raw2490Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2490 raw2490Labels permutation32 permutation4
    mixedMoment B raw2490step0 raw2490step0Labels = mixedMoment B raw2490step1 raw2490step1Labels := by
      have ha : raw2490step1 = raw2490step0 := by apply Matrix.ext; unfold raw2490step1 raw2490step0; decide +kernel
      have hl : raw2490step0Labels = labelEmbedding7 ∘ raw2490step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2490step0 raw2490step0Labels raw2490step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5411 node5411Labels := by rfl

theorem canonical2491 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2491 raw2491Labels = mixedMoment B node3809 node3809Labels := by
  calc
    mixedMoment B raw2491 raw2491Labels = mixedMoment B raw2491step0 raw2491step0Labels := by
      have ha : raw2491step0 = (fun i j => raw2491 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2491step0 raw2491; decide +kernel
      have hl : raw2491step0Labels = raw2491Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2491 raw2491Labels permutation32 permutation4
    _ = mixedMoment B node3809 node3809Labels := by rfl

theorem canonical2492 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2492 raw2492Labels = mixedMoment B node3813 node3813Labels := by
  calc
    mixedMoment B raw2492 raw2492Labels = mixedMoment B raw2492step0 raw2492step0Labels := by
      have ha : raw2492step0 = (fun i j => raw2492 (permutation36 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2492step0 raw2492; decide +kernel
      have hl : raw2492step0Labels = raw2492Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2492 raw2492Labels permutation36 permutation6
    mixedMoment B raw2492step0 raw2492step0Labels = mixedMoment B raw2492step1 raw2492step1Labels := by
      have ha : raw2492step1 = -raw2492step0 := by apply Matrix.ext; change ∀ i j, raw2492step1 i j = -(raw2492step0 i j); unfold raw2492step1 raw2492step0; decide +kernel
      have hl : raw2492step1Labels = raw2492step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2492step1 raw2492step1Labels = mixedMoment B raw2492step2 raw2492step2Labels := by
      have ha : raw2492step2 = raw2492step1 := by apply Matrix.ext; unfold raw2492step2 raw2492step1; decide +kernel
      have hl : raw2492step1Labels = labelEmbedding1 ∘ raw2492step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2492step1 raw2492step1Labels raw2492step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3813 node3813Labels := by rfl

theorem canonical2517 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2517 raw2517Labels = mixedMoment B node5428 node5428Labels := by
  calc
    mixedMoment B raw2517 raw2517Labels = mixedMoment B raw2517step0 raw2517step0Labels := by
      have ha : raw2517step0 = (fun i j => raw2517 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2517step0 raw2517; decide +kernel
      have hl : raw2517step0Labels = raw2517Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2517 raw2517Labels permutation32 permutation4
    mixedMoment B raw2517step0 raw2517step0Labels = mixedMoment B raw2517step1 raw2517step1Labels := by
      have ha : raw2517step1 = raw2517step0 := by apply Matrix.ext; unfold raw2517step1 raw2517step0; decide +kernel
      have hl : raw2517step0Labels = labelEmbedding7 ∘ raw2517step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2517step0 raw2517step0Labels raw2517step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5428 node5428Labels := by rfl

theorem canonical2518 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2518 raw2518Labels = mixedMoment B node3845 node3845Labels := by
  calc
    mixedMoment B raw2518 raw2518Labels = mixedMoment B raw2518step0 raw2518step0Labels := by
      have ha : raw2518step0 = (fun i j => raw2518 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2518step0 raw2518; decide +kernel
      have hl : raw2518step0Labels = raw2518Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2518 raw2518Labels permutation32 permutation4
    _ = mixedMoment B node3845 node3845Labels := by rfl

theorem canonical2519 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2519 raw2519Labels = mixedMoment B node3845 node3845Labels := by
  calc
    mixedMoment B raw2519 raw2519Labels = mixedMoment B raw2519step0 raw2519step0Labels := by
      have ha : raw2519step0 = (fun i j => raw2519 (permutation39 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2519step0 raw2519; decide +kernel
      have hl : raw2519step0Labels = raw2519Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2519 raw2519Labels permutation39 permutation6
    mixedMoment B raw2519step0 raw2519step0Labels = mixedMoment B raw2519step1 raw2519step1Labels := by
      have ha : raw2519step1 = -raw2519step0 := by apply Matrix.ext; change ∀ i j, raw2519step1 i j = -(raw2519step0 i j); unfold raw2519step1 raw2519step0; decide +kernel
      have hl : raw2519step1Labels = raw2519step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2519step1 raw2519step1Labels = mixedMoment B raw2519step2 raw2519step2Labels := by
      have ha : raw2519step2 = raw2519step1 := by apply Matrix.ext; unfold raw2519step2 raw2519step1; decide +kernel
      have hl : raw2519step1Labels = labelEmbedding1 ∘ raw2519step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2519step1 raw2519step1Labels raw2519step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3845 node3845Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical272
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical34941 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34941 raw34941Labels = mixedMoment B node5141 node5141Labels := by
  calc
    mixedMoment B raw34941 raw34941Labels = mixedMoment B raw34941step0 raw34941step0Labels := by
      have hz : ∀ j, raw34941 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34941step0 = (fun i j => raw34941 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34941step0 raw34941; decide +kernel
      have hl : raw34941step0Labels = raw34941Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34941 raw34941Labels permutation346 hz
    mixedMoment B raw34941step0 raw34941step0Labels = mixedMoment B raw34941step1 raw34941step1Labels := by
      have ha : raw34941step1 = (fun i j => raw34941step0 (permutation57 i) (permutation2 j)) := by apply Matrix.ext; unfold raw34941step1 raw34941step0; decide +kernel
      have hl : raw34941step1Labels = raw34941step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34941step0 raw34941step0Labels permutation57 permutation2
    _ = mixedMoment B node5141 node5141Labels := by rfl

theorem canonical34942 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34942 raw34942Labels = mixedMoment B node5351 node5351Labels := by
  calc
    mixedMoment B raw34942 raw34942Labels = mixedMoment B raw34942step0 raw34942step0Labels := by
      have ha : raw34942step0 = (fun i j => raw34942 (permutation585 i) (permutation2 j)) := by apply Matrix.ext; unfold raw34942step0 raw34942; decide +kernel
      have hl : raw34942step0Labels = raw34942Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34942 raw34942Labels permutation585 permutation2
    mixedMoment B raw34942step0 raw34942step0Labels = mixedMoment B raw34942step1 raw34942step1Labels := by
      have ha : raw34942step1 = -raw34942step0 := by apply Matrix.ext; change ∀ i j, raw34942step1 i j = -(raw34942step0 i j); unfold raw34942step1 raw34942step0; decide +kernel
      have hl : raw34942step1Labels = raw34942step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5351 node5351Labels := by rfl

theorem canonical34943 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34943 raw34943Labels = mixedMoment B node5367 node5367Labels := by
  calc
    mixedMoment B raw34943 raw34943Labels = mixedMoment B raw34943step0 raw34943step0Labels := by
      have hz : ∀ j, raw34943 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34943step0 = (fun i j => raw34943 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34943step0 raw34943; decide +kernel
      have hl : raw34943step0Labels = raw34943Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34943 raw34943Labels permutation346 hz
    mixedMoment B raw34943step0 raw34943step0Labels = mixedMoment B raw34943step1 raw34943step1Labels := by
      have ha : raw34943step1 = (fun i j => raw34943step0 (permutation123 i) (permutation2 j)) := by apply Matrix.ext; unfold raw34943step1 raw34943step0; decide +kernel
      have hl : raw34943step1Labels = raw34943step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34943step0 raw34943step0Labels permutation123 permutation2
    mixedMoment B raw34943step1 raw34943step1Labels = mixedMoment B raw34943step2 raw34943step2Labels := by
      have ha : raw34943step2 = -raw34943step1 := by apply Matrix.ext; change ∀ i j, raw34943step2 i j = -(raw34943step1 i j); unfold raw34943step2 raw34943step1; decide +kernel
      have hl : raw34943step2Labels = raw34943step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5367 node5367Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical273
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical34944 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34944 raw34944Labels = mixedMoment B node5409 node5409Labels := by
  calc
    mixedMoment B raw34944 raw34944Labels = mixedMoment B raw34944step0 raw34944step0Labels := by
      have hz : ∀ j, raw34944 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34944step0 = (fun i j => raw34944 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34944step0 raw34944; decide +kernel
      have hl : raw34944step0Labels = raw34944Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34944 raw34944Labels permutation346 hz
    mixedMoment B raw34944step0 raw34944step0Labels = mixedMoment B raw34944step1 raw34944step1Labels := by
      have ha : raw34944step1 = (fun i j => raw34944step0 (permutation126 i) (permutation2 j)) := by apply Matrix.ext; unfold raw34944step1 raw34944step0; decide +kernel
      have hl : raw34944step1Labels = raw34944step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34944step0 raw34944step0Labels permutation126 permutation2
    mixedMoment B raw34944step1 raw34944step1Labels = mixedMoment B raw34944step2 raw34944step2Labels := by
      have ha : raw34944step2 = -raw34944step1 := by apply Matrix.ext; change ∀ i j, raw34944step2 i j = -(raw34944step1 i j); unfold raw34944step2 raw34944step1; decide +kernel
      have hl : raw34944step2Labels = raw34944step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5409 node5409Labels := by rfl

theorem canonical34945 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34945 raw34945Labels = mixedMoment B node5446 node5446Labels := by
  calc
    mixedMoment B raw34945 raw34945Labels = mixedMoment B raw34945step0 raw34945step0Labels := by
      have hz : ∀ j, raw34945 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34945step0 = (fun i j => raw34945 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34945step0 raw34945; decide +kernel
      have hl : raw34945step0Labels = raw34945Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34945 raw34945Labels permutation346 hz
    mixedMoment B raw34945step0 raw34945step0Labels = mixedMoment B raw34945step1 raw34945step1Labels := by
      have ha : raw34945step1 = (fun i j => raw34945step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34945step1 raw34945step0; decide +kernel
      have hl : raw34945step1Labels = raw34945step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34945step0 raw34945step0Labels permutation32 permutation3
    mixedMoment B raw34945step1 raw34945step1Labels = mixedMoment B raw34945step2 raw34945step2Labels := by
      have ha : raw34945step2 = raw34945step1 := by apply Matrix.ext; unfold raw34945step2 raw34945step1; decide +kernel
      have hl : raw34945step1Labels = labelEmbedding6 ∘ raw34945step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34945step1 raw34945step1Labels raw34945step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5446 node5446Labels := by rfl

theorem canonical34946 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34946 raw34946Labels = mixedMoment B node4668 node4668Labels := by
  calc
    mixedMoment B raw34946 raw34946Labels = mixedMoment B raw34946step0 raw34946step0Labels := by
      have ha : raw34946step0 = (fun i j => raw34946 (permutation158 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34946step0 raw34946; decide +kernel
      have hl : raw34946step0Labels = raw34946Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34946 raw34946Labels permutation158 permutation3
    mixedMoment B raw34946step0 raw34946step0Labels = mixedMoment B raw34946step1 raw34946step1Labels := by
      have ha : raw34946step1 = raw34946step0 := by apply Matrix.ext; unfold raw34946step1 raw34946step0; decide +kernel
      have hl : raw34946step0Labels = labelEmbedding6 ∘ raw34946step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34946step0 raw34946step0Labels raw34946step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4668 node4668Labels := by rfl

theorem canonical34947 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34947 raw34947Labels = mixedMoment B node4955 node4955Labels := by
  calc
    mixedMoment B raw34947 raw34947Labels = mixedMoment B raw34947step0 raw34947step0Labels := by
      have ha : raw34947step0 = (fun i j => raw34947 (permutation272 i) (permutation2 j)) := by apply Matrix.ext; unfold raw34947step0 raw34947; decide +kernel
      have hl : raw34947step0Labels = raw34947Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34947 raw34947Labels permutation272 permutation2
    _ = mixedMoment B node4955 node4955Labels := by rfl

theorem canonical34948 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34948 raw34948Labels = mixedMoment B node5336 node5336Labels := by
  calc
    mixedMoment B raw34948 raw34948Labels = mixedMoment B raw34948step0 raw34948step0Labels := by
      have ha : raw34948step0 = (fun i j => raw34948 (permutation583 i) (permutation2 j)) := by apply Matrix.ext; unfold raw34948step0 raw34948; decide +kernel
      have hl : raw34948step0Labels = raw34948Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34948 raw34948Labels permutation583 permutation2
    mixedMoment B raw34948step0 raw34948step0Labels = mixedMoment B raw34948step1 raw34948step1Labels := by
      have ha : raw34948step1 = -raw34948step0 := by apply Matrix.ext; change ∀ i j, raw34948step1 i j = -(raw34948step0 i j); unfold raw34948step1 raw34948step0; decide +kernel
      have hl : raw34948step1Labels = raw34948step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5336 node5336Labels := by rfl

theorem canonical34949 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34949 raw34949Labels = mixedMoment B node5378 node5378Labels := by
  calc
    mixedMoment B raw34949 raw34949Labels = mixedMoment B raw34949step0 raw34949step0Labels := by
      have ha : raw34949step0 = (fun i j => raw34949 (permutation272 i) (permutation2 j)) := by apply Matrix.ext; unfold raw34949step0 raw34949; decide +kernel
      have hl : raw34949step0Labels = raw34949Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34949 raw34949Labels permutation272 permutation2
    _ = mixedMoment B node5378 node5378Labels := by rfl

theorem canonical34950 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34950 raw34950Labels = mixedMoment B node4690 node4690Labels := by
  calc
    mixedMoment B raw34950 raw34950Labels = mixedMoment B raw34950step0 raw34950step0Labels := by
      have hz : ∀ j, raw34950 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34950step0 = (fun i j => raw34950 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34950step0 raw34950; decide +kernel
      have hl : raw34950step0Labels = raw34950Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34950 raw34950Labels permutation346 hz
    mixedMoment B raw34950step0 raw34950step0Labels = mixedMoment B raw34950step1 raw34950step1Labels := by
      have ha : raw34950step1 = (fun i j => raw34950step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34950step1 raw34950step0; decide +kernel
      have hl : raw34950step1Labels = raw34950step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34950step0 raw34950step0Labels permutation32 permutation3
    mixedMoment B raw34950step1 raw34950step1Labels = mixedMoment B raw34950step2 raw34950step2Labels := by
      have ha : raw34950step2 = raw34950step1 := by apply Matrix.ext; unfold raw34950step2 raw34950step1; decide +kernel
      have hl : raw34950step1Labels = labelEmbedding6 ∘ raw34950step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34950step1 raw34950step1Labels raw34950step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4690 node4690Labels := by rfl

theorem canonical34951 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34951 raw34951Labels = mixedMoment B node4966 node4966Labels := by
  calc
    mixedMoment B raw34951 raw34951Labels = mixedMoment B raw34951step0 raw34951step0Labels := by
      have hz : ∀ j, raw34951 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34951step0 = (fun i j => raw34951 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34951step0 raw34951; decide +kernel
      have hl : raw34951step0Labels = raw34951Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34951 raw34951Labels permutation346 hz
    mixedMoment B raw34951step0 raw34951step0Labels = mixedMoment B raw34951step1 raw34951step1Labels := by
      have ha : raw34951step1 = (fun i j => raw34951step0 (permutation57 i) (permutation2 j)) := by apply Matrix.ext; unfold raw34951step1 raw34951step0; decide +kernel
      have hl : raw34951step1Labels = raw34951step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34951step0 raw34951step0Labels permutation57 permutation2
    _ = mixedMoment B node4966 node4966Labels := by rfl

theorem canonical34952 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34952 raw34952Labels = mixedMoment B node5339 node5339Labels := by
  calc
    mixedMoment B raw34952 raw34952Labels = mixedMoment B raw34952step0 raw34952step0Labels := by
      have ha : raw34952step0 = (fun i j => raw34952 (permutation588 i) (permutation2 j)) := by apply Matrix.ext; unfold raw34952step0 raw34952; decide +kernel
      have hl : raw34952step0Labels = raw34952Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34952 raw34952Labels permutation588 permutation2
    mixedMoment B raw34952step0 raw34952step0Labels = mixedMoment B raw34952step1 raw34952step1Labels := by
      have ha : raw34952step1 = -raw34952step0 := by apply Matrix.ext; change ∀ i j, raw34952step1 i j = -(raw34952step0 i j); unfold raw34952step1 raw34952step0; decide +kernel
      have hl : raw34952step1Labels = raw34952step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5339 node5339Labels := by rfl

theorem canonical34953 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34953 raw34953Labels = mixedMoment B node5384 node5384Labels := by
  calc
    mixedMoment B raw34953 raw34953Labels = mixedMoment B raw34953step0 raw34953step0Labels := by
      have hz : ∀ j, raw34953 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34953step0 = (fun i j => raw34953 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34953step0 raw34953; decide +kernel
      have hl : raw34953step0Labels = raw34953Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34953 raw34953Labels permutation346 hz
    mixedMoment B raw34953step0 raw34953step0Labels = mixedMoment B raw34953step1 raw34953step1Labels := by
      have ha : raw34953step1 = (fun i j => raw34953step0 (permutation57 i) (permutation2 j)) := by apply Matrix.ext; unfold raw34953step1 raw34953step0; decide +kernel
      have hl : raw34953step1Labels = raw34953step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34953step0 raw34953step0Labels permutation57 permutation2
    _ = mixedMoment B node5384 node5384Labels := by rfl

theorem canonical34954 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34954 raw34954Labels = mixedMoment B node4670 node4670Labels := by
  calc
    mixedMoment B raw34954 raw34954Labels = mixedMoment B raw34954step0 raw34954step0Labels := by
      have hz : ∀ j, raw34954 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34954step0 = (fun i j => raw34954 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34954step0 raw34954; decide +kernel
      have hl : raw34954step0Labels = raw34954Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34954 raw34954Labels permutation346 hz
    mixedMoment B raw34954step0 raw34954step0Labels = mixedMoment B raw34954step1 raw34954step1Labels := by
      have ha : raw34954step1 = (fun i j => raw34954step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34954step1 raw34954step0; decide +kernel
      have hl : raw34954step1Labels = raw34954step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34954step0 raw34954step0Labels permutation33 permutation3
    mixedMoment B raw34954step1 raw34954step1Labels = mixedMoment B raw34954step2 raw34954step2Labels := by
      have ha : raw34954step2 = raw34954step1 := by apply Matrix.ext; unfold raw34954step2 raw34954step1; decide +kernel
      have hl : raw34954step1Labels = labelEmbedding6 ∘ raw34954step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34954step1 raw34954step1Labels raw34954step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4670 node4670Labels := by rfl

theorem canonical34955 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34955 raw34955Labels = mixedMoment B node4934 node4934Labels := by
  calc
    mixedMoment B raw34955 raw34955Labels = mixedMoment B raw34955step0 raw34955step0Labels := by
      have hz : ∀ j, raw34955 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34955step0 = (fun i j => raw34955 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34955step0 raw34955; decide +kernel
      have hl : raw34955step0Labels = raw34955Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34955 raw34955Labels permutation346 hz
    mixedMoment B raw34955step0 raw34955step0Labels = mixedMoment B raw34955step1 raw34955step1Labels := by
      have ha : raw34955step1 = (fun i j => raw34955step0 (permutation126 i) (permutation2 j)) := by apply Matrix.ext; unfold raw34955step1 raw34955step0; decide +kernel
      have hl : raw34955step1Labels = raw34955step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34955step0 raw34955step0Labels permutation126 permutation2
    mixedMoment B raw34955step1 raw34955step1Labels = mixedMoment B raw34955step2 raw34955step2Labels := by
      have ha : raw34955step2 = -raw34955step1 := by apply Matrix.ext; change ∀ i j, raw34955step2 i j = -(raw34955step1 i j); unfold raw34955step2 raw34955step1; decide +kernel
      have hl : raw34955step2Labels = raw34955step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4934 node4934Labels := by rfl

theorem canonical34956 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34956 raw34956Labels = mixedMoment B node4931 node4931Labels := by
  calc
    mixedMoment B raw34956 raw34956Labels = mixedMoment B raw34956step0 raw34956step0Labels := by
      have ha : raw34956step0 = (fun i j => raw34956 (permutation588 i) (permutation2 j)) := by apply Matrix.ext; unfold raw34956step0 raw34956; decide +kernel
      have hl : raw34956step0Labels = raw34956Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34956 raw34956Labels permutation588 permutation2
    mixedMoment B raw34956step0 raw34956step0Labels = mixedMoment B raw34956step1 raw34956step1Labels := by
      have ha : raw34956step1 = -raw34956step0 := by apply Matrix.ext; change ∀ i j, raw34956step1 i j = -(raw34956step0 i j); unfold raw34956step1 raw34956step0; decide +kernel
      have hl : raw34956step1Labels = raw34956step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4931 node4931Labels := by rfl

theorem canonical34957 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34957 raw34957Labels = mixedMoment B node4949 node4949Labels := by
  calc
    mixedMoment B raw34957 raw34957Labels = mixedMoment B raw34957step0 raw34957step0Labels := by
      have hz : ∀ j, raw34957 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34957step0 = (fun i j => raw34957 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34957step0 raw34957; decide +kernel
      have hl : raw34957step0Labels = raw34957Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34957 raw34957Labels permutation346 hz
    mixedMoment B raw34957step0 raw34957step0Labels = mixedMoment B raw34957step1 raw34957step1Labels := by
      have ha : raw34957step1 = (fun i j => raw34957step0 (permutation126 i) (permutation2 j)) := by apply Matrix.ext; unfold raw34957step1 raw34957step0; decide +kernel
      have hl : raw34957step1Labels = raw34957step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34957step0 raw34957step0Labels permutation126 permutation2
    mixedMoment B raw34957step1 raw34957step1Labels = mixedMoment B raw34957step2 raw34957step2Labels := by
      have ha : raw34957step2 = -raw34957step1 := by apply Matrix.ext; change ∀ i j, raw34957step2 i j = -(raw34957step1 i j); unfold raw34957step2 raw34957step1; decide +kernel
      have hl : raw34957step2Labels = raw34957step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4949 node4949Labels := by rfl

theorem canonical34958 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34958 raw34958Labels = mixedMoment B node5080 node5080Labels := by
  calc
    mixedMoment B raw34958 raw34958Labels = mixedMoment B raw34958step0 raw34958step0Labels := by
      have hz : ∀ j, raw34958 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34958step0 = (fun i j => raw34958 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34958step0 raw34958; decide +kernel
      have hl : raw34958step0Labels = raw34958Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34958 raw34958Labels permutation346 hz
    mixedMoment B raw34958step0 raw34958step0Labels = mixedMoment B raw34958step1 raw34958step1Labels := by
      have ha : raw34958step1 = (fun i j => raw34958step0 (permutation126 i) (permutation2 j)) := by apply Matrix.ext; unfold raw34958step1 raw34958step0; decide +kernel
      have hl : raw34958step1Labels = raw34958step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34958step0 raw34958step0Labels permutation126 permutation2
    mixedMoment B raw34958step1 raw34958step1Labels = mixedMoment B raw34958step2 raw34958step2Labels := by
      have ha : raw34958step2 = -raw34958step1 := by apply Matrix.ext; change ∀ i j, raw34958step2 i j = -(raw34958step1 i j); unfold raw34958step2 raw34958step1; decide +kernel
      have hl : raw34958step2Labels = raw34958step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5080 node5080Labels := by rfl

theorem canonical34959 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34959 raw34959Labels = mixedMoment B node4669 node4669Labels := by
  calc
    mixedMoment B raw34959 raw34959Labels = mixedMoment B raw34959step0 raw34959step0Labels := by
      have hz : ∀ j, raw34959 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34959step0 = (fun i j => raw34959 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34959step0 raw34959; decide +kernel
      have hl : raw34959step0Labels = raw34959Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34959 raw34959Labels permutation346 hz
    mixedMoment B raw34959step0 raw34959step0Labels = mixedMoment B raw34959step1 raw34959step1Labels := by
      have ha : raw34959step1 = (fun i j => raw34959step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34959step1 raw34959step0; decide +kernel
      have hl : raw34959step1Labels = raw34959step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34959step0 raw34959step0Labels permutation32 permutation3
    mixedMoment B raw34959step1 raw34959step1Labels = mixedMoment B raw34959step2 raw34959step2Labels := by
      have ha : raw34959step2 = raw34959step1 := by apply Matrix.ext; unfold raw34959step2 raw34959step1; decide +kernel
      have hl : raw34959step1Labels = labelEmbedding6 ∘ raw34959step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34959step1 raw34959step1Labels raw34959step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4669 node4669Labels := by rfl

theorem canonical34960 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34960 raw34960Labels = mixedMoment B node4959 node4959Labels := by
  calc
    mixedMoment B raw34960 raw34960Labels = mixedMoment B raw34960step0 raw34960step0Labels := by
      have hz : ∀ j, raw34960 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34960step0 = (fun i j => raw34960 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34960step0 raw34960; decide +kernel
      have hl : raw34960step0Labels = raw34960Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34960 raw34960Labels permutation346 hz
    mixedMoment B raw34960step0 raw34960step0Labels = mixedMoment B raw34960step1 raw34960step1Labels := by
      have ha : raw34960step1 = (fun i j => raw34960step0 (permutation56 i) (permutation2 j)) := by apply Matrix.ext; unfold raw34960step1 raw34960step0; decide +kernel
      have hl : raw34960step1Labels = raw34960step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34960step0 raw34960step0Labels permutation56 permutation2
    _ = mixedMoment B node4959 node4959Labels := by rfl

theorem canonical34961 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34961 raw34961Labels = mixedMoment B node4957 node4957Labels := by
  calc
    mixedMoment B raw34961 raw34961Labels = mixedMoment B raw34961step0 raw34961step0Labels := by
      have ha : raw34961step0 = (fun i j => raw34961 (permutation688 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34961step0 raw34961; decide +kernel
      have hl : raw34961step0Labels = raw34961Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34961 raw34961Labels permutation688 permutation3
    mixedMoment B raw34961step0 raw34961step0Labels = mixedMoment B raw34961step1 raw34961step1Labels := by
      have ha : raw34961step1 = -raw34961step0 := by apply Matrix.ext; change ∀ i j, raw34961step1 i j = -(raw34961step0 i j); unfold raw34961step1 raw34961step0; decide +kernel
      have hl : raw34961step1Labels = raw34961step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34961step1 raw34961step1Labels = mixedMoment B raw34961step2 raw34961step2Labels := by
      have ha : raw34961step2 = raw34961step1 := by apply Matrix.ext; unfold raw34961step2 raw34961step1; decide +kernel
      have hl : raw34961step1Labels = labelEmbedding6 ∘ raw34961step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34961step1 raw34961step1Labels raw34961step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4957 node4957Labels := by rfl

theorem canonical34962 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34962 raw34962Labels = mixedMoment B node4973 node4973Labels := by
  calc
    mixedMoment B raw34962 raw34962Labels = mixedMoment B raw34962step0 raw34962step0Labels := by
      have hz : ∀ j, raw34962 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34962step0 = (fun i j => raw34962 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34962step0 raw34962; decide +kernel
      have hl : raw34962step0Labels = raw34962Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34962 raw34962Labels permutation346 hz
    mixedMoment B raw34962step0 raw34962step0Labels = mixedMoment B raw34962step1 raw34962step1Labels := by
      have ha : raw34962step1 = (fun i j => raw34962step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34962step1 raw34962step0; decide +kernel
      have hl : raw34962step1Labels = raw34962step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34962step0 raw34962step0Labels permutation151 permutation3
    mixedMoment B raw34962step1 raw34962step1Labels = mixedMoment B raw34962step2 raw34962step2Labels := by
      have ha : raw34962step2 = -raw34962step1 := by apply Matrix.ext; change ∀ i j, raw34962step2 i j = -(raw34962step1 i j); unfold raw34962step2 raw34962step1; decide +kernel
      have hl : raw34962step2Labels = raw34962step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34962step2 raw34962step2Labels = mixedMoment B raw34962step3 raw34962step3Labels := by
      have ha : raw34962step3 = raw34962step2 := by apply Matrix.ext; unfold raw34962step3 raw34962step2; decide +kernel
      have hl : raw34962step2Labels = labelEmbedding6 ∘ raw34962step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34962step2 raw34962step2Labels raw34962step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4973 node4973Labels := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons77
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singleton4949 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4949 node4949Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2341 node2341Labels + mixedMoment B node3417 node3417Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1920 singletonSmall4949
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4949) = raw1920Labels := by decide +kernel
  rw [hl, canonical1920 B hB] at h
  have hc0 : mixedMoment B raw1920 (Fin.cases (0 : Fin 2) singletonSmall4949) =
      mixedMoment B node2341 node2341Labels := by
    have ha : raw1920 = raw1921 := by apply Matrix.ext; unfold raw1920 raw1921; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4949 = raw1921Labels := by decide +kernel
    rw [ha, hj, canonical1921 B hB]
  have hc1 : mixedMoment B raw1920 (Fin.cases (1 : Fin 2) singletonSmall4949) =
      mixedMoment B node3417 node3417Labels := by
    have ha : raw1920 = raw1922 := by apply Matrix.ext; unfold raw1920 raw1922; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4949 = raw1922Labels := by decide +kernel
    rw [ha, hj, canonical1922 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4973 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4973 node4973Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2817 node2817Labels + mixedMoment B node3591 node3591Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1959 singletonSmall4973
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4973) = raw1959Labels := by decide +kernel
  rw [hl, canonical1959 B hB] at h
  have hc0 : mixedMoment B raw1959 (Fin.cases (0 : Fin 2) singletonSmall4973) =
      mixedMoment B node2817 node2817Labels := by
    have ha : raw1959 = raw1960 := by apply Matrix.ext; unfold raw1959 raw1960; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4973 = raw1960Labels := by decide +kernel
    rw [ha, hj, canonical1960 B hB]
  have hc1 : mixedMoment B raw1959 (Fin.cases (1 : Fin 2) singletonSmall4973) =
      mixedMoment B node3591 node3591Labels := by
    have ha : raw1959 = raw1961 := by apply Matrix.ext; unfold raw1959 raw1961; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4973 = raw1961Labels := by decide +kernel
    rw [ha, hj, canonical1961 B hB]
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

theorem singleton5141 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5141 node5141Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2561 node2561Labels + mixedMoment B node3522 node3522Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2169 singletonSmall5141
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5141) = raw2169Labels := by decide +kernel
  rw [hl, canonical2169 B hB] at h
  have hc0 : mixedMoment B raw2169 (Fin.cases (0 : Fin 2) singletonSmall5141) =
      mixedMoment B node2561 node2561Labels := by
    have ha : raw2169 = raw2170 := by apply Matrix.ext; unfold raw2169 raw2170; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5141 = raw2170Labels := by decide +kernel
    rw [ha, hj, canonical2170 B hB]
  have hc1 : mixedMoment B raw2169 (Fin.cases (1 : Fin 2) singletonSmall5141) =
      mixedMoment B node3522 node3522Labels := by
    have ha : raw2169 = raw2171 := by apply Matrix.ext; unfold raw2169 raw2171; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5141 = raw2171Labels := by decide +kernel
    rw [ha, hj, canonical2171 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons83
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singleton5336 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5336 node5336Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3671 node3671Labels + mixedMoment B node3754 node3754Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2373 singletonSmall5336
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5336) = raw2373Labels := by decide +kernel
  rw [hl, canonical2373 B hB] at h
  have hc0 : mixedMoment B raw2373 (Fin.cases (0 : Fin 2) singletonSmall5336) =
      mixedMoment B node3671 node3671Labels := by
    have ha : raw2373 = raw2374 := by apply Matrix.ext; unfold raw2373 raw2374; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5336 = raw2374Labels := by decide +kernel
    rw [ha, hj, canonical2374 B hB]
  have hc1 : mixedMoment B raw2373 (Fin.cases (1 : Fin 2) singletonSmall5336) =
      mixedMoment B node3754 node3754Labels := by
    have ha : raw2373 = raw2375 := by apply Matrix.ext; unfold raw2373 raw2375; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5336 = raw2375Labels := by decide +kernel
    rw [ha, hj, canonical2375 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton5351 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5351 node5351Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3689 node3689Labels + mixedMoment B node3757 node3757Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2391 singletonSmall5351
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5351) = raw2391Labels := by decide +kernel
  rw [hl, canonical2391 B hB] at h
  have hc0 : mixedMoment B raw2391 (Fin.cases (0 : Fin 2) singletonSmall5351) =
      mixedMoment B node3689 node3689Labels := by
    have ha : raw2391 = raw2392 := by apply Matrix.ext; unfold raw2391 raw2392; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5351 = raw2392Labels := by decide +kernel
    rw [ha, hj, canonical2392 B hB]
  have hc1 : mixedMoment B raw2391 (Fin.cases (1 : Fin 2) singletonSmall5351) =
      mixedMoment B node3757 node3757Labels := by
    have ha : raw2391 = raw2393 := by apply Matrix.ext; unfold raw2391 raw2393; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5351 = raw2393Labels := by decide +kernel
    rw [ha, hj, canonical2393 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton5370 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5370 node5370Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3706 node3706Labels + mixedMoment B node3771 node3771Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2418 singletonSmall5370
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5370) = raw2418Labels := by decide +kernel
  rw [hl, canonical2418 B hB] at h
  have hc0 : mixedMoment B raw2418 (Fin.cases (0 : Fin 2) singletonSmall5370) =
      mixedMoment B node3706 node3706Labels := by
    have ha : raw2418 = raw2419 := by apply Matrix.ext; unfold raw2418 raw2419; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5370 = raw2419Labels := by decide +kernel
    rw [ha, hj, canonical2419 B hB]
  have hc1 : mixedMoment B raw2418 (Fin.cases (1 : Fin 2) singletonSmall5370) =
      mixedMoment B node3771 node3771Labels := by
    have ha : raw2418 = raw2420 := by apply Matrix.ext; unfold raw2418 raw2420; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5370 = raw2420Labels := by decide +kernel
    rw [ha, hj, canonical2420 B hB]
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

theorem singleton5378 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5378 node5378Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3719 node3719Labels + mixedMoment B node3795 node3795Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2430 singletonSmall5378
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5378) = raw2430Labels := by decide +kernel
  rw [hl, canonical2430 B hB] at h
  have hc0 : mixedMoment B raw2430 (Fin.cases (0 : Fin 2) singletonSmall5378) =
      mixedMoment B node3719 node3719Labels := by
    have ha : raw2430 = raw2431 := by apply Matrix.ext; unfold raw2430 raw2431; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5378 = raw2431Labels := by decide +kernel
    rw [ha, hj, canonical2431 B hB]
  have hc1 : mixedMoment B raw2430 (Fin.cases (1 : Fin 2) singletonSmall5378) =
      mixedMoment B node3795 node3795Labels := by
    have ha : raw2430 = raw2432 := by apply Matrix.ext; unfold raw2430 raw2432; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5378 = raw2432Labels := by decide +kernel
    rw [ha, hj, canonical2432 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton5384 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5384 node5384Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3732 node3732Labels + mixedMoment B node3811 node3811Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2439 singletonSmall5384
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5384) = raw2439Labels := by decide +kernel
  rw [hl, canonical2439 B hB] at h
  have hc0 : mixedMoment B raw2439 (Fin.cases (0 : Fin 2) singletonSmall5384) =
      mixedMoment B node3732 node3732Labels := by
    have ha : raw2439 = raw2440 := by apply Matrix.ext; unfold raw2439 raw2440; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5384 = raw2440Labels := by decide +kernel
    rw [ha, hj, canonical2440 B hB]
  have hc1 : mixedMoment B raw2439 (Fin.cases (1 : Fin 2) singletonSmall5384) =
      mixedMoment B node3811 node3811Labels := by
    have ha : raw2439 = raw2441 := by apply Matrix.ext; unfold raw2439 raw2441; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5384 = raw2441Labels := by decide +kernel
    rw [ha, hj, canonical2441 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton5411 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5411 node5411Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3809 node3809Labels + mixedMoment B node3813 node3813Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2490 singletonSmall5411
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5411) = raw2490Labels := by decide +kernel
  rw [hl, canonical2490 B hB] at h
  have hc0 : mixedMoment B raw2490 (Fin.cases (0 : Fin 2) singletonSmall5411) =
      mixedMoment B node3809 node3809Labels := by
    have ha : raw2490 = raw2491 := by apply Matrix.ext; unfold raw2490 raw2491; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5411 = raw2491Labels := by decide +kernel
    rw [ha, hj, canonical2491 B hB]
  have hc1 : mixedMoment B raw2490 (Fin.cases (1 : Fin 2) singletonSmall5411) =
      mixedMoment B node3813 node3813Labels := by
    have ha : raw2490 = raw2492 := by apply Matrix.ext; unfold raw2490 raw2492; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5411 = raw2492Labels := by decide +kernel
    rw [ha, hj, canonical2492 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton5428 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5428 node5428Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3845 node3845Labels + mixedMoment B node3845 node3845Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2517 singletonSmall5428
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5428) = raw2517Labels := by decide +kernel
  rw [hl, canonical2517 B hB] at h
  have hc0 : mixedMoment B raw2517 (Fin.cases (0 : Fin 2) singletonSmall5428) =
      mixedMoment B node3845 node3845Labels := by
    have ha : raw2517 = raw2518 := by apply Matrix.ext; unfold raw2517 raw2518; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5428 = raw2518Labels := by decide +kernel
    rw [ha, hj, canonical2518 B hB]
  have hc1 : mixedMoment B raw2517 (Fin.cases (1 : Fin 2) singletonSmall5428) =
      mixedMoment B node3845 node3845Labels := by
    have ha : raw2517 = raw2519 := by apply Matrix.ext; unfold raw2517 raw2519; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5428 = raw2519Labels := by decide +kernel
    rw [ha, hj, canonical2519 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound36
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound2341 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2341 node2341Labels = Sparse.eval nodeValue2341 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2341) = mixedMoment B node2341 node2341Labels := rfl
  simpa [nodeValue2341, Sparse.eval] using hc.symm

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

theorem sound2488 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2488 node2488Labels = Sparse.eval nodeValue2488 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2488) = mixedMoment B node2488 node2488Labels := rfl
  simpa [nodeValue2488, Sparse.eval] using hc.symm

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

theorem sound2561 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2561 node2561Labels = Sparse.eval nodeValue2561 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2561) = mixedMoment B node2561 node2561Labels := rfl
  simpa [nodeValue2561, Sparse.eval] using hc.symm

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

theorem sound2817 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2817 node2817Labels = Sparse.eval nodeValue2817 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2817) = mixedMoment B node2817 node2817Labels := rfl
  simpa [nodeValue2817, Sparse.eval] using hc.symm

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

theorem sound3417 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3417 node3417Labels = Sparse.eval nodeValue3417 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3417) = mixedMoment B node3417 node3417Labels := rfl
  simpa [nodeValue3417, Sparse.eval] using hc.symm

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

theorem sound3478 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3478 node3478Labels = Sparse.eval nodeValue3478 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3478) = mixedMoment B node3478 node3478Labels := rfl
  simpa [nodeValue3478, Sparse.eval] using hc.symm

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

theorem sound3522 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3522 node3522Labels = Sparse.eval nodeValue3522 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3522) = mixedMoment B node3522 node3522Labels := rfl
  simpa [nodeValue3522, Sparse.eval] using hc.symm

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

theorem sound3591 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3591 node3591Labels = Sparse.eval nodeValue3591 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3591) = mixedMoment B node3591 node3591Labels := rfl
  simpa [nodeValue3591, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound57
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound3671 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3671 node3671Labels = Sparse.eval nodeValue3671 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3671) = mixedMoment B node3671 node3671Labels := rfl
  simpa [nodeValue3671, Sparse.eval] using hc.symm

theorem sound3689 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3689 node3689Labels = Sparse.eval nodeValue3689 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3689) = mixedMoment B node3689 node3689Labels := rfl
  simpa [nodeValue3689, Sparse.eval] using hc.symm

theorem sound3706 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3706 node3706Labels = Sparse.eval nodeValue3706 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3706) = mixedMoment B node3706 node3706Labels := rfl
  simpa [nodeValue3706, Sparse.eval] using hc.symm

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

theorem sound3719 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3719 node3719Labels = Sparse.eval nodeValue3719 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3719) = mixedMoment B node3719 node3719Labels := rfl
  simpa [nodeValue3719, Sparse.eval] using hc.symm

theorem sound3732 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3732 node3732Labels = Sparse.eval nodeValue3732 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3732) = mixedMoment B node3732 node3732Labels := rfl
  simpa [nodeValue3732, Sparse.eval] using hc.symm

theorem sound3754 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3754 node3754Labels = Sparse.eval nodeValue3754 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3754) = mixedMoment B node3754 node3754Labels := rfl
  simpa [nodeValue3754, Sparse.eval] using hc.symm

theorem sound3757 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3757 node3757Labels = Sparse.eval nodeValue3757 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3757) = mixedMoment B node3757 node3757Labels := rfl
  simpa [nodeValue3757, Sparse.eval] using hc.symm

theorem sound3771 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3771 node3771Labels = Sparse.eval nodeValue3771 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3771) = mixedMoment B node3771 node3771Labels := rfl
  simpa [nodeValue3771, Sparse.eval] using hc.symm

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

theorem sound3795 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3795 node3795Labels = Sparse.eval nodeValue3795 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3795) = mixedMoment B node3795 node3795Labels := rfl
  simpa [nodeValue3795, Sparse.eval] using hc.symm

theorem sound3809 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3809 node3809Labels = Sparse.eval nodeValue3809 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3809) = mixedMoment B node3809 node3809Labels := rfl
  simpa [nodeValue3809, Sparse.eval] using hc.symm

theorem sound3811 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3811 node3811Labels = Sparse.eval nodeValue3811 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3811) = mixedMoment B node3811 node3811Labels := rfl
  simpa [nodeValue3811, Sparse.eval] using hc.symm

theorem sound3813 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3813 node3813Labels = Sparse.eval nodeValue3813 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3813) = mixedMoment B node3813 node3813Labels := rfl
  simpa [nodeValue3813, Sparse.eval] using hc.symm

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

theorem sound3845 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3845 node3845Labels = Sparse.eval nodeValue3845 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3845) = mixedMoment B node3845 node3845Labels := rfl
  simpa [nodeValue3845, Sparse.eval] using hc.symm

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

theorem sound4668 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4668 node4668Labels = Sparse.eval nodeValue4668 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4668) = mixedMoment B node4668 node4668Labels := rfl
  simpa [nodeValue4668, Sparse.eval] using hc.symm

theorem sound4669 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4669 node4669Labels = Sparse.eval nodeValue4669 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4669) = mixedMoment B node4669 node4669Labels := rfl
  simpa [nodeValue4669, Sparse.eval] using hc.symm

theorem sound4670 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4670 node4670Labels = Sparse.eval nodeValue4670 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4670) = mixedMoment B node4670 node4670Labels := rfl
  simpa [nodeValue4670, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound73
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound4690 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4690 node4690Labels = Sparse.eval nodeValue4690 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4690) = mixedMoment B node4690 node4690Labels := rfl
  simpa [nodeValue4690, Sparse.eval] using hc.symm

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

theorem sound4856 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4856 node4856Labels = Sparse.eval nodeValue4856 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4856) = mixedMoment B node4856 node4856Labels := rfl
  simpa [nodeValue4856, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound77
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound4931 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4931 node4931Labels = Sparse.eval nodeValue4931 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4931) = mixedMoment B node4931 node4931Labels := rfl
  simpa [nodeValue4931, Sparse.eval] using hc.symm

theorem sound4934 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4934 node4934Labels = Sparse.eval nodeValue4934 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4934) = mixedMoment B node4934 node4934Labels := rfl
  simpa [nodeValue4934, Sparse.eval] using hc.symm

theorem sound4949 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4949 node4949Labels = Sparse.eval nodeValue4949 (mixedVector B) := by
  have h := singleton4949 B _hB
  rw [sound2341 B _hB _hF, sound3417 B _hB _hF] at h
  norm_num [nodeValue4949, nodeValue2341, nodeValue3417, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4955 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4955 node4955Labels = Sparse.eval nodeValue4955 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4955) = mixedMoment B node4955 node4955Labels := rfl
  simpa [nodeValue4955, Sparse.eval] using hc.symm

theorem sound4957 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4957 node4957Labels = Sparse.eval nodeValue4957 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4957) = mixedMoment B node4957 node4957Labels := rfl
  simpa [nodeValue4957, Sparse.eval] using hc.symm

theorem sound4959 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4959 node4959Labels = Sparse.eval nodeValue4959 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4959) = mixedMoment B node4959 node4959Labels := rfl
  simpa [nodeValue4959, Sparse.eval] using hc.symm

theorem sound4966 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4966 node4966Labels = Sparse.eval nodeValue4966 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4966) = mixedMoment B node4966 node4966Labels := rfl
  simpa [nodeValue4966, Sparse.eval] using hc.symm

theorem sound4973 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4973 node4973Labels = Sparse.eval nodeValue4973 (mixedVector B) := by
  have h := singleton4973 B _hB
  rw [sound2817 B _hB _hF, sound3591 B _hB _hF] at h
  norm_num [nodeValue4973, nodeValue2817, nodeValue3591, Sparse.eval] at h ⊢
  linarith only [h]

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

theorem sound5080 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5080 node5080Labels = Sparse.eval nodeValue5080 (mixedVector B) := by
  have h := singleton5080 B _hB
  rw [sound2488 B _hB _hF, sound3478 B _hB _hF] at h
  norm_num [nodeValue5080, nodeValue2488, nodeValue3478, Sparse.eval] at h ⊢
  linarith only [h]

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

theorem sound5141 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5141 node5141Labels = Sparse.eval nodeValue5141 (mixedVector B) := by
  have h := singleton5141 B _hB
  rw [sound2561 B _hB _hF, sound3522 B _hB _hF] at h
  norm_num [nodeValue5141, nodeValue2561, nodeValue3522, Sparse.eval] at h ⊢
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

theorem sound5188 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5188 node5188Labels = Sparse.eval nodeValue5188 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5188) = mixedMoment B node5188 node5188Labels := rfl
  simpa [nodeValue5188, Sparse.eval] using hc.symm

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

theorem zero5367 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5367 node5367Labels = 0 := by
  exact mixedMoment_order_one B hB node5367 node5367Labels 1
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

theorem sound5336 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5336 node5336Labels = Sparse.eval nodeValue5336 (mixedVector B) := by
  have h := singleton5336 B _hB
  rw [sound3671 B _hB _hF, sound3754 B _hB _hF] at h
  norm_num [nodeValue5336, nodeValue3671, nodeValue3754, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5339 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5339 node5339Labels = Sparse.eval nodeValue5339 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5339) = mixedMoment B node5339 node5339Labels := rfl
  simpa [nodeValue5339, Sparse.eval] using hc.symm

theorem sound5351 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5351 node5351Labels = Sparse.eval nodeValue5351 (mixedVector B) := by
  have h := singleton5351 B _hB
  rw [sound3689 B _hB _hF, sound3757 B _hB _hF] at h
  norm_num [nodeValue5351, nodeValue3689, nodeValue3757, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5353 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5353 node5353Labels = Sparse.eval nodeValue5353 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5353) = mixedMoment B node5353 node5353Labels := rfl
  simpa [nodeValue5353, Sparse.eval] using hc.symm

theorem sound5367 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5367 node5367Labels = Sparse.eval nodeValue5367 (mixedVector B) := by
  simpa only [nodeValue5367, Sparse.eval_nil] using zero5367 B _hB _hF

theorem sound5370 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5370 node5370Labels = Sparse.eval nodeValue5370 (mixedVector B) := by
  have h := singleton5370 B _hB
  rw [sound3706 B _hB _hF, sound3771 B _hB _hF] at h
  norm_num [nodeValue5370, nodeValue3706, nodeValue3771, Sparse.eval] at h ⊢
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

theorem sound5378 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5378 node5378Labels = Sparse.eval nodeValue5378 (mixedVector B) := by
  have h := singleton5378 B _hB
  rw [sound3719 B _hB _hF, sound3795 B _hB _hF] at h
  norm_num [nodeValue5378, nodeValue3719, nodeValue3795, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5379 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5379 node5379Labels = Sparse.eval nodeValue5379 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5379) = mixedMoment B node5379 node5379Labels := rfl
  simpa [nodeValue5379, Sparse.eval] using hc.symm

theorem sound5384 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5384 node5384Labels = Sparse.eval nodeValue5384 (mixedVector B) := by
  have h := singleton5384 B _hB
  rw [sound3732 B _hB _hF, sound3811 B _hB _hF] at h
  norm_num [nodeValue5384, nodeValue3732, nodeValue3811, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5385 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5385 node5385Labels = Sparse.eval nodeValue5385 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5385) = mixedMoment B node5385 node5385Labels := rfl
  simpa [nodeValue5385, Sparse.eval] using hc.symm

theorem sound5409 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5409 node5409Labels = Sparse.eval nodeValue5409 (mixedVector B) := by
  simpa only [nodeValue5409, Sparse.eval_nil] using zero5409 B _hB _hF

theorem sound5411 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5411 node5411Labels = Sparse.eval nodeValue5411 (mixedVector B) := by
  have h := singleton5411 B _hB
  rw [sound3809 B _hB _hF, sound3813 B _hB _hF] at h
  norm_num [nodeValue5411, nodeValue3809, nodeValue3813, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5428 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5428 node5428Labels = Sparse.eval nodeValue5428 (mixedVector B) := by
  have h := singleton5428 B _hB
  rw [sound3845 B _hB _hF] at h
  norm_num [nodeValue5428, nodeValue3845, Sparse.eval] at h ⊢
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

theorem sound5446 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5446 node5446Labels = Sparse.eval nodeValue5446 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5446) = mixedMoment B node5446 node5446Labels := rfl
  simpa [nodeValue5446, Sparse.eval] using hc.symm

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources79
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sourceEq2532 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2532 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2532 + difference 0 1) (sourceB2532 + difference 1 0) sourceC2532) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5141) := by
    have ha : (tripleCharges (sourceA2532 + difference 0 1) (sourceB2532 + difference 1 0) sourceC2532) = raw34941 := by
      apply Matrix.ext; unfold tripleCharges sourceA2532 sourceB2532 sourceC2532 difference raw34941; decide +kernel
    rw [ha]
    exact (canonical34941 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2532 + difference 0 2) (sourceB2532 + difference 2 0) sourceC2532) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5351) := by
    have ha : (tripleCharges (sourceA2532 + difference 0 2) (sourceB2532 + difference 2 0) sourceC2532) = raw34942 := by
      apply Matrix.ext; unfold tripleCharges sourceA2532 sourceB2532 sourceC2532 difference raw34942; decide +kernel
    rw [ha]
    exact (canonical34942 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2532 + difference 0 3) (sourceB2532 + difference 3 0) sourceC2532) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5367) := by
    have ha : (tripleCharges (sourceA2532 + difference 0 3) (sourceB2532 + difference 3 0) sourceC2532) = raw34943 := by
      apply Matrix.ext; unfold tripleCharges sourceA2532 sourceB2532 sourceC2532 difference raw34943; decide +kernel
    rw [ha]
    exact (canonical34943 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2532 + difference 0 4) (sourceB2532 + difference 4 0) sourceC2532) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5428) := by
    have ha : (tripleCharges (sourceA2532 + difference 0 4) (sourceB2532 + difference 4 0) sourceC2532) = raw16442 := by
      apply Matrix.ext; unfold tripleCharges sourceA2532 sourceB2532 sourceC2532 difference raw16442; decide +kernel
    rw [ha]
    exact (canonical16442 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2532 + difference 0 5) (sourceB2532 + difference 5 0) sourceC2532) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5409) := by
    have ha : (tripleCharges (sourceA2532 + difference 0 5) (sourceB2532 + difference 5 0) sourceC2532) = raw34944 := by
      apply Matrix.ext; unfold tripleCharges sourceA2532 sourceB2532 sourceC2532 difference raw34944; decide +kernel
    rw [ha]
    exact (canonical34944 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2532 + difference 1 0) (sourceB2532 + difference 0 1) sourceC2532) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4856) := by
    have ha : (tripleCharges (sourceA2532 + difference 1 0) (sourceB2532 + difference 0 1) sourceC2532) = raw16462 := by
      apply Matrix.ext; unfold tripleCharges sourceA2532 sourceB2532 sourceC2532 difference raw16462; decide +kernel
    rw [ha]
    exact (canonical16462 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2532 + difference 1 2) (sourceB2532 + difference 2 1) sourceC2532) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5353) := by
    have ha : (tripleCharges (sourceA2532 + difference 1 2) (sourceB2532 + difference 2 1) sourceC2532) = raw16464 := by
      apply Matrix.ext; unfold tripleCharges sourceA2532 sourceB2532 sourceC2532 difference raw16464; decide +kernel
    rw [ha]
    exact (canonical16464 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2532 + difference 1 3) (sourceB2532 + difference 3 1) sourceC2532) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5370) := by
    have ha : (tripleCharges (sourceA2532 + difference 1 3) (sourceB2532 + difference 3 1) sourceC2532) = raw16465 := by
      apply Matrix.ext; unfold tripleCharges sourceA2532 sourceB2532 sourceC2532 difference raw16465; decide +kernel
    rw [ha]
    exact (canonical16465 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2532 + difference 1 4) (sourceB2532 + difference 4 1) sourceC2532) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5446) := by
    have ha : (tripleCharges (sourceA2532 + difference 1 4) (sourceB2532 + difference 4 1) sourceC2532) = raw34945 := by
      apply Matrix.ext; unfold tripleCharges sourceA2532 sourceB2532 sourceC2532 difference raw34945; decide +kernel
    rw [ha]
    exact (canonical34945 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2532 + difference 1 5) (sourceB2532 + difference 5 1) sourceC2532) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5411) := by
    have ha : (tripleCharges (sourceA2532 + difference 1 5) (sourceB2532 + difference 5 1) sourceC2532) = raw16466 := by
      apply Matrix.ext; unfold tripleCharges sourceA2532 sourceB2532 sourceC2532 difference raw16466; decide +kernel
    rw [ha]
    exact (canonical16466 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2532 + difference 2 0) (sourceB2532 + difference 0 2) sourceC2532) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4668) := by
    have ha : (tripleCharges (sourceA2532 + difference 2 0) (sourceB2532 + difference 0 2) sourceC2532) = raw34946 := by
      apply Matrix.ext; unfold tripleCharges sourceA2532 sourceB2532 sourceC2532 difference raw34946; decide +kernel
    rw [ha]
    exact (canonical34946 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2532 + difference 2 1) (sourceB2532 + difference 1 2) sourceC2532) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4955) := by
    have ha : (tripleCharges (sourceA2532 + difference 2 1) (sourceB2532 + difference 1 2) sourceC2532) = raw34947 := by
      apply Matrix.ext; unfold tripleCharges sourceA2532 sourceB2532 sourceC2532 difference raw34947; decide +kernel
    rw [ha]
    exact (canonical34947 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2532 + difference 2 3) (sourceB2532 + difference 3 2) sourceC2532) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5336) := by
    have ha : (tripleCharges (sourceA2532 + difference 2 3) (sourceB2532 + difference 3 2) sourceC2532) = raw34948 := by
      apply Matrix.ext; unfold tripleCharges sourceA2532 sourceB2532 sourceC2532 difference raw34948; decide +kernel
    rw [ha]
    exact (canonical34948 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2532 + difference 2 4) (sourceB2532 + difference 4 2) sourceC2532) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5379) := by
    have ha : (tripleCharges (sourceA2532 + difference 2 4) (sourceB2532 + difference 4 2) sourceC2532) = raw16453 := by
      apply Matrix.ext; unfold tripleCharges sourceA2532 sourceB2532 sourceC2532 difference raw16453; decide +kernel
    rw [ha]
    exact (canonical16453 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2532 + difference 2 5) (sourceB2532 + difference 5 2) sourceC2532) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5378) := by
    have ha : (tripleCharges (sourceA2532 + difference 2 5) (sourceB2532 + difference 5 2) sourceC2532) = raw34949 := by
      apply Matrix.ext; unfold tripleCharges sourceA2532 sourceB2532 sourceC2532 difference raw34949; decide +kernel
    rw [ha]
    exact (canonical34949 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2532 + difference 3 0) (sourceB2532 + difference 0 3) sourceC2532) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4690) := by
    have ha : (tripleCharges (sourceA2532 + difference 3 0) (sourceB2532 + difference 0 3) sourceC2532) = raw34950 := by
      apply Matrix.ext; unfold tripleCharges sourceA2532 sourceB2532 sourceC2532 difference raw34950; decide +kernel
    rw [ha]
    exact (canonical34950 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2532 + difference 3 1) (sourceB2532 + difference 1 3) sourceC2532) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4966) := by
    have ha : (tripleCharges (sourceA2532 + difference 3 1) (sourceB2532 + difference 1 3) sourceC2532) = raw34951 := by
      apply Matrix.ext; unfold tripleCharges sourceA2532 sourceB2532 sourceC2532 difference raw34951; decide +kernel
    rw [ha]
    exact (canonical34951 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2532 + difference 3 2) (sourceB2532 + difference 2 3) sourceC2532) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5339) := by
    have ha : (tripleCharges (sourceA2532 + difference 3 2) (sourceB2532 + difference 2 3) sourceC2532) = raw34952 := by
      apply Matrix.ext; unfold tripleCharges sourceA2532 sourceB2532 sourceC2532 difference raw34952; decide +kernel
    rw [ha]
    exact (canonical34952 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2532 + difference 3 4) (sourceB2532 + difference 4 3) sourceC2532) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5385) := by
    have ha : (tripleCharges (sourceA2532 + difference 3 4) (sourceB2532 + difference 4 3) sourceC2532) = raw16458 := by
      apply Matrix.ext; unfold tripleCharges sourceA2532 sourceB2532 sourceC2532 difference raw16458; decide +kernel
    rw [ha]
    exact (canonical16458 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2532 + difference 3 5) (sourceB2532 + difference 5 3) sourceC2532) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5384) := by
    have ha : (tripleCharges (sourceA2532 + difference 3 5) (sourceB2532 + difference 5 3) sourceC2532) = raw34953 := by
      apply Matrix.ext; unfold tripleCharges sourceA2532 sourceB2532 sourceC2532 difference raw34953; decide +kernel
    rw [ha]
    exact (canonical34953 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2532 + difference 4 0) (sourceB2532 + difference 0 4) sourceC2532) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4670) := by
    have ha : (tripleCharges (sourceA2532 + difference 4 0) (sourceB2532 + difference 0 4) sourceC2532) = raw34954 := by
      apply Matrix.ext; unfold tripleCharges sourceA2532 sourceB2532 sourceC2532 difference raw34954; decide +kernel
    rw [ha]
    exact (canonical34954 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2532 + difference 4 1) (sourceB2532 + difference 1 4) sourceC2532) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4934) := by
    have ha : (tripleCharges (sourceA2532 + difference 4 1) (sourceB2532 + difference 1 4) sourceC2532) = raw34955 := by
      apply Matrix.ext; unfold tripleCharges sourceA2532 sourceB2532 sourceC2532 difference raw34955; decide +kernel
    rw [ha]
    exact (canonical34955 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2532 + difference 4 2) (sourceB2532 + difference 2 4) sourceC2532) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4931) := by
    have ha : (tripleCharges (sourceA2532 + difference 4 2) (sourceB2532 + difference 2 4) sourceC2532) = raw34956 := by
      apply Matrix.ext; unfold tripleCharges sourceA2532 sourceB2532 sourceC2532 difference raw34956; decide +kernel
    rw [ha]
    exact (canonical34956 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2532 + difference 4 3) (sourceB2532 + difference 3 4) sourceC2532) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4949) := by
    have ha : (tripleCharges (sourceA2532 + difference 4 3) (sourceB2532 + difference 3 4) sourceC2532) = raw34957 := by
      apply Matrix.ext; unfold tripleCharges sourceA2532 sourceB2532 sourceC2532 difference raw34957; decide +kernel
    rw [ha]
    exact (canonical34957 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2532 + difference 4 5) (sourceB2532 + difference 5 4) sourceC2532) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5080) := by
    have ha : (tripleCharges (sourceA2532 + difference 4 5) (sourceB2532 + difference 5 4) sourceC2532) = raw34958 := by
      apply Matrix.ext; unfold tripleCharges sourceA2532 sourceB2532 sourceC2532 difference raw34958; decide +kernel
    rw [ha]
    exact (canonical34958 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2532 + difference 5 0) (sourceB2532 + difference 0 5) sourceC2532) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4669) := by
    have ha : (tripleCharges (sourceA2532 + difference 5 0) (sourceB2532 + difference 0 5) sourceC2532) = raw34959 := by
      apply Matrix.ext; unfold tripleCharges sourceA2532 sourceB2532 sourceC2532 difference raw34959; decide +kernel
    rw [ha]
    exact (canonical34959 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2532 + difference 5 1) (sourceB2532 + difference 1 5) sourceC2532) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4959) := by
    have ha : (tripleCharges (sourceA2532 + difference 5 1) (sourceB2532 + difference 1 5) sourceC2532) = raw34960 := by
      apply Matrix.ext; unfold tripleCharges sourceA2532 sourceB2532 sourceC2532 difference raw34960; decide +kernel
    rw [ha]
    exact (canonical34960 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2532 + difference 5 2) (sourceB2532 + difference 2 5) sourceC2532) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4957) := by
    have ha : (tripleCharges (sourceA2532 + difference 5 2) (sourceB2532 + difference 2 5) sourceC2532) = raw34961 := by
      apply Matrix.ext; unfold tripleCharges sourceA2532 sourceB2532 sourceC2532 difference raw34961; decide +kernel
    rw [ha]
    exact (canonical34961 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2532 + difference 5 3) (sourceB2532 + difference 3 5) sourceC2532) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4973) := by
    have ha : (tripleCharges (sourceA2532 + difference 5 3) (sourceB2532 + difference 3 5) sourceC2532) = raw34962 := by
      apply Matrix.ext; unfold tripleCharges sourceA2532 sourceB2532 sourceC2532 difference raw34962; decide +kernel
    rw [ha]
    exact (canonical34962 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2532 + difference 5 4) (sourceB2532 + difference 4 5) sourceC2532) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5188) := by
    have ha : (tripleCharges (sourceA2532 + difference 5 4) (sourceB2532 + difference 4 5) sourceC2532) = raw16468 := by
      apply Matrix.ext; unfold tripleCharges sourceA2532 sourceB2532 sourceC2532 difference raw16468; decide +kernel
    rw [ha]
    exact (canonical16468 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2532 sourceB2532 sourceC2532
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2532, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic127
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reindexCheck2039 : Integer.Sparse.reindex keyMap MixedData.row2039 = numericRow2039 := by decide +kernel

theorem numericCheck2039 (x : Master → ℝ) : Integer.Sparse.eval numericRow2039 x =
    (4 : ℝ) * reducedSource2039 x := by
  norm_num [numericRow2039, reducedSource2039, Integer.Sparse.eval, Sparse.eval, nodeValue4668, nodeValue4669, nodeValue4670, nodeValue4690, nodeValue4856, nodeValue4931, nodeValue4934, nodeValue4949, nodeValue4955, nodeValue4957, nodeValue4959, nodeValue4966, nodeValue4973, nodeValue5080, nodeValue5141, nodeValue5188, nodeValue5336, nodeValue5339, nodeValue5351, nodeValue5353, nodeValue5367, nodeValue5370, nodeValue5378, nodeValue5379, nodeValue5384, nodeValue5385, nodeValue5409, nodeValue5411, nodeValue5428, nodeValue5446] <;> ring

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Rows127
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero2039 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource2039 (mixedVector B) = 0 := by
  have h4668 : mixedVector B (Sum.inr 4668) = Sparse.eval nodeValue4668 (mixedVector B) := by
    change mixedMoment B node4668 node4668Labels = _
    exact sound4668 B hB hF
  have h4669 : mixedVector B (Sum.inr 4669) = Sparse.eval nodeValue4669 (mixedVector B) := by
    change mixedMoment B node4669 node4669Labels = _
    exact sound4669 B hB hF
  have h4670 : mixedVector B (Sum.inr 4670) = Sparse.eval nodeValue4670 (mixedVector B) := by
    change mixedMoment B node4670 node4670Labels = _
    exact sound4670 B hB hF
  have h4690 : mixedVector B (Sum.inr 4690) = Sparse.eval nodeValue4690 (mixedVector B) := by
    change mixedMoment B node4690 node4690Labels = _
    exact sound4690 B hB hF
  have h4856 : mixedVector B (Sum.inr 4856) = Sparse.eval nodeValue4856 (mixedVector B) := by
    change mixedMoment B node4856 node4856Labels = _
    exact sound4856 B hB hF
  have h4931 : mixedVector B (Sum.inr 4931) = Sparse.eval nodeValue4931 (mixedVector B) := by
    change mixedMoment B node4931 node4931Labels = _
    exact sound4931 B hB hF
  have h4934 : mixedVector B (Sum.inr 4934) = Sparse.eval nodeValue4934 (mixedVector B) := by
    change mixedMoment B node4934 node4934Labels = _
    exact sound4934 B hB hF
  have h4949 : mixedVector B (Sum.inr 4949) = Sparse.eval nodeValue4949 (mixedVector B) := by
    change mixedMoment B node4949 node4949Labels = _
    exact sound4949 B hB hF
  have h4955 : mixedVector B (Sum.inr 4955) = Sparse.eval nodeValue4955 (mixedVector B) := by
    change mixedMoment B node4955 node4955Labels = _
    exact sound4955 B hB hF
  have h4957 : mixedVector B (Sum.inr 4957) = Sparse.eval nodeValue4957 (mixedVector B) := by
    change mixedMoment B node4957 node4957Labels = _
    exact sound4957 B hB hF
  have h4959 : mixedVector B (Sum.inr 4959) = Sparse.eval nodeValue4959 (mixedVector B) := by
    change mixedMoment B node4959 node4959Labels = _
    exact sound4959 B hB hF
  have h4966 : mixedVector B (Sum.inr 4966) = Sparse.eval nodeValue4966 (mixedVector B) := by
    change mixedMoment B node4966 node4966Labels = _
    exact sound4966 B hB hF
  have h4973 : mixedVector B (Sum.inr 4973) = Sparse.eval nodeValue4973 (mixedVector B) := by
    change mixedMoment B node4973 node4973Labels = _
    exact sound4973 B hB hF
  have h5080 : mixedVector B (Sum.inr 5080) = Sparse.eval nodeValue5080 (mixedVector B) := by
    change mixedMoment B node5080 node5080Labels = _
    exact sound5080 B hB hF
  have h5141 : mixedVector B (Sum.inr 5141) = Sparse.eval nodeValue5141 (mixedVector B) := by
    change mixedMoment B node5141 node5141Labels = _
    exact sound5141 B hB hF
  have h5188 : mixedVector B (Sum.inr 5188) = Sparse.eval nodeValue5188 (mixedVector B) := by
    change mixedMoment B node5188 node5188Labels = _
    exact sound5188 B hB hF
  have h5336 : mixedVector B (Sum.inr 5336) = Sparse.eval nodeValue5336 (mixedVector B) := by
    change mixedMoment B node5336 node5336Labels = _
    exact sound5336 B hB hF
  have h5339 : mixedVector B (Sum.inr 5339) = Sparse.eval nodeValue5339 (mixedVector B) := by
    change mixedMoment B node5339 node5339Labels = _
    exact sound5339 B hB hF
  have h5351 : mixedVector B (Sum.inr 5351) = Sparse.eval nodeValue5351 (mixedVector B) := by
    change mixedMoment B node5351 node5351Labels = _
    exact sound5351 B hB hF
  have h5353 : mixedVector B (Sum.inr 5353) = Sparse.eval nodeValue5353 (mixedVector B) := by
    change mixedMoment B node5353 node5353Labels = _
    exact sound5353 B hB hF
  have h5367 : mixedVector B (Sum.inr 5367) = Sparse.eval nodeValue5367 (mixedVector B) := by
    change mixedMoment B node5367 node5367Labels = _
    exact sound5367 B hB hF
  have h5370 : mixedVector B (Sum.inr 5370) = Sparse.eval nodeValue5370 (mixedVector B) := by
    change mixedMoment B node5370 node5370Labels = _
    exact sound5370 B hB hF
  have h5378 : mixedVector B (Sum.inr 5378) = Sparse.eval nodeValue5378 (mixedVector B) := by
    change mixedMoment B node5378 node5378Labels = _
    exact sound5378 B hB hF
  have h5379 : mixedVector B (Sum.inr 5379) = Sparse.eval nodeValue5379 (mixedVector B) := by
    change mixedMoment B node5379 node5379Labels = _
    exact sound5379 B hB hF
  have h5384 : mixedVector B (Sum.inr 5384) = Sparse.eval nodeValue5384 (mixedVector B) := by
    change mixedMoment B node5384 node5384Labels = _
    exact sound5384 B hB hF
  have h5385 : mixedVector B (Sum.inr 5385) = Sparse.eval nodeValue5385 (mixedVector B) := by
    change mixedMoment B node5385 node5385Labels = _
    exact sound5385 B hB hF
  have h5409 : mixedVector B (Sum.inr 5409) = Sparse.eval nodeValue5409 (mixedVector B) := by
    change mixedMoment B node5409 node5409Labels = _
    exact sound5409 B hB hF
  have h5411 : mixedVector B (Sum.inr 5411) = Sparse.eval nodeValue5411 (mixedVector B) := by
    change mixedMoment B node5411 node5411Labels = _
    exact sound5411 B hB hF
  have h5428 : mixedVector B (Sum.inr 5428) = Sparse.eval nodeValue5428 (mixedVector B) := by
    change mixedMoment B node5428 node5428Labels = _
    exact sound5428 B hB hF
  have h5446 : mixedVector B (Sum.inr 5446) = Sparse.eval nodeValue5446 (mixedVector B) := by
    change mixedMoment B node5446 node5446Labels = _
    exact sound5446 B hB hF
  simpa only [sourceForm2532, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4668, h4669, h4670, h4690, h4856, h4931, h4934, h4949, h4955, h4957, h4959, h4966, h4973, h5080, h5141, h5188, h5336, h5339, h5351, h5353, h5367, h5370, h5378, h5379, h5384, h5385, h5409, h5411, h5428, h5446, reducedSource2039] using sourceEq2532 B hB

theorem rowSound2039_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row2039 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck2039, numericCheck2039, reducedZero2039 B hB hF, mul_zero]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedSourceBridge.rowSound2039_e_oai := @OAI.MUB6.Certificate.MixedSourceBridge.rowSound2039_e_oai
