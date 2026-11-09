-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedSourceBridge.rowSound920_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T02:53:10.015136+00:00
-- url     : https://prove2.me/submissions/1a683456-4afd-4013-bea2-14863cdbc78d

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E086
import Definitions.Def_OAIQ106E092
import Definitions.Def_OAIQ106E093
import Definitions.Def_OAIQ106E188
import Definitions.Def_OAIQ106E190
import Definitions.Def_OAIQ106E100
import Definitions.Def_OAIQ106E194
import Definitions.Def_OAIQ106E195
import Definitions.Def_OAIQ106E119
import Definitions.Def_OAIQ106E123
import Definitions.Def_OAIQ106E128
import Definitions.Def_OAIQ106E140
import Definitions.Def_OAIQ106E147
import Definitions.Def_OAIQ106E170
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound5434_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound5435_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound5483_e

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical131
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical16843 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16843 raw16843Labels = mixedMoment B node5483 node5483Labels := by
  calc
    mixedMoment B raw16843 raw16843Labels = mixedMoment B raw16843step0 raw16843step0Labels := by
      have hz : ∀ j, raw16843 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw16843step0 = (fun i j => raw16843 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw16843step0 raw16843; decide +kernel
      have hl : raw16843step0Labels = raw16843Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16843 raw16843Labels permutation434 hz
    mixedMoment B raw16843step0 raw16843step0Labels = mixedMoment B raw16843step1 raw16843step1Labels := by
      have ha : raw16843step1 = (fun i j => raw16843step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw16843step1 raw16843step0; decide +kernel
      have hl : raw16843step1Labels = raw16843step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16843step0 raw16843step0Labels permutation32 permutation6
    mixedMoment B raw16843step1 raw16843step1Labels = mixedMoment B raw16843step2 raw16843step2Labels := by
      have ha : raw16843step2 = raw16843step1 := by apply Matrix.ext; unfold raw16843step2 raw16843step1; decide +kernel
      have hl : raw16843step1Labels = labelEmbedding9 ∘ raw16843step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16843step1 raw16843step1Labels raw16843step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5483 node5483Labels := by rfl

theorem canonical16862 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16862 raw16862Labels = mixedMoment B node5428 node5428Labels := by
  calc
    mixedMoment B raw16862 raw16862Labels = mixedMoment B raw16862step0 raw16862step0Labels := by
      have hz : ∀ j, raw16862 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw16862step0 = (fun i j => raw16862 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw16862step0 raw16862; decide +kernel
      have hl : raw16862step0Labels = raw16862Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16862 raw16862Labels permutation434 hz
    mixedMoment B raw16862step0 raw16862step0Labels = mixedMoment B raw16862step1 raw16862step1Labels := by
      have ha : raw16862step1 = (fun i j => raw16862step0 (permutation144 i) (permutation4 j)) := by apply Matrix.ext; unfold raw16862step1 raw16862step0; decide +kernel
      have hl : raw16862step1Labels = raw16862step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16862step0 raw16862step0Labels permutation144 permutation4
    mixedMoment B raw16862step1 raw16862step1Labels = mixedMoment B raw16862step2 raw16862step2Labels := by
      have ha : raw16862step2 = raw16862step1 := by apply Matrix.ext; unfold raw16862step2 raw16862step1; decide +kernel
      have hl : raw16862step1Labels = labelEmbedding7 ∘ raw16862step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16862step1 raw16862step1Labels raw16862step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5428 node5428Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical133
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical17126 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17126 raw17126Labels = mixedMoment B node5442 node5442Labels := by
  calc
    mixedMoment B raw17126 raw17126Labels = mixedMoment B raw17126step0 raw17126step0Labels := by
      have hz : ∀ j, raw17126 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw17126step0 = (fun i j => raw17126 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw17126step0 raw17126; decide +kernel
      have hl : raw17126step0Labels = raw17126Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17126 raw17126Labels permutation434 hz
    mixedMoment B raw17126step0 raw17126step0Labels = mixedMoment B raw17126step1 raw17126step1Labels := by
      have hz : ∀ j, raw17126step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw17126step1 = (fun i j => raw17126step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw17126step1 raw17126step0; decide +kernel
      have hl : raw17126step1Labels = raw17126step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17126step0 raw17126step0Labels permutation80 hz
    mixedMoment B raw17126step1 raw17126step1Labels = mixedMoment B raw17126step2 raw17126step2Labels := by
      have ha : raw17126step2 = (fun i j => raw17126step1 (permutation31 i) (permutation6 j)) := by apply Matrix.ext; unfold raw17126step2 raw17126step1; decide +kernel
      have hl : raw17126step2Labels = raw17126step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17126step1 raw17126step1Labels permutation31 permutation6
    mixedMoment B raw17126step2 raw17126step2Labels = mixedMoment B raw17126step3 raw17126step3Labels := by
      have ha : raw17126step3 = -raw17126step2 := by apply Matrix.ext; change ∀ i j, raw17126step3 i j = -(raw17126step2 i j); unfold raw17126step3 raw17126step2; decide +kernel
      have hl : raw17126step3Labels = raw17126step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw17126step3 raw17126step3Labels = mixedMoment B raw17126step4 raw17126step4Labels := by
      have ha : raw17126step4 = raw17126step3 := by apply Matrix.ext; unfold raw17126step4 raw17126step3; decide +kernel
      have hl : raw17126step3Labels = labelEmbedding9 ∘ raw17126step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17126step3 raw17126step3Labels raw17126step4Labels labelEmbedding9 hl
    _ = mixedMoment B node5442 node5442Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical135
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical17376 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17376 raw17376Labels = mixedMoment B node5425 node5425Labels := by
  calc
    mixedMoment B raw17376 raw17376Labels = mixedMoment B raw17376step0 raw17376step0Labels := by
      have ha : raw17376step0 = (fun i j => raw17376 (permutation152 i) (permutation7 j)) := by apply Matrix.ext; unfold raw17376step0 raw17376; decide +kernel
      have hl : raw17376step0Labels = raw17376Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17376 raw17376Labels permutation152 permutation7
    mixedMoment B raw17376step0 raw17376step0Labels = mixedMoment B raw17376step1 raw17376step1Labels := by
      have ha : raw17376step1 = raw17376step0 := by apply Matrix.ext; unfold raw17376step1 raw17376step0; decide +kernel
      have hl : raw17376step0Labels = labelEmbedding10 ∘ raw17376step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17376step0 raw17376step0Labels raw17376step1Labels labelEmbedding10 hl
    _ = mixedMoment B node5425 node5425Labels := by rfl

theorem canonical17380 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17380 raw17380Labels = mixedMoment B node5430 node5430Labels := by
  calc
    mixedMoment B raw17380 raw17380Labels = mixedMoment B raw17380step0 raw17380step0Labels := by
      have ha : raw17380step0 = (fun i j => raw17380 (permutation634 i) (permutation4 j)) := by apply Matrix.ext; unfold raw17380step0 raw17380; decide +kernel
      have hl : raw17380step0Labels = raw17380Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17380 raw17380Labels permutation634 permutation4
    mixedMoment B raw17380step0 raw17380step0Labels = mixedMoment B raw17380step1 raw17380step1Labels := by
      have ha : raw17380step1 = raw17380step0 := by apply Matrix.ext; unfold raw17380step1 raw17380step0; decide +kernel
      have hl : raw17380step0Labels = labelEmbedding7 ∘ raw17380step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17380step0 raw17380step0Labels raw17380step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5430 node5430Labels := by rfl

theorem canonical17384 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17384 raw17384Labels = mixedMoment B node5382 node5382Labels := by
  calc
    mixedMoment B raw17384 raw17384Labels = mixedMoment B raw17384step0 raw17384step0Labels := by
      have ha : raw17384step0 = (fun i j => raw17384 (permutation646 i) (permutation4 j)) := by apply Matrix.ext; unfold raw17384step0 raw17384; decide +kernel
      have hl : raw17384step0Labels = raw17384Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17384 raw17384Labels permutation646 permutation4
    mixedMoment B raw17384step0 raw17384step0Labels = mixedMoment B raw17384step1 raw17384step1Labels := by
      have ha : raw17384step1 = raw17384step0 := by apply Matrix.ext; unfold raw17384step1 raw17384step0; decide +kernel
      have hl : raw17384step0Labels = labelEmbedding7 ∘ raw17384step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17384step0 raw17384step0Labels raw17384step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5382 node5382Labels := by rfl

theorem canonical17388 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17388 raw17388Labels = mixedMoment B node5409 node5409Labels := by
  calc
    mixedMoment B raw17388 raw17388Labels = mixedMoment B raw17388step0 raw17388step0Labels := by
      have hz : ∀ j, raw17388 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw17388step0 = (fun i j => raw17388 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw17388step0 raw17388; decide +kernel
      have hl : raw17388step0Labels = raw17388Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17388 raw17388Labels permutation434 hz
    mixedMoment B raw17388step0 raw17388step0Labels = mixedMoment B raw17388step1 raw17388step1Labels := by
      have ha : raw17388step1 = (fun i j => raw17388step0 (permutation34 i) (permutation4 j)) := by apply Matrix.ext; unfold raw17388step1 raw17388step0; decide +kernel
      have hl : raw17388step1Labels = raw17388step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17388step0 raw17388step0Labels permutation34 permutation4
    mixedMoment B raw17388step1 raw17388step1Labels = mixedMoment B raw17388step2 raw17388step2Labels := by
      have ha : raw17388step2 = -raw17388step1 := by apply Matrix.ext; change ∀ i j, raw17388step2 i j = -(raw17388step1 i j); unfold raw17388step2 raw17388step1; decide +kernel
      have hl : raw17388step2Labels = raw17388step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw17388step2 raw17388step2Labels = mixedMoment B raw17388step3 raw17388step3Labels := by
      have ha : raw17388step3 = raw17388step2 := by apply Matrix.ext; unfold raw17388step3 raw17388step2; decide +kernel
      have hl : raw17388step2Labels = labelEmbedding7 ∘ raw17388step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17388step2 raw17388step2Labels raw17388step3Labels labelEmbedding7 hl
    _ = mixedMoment B node5409 node5409Labels := by rfl

theorem canonical17393 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17393 raw17393Labels = mixedMoment B node5160 node5160Labels := by
  calc
    mixedMoment B raw17393 raw17393Labels = mixedMoment B raw17393step0 raw17393step0Labels := by
      have ha : raw17393step0 = (fun i j => raw17393 (permutation646 i) (permutation4 j)) := by apply Matrix.ext; unfold raw17393step0 raw17393; decide +kernel
      have hl : raw17393step0Labels = raw17393Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17393 raw17393Labels permutation646 permutation4
    mixedMoment B raw17393step0 raw17393step0Labels = mixedMoment B raw17393step1 raw17393step1Labels := by
      have ha : raw17393step1 = raw17393step0 := by apply Matrix.ext; unfold raw17393step1 raw17393step0; decide +kernel
      have hl : raw17393step0Labels = labelEmbedding7 ∘ raw17393step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17393step0 raw17393step0Labels raw17393step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5160 node5160Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical136
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical17472 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17472 raw17472Labels = mixedMoment B node5424 node5424Labels := by
  calc
    mixedMoment B raw17472 raw17472Labels = mixedMoment B raw17472step0 raw17472step0Labels := by
      have ha : raw17472step0 = (fun i j => raw17472 (permutation152 i) (permutation7 j)) := by apply Matrix.ext; unfold raw17472step0 raw17472; decide +kernel
      have hl : raw17472step0Labels = raw17472Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17472 raw17472Labels permutation152 permutation7
    mixedMoment B raw17472step0 raw17472step0Labels = mixedMoment B raw17472step1 raw17472step1Labels := by
      have ha : raw17472step1 = raw17472step0 := by apply Matrix.ext; unfold raw17472step1 raw17472step0; decide +kernel
      have hl : raw17472step0Labels = labelEmbedding10 ∘ raw17472step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17472step0 raw17472step0Labels raw17472step1Labels labelEmbedding10 hl
    _ = mixedMoment B node5424 node5424Labels := by rfl

theorem canonical17477 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17477 raw17477Labels = mixedMoment B node5477 node5477Labels := by
  calc
    mixedMoment B raw17477 raw17477Labels = mixedMoment B raw17477step0 raw17477step0Labels := by
      have ha : raw17477step0 = (fun i j => raw17477 (permutation152 i) (permutation7 j)) := by apply Matrix.ext; unfold raw17477step0 raw17477; decide +kernel
      have hl : raw17477step0Labels = raw17477Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17477 raw17477Labels permutation152 permutation7
    mixedMoment B raw17477step0 raw17477step0Labels = mixedMoment B raw17477step1 raw17477step1Labels := by
      have ha : raw17477step1 = raw17477step0 := by apply Matrix.ext; unfold raw17477step1 raw17477step0; decide +kernel
      have hl : raw17477step0Labels = labelEmbedding10 ∘ raw17477step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17477step0 raw17477step0Labels raw17477step1Labels labelEmbedding10 hl
    _ = mixedMoment B node5477 node5477Labels := by rfl

theorem canonical17482 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17482 raw17482Labels = mixedMoment B node5445 node5445Labels := by
  calc
    mixedMoment B raw17482 raw17482Labels = mixedMoment B raw17482step0 raw17482step0Labels := by
      have ha : raw17482step0 = (fun i j => raw17482 (permutation351 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17482step0 raw17482; decide +kernel
      have hl : raw17482step0Labels = raw17482Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17482 raw17482Labels permutation351 permutation3
    mixedMoment B raw17482step0 raw17482step0Labels = mixedMoment B raw17482step1 raw17482step1Labels := by
      have ha : raw17482step1 = -raw17482step0 := by apply Matrix.ext; change ∀ i j, raw17482step1 i j = -(raw17482step0 i j); unfold raw17482step1 raw17482step0; decide +kernel
      have hl : raw17482step1Labels = raw17482step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw17482step1 raw17482step1Labels = mixedMoment B raw17482step2 raw17482step2Labels := by
      have ha : raw17482step2 = raw17482step1 := by apply Matrix.ext; unfold raw17482step2 raw17482step1; decide +kernel
      have hl : raw17482step1Labels = labelEmbedding6 ∘ raw17482step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17482step1 raw17482step1Labels raw17482step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5445 node5445Labels := by rfl

theorem canonical17490 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17490 raw17490Labels = mixedMoment B node5394 node5394Labels := by
  calc
    mixedMoment B raw17490 raw17490Labels = mixedMoment B raw17490step0 raw17490step0Labels := by
      have ha : raw17490step0 = (fun i j => raw17490 (permutation682 i) (permutation4 j)) := by apply Matrix.ext; unfold raw17490step0 raw17490; decide +kernel
      have hl : raw17490step0Labels = raw17490Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17490 raw17490Labels permutation682 permutation4
    mixedMoment B raw17490step0 raw17490step0Labels = mixedMoment B raw17490step1 raw17490step1Labels := by
      have ha : raw17490step1 = raw17490step0 := by apply Matrix.ext; unfold raw17490step1 raw17490step0; decide +kernel
      have hl : raw17490step0Labels = labelEmbedding7 ∘ raw17490step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17490step0 raw17490step0Labels raw17490step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5394 node5394Labels := by rfl

theorem canonical17491 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17491 raw17491Labels = mixedMoment B node5395 node5395Labels := by
  calc
    mixedMoment B raw17491 raw17491Labels = mixedMoment B raw17491step0 raw17491step0Labels := by
      have ha : raw17491step0 = (fun i j => raw17491 (permutation681 i) (permutation4 j)) := by apply Matrix.ext; unfold raw17491step0 raw17491; decide +kernel
      have hl : raw17491step0Labels = raw17491Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17491 raw17491Labels permutation681 permutation4
    mixedMoment B raw17491step0 raw17491step0Labels = mixedMoment B raw17491step1 raw17491step1Labels := by
      have ha : raw17491step1 = raw17491step0 := by apply Matrix.ext; unfold raw17491step1 raw17491step0; decide +kernel
      have hl : raw17491step0Labels = labelEmbedding7 ∘ raw17491step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17491step0 raw17491step0Labels raw17491step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5395 node5395Labels := by rfl

theorem canonical17492 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17492 raw17492Labels = mixedMoment B node5410 node5410Labels := by
  calc
    mixedMoment B raw17492 raw17492Labels = mixedMoment B raw17492step0 raw17492step0Labels := by
      have hz : ∀ j, raw17492 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw17492step0 = (fun i j => raw17492 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw17492step0 raw17492; decide +kernel
      have hl : raw17492step0Labels = raw17492Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17492 raw17492Labels permutation346 hz
    mixedMoment B raw17492step0 raw17492step0Labels = mixedMoment B raw17492step1 raw17492step1Labels := by
      have ha : raw17492step1 = (fun i j => raw17492step0 (permutation151 i) (permutation6 j)) := by apply Matrix.ext; unfold raw17492step1 raw17492step0; decide +kernel
      have hl : raw17492step1Labels = raw17492step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17492step0 raw17492step0Labels permutation151 permutation6
    mixedMoment B raw17492step1 raw17492step1Labels = mixedMoment B raw17492step2 raw17492step2Labels := by
      have ha : raw17492step2 = -raw17492step1 := by apply Matrix.ext; change ∀ i j, raw17492step2 i j = -(raw17492step1 i j); unfold raw17492step2 raw17492step1; decide +kernel
      have hl : raw17492step2Labels = raw17492step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw17492step2 raw17492step2Labels = mixedMoment B raw17492step3 raw17492step3Labels := by
      have ha : raw17492step3 = raw17492step2 := by apply Matrix.ext; unfold raw17492step3 raw17492step2; decide +kernel
      have hl : raw17492step2Labels = labelEmbedding9 ∘ raw17492step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17492step2 raw17492step2Labels raw17492step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5410 node5410Labels := by rfl

theorem canonical17493 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17493 raw17493Labels = mixedMoment B node5397 node5397Labels := by
  calc
    mixedMoment B raw17493 raw17493Labels = mixedMoment B raw17493step0 raw17493step0Labels := by
      have ha : raw17493step0 = (fun i j => raw17493 (permutation679 i) (permutation4 j)) := by apply Matrix.ext; unfold raw17493step0 raw17493; decide +kernel
      have hl : raw17493step0Labels = raw17493Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17493 raw17493Labels permutation679 permutation4
    mixedMoment B raw17493step0 raw17493step0Labels = mixedMoment B raw17493step1 raw17493step1Labels := by
      have ha : raw17493step1 = raw17493step0 := by apply Matrix.ext; unfold raw17493step1 raw17493step0; decide +kernel
      have hl : raw17493step0Labels = labelEmbedding7 ∘ raw17493step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17493step0 raw17493step0Labels raw17493step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5397 node5397Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical137
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical17633 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17633 raw17633Labels = mixedMoment B node5425 node5425Labels := by
  calc
    mixedMoment B raw17633 raw17633Labels = mixedMoment B raw17633step0 raw17633step0Labels := by
      have ha : raw17633step0 = (fun i j => raw17633 (permutation682 i) (permutation6 j)) := by apply Matrix.ext; unfold raw17633step0 raw17633; decide +kernel
      have hl : raw17633step0Labels = raw17633Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17633 raw17633Labels permutation682 permutation6
    mixedMoment B raw17633step0 raw17633step0Labels = mixedMoment B raw17633step1 raw17633step1Labels := by
      have ha : raw17633step1 = -raw17633step0 := by apply Matrix.ext; change ∀ i j, raw17633step1 i j = -(raw17633step0 i j); unfold raw17633step1 raw17633step0; decide +kernel
      have hl : raw17633step1Labels = raw17633step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw17633step1 raw17633step1Labels = mixedMoment B raw17633step2 raw17633step2Labels := by
      have ha : raw17633step2 = raw17633step1 := by apply Matrix.ext; unfold raw17633step2 raw17633step1; decide +kernel
      have hl : raw17633step1Labels = labelEmbedding9 ∘ raw17633step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17633step1 raw17633step1Labels raw17633step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5425 node5425Labels := by rfl

theorem canonical17634 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17634 raw17634Labels = mixedMoment B node5435 node5435Labels := by
  calc
    mixedMoment B raw17634 raw17634Labels = mixedMoment B raw17634step0 raw17634step0Labels := by
      have hz : ∀ j, raw17634 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw17634step0 = (fun i j => raw17634 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw17634step0 raw17634; decide +kernel
      have hl : raw17634step0Labels = raw17634Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17634 raw17634Labels permutation346 hz
    mixedMoment B raw17634step0 raw17634step0Labels = mixedMoment B raw17634step1 raw17634step1Labels := by
      have ha : raw17634step1 = (fun i j => raw17634step0 (permutation151 i) (permutation6 j)) := by apply Matrix.ext; unfold raw17634step1 raw17634step0; decide +kernel
      have hl : raw17634step1Labels = raw17634step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17634step0 raw17634step0Labels permutation151 permutation6
    mixedMoment B raw17634step1 raw17634step1Labels = mixedMoment B raw17634step2 raw17634step2Labels := by
      have ha : raw17634step2 = -raw17634step1 := by apply Matrix.ext; change ∀ i j, raw17634step2 i j = -(raw17634step1 i j); unfold raw17634step2 raw17634step1; decide +kernel
      have hl : raw17634step2Labels = raw17634step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw17634step2 raw17634step2Labels = mixedMoment B raw17634step3 raw17634step3Labels := by
      have ha : raw17634step3 = raw17634step2 := by apply Matrix.ext; unfold raw17634step3 raw17634step2; decide +kernel
      have hl : raw17634step2Labels = labelEmbedding9 ∘ raw17634step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17634step2 raw17634step2Labels raw17634step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5435 node5435Labels := by rfl

theorem canonical17635 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17635 raw17635Labels = mixedMoment B node5426 node5426Labels := by
  calc
    mixedMoment B raw17635 raw17635Labels = mixedMoment B raw17635step0 raw17635step0Labels := by
      have ha : raw17635step0 = (fun i j => raw17635 (permutation181 i) (permutation2 j)) := by apply Matrix.ext; unfold raw17635step0 raw17635; decide +kernel
      have hl : raw17635step0Labels = raw17635Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17635 raw17635Labels permutation181 permutation2
    mixedMoment B raw17635step0 raw17635step0Labels = mixedMoment B raw17635step1 raw17635step1Labels := by
      have ha : raw17635step1 = -raw17635step0 := by apply Matrix.ext; change ∀ i j, raw17635step1 i j = -(raw17635step0 i j); unfold raw17635step1 raw17635step0; decide +kernel
      have hl : raw17635step1Labels = raw17635step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5426 node5426Labels := by rfl

theorem canonical17636 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17636 raw17636Labels = mixedMoment B node5423 node5423Labels := by
  calc
    mixedMoment B raw17636 raw17636Labels = mixedMoment B raw17636step0 raw17636step0Labels := by
      have ha : raw17636step0 = (fun i j => raw17636 (permutation644 i) (permutation4 j)) := by apply Matrix.ext; unfold raw17636step0 raw17636; decide +kernel
      have hl : raw17636step0Labels = raw17636Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17636 raw17636Labels permutation644 permutation4
    mixedMoment B raw17636step0 raw17636step0Labels = mixedMoment B raw17636step1 raw17636step1Labels := by
      have ha : raw17636step1 = raw17636step0 := by apply Matrix.ext; unfold raw17636step1 raw17636step0; decide +kernel
      have hl : raw17636step0Labels = labelEmbedding7 ∘ raw17636step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17636step0 raw17636step0Labels raw17636step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5423 node5423Labels := by rfl

theorem canonical17637 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17637 raw17637Labels = mixedMoment B node5434 node5434Labels := by
  calc
    mixedMoment B raw17637 raw17637Labels = mixedMoment B raw17637step0 raw17637step0Labels := by
      have hz : ∀ j, raw17637 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw17637step0 = (fun i j => raw17637 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw17637step0 raw17637; decide +kernel
      have hl : raw17637step0Labels = raw17637Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17637 raw17637Labels permutation346 hz
    mixedMoment B raw17637step0 raw17637step0Labels = mixedMoment B raw17637step1 raw17637step1Labels := by
      have ha : raw17637step1 = (fun i j => raw17637step0 (permutation151 i) (permutation6 j)) := by apply Matrix.ext; unfold raw17637step1 raw17637step0; decide +kernel
      have hl : raw17637step1Labels = raw17637step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17637step0 raw17637step0Labels permutation151 permutation6
    mixedMoment B raw17637step1 raw17637step1Labels = mixedMoment B raw17637step2 raw17637step2Labels := by
      have ha : raw17637step2 = -raw17637step1 := by apply Matrix.ext; change ∀ i j, raw17637step2 i j = -(raw17637step1 i j); unfold raw17637step2 raw17637step1; decide +kernel
      have hl : raw17637step2Labels = raw17637step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw17637step2 raw17637step2Labels = mixedMoment B raw17637step3 raw17637step3Labels := by
      have ha : raw17637step3 = raw17637step2 := by apply Matrix.ext; unfold raw17637step3 raw17637step2; decide +kernel
      have hl : raw17637step2Labels = labelEmbedding9 ∘ raw17637step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17637step2 raw17637step2Labels raw17637step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5434 node5434Labels := by rfl

theorem canonical17638 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17638 raw17638Labels = mixedMoment B node5425 node5425Labels := by
  calc
    mixedMoment B raw17638 raw17638Labels = mixedMoment B raw17638step0 raw17638step0Labels := by
      have ha : raw17638step0 = (fun i j => raw17638 (permutation643 i) (permutation4 j)) := by apply Matrix.ext; unfold raw17638step0 raw17638; decide +kernel
      have hl : raw17638step0Labels = raw17638Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17638 raw17638Labels permutation643 permutation4
    mixedMoment B raw17638step0 raw17638step0Labels = mixedMoment B raw17638step1 raw17638step1Labels := by
      have ha : raw17638step1 = raw17638step0 := by apply Matrix.ext; unfold raw17638step1 raw17638step0; decide +kernel
      have hl : raw17638step0Labels = labelEmbedding7 ∘ raw17638step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17638step0 raw17638step0Labels raw17638step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5425 node5425Labels := by rfl

theorem canonical17639 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17639 raw17639Labels = mixedMoment B node5378 node5378Labels := by
  calc
    mixedMoment B raw17639 raw17639Labels = mixedMoment B raw17639step0 raw17639step0Labels := by
      have ha : raw17639step0 = (fun i j => raw17639 (permutation646 i) (permutation4 j)) := by apply Matrix.ext; unfold raw17639step0 raw17639; decide +kernel
      have hl : raw17639step0Labels = raw17639Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17639 raw17639Labels permutation646 permutation4
    mixedMoment B raw17639step0 raw17639step0Labels = mixedMoment B raw17639step1 raw17639step1Labels := by
      have ha : raw17639step1 = raw17639step0 := by apply Matrix.ext; unfold raw17639step1 raw17639step0; decide +kernel
      have hl : raw17639step0Labels = labelEmbedding7 ∘ raw17639step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17639step0 raw17639step0Labels raw17639step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5378 node5378Labels := by rfl

theorem canonical17640 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17640 raw17640Labels = mixedMoment B node5379 node5379Labels := by
  calc
    mixedMoment B raw17640 raw17640Labels = mixedMoment B raw17640step0 raw17640step0Labels := by
      have ha : raw17640step0 = (fun i j => raw17640 (permutation645 i) (permutation4 j)) := by apply Matrix.ext; unfold raw17640step0 raw17640; decide +kernel
      have hl : raw17640step0Labels = raw17640Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17640 raw17640Labels permutation645 permutation4
    mixedMoment B raw17640step0 raw17640step0Labels = mixedMoment B raw17640step1 raw17640step1Labels := by
      have ha : raw17640step1 = raw17640step0 := by apply Matrix.ext; unfold raw17640step1 raw17640step0; decide +kernel
      have hl : raw17640step0Labels = labelEmbedding7 ∘ raw17640step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17640step0 raw17640step0Labels raw17640step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5379 node5379Labels := by rfl

theorem canonical17641 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17641 raw17641Labels = mixedMoment B node5381 node5381Labels := by
  calc
    mixedMoment B raw17641 raw17641Labels = mixedMoment B raw17641step0 raw17641step0Labels := by
      have ha : raw17641step0 = (fun i j => raw17641 (permutation643 i) (permutation4 j)) := by apply Matrix.ext; unfold raw17641step0 raw17641; decide +kernel
      have hl : raw17641step0Labels = raw17641Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17641 raw17641Labels permutation643 permutation4
    mixedMoment B raw17641step0 raw17641step0Labels = mixedMoment B raw17641step1 raw17641step1Labels := by
      have ha : raw17641step1 = raw17641step0 := by apply Matrix.ext; unfold raw17641step1 raw17641step0; decide +kernel
      have hl : raw17641step0Labels = labelEmbedding7 ∘ raw17641step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17641step0 raw17641step0Labels raw17641step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5381 node5381Labels := by rfl

theorem canonical17642 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17642 raw17642Labels = mixedMoment B node5438 node5438Labels := by
  calc
    mixedMoment B raw17642 raw17642Labels = mixedMoment B raw17642step0 raw17642step0Labels := by
      have hz : ∀ j, raw17642 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw17642step0 = (fun i j => raw17642 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw17642step0 raw17642; decide +kernel
      have hl : raw17642step0Labels = raw17642Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17642 raw17642Labels permutation434 hz
    mixedMoment B raw17642step0 raw17642step0Labels = mixedMoment B raw17642step1 raw17642step1Labels := by
      have ha : raw17642step1 = (fun i j => raw17642step0 (permutation145 i) (permutation4 j)) := by apply Matrix.ext; unfold raw17642step1 raw17642step0; decide +kernel
      have hl : raw17642step1Labels = raw17642step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17642step0 raw17642step0Labels permutation145 permutation4
    mixedMoment B raw17642step1 raw17642step1Labels = mixedMoment B raw17642step2 raw17642step2Labels := by
      have ha : raw17642step2 = raw17642step1 := by apply Matrix.ext; unfold raw17642step2 raw17642step1; decide +kernel
      have hl : raw17642step1Labels = labelEmbedding7 ∘ raw17642step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17642step1 raw17642step1Labels raw17642step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5438 node5438Labels := by rfl

theorem canonical17643 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17643 raw17643Labels = mixedMoment B node5477 node5477Labels := by
  calc
    mixedMoment B raw17643 raw17643Labels = mixedMoment B raw17643step0 raw17643step0Labels := by
      have ha : raw17643step0 = (fun i j => raw17643 (permutation158 i) (permutation6 j)) := by apply Matrix.ext; unfold raw17643step0 raw17643; decide +kernel
      have hl : raw17643step0Labels = raw17643Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17643 raw17643Labels permutation158 permutation6
    mixedMoment B raw17643step0 raw17643step0Labels = mixedMoment B raw17643step1 raw17643step1Labels := by
      have ha : raw17643step1 = raw17643step0 := by apply Matrix.ext; unfold raw17643step1 raw17643step0; decide +kernel
      have hl : raw17643step0Labels = labelEmbedding9 ∘ raw17643step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17643step0 raw17643step0Labels raw17643step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5477 node5477Labels := by rfl

theorem canonical17644 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17644 raw17644Labels = mixedMoment B node5134 node5134Labels := by
  calc
    mixedMoment B raw17644 raw17644Labels = mixedMoment B raw17644step0 raw17644step0Labels := by
      have ha : raw17644step0 = (fun i j => raw17644 (permutation646 i) (permutation4 j)) := by apply Matrix.ext; unfold raw17644step0 raw17644; decide +kernel
      have hl : raw17644step0Labels = raw17644Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17644 raw17644Labels permutation646 permutation4
    mixedMoment B raw17644step0 raw17644step0Labels = mixedMoment B raw17644step1 raw17644step1Labels := by
      have ha : raw17644step1 = raw17644step0 := by apply Matrix.ext; unfold raw17644step1 raw17644step0; decide +kernel
      have hl : raw17644step0Labels = labelEmbedding7 ∘ raw17644step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17644step0 raw17644step0Labels raw17644step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5134 node5134Labels := by rfl

theorem canonical17645 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17645 raw17645Labels = mixedMoment B node5135 node5135Labels := by
  calc
    mixedMoment B raw17645 raw17645Labels = mixedMoment B raw17645step0 raw17645step0Labels := by
      have ha : raw17645step0 = (fun i j => raw17645 (permutation645 i) (permutation4 j)) := by apply Matrix.ext; unfold raw17645step0 raw17645; decide +kernel
      have hl : raw17645step0Labels = raw17645Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17645 raw17645Labels permutation645 permutation4
    mixedMoment B raw17645step0 raw17645step0Labels = mixedMoment B raw17645step1 raw17645step1Labels := by
      have ha : raw17645step1 = raw17645step0 := by apply Matrix.ext; unfold raw17645step1 raw17645step0; decide +kernel
      have hl : raw17645step0Labels = labelEmbedding7 ∘ raw17645step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17645step0 raw17645step0Labels raw17645step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5135 node5135Labels := by rfl

theorem canonical17646 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17646 raw17646Labels = mixedMoment B node5271 node5271Labels := by
  calc
    mixedMoment B raw17646 raw17646Labels = mixedMoment B raw17646step0 raw17646step0Labels := by
      have hz : ∀ j, raw17646 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw17646step0 = (fun i j => raw17646 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw17646step0 raw17646; decide +kernel
      have hl : raw17646step0Labels = raw17646Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17646 raw17646Labels permutation346 hz
    mixedMoment B raw17646step0 raw17646step0Labels = mixedMoment B raw17646step1 raw17646step1Labels := by
      have ha : raw17646step1 = (fun i j => raw17646step0 (permutation151 i) (permutation4 j)) := by apply Matrix.ext; unfold raw17646step1 raw17646step0; decide +kernel
      have hl : raw17646step1Labels = raw17646step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17646step0 raw17646step0Labels permutation151 permutation4
    mixedMoment B raw17646step1 raw17646step1Labels = mixedMoment B raw17646step2 raw17646step2Labels := by
      have ha : raw17646step2 = raw17646step1 := by apply Matrix.ext; unfold raw17646step2 raw17646step1; decide +kernel
      have hl : raw17646step1Labels = labelEmbedding7 ∘ raw17646step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17646step1 raw17646step1Labels raw17646step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5271 node5271Labels := by rfl

theorem canonical17647 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17647 raw17647Labels = mixedMoment B node5138 node5138Labels := by
  calc
    mixedMoment B raw17647 raw17647Labels = mixedMoment B raw17647step0 raw17647step0Labels := by
      have ha : raw17647step0 = (fun i j => raw17647 (permutation643 i) (permutation4 j)) := by apply Matrix.ext; unfold raw17647step0 raw17647; decide +kernel
      have hl : raw17647step0Labels = raw17647Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17647 raw17647Labels permutation643 permutation4
    mixedMoment B raw17647step0 raw17647step0Labels = mixedMoment B raw17647step1 raw17647step1Labels := by
      have ha : raw17647step1 = raw17647step0 := by apply Matrix.ext; unfold raw17647step1 raw17647step0; decide +kernel
      have hl : raw17647step0Labels = labelEmbedding7 ∘ raw17647step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17647step0 raw17647step0Labels raw17647step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5138 node5138Labels := by rfl

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

theorem canonical2463 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2463 raw2463Labels = mixedMoment B node5395 node5395Labels := by
  calc
    mixedMoment B raw2463 raw2463Labels = mixedMoment B raw2463step0 raw2463step0Labels := by
      have ha : raw2463step0 = (fun i j => raw2463 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2463step0 raw2463; decide +kernel
      have hl : raw2463step0Labels = raw2463Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2463 raw2463Labels permutation152 permutation4
    mixedMoment B raw2463step0 raw2463step0Labels = mixedMoment B raw2463step1 raw2463step1Labels := by
      have ha : raw2463step1 = raw2463step0 := by apply Matrix.ext; unfold raw2463step1 raw2463step0; decide +kernel
      have hl : raw2463step0Labels = labelEmbedding7 ∘ raw2463step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2463step0 raw2463step0Labels raw2463step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5395 node5395Labels := by rfl

theorem canonical2464 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2464 raw2464Labels = mixedMoment B node3781 node3781Labels := by
  calc
    mixedMoment B raw2464 raw2464Labels = mixedMoment B raw2464step0 raw2464step0Labels := by
      have ha : raw2464step0 = (fun i j => raw2464 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2464step0 raw2464; decide +kernel
      have hl : raw2464step0Labels = raw2464Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2464 raw2464Labels permutation152 permutation4
    _ = mixedMoment B node3781 node3781Labels := by rfl

theorem canonical2465 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2465 raw2465Labels = mixedMoment B node3794 node3794Labels := by
  calc
    mixedMoment B raw2465 raw2465Labels = mixedMoment B raw2465step0 raw2465step0Labels := by
      have ha : raw2465step0 = (fun i j => raw2465 (permutation153 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2465step0 raw2465; decide +kernel
      have hl : raw2465step0Labels = raw2465Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2465 raw2465Labels permutation153 permutation6
    mixedMoment B raw2465step0 raw2465step0Labels = mixedMoment B raw2465step1 raw2465step1Labels := by
      have ha : raw2465step1 = -raw2465step0 := by apply Matrix.ext; change ∀ i j, raw2465step1 i j = -(raw2465step0 i j); unfold raw2465step1 raw2465step0; decide +kernel
      have hl : raw2465step1Labels = raw2465step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2465step1 raw2465step1Labels = mixedMoment B raw2465step2 raw2465step2Labels := by
      have ha : raw2465step2 = raw2465step1 := by apply Matrix.ext; unfold raw2465step2 raw2465step1; decide +kernel
      have hl : raw2465step1Labels = labelEmbedding1 ∘ raw2465step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2465step1 raw2465step1Labels raw2465step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3794 node3794Labels := by rfl

theorem canonical2466 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2466 raw2466Labels = mixedMoment B node5397 node5397Labels := by
  calc
    mixedMoment B raw2466 raw2466Labels = mixedMoment B raw2466step0 raw2466step0Labels := by
      have ha : raw2466step0 = (fun i j => raw2466 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2466step0 raw2466; decide +kernel
      have hl : raw2466step0Labels = raw2466Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2466 raw2466Labels permutation152 permutation4
    mixedMoment B raw2466step0 raw2466step0Labels = mixedMoment B raw2466step1 raw2466step1Labels := by
      have ha : raw2466step1 = raw2466step0 := by apply Matrix.ext; unfold raw2466step1 raw2466step0; decide +kernel
      have hl : raw2466step0Labels = labelEmbedding7 ∘ raw2466step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2466step0 raw2466step0Labels raw2466step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5397 node5397Labels := by rfl

theorem canonical2467 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2467 raw2467Labels = mixedMoment B node3782 node3782Labels := by
  calc
    mixedMoment B raw2467 raw2467Labels = mixedMoment B raw2467step0 raw2467step0Labels := by
      have ha : raw2467step0 = (fun i j => raw2467 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2467step0 raw2467; decide +kernel
      have hl : raw2467step0Labels = raw2467Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2467 raw2467Labels permutation152 permutation4
    _ = mixedMoment B node3782 node3782Labels := by rfl

theorem canonical2468 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2468 raw2468Labels = mixedMoment B node3796 node3796Labels := by
  calc
    mixedMoment B raw2468 raw2468Labels = mixedMoment B raw2468step0 raw2468step0Labels := by
      have ha : raw2468step0 = (fun i j => raw2468 (permutation156 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2468step0 raw2468; decide +kernel
      have hl : raw2468step0Labels = raw2468Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2468 raw2468Labels permutation156 permutation6
    mixedMoment B raw2468step0 raw2468step0Labels = mixedMoment B raw2468step1 raw2468step1Labels := by
      have ha : raw2468step1 = -raw2468step0 := by apply Matrix.ext; change ∀ i j, raw2468step1 i j = -(raw2468step0 i j); unfold raw2468step1 raw2468step0; decide +kernel
      have hl : raw2468step1Labels = raw2468step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2468step1 raw2468step1Labels = mixedMoment B raw2468step2 raw2468step2Labels := by
      have ha : raw2468step2 = raw2468step1 := by apply Matrix.ext; unfold raw2468step2 raw2468step1; decide +kernel
      have hl : raw2468step1Labels = labelEmbedding1 ∘ raw2468step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2468step1 raw2468step1Labels raw2468step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3796 node3796Labels := by rfl

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

theorem canonical2514 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2514 raw2514Labels = mixedMoment B node5424 node5424Labels := by
  calc
    mixedMoment B raw2514 raw2514Labels = mixedMoment B raw2514step0 raw2514step0Labels := by
      have ha : raw2514step0 = (fun i j => raw2514 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2514step0 raw2514; decide +kernel
      have hl : raw2514step0Labels = raw2514Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2514 raw2514Labels permutation152 permutation4
    mixedMoment B raw2514step0 raw2514step0Labels = mixedMoment B raw2514step1 raw2514step1Labels := by
      have ha : raw2514step1 = raw2514step0 := by apply Matrix.ext; unfold raw2514step1 raw2514step0; decide +kernel
      have hl : raw2514step0Labels = labelEmbedding7 ∘ raw2514step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2514step0 raw2514step0Labels raw2514step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5424 node5424Labels := by rfl

theorem canonical2515 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2515 raw2515Labels = mixedMoment B node3838 node3838Labels := by
  calc
    mixedMoment B raw2515 raw2515Labels = mixedMoment B raw2515step0 raw2515step0Labels := by
      have ha : raw2515step0 = (fun i j => raw2515 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2515step0 raw2515; decide +kernel
      have hl : raw2515step0Labels = raw2515Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2515 raw2515Labels permutation152 permutation4
    _ = mixedMoment B node3838 node3838Labels := by rfl

theorem canonical2516 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2516 raw2516Labels = mixedMoment B node3843 node3843Labels := by
  calc
    mixedMoment B raw2516 raw2516Labels = mixedMoment B raw2516step0 raw2516step0Labels := by
      have ha : raw2516step0 = (fun i j => raw2516 (permutation176 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2516step0 raw2516; decide +kernel
      have hl : raw2516step0Labels = raw2516Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2516 raw2516Labels permutation176 permutation6
    mixedMoment B raw2516step0 raw2516step0Labels = mixedMoment B raw2516step1 raw2516step1Labels := by
      have ha : raw2516step1 = -raw2516step0 := by apply Matrix.ext; change ∀ i j, raw2516step1 i j = -(raw2516step0 i j); unfold raw2516step1 raw2516step0; decide +kernel
      have hl : raw2516step1Labels = raw2516step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2516step1 raw2516step1Labels = mixedMoment B raw2516step2 raw2516step2Labels := by
      have ha : raw2516step2 = raw2516step1 := by apply Matrix.ext; unfold raw2516step2 raw2516step1; decide +kernel
      have hl : raw2516step1Labels = labelEmbedding1 ∘ raw2516step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2516step1 raw2516step1Labels raw2516step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3843 node3843Labels := by rfl

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

theorem canonical2538 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2538 raw2538Labels = mixedMoment B node5438 node5438Labels := by
  calc
    mixedMoment B raw2538 raw2538Labels = mixedMoment B raw2538step0 raw2538step0Labels := by
      have ha : raw2538step0 = (fun i j => raw2538 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2538step0 raw2538; decide +kernel
      have hl : raw2538step0Labels = raw2538Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2538 raw2538Labels permutation32 permutation4
    mixedMoment B raw2538step0 raw2538step0Labels = mixedMoment B raw2538step1 raw2538step1Labels := by
      have ha : raw2538step1 = raw2538step0 := by apply Matrix.ext; unfold raw2538step1 raw2538step0; decide +kernel
      have hl : raw2538step0Labels = labelEmbedding7 ∘ raw2538step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2538step0 raw2538step0Labels raw2538step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5438 node5438Labels := by rfl

theorem canonical2539 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2539 raw2539Labels = mixedMoment B node3857 node3857Labels := by
  calc
    mixedMoment B raw2539 raw2539Labels = mixedMoment B raw2539step0 raw2539step0Labels := by
      have ha : raw2539step0 = (fun i j => raw2539 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2539step0 raw2539; decide +kernel
      have hl : raw2539step0Labels = raw2539Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2539 raw2539Labels permutation32 permutation4
    _ = mixedMoment B node3857 node3857Labels := by rfl

theorem canonical2540 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2540 raw2540Labels = mixedMoment B node3876 node3876Labels := by
  calc
    mixedMoment B raw2540 raw2540Labels = mixedMoment B raw2540step0 raw2540step0Labels := by
      have ha : raw2540step0 = (fun i j => raw2540 (permutation38 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2540step0 raw2540; decide +kernel
      have hl : raw2540step0Labels = raw2540Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2540 raw2540Labels permutation38 permutation6
    mixedMoment B raw2540step0 raw2540step0Labels = mixedMoment B raw2540step1 raw2540step1Labels := by
      have ha : raw2540step1 = -raw2540step0 := by apply Matrix.ext; change ∀ i j, raw2540step1 i j = -(raw2540step0 i j); unfold raw2540step1 raw2540step0; decide +kernel
      have hl : raw2540step1Labels = raw2540step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2540step1 raw2540step1Labels = mixedMoment B raw2540step2 raw2540step2Labels := by
      have ha : raw2540step2 = raw2540step1 := by apply Matrix.ext; unfold raw2540step2 raw2540step1; decide +kernel
      have hl : raw2540step1Labels = labelEmbedding1 ∘ raw2540step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2540step1 raw2540step1Labels raw2540step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3876 node3876Labels := by rfl

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

theorem singleton5395 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5395 node5395Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3781 node3781Labels + mixedMoment B node3794 node3794Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2463 singletonSmall5395
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5395) = raw2463Labels := by decide +kernel
  rw [hl, canonical2463 B hB] at h
  have hc0 : mixedMoment B raw2463 (Fin.cases (0 : Fin 2) singletonSmall5395) =
      mixedMoment B node3781 node3781Labels := by
    have ha : raw2463 = raw2464 := by apply Matrix.ext; unfold raw2463 raw2464; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5395 = raw2464Labels := by decide +kernel
    rw [ha, hj, canonical2464 B hB]
  have hc1 : mixedMoment B raw2463 (Fin.cases (1 : Fin 2) singletonSmall5395) =
      mixedMoment B node3794 node3794Labels := by
    have ha : raw2463 = raw2465 := by apply Matrix.ext; unfold raw2463 raw2465; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5395 = raw2465Labels := by decide +kernel
    rw [ha, hj, canonical2465 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton5397 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5397 node5397Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3782 node3782Labels + mixedMoment B node3796 node3796Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2466 singletonSmall5397
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5397) = raw2466Labels := by decide +kernel
  rw [hl, canonical2466 B hB] at h
  have hc0 : mixedMoment B raw2466 (Fin.cases (0 : Fin 2) singletonSmall5397) =
      mixedMoment B node3782 node3782Labels := by
    have ha : raw2466 = raw2467 := by apply Matrix.ext; unfold raw2466 raw2467; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5397 = raw2467Labels := by decide +kernel
    rw [ha, hj, canonical2467 B hB]
  have hc1 : mixedMoment B raw2466 (Fin.cases (1 : Fin 2) singletonSmall5397) =
      mixedMoment B node3796 node3796Labels := by
    have ha : raw2466 = raw2468 := by apply Matrix.ext; unfold raw2466 raw2468; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5397 = raw2468Labels := by decide +kernel
    rw [ha, hj, canonical2468 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

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

theorem singleton5424 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5424 node5424Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3838 node3838Labels + mixedMoment B node3843 node3843Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2514 singletonSmall5424
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5424) = raw2514Labels := by decide +kernel
  rw [hl, canonical2514 B hB] at h
  have hc0 : mixedMoment B raw2514 (Fin.cases (0 : Fin 2) singletonSmall5424) =
      mixedMoment B node3838 node3838Labels := by
    have ha : raw2514 = raw2515 := by apply Matrix.ext; unfold raw2514 raw2515; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5424 = raw2515Labels := by decide +kernel
    rw [ha, hj, canonical2515 B hB]
  have hc1 : mixedMoment B raw2514 (Fin.cases (1 : Fin 2) singletonSmall5424) =
      mixedMoment B node3843 node3843Labels := by
    have ha : raw2514 = raw2516 := by apply Matrix.ext; unfold raw2514 raw2516; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5424 = raw2516Labels := by decide +kernel
    rw [ha, hj, canonical2516 B hB]
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

theorem singleton5438 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5438 node5438Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3857 node3857Labels + mixedMoment B node3876 node3876Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2538 singletonSmall5438
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5438) = raw2538Labels := by decide +kernel
  rw [hl, canonical2538 B hB] at h
  have hc0 : mixedMoment B raw2538 (Fin.cases (0 : Fin 2) singletonSmall5438) =
      mixedMoment B node3857 node3857Labels := by
    have ha : raw2538 = raw2539 := by apply Matrix.ext; unfold raw2538 raw2539; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5438 = raw2539Labels := by decide +kernel
    rw [ha, hj, canonical2539 B hB]
  have hc1 : mixedMoment B raw2538 (Fin.cases (1 : Fin 2) singletonSmall5438) =
      mixedMoment B node3876 node3876Labels := by
    have ha : raw2538 = raw2540 := by apply Matrix.ext; unfold raw2538 raw2540; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5438 = raw2540Labels := by decide +kernel
    rw [ha, hj, canonical2540 B hB]
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

theorem zero5442 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5442 node5442Labels = 0 := by
  exact mixedMoment_order_one B hB node5442 node5442Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero5477 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node5477 node5477Labels = 0 := by
  exact mixedMoment_alpha B hF node5477 node5477Labels 2 permutation152
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

theorem sound2553 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2553 node2553Labels = Sparse.eval nodeValue2553 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2553) = mixedMoment B node2553 node2553Labels := rfl
  simpa [nodeValue2553, Sparse.eval] using hc.symm

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

theorem sound2739 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2739 node2739Labels = Sparse.eval nodeValue2739 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2739) = mixedMoment B node2739 node2739Labels := rfl
  simpa [nodeValue2739, Sparse.eval] using hc.symm

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

theorem sound3534 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3534 node3534Labels = Sparse.eval nodeValue3534 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3534) = mixedMoment B node3534 node3534Labels := rfl
  simpa [nodeValue3534, Sparse.eval] using hc.symm

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

theorem sound3781 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3781 node3781Labels = Sparse.eval nodeValue3781 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3781) = mixedMoment B node3781 node3781Labels := rfl
  simpa [nodeValue3781, Sparse.eval] using hc.symm

theorem sound3782 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3782 node3782Labels = Sparse.eval nodeValue3782 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3782) = mixedMoment B node3782 node3782Labels := rfl
  simpa [nodeValue3782, Sparse.eval] using hc.symm

theorem sound3794 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3794 node3794Labels = Sparse.eval nodeValue3794 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3794) = mixedMoment B node3794 node3794Labels := rfl
  simpa [nodeValue3794, Sparse.eval] using hc.symm

theorem sound3795 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3795 node3795Labels = Sparse.eval nodeValue3795 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3795) = mixedMoment B node3795 node3795Labels := rfl
  simpa [nodeValue3795, Sparse.eval] using hc.symm

theorem sound3796 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3796 node3796Labels = Sparse.eval nodeValue3796 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3796) = mixedMoment B node3796 node3796Labels := rfl
  simpa [nodeValue3796, Sparse.eval] using hc.symm

theorem sound3837 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3837 node3837Labels = Sparse.eval nodeValue3837 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3837) = mixedMoment B node3837 node3837Labels := rfl
  simpa [nodeValue3837, Sparse.eval] using hc.symm

theorem sound3838 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3838 node3838Labels = Sparse.eval nodeValue3838 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3838) = mixedMoment B node3838 node3838Labels := rfl
  simpa [nodeValue3838, Sparse.eval] using hc.symm

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

theorem sound3845 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3845 node3845Labels = Sparse.eval nodeValue3845 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3845) = mixedMoment B node3845 node3845Labels := rfl
  simpa [nodeValue3845, Sparse.eval] using hc.symm

theorem sound3857 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3857 node3857Labels = Sparse.eval nodeValue3857 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3857) = mixedMoment B node3857 node3857Labels := rfl
  simpa [nodeValue3857, Sparse.eval] using hc.symm

theorem sound3876 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3876 node3876Labels = Sparse.eval nodeValue3876 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3876) = mixedMoment B node3876 node3876Labels := rfl
  simpa [nodeValue3876, Sparse.eval] using hc.symm

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

theorem zero5135 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node5135 node5135Labels = 0 := by
  exact mixedMoment_alpha B hF node5135 node5135Labels 1 permutation160
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

theorem sound5134 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5134 node5134Labels = Sparse.eval nodeValue5134 (mixedVector B) := by
  have h := singleton5134 B _hB
  rw [sound2553 B _hB _hF, sound3514 B _hB _hF] at h
  norm_num [nodeValue5134, nodeValue2553, nodeValue3514, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5135 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5135 node5135Labels = Sparse.eval nodeValue5135 (mixedVector B) := by
  simpa only [nodeValue5135, Sparse.eval_nil] using zero5135 B _hB _hF

theorem sound5138 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5138 node5138Labels = Sparse.eval nodeValue5138 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5138) = mixedMoment B node5138 node5138Labels := rfl
  simpa [nodeValue5138, Sparse.eval] using hc.symm

theorem sound5160 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5160 node5160Labels = Sparse.eval nodeValue5160 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5160) = mixedMoment B node5160 node5160Labels := rfl
  simpa [nodeValue5160, Sparse.eval] using hc.symm

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

theorem sound5271 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5271 node5271Labels = Sparse.eval nodeValue5271 (mixedVector B) := by
  have h := singleton5271 B _hB
  rw [sound2739 B _hB _hF, sound3534 B _hB _hF] at h
  norm_num [nodeValue5271, nodeValue2739, nodeValue3534, Sparse.eval] at h ⊢
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

theorem zero5394 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5394 node5394Labels = 0 := by
  exact mixedMoment_order_one B hB node5394 node5394Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero5409 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5409 node5409Labels = 0 := by
  exact mixedMoment_order_one B hB node5409 node5409Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero5410 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5410 node5410Labels = 0 := by
  exact mixedMoment_order_one B hB node5410 node5410Labels 1
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

theorem sound5381 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5381 node5381Labels = Sparse.eval nodeValue5381 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5381) = mixedMoment B node5381 node5381Labels := rfl
  simpa [nodeValue5381, Sparse.eval] using hc.symm

theorem sound5382 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5382 node5382Labels = Sparse.eval nodeValue5382 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5382) = mixedMoment B node5382 node5382Labels := rfl
  simpa [nodeValue5382, Sparse.eval] using hc.symm

theorem sound5394 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5394 node5394Labels = Sparse.eval nodeValue5394 (mixedVector B) := by
  simpa only [nodeValue5394, Sparse.eval_nil] using zero5394 B _hB _hF

theorem sound5395 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5395 node5395Labels = Sparse.eval nodeValue5395 (mixedVector B) := by
  have h := singleton5395 B _hB
  rw [sound3781 B _hB _hF, sound3794 B _hB _hF] at h
  norm_num [nodeValue5395, nodeValue3781, nodeValue3794, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5397 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5397 node5397Labels = Sparse.eval nodeValue5397 (mixedVector B) := by
  have h := singleton5397 B _hB
  rw [sound3782 B _hB _hF, sound3796 B _hB _hF] at h
  norm_num [nodeValue5397, nodeValue3782, nodeValue3796, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5409 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5409 node5409Labels = Sparse.eval nodeValue5409 (mixedVector B) := by
  simpa only [nodeValue5409, Sparse.eval_nil] using zero5409 B _hB _hF

theorem sound5410 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5410 node5410Labels = Sparse.eval nodeValue5410 (mixedVector B) := by
  simpa only [nodeValue5410, Sparse.eval_nil] using zero5410 B _hB _hF

theorem sound5423 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5423 node5423Labels = Sparse.eval nodeValue5423 (mixedVector B) := by
  have h := singleton5423 B _hB
  rw [sound3837 B _hB _hF] at h
  norm_num [nodeValue5423, nodeValue3837, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5424 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5424 node5424Labels = Sparse.eval nodeValue5424 (mixedVector B) := by
  have h := singleton5424 B _hB
  rw [sound3838 B _hB _hF, sound3843 B _hB _hF] at h
  norm_num [nodeValue5424, nodeValue3838, nodeValue3843, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5425 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5425 node5425Labels = Sparse.eval nodeValue5425 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5425) = mixedMoment B node5425 node5425Labels := rfl
  simpa [nodeValue5425, Sparse.eval] using hc.symm

theorem sound5426 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5426 node5426Labels = Sparse.eval nodeValue5426 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5426) = mixedMoment B node5426 node5426Labels := rfl
  simpa [nodeValue5426, Sparse.eval] using hc.symm

theorem sound5428 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5428 node5428Labels = Sparse.eval nodeValue5428 (mixedVector B) := by
  have h := singleton5428 B _hB
  rw [sound3845 B _hB _hF] at h
  norm_num [nodeValue5428, nodeValue3845, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5430 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5430 node5430Labels = Sparse.eval nodeValue5430 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5430) = mixedMoment B node5430 node5430Labels := rfl
  simpa [nodeValue5430, Sparse.eval] using hc.symm

theorem sound5438 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5438 node5438Labels = Sparse.eval nodeValue5438 (mixedVector B) := by
  have h := singleton5438 B _hB
  rw [sound3857 B _hB _hF, sound3876 B _hB _hF] at h
  norm_num [nodeValue5438, nodeValue3857, nodeValue3876, Sparse.eval] at h ⊢
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

theorem sound5442 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5442 node5442Labels = Sparse.eval nodeValue5442 (mixedVector B) := by
  simpa only [nodeValue5442, Sparse.eval_nil] using zero5442 B _hB _hF

theorem sound5445 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5445 node5445Labels = Sparse.eval nodeValue5445 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5445) = mixedMoment B node5445 node5445Labels := rfl
  simpa [nodeValue5445, Sparse.eval] using hc.symm

theorem sound5477 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5477 node5477Labels = Sparse.eval nodeValue5477 (mixedVector B) := by
  simpa only [nodeValue5477, Sparse.eval_nil] using zero5477 B _hB _hF

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources33
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sourceEq1067 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1067 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1067 + difference 0 1) (sourceB1067 + difference 1 0) sourceC1067) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5425) := by
    have ha : (tripleCharges (sourceA1067 + difference 0 1) (sourceB1067 + difference 1 0) sourceC1067) = raw17633 := by
      apply Matrix.ext; unfold tripleCharges sourceA1067 sourceB1067 sourceC1067 difference raw17633; decide +kernel
    rw [ha]
    exact (canonical17633 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1067 + difference 0 2) (sourceB1067 + difference 2 0) sourceC1067) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5435) := by
    have ha : (tripleCharges (sourceA1067 + difference 0 2) (sourceB1067 + difference 2 0) sourceC1067) = raw17634 := by
      apply Matrix.ext; unfold tripleCharges sourceA1067 sourceB1067 sourceC1067 difference raw17634; decide +kernel
    rw [ha]
    exact (canonical17634 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1067 + difference 0 3) (sourceB1067 + difference 3 0) sourceC1067) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5426) := by
    have ha : (tripleCharges (sourceA1067 + difference 0 3) (sourceB1067 + difference 3 0) sourceC1067) = raw17635 := by
      apply Matrix.ext; unfold tripleCharges sourceA1067 sourceB1067 sourceC1067 difference raw17635; decide +kernel
    rw [ha]
    exact (canonical17635 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1067 + difference 0 4) (sourceB1067 + difference 4 0) sourceC1067) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5425) := by
    have ha : (tripleCharges (sourceA1067 + difference 0 4) (sourceB1067 + difference 4 0) sourceC1067) = raw17376 := by
      apply Matrix.ext; unfold tripleCharges sourceA1067 sourceB1067 sourceC1067 difference raw17376; decide +kernel
    rw [ha]
    exact (canonical17376 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1067 + difference 0 5) (sourceB1067 + difference 5 0) sourceC1067) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5424) := by
    have ha : (tripleCharges (sourceA1067 + difference 0 5) (sourceB1067 + difference 5 0) sourceC1067) = raw17472 := by
      apply Matrix.ext; unfold tripleCharges sourceA1067 sourceB1067 sourceC1067 difference raw17472; decide +kernel
    rw [ha]
    exact (canonical17472 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1067 + difference 1 0) (sourceB1067 + difference 0 1) sourceC1067) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5423) := by
    have ha : (tripleCharges (sourceA1067 + difference 1 0) (sourceB1067 + difference 0 1) sourceC1067) = raw17636 := by
      apply Matrix.ext; unfold tripleCharges sourceA1067 sourceB1067 sourceC1067 difference raw17636; decide +kernel
    rw [ha]
    exact (canonical17636 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1067 + difference 1 2) (sourceB1067 + difference 2 1) sourceC1067) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5434) := by
    have ha : (tripleCharges (sourceA1067 + difference 1 2) (sourceB1067 + difference 2 1) sourceC1067) = raw17637 := by
      apply Matrix.ext; unfold tripleCharges sourceA1067 sourceB1067 sourceC1067 difference raw17637; decide +kernel
    rw [ha]
    exact (canonical17637 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1067 + difference 1 3) (sourceB1067 + difference 3 1) sourceC1067) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5425) := by
    have ha : (tripleCharges (sourceA1067 + difference 1 3) (sourceB1067 + difference 3 1) sourceC1067) = raw17638 := by
      apply Matrix.ext; unfold tripleCharges sourceA1067 sourceB1067 sourceC1067 difference raw17638; decide +kernel
    rw [ha]
    exact (canonical17638 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1067 + difference 1 4) (sourceB1067 + difference 4 1) sourceC1067) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5430) := by
    have ha : (tripleCharges (sourceA1067 + difference 1 4) (sourceB1067 + difference 4 1) sourceC1067) = raw17380 := by
      apply Matrix.ext; unfold tripleCharges sourceA1067 sourceB1067 sourceC1067 difference raw17380; decide +kernel
    rw [ha]
    exact (canonical17380 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1067 + difference 1 5) (sourceB1067 + difference 5 1) sourceC1067) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5477) := by
    have ha : (tripleCharges (sourceA1067 + difference 1 5) (sourceB1067 + difference 5 1) sourceC1067) = raw17477 := by
      apply Matrix.ext; unfold tripleCharges sourceA1067 sourceB1067 sourceC1067 difference raw17477; decide +kernel
    rw [ha]
    exact (canonical17477 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1067 + difference 2 0) (sourceB1067 + difference 0 2) sourceC1067) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5378) := by
    have ha : (tripleCharges (sourceA1067 + difference 2 0) (sourceB1067 + difference 0 2) sourceC1067) = raw17639 := by
      apply Matrix.ext; unfold tripleCharges sourceA1067 sourceB1067 sourceC1067 difference raw17639; decide +kernel
    rw [ha]
    exact (canonical17639 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1067 + difference 2 1) (sourceB1067 + difference 1 2) sourceC1067) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5379) := by
    have ha : (tripleCharges (sourceA1067 + difference 2 1) (sourceB1067 + difference 1 2) sourceC1067) = raw17640 := by
      apply Matrix.ext; unfold tripleCharges sourceA1067 sourceB1067 sourceC1067 difference raw17640; decide +kernel
    rw [ha]
    exact (canonical17640 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1067 + difference 2 3) (sourceB1067 + difference 3 2) sourceC1067) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5381) := by
    have ha : (tripleCharges (sourceA1067 + difference 2 3) (sourceB1067 + difference 3 2) sourceC1067) = raw17641 := by
      apply Matrix.ext; unfold tripleCharges sourceA1067 sourceB1067 sourceC1067 difference raw17641; decide +kernel
    rw [ha]
    exact (canonical17641 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1067 + difference 2 4) (sourceB1067 + difference 4 2) sourceC1067) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5382) := by
    have ha : (tripleCharges (sourceA1067 + difference 2 4) (sourceB1067 + difference 4 2) sourceC1067) = raw17384 := by
      apply Matrix.ext; unfold tripleCharges sourceA1067 sourceB1067 sourceC1067 difference raw17384; decide +kernel
    rw [ha]
    exact (canonical17384 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1067 + difference 2 5) (sourceB1067 + difference 5 2) sourceC1067) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5445) := by
    have ha : (tripleCharges (sourceA1067 + difference 2 5) (sourceB1067 + difference 5 2) sourceC1067) = raw17482 := by
      apply Matrix.ext; unfold tripleCharges sourceA1067 sourceB1067 sourceC1067 difference raw17482; decide +kernel
    rw [ha]
    exact (canonical17482 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1067 + difference 3 0) (sourceB1067 + difference 0 3) sourceC1067) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5409) := by
    have ha : (tripleCharges (sourceA1067 + difference 3 0) (sourceB1067 + difference 0 3) sourceC1067) = raw17388 := by
      apply Matrix.ext; unfold tripleCharges sourceA1067 sourceB1067 sourceC1067 difference raw17388; decide +kernel
    rw [ha]
    exact (canonical17388 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1067 + difference 3 1) (sourceB1067 + difference 1 3) sourceC1067) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5428) := by
    have ha : (tripleCharges (sourceA1067 + difference 3 1) (sourceB1067 + difference 1 3) sourceC1067) = raw16862 := by
      apply Matrix.ext; unfold tripleCharges sourceA1067 sourceB1067 sourceC1067 difference raw16862; decide +kernel
    rw [ha]
    exact (canonical16862 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1067 + difference 3 2) (sourceB1067 + difference 2 3) sourceC1067) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5442) := by
    have ha : (tripleCharges (sourceA1067 + difference 3 2) (sourceB1067 + difference 2 3) sourceC1067) = raw17126 := by
      apply Matrix.ext; unfold tripleCharges sourceA1067 sourceB1067 sourceC1067 difference raw17126; decide +kernel
    rw [ha]
    exact (canonical17126 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1067 + difference 3 4) (sourceB1067 + difference 4 3) sourceC1067) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5438) := by
    have ha : (tripleCharges (sourceA1067 + difference 3 4) (sourceB1067 + difference 4 3) sourceC1067) = raw17642 := by
      apply Matrix.ext; unfold tripleCharges sourceA1067 sourceB1067 sourceC1067 difference raw17642; decide +kernel
    rw [ha]
    exact (canonical17642 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1067 + difference 3 5) (sourceB1067 + difference 5 3) sourceC1067) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5483) := by
    have ha : (tripleCharges (sourceA1067 + difference 3 5) (sourceB1067 + difference 5 3) sourceC1067) = raw16843 := by
      apply Matrix.ext; unfold tripleCharges sourceA1067 sourceB1067 sourceC1067 difference raw16843; decide +kernel
    rw [ha]
    exact (canonical16843 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1067 + difference 4 0) (sourceB1067 + difference 0 4) sourceC1067) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5394) := by
    have ha : (tripleCharges (sourceA1067 + difference 4 0) (sourceB1067 + difference 0 4) sourceC1067) = raw17490 := by
      apply Matrix.ext; unfold tripleCharges sourceA1067 sourceB1067 sourceC1067 difference raw17490; decide +kernel
    rw [ha]
    exact (canonical17490 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1067 + difference 4 1) (sourceB1067 + difference 1 4) sourceC1067) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5395) := by
    have ha : (tripleCharges (sourceA1067 + difference 4 1) (sourceB1067 + difference 1 4) sourceC1067) = raw17491 := by
      apply Matrix.ext; unfold tripleCharges sourceA1067 sourceB1067 sourceC1067 difference raw17491; decide +kernel
    rw [ha]
    exact (canonical17491 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1067 + difference 4 2) (sourceB1067 + difference 2 4) sourceC1067) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5410) := by
    have ha : (tripleCharges (sourceA1067 + difference 4 2) (sourceB1067 + difference 2 4) sourceC1067) = raw17492 := by
      apply Matrix.ext; unfold tripleCharges sourceA1067 sourceB1067 sourceC1067 difference raw17492; decide +kernel
    rw [ha]
    exact (canonical17492 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1067 + difference 4 3) (sourceB1067 + difference 3 4) sourceC1067) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5397) := by
    have ha : (tripleCharges (sourceA1067 + difference 4 3) (sourceB1067 + difference 3 4) sourceC1067) = raw17493 := by
      apply Matrix.ext; unfold tripleCharges sourceA1067 sourceB1067 sourceC1067 difference raw17493; decide +kernel
    rw [ha]
    exact (canonical17493 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1067 + difference 4 5) (sourceB1067 + difference 5 4) sourceC1067) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5477) := by
    have ha : (tripleCharges (sourceA1067 + difference 4 5) (sourceB1067 + difference 5 4) sourceC1067) = raw17643 := by
      apply Matrix.ext; unfold tripleCharges sourceA1067 sourceB1067 sourceC1067 difference raw17643; decide +kernel
    rw [ha]
    exact (canonical17643 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1067 + difference 5 0) (sourceB1067 + difference 0 5) sourceC1067) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5134) := by
    have ha : (tripleCharges (sourceA1067 + difference 5 0) (sourceB1067 + difference 0 5) sourceC1067) = raw17644 := by
      apply Matrix.ext; unfold tripleCharges sourceA1067 sourceB1067 sourceC1067 difference raw17644; decide +kernel
    rw [ha]
    exact (canonical17644 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1067 + difference 5 1) (sourceB1067 + difference 1 5) sourceC1067) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5135) := by
    have ha : (tripleCharges (sourceA1067 + difference 5 1) (sourceB1067 + difference 1 5) sourceC1067) = raw17645 := by
      apply Matrix.ext; unfold tripleCharges sourceA1067 sourceB1067 sourceC1067 difference raw17645; decide +kernel
    rw [ha]
    exact (canonical17645 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1067 + difference 5 2) (sourceB1067 + difference 2 5) sourceC1067) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5271) := by
    have ha : (tripleCharges (sourceA1067 + difference 5 2) (sourceB1067 + difference 2 5) sourceC1067) = raw17646 := by
      apply Matrix.ext; unfold tripleCharges sourceA1067 sourceB1067 sourceC1067 difference raw17646; decide +kernel
    rw [ha]
    exact (canonical17646 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1067 + difference 5 3) (sourceB1067 + difference 3 5) sourceC1067) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5138) := by
    have ha : (tripleCharges (sourceA1067 + difference 5 3) (sourceB1067 + difference 3 5) sourceC1067) = raw17647 := by
      apply Matrix.ext; unfold tripleCharges sourceA1067 sourceB1067 sourceC1067 difference raw17647; decide +kernel
    rw [ha]
    exact (canonical17647 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1067 + difference 5 4) (sourceB1067 + difference 4 5) sourceC1067) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5160) := by
    have ha : (tripleCharges (sourceA1067 + difference 5 4) (sourceB1067 + difference 4 5) sourceC1067) = raw17393 := by
      apply Matrix.ext; unfold tripleCharges sourceA1067 sourceB1067 sourceC1067 difference raw17393; decide +kernel
    rw [ha]
    exact (canonical17393 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1067 sourceB1067 sourceC1067
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1067, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic57
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reindexCheck920 : Integer.Sparse.reindex keyMap MixedData.row920 = numericRow920 := by decide +kernel

theorem numericCheck920 (x : Master → ℝ) : Integer.Sparse.eval numericRow920 x =
    (17280 : ℝ) * reducedSource920 x := by
  norm_num [numericRow920, reducedSource920, Integer.Sparse.eval, Sparse.eval, nodeValue5134, nodeValue5135, nodeValue5138, nodeValue5160, nodeValue5271, nodeValue5378, nodeValue5379, nodeValue5381, nodeValue5382, nodeValue5394, nodeValue5395, nodeValue5397, nodeValue5409, nodeValue5410, nodeValue5423, nodeValue5424, nodeValue5425, nodeValue5426, nodeValue5428, nodeValue5430, nodeValue5434, nodeValue5435, nodeValue5438, nodeValue5442, nodeValue5445, nodeValue5477, nodeValue5483]
  ring

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Rows57
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero920 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource920 (mixedVector B) = 0 := by
  have h5134 : mixedVector B (Sum.inr 5134) = Sparse.eval nodeValue5134 (mixedVector B) := by
    change mixedMoment B node5134 node5134Labels = _
    exact sound5134 B hB hF
  have h5135 : mixedVector B (Sum.inr 5135) = Sparse.eval nodeValue5135 (mixedVector B) := by
    change mixedMoment B node5135 node5135Labels = _
    exact sound5135 B hB hF
  have h5138 : mixedVector B (Sum.inr 5138) = Sparse.eval nodeValue5138 (mixedVector B) := by
    change mixedMoment B node5138 node5138Labels = _
    exact sound5138 B hB hF
  have h5160 : mixedVector B (Sum.inr 5160) = Sparse.eval nodeValue5160 (mixedVector B) := by
    change mixedMoment B node5160 node5160Labels = _
    exact sound5160 B hB hF
  have h5271 : mixedVector B (Sum.inr 5271) = Sparse.eval nodeValue5271 (mixedVector B) := by
    change mixedMoment B node5271 node5271Labels = _
    exact sound5271 B hB hF
  have h5378 : mixedVector B (Sum.inr 5378) = Sparse.eval nodeValue5378 (mixedVector B) := by
    change mixedMoment B node5378 node5378Labels = _
    exact sound5378 B hB hF
  have h5379 : mixedVector B (Sum.inr 5379) = Sparse.eval nodeValue5379 (mixedVector B) := by
    change mixedMoment B node5379 node5379Labels = _
    exact sound5379 B hB hF
  have h5381 : mixedVector B (Sum.inr 5381) = Sparse.eval nodeValue5381 (mixedVector B) := by
    change mixedMoment B node5381 node5381Labels = _
    exact sound5381 B hB hF
  have h5382 : mixedVector B (Sum.inr 5382) = Sparse.eval nodeValue5382 (mixedVector B) := by
    change mixedMoment B node5382 node5382Labels = _
    exact sound5382 B hB hF
  have h5394 : mixedVector B (Sum.inr 5394) = Sparse.eval nodeValue5394 (mixedVector B) := by
    change mixedMoment B node5394 node5394Labels = _
    exact sound5394 B hB hF
  have h5395 : mixedVector B (Sum.inr 5395) = Sparse.eval nodeValue5395 (mixedVector B) := by
    change mixedMoment B node5395 node5395Labels = _
    exact sound5395 B hB hF
  have h5397 : mixedVector B (Sum.inr 5397) = Sparse.eval nodeValue5397 (mixedVector B) := by
    change mixedMoment B node5397 node5397Labels = _
    exact sound5397 B hB hF
  have h5409 : mixedVector B (Sum.inr 5409) = Sparse.eval nodeValue5409 (mixedVector B) := by
    change mixedMoment B node5409 node5409Labels = _
    exact sound5409 B hB hF
  have h5410 : mixedVector B (Sum.inr 5410) = Sparse.eval nodeValue5410 (mixedVector B) := by
    change mixedMoment B node5410 node5410Labels = _
    exact sound5410 B hB hF
  have h5423 : mixedVector B (Sum.inr 5423) = Sparse.eval nodeValue5423 (mixedVector B) := by
    change mixedMoment B node5423 node5423Labels = _
    exact sound5423 B hB hF
  have h5424 : mixedVector B (Sum.inr 5424) = Sparse.eval nodeValue5424 (mixedVector B) := by
    change mixedMoment B node5424 node5424Labels = _
    exact sound5424 B hB hF
  have h5425 : mixedVector B (Sum.inr 5425) = Sparse.eval nodeValue5425 (mixedVector B) := by
    change mixedMoment B node5425 node5425Labels = _
    exact sound5425 B hB hF
  have h5426 : mixedVector B (Sum.inr 5426) = Sparse.eval nodeValue5426 (mixedVector B) := by
    change mixedMoment B node5426 node5426Labels = _
    exact sound5426 B hB hF
  have h5428 : mixedVector B (Sum.inr 5428) = Sparse.eval nodeValue5428 (mixedVector B) := by
    change mixedMoment B node5428 node5428Labels = _
    exact sound5428 B hB hF
  have h5430 : mixedVector B (Sum.inr 5430) = Sparse.eval nodeValue5430 (mixedVector B) := by
    change mixedMoment B node5430 node5430Labels = _
    exact sound5430 B hB hF
  have h5434 : mixedVector B (Sum.inr 5434) = Sparse.eval nodeValue5434 (mixedVector B) := by
    change mixedMoment B node5434 node5434Labels = _
    exact sound5434_e B hB hF
  have h5435 : mixedVector B (Sum.inr 5435) = Sparse.eval nodeValue5435 (mixedVector B) := by
    change mixedMoment B node5435 node5435Labels = _
    exact sound5435_e B hB hF
  have h5438 : mixedVector B (Sum.inr 5438) = Sparse.eval nodeValue5438 (mixedVector B) := by
    change mixedMoment B node5438 node5438Labels = _
    exact sound5438 B hB hF
  have h5442 : mixedVector B (Sum.inr 5442) = Sparse.eval nodeValue5442 (mixedVector B) := by
    change mixedMoment B node5442 node5442Labels = _
    exact sound5442 B hB hF
  have h5445 : mixedVector B (Sum.inr 5445) = Sparse.eval nodeValue5445 (mixedVector B) := by
    change mixedMoment B node5445 node5445Labels = _
    exact sound5445 B hB hF
  have h5477 : mixedVector B (Sum.inr 5477) = Sparse.eval nodeValue5477 (mixedVector B) := by
    change mixedMoment B node5477 node5477Labels = _
    exact sound5477 B hB hF
  have h5483 : mixedVector B (Sum.inr 5483) = Sparse.eval nodeValue5483 (mixedVector B) := by
    change mixedMoment B node5483 node5483Labels = _
    exact sound5483_e B hB hF
  simpa only [sourceForm1067, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h5134, h5135, h5138, h5160, h5271, h5378, h5379, h5381, h5382, h5394, h5395, h5397, h5409, h5410, h5423, h5424, h5425, h5426, h5428, h5430, h5434, h5435, h5438, h5442, h5445, h5477, h5483, reducedSource920] using sourceEq1067 B hB

theorem rowSound920_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row920 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck920, numericCheck920, reducedZero920 B hB hF, mul_zero]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedSourceBridge.rowSound920_e_oai := @OAI.MUB6.Certificate.MixedSourceBridge.rowSound920_e_oai
