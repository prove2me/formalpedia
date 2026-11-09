-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedSourceBridge.rowSound1679_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-08T21:39:30.494842+00:00
-- url     : https://prove2.me/submissions/68b619ab-21ed-4ad5-bdd2-beb9d6eeb4a8

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E070
import Definitions.Def_OAIQ106E086
import Definitions.Def_OAIQ106E088
import Definitions.Def_OAIQ106E092
import Definitions.Def_OAIQ106E093
import Definitions.Def_OAIQ106E094
import Definitions.Def_OAIQ106E097
import Definitions.Def_OAIQ106E102
import Definitions.Def_OAIQ106E103
import Definitions.Def_OAIQ106E119
import Definitions.Def_OAIQ106E120
import Definitions.Def_OAIQ106E125
import Definitions.Def_OAIQ106E140
import Definitions.Def_OAIQ106E147
import Definitions.Def_OAIQ106E170
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound5174_e

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical12
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical1644 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1644 raw1644Labels = mixedMoment B node4729 node4729Labels := by
  calc
    mixedMoment B raw1644 raw1644Labels = mixedMoment B raw1644step0 raw1644step0Labels := by
      have ha : raw1644step0 = (fun i j => raw1644 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1644step0 raw1644; decide +kernel
      have hl : raw1644step0Labels = raw1644Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1644 raw1644Labels permutation152 permutation4
    mixedMoment B raw1644step0 raw1644step0Labels = mixedMoment B raw1644step1 raw1644step1Labels := by
      have ha : raw1644step1 = raw1644step0 := by apply Matrix.ext; unfold raw1644step1 raw1644step0; decide +kernel
      have hl : raw1644step0Labels = labelEmbedding7 ∘ raw1644step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1644step0 raw1644step0Labels raw1644step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4729 node4729Labels := by rfl

theorem canonical1645 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1645 raw1645Labels = mixedMoment B node1898 node1898Labels := by
  calc
    mixedMoment B raw1645 raw1645Labels = mixedMoment B raw1645step0 raw1645step0Labels := by
      have ha : raw1645step0 = (fun i j => raw1645 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1645step0 raw1645; decide +kernel
      have hl : raw1645step0Labels = raw1645Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1645 raw1645Labels permutation152 permutation4
    _ = mixedMoment B node1898 node1898Labels := by rfl

theorem canonical1646 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1646 raw1646Labels = mixedMoment B node1940 node1940Labels := by
  calc
    mixedMoment B raw1646 raw1646Labels = mixedMoment B raw1646step0 raw1646step0Labels := by
      have ha : raw1646step0 = (fun i j => raw1646 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1646step0 raw1646; decide +kernel
      have hl : raw1646step0Labels = raw1646Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1646 raw1646Labels permutation152 permutation6
    mixedMoment B raw1646step0 raw1646step0Labels = mixedMoment B raw1646step1 raw1646step1Labels := by
      have ha : raw1646step1 = -raw1646step0 := by apply Matrix.ext; change ∀ i j, raw1646step1 i j = -(raw1646step0 i j); unfold raw1646step1 raw1646step0; decide +kernel
      have hl : raw1646step1Labels = raw1646step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1646step1 raw1646step1Labels = mixedMoment B raw1646step2 raw1646step2Labels := by
      have ha : raw1646step2 = raw1646step1 := by apply Matrix.ext; unfold raw1646step2 raw1646step1; decide +kernel
      have hl : raw1646step1Labels = labelEmbedding1 ∘ raw1646step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1646step1 raw1646step1Labels raw1646step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1940 node1940Labels := by rfl

theorem canonical1659 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1659 raw1659Labels = mixedMoment B node4742 node4742Labels := by
  calc
    mixedMoment B raw1659 raw1659Labels = mixedMoment B raw1659step0 raw1659step0Labels := by
      have ha : raw1659step0 = (fun i j => raw1659 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1659step0 raw1659; decide +kernel
      have hl : raw1659step0Labels = raw1659Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1659 raw1659Labels permutation32 permutation4
    mixedMoment B raw1659step0 raw1659step0Labels = mixedMoment B raw1659step1 raw1659step1Labels := by
      have ha : raw1659step1 = raw1659step0 := by apply Matrix.ext; unfold raw1659step1 raw1659step0; decide +kernel
      have hl : raw1659step0Labels = labelEmbedding7 ∘ raw1659step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1659step0 raw1659step0Labels raw1659step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4742 node4742Labels := by rfl

theorem canonical1660 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1660 raw1660Labels = mixedMoment B node1915 node1915Labels := by
  calc
    mixedMoment B raw1660 raw1660Labels = mixedMoment B raw1660step0 raw1660step0Labels := by
      have ha : raw1660step0 = (fun i j => raw1660 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1660step0 raw1660; decide +kernel
      have hl : raw1660step0Labels = raw1660Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1660 raw1660Labels permutation32 permutation4
    _ = mixedMoment B node1915 node1915Labels := by rfl

theorem canonical1661 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1661 raw1661Labels = mixedMoment B node1946 node1946Labels := by
  calc
    mixedMoment B raw1661 raw1661Labels = mixedMoment B raw1661step0 raw1661step0Labels := by
      have ha : raw1661step0 = (fun i j => raw1661 (permutation33 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1661step0 raw1661; decide +kernel
      have hl : raw1661step0Labels = raw1661Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1661 raw1661Labels permutation33 permutation6
    mixedMoment B raw1661step0 raw1661step0Labels = mixedMoment B raw1661step1 raw1661step1Labels := by
      have ha : raw1661step1 = -raw1661step0 := by apply Matrix.ext; change ∀ i j, raw1661step1 i j = -(raw1661step0 i j); unfold raw1661step1 raw1661step0; decide +kernel
      have hl : raw1661step1Labels = raw1661step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1661step1 raw1661step1Labels = mixedMoment B raw1661step2 raw1661step2Labels := by
      have ha : raw1661step2 = raw1661step1 := by apply Matrix.ext; unfold raw1661step2 raw1661step1; decide +kernel
      have hl : raw1661step1Labels = labelEmbedding1 ∘ raw1661step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1661step1 raw1661step1Labels raw1661step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1946 node1946Labels := by rfl

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

theorem canonical1668 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1668 raw1668Labels = mixedMoment B node4747 node4747Labels := by
  calc
    mixedMoment B raw1668 raw1668Labels = mixedMoment B raw1668step0 raw1668step0Labels := by
      have ha : raw1668step0 = (fun i j => raw1668 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1668step0 raw1668; decide +kernel
      have hl : raw1668step0Labels = raw1668Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1668 raw1668Labels permutation32 permutation4
    mixedMoment B raw1668step0 raw1668step0Labels = mixedMoment B raw1668step1 raw1668step1Labels := by
      have ha : raw1668step1 = raw1668step0 := by apply Matrix.ext; unfold raw1668step1 raw1668step0; decide +kernel
      have hl : raw1668step0Labels = labelEmbedding7 ∘ raw1668step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1668step0 raw1668step0Labels raw1668step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4747 node4747Labels := by rfl

theorem canonical1669 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1669 raw1669Labels = mixedMoment B node1926 node1926Labels := by
  calc
    mixedMoment B raw1669 raw1669Labels = mixedMoment B raw1669step0 raw1669step0Labels := by
      have ha : raw1669step0 = (fun i j => raw1669 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1669step0 raw1669; decide +kernel
      have hl : raw1669step0Labels = raw1669Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1669 raw1669Labels permutation32 permutation4
    _ = mixedMoment B node1926 node1926Labels := by rfl

theorem canonical1670 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1670 raw1670Labels = mixedMoment B node1948 node1948Labels := by
  calc
    mixedMoment B raw1670 raw1670Labels = mixedMoment B raw1670step0 raw1670step0Labels := by
      have ha : raw1670step0 = (fun i j => raw1670 (permutation35 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1670step0 raw1670; decide +kernel
      have hl : raw1670step0Labels = raw1670Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1670 raw1670Labels permutation35 permutation6
    mixedMoment B raw1670step0 raw1670step0Labels = mixedMoment B raw1670step1 raw1670step1Labels := by
      have ha : raw1670step1 = -raw1670step0 := by apply Matrix.ext; change ∀ i j, raw1670step1 i j = -(raw1670step0 i j); unfold raw1670step1 raw1670step0; decide +kernel
      have hl : raw1670step1Labels = raw1670step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1670step1 raw1670step1Labels = mixedMoment B raw1670step2 raw1670step2Labels := by
      have ha : raw1670step2 = raw1670step1 := by apply Matrix.ext; unfold raw1670step2 raw1670step1; decide +kernel
      have hl : raw1670step1Labels = labelEmbedding1 ∘ raw1670step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1670step1 raw1670step1Labels raw1670step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1948 node1948Labels := by rfl

theorem canonical1713 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1713 raw1713Labels = mixedMoment B node4779 node4779Labels := by
  calc
    mixedMoment B raw1713 raw1713Labels = mixedMoment B raw1713step0 raw1713step0Labels := by
      have ha : raw1713step0 = (fun i j => raw1713 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1713step0 raw1713; decide +kernel
      have hl : raw1713step0Labels = raw1713Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1713 raw1713Labels permutation152 permutation4
    mixedMoment B raw1713step0 raw1713step0Labels = mixedMoment B raw1713step1 raw1713step1Labels := by
      have ha : raw1713step1 = raw1713step0 := by apply Matrix.ext; unfold raw1713step1 raw1713step0; decide +kernel
      have hl : raw1713step0Labels = labelEmbedding7 ∘ raw1713step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1713step0 raw1713step0Labels raw1713step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4779 node4779Labels := by rfl

theorem canonical1714 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1714 raw1714Labels = mixedMoment B node1987 node1987Labels := by
  calc
    mixedMoment B raw1714 raw1714Labels = mixedMoment B raw1714step0 raw1714step0Labels := by
      have ha : raw1714step0 = (fun i j => raw1714 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1714step0 raw1714; decide +kernel
      have hl : raw1714step0Labels = raw1714Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1714 raw1714Labels permutation152 permutation4
    _ = mixedMoment B node1987 node1987Labels := by rfl

theorem canonical1715 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1715 raw1715Labels = mixedMoment B node1996 node1996Labels := by
  calc
    mixedMoment B raw1715 raw1715Labels = mixedMoment B raw1715step0 raw1715step0Labels := by
      have ha : raw1715step0 = (fun i j => raw1715 (permutation176 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1715step0 raw1715; decide +kernel
      have hl : raw1715step0Labels = raw1715Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1715 raw1715Labels permutation176 permutation6
    mixedMoment B raw1715step0 raw1715step0Labels = mixedMoment B raw1715step1 raw1715step1Labels := by
      have ha : raw1715step1 = -raw1715step0 := by apply Matrix.ext; change ∀ i j, raw1715step1 i j = -(raw1715step0 i j); unfold raw1715step1 raw1715step0; decide +kernel
      have hl : raw1715step1Labels = raw1715step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1715step1 raw1715step1Labels = mixedMoment B raw1715step2 raw1715step2Labels := by
      have ha : raw1715step2 = raw1715step1 := by apply Matrix.ext; unfold raw1715step2 raw1715step1; decide +kernel
      have hl : raw1715step1Labels = labelEmbedding1 ∘ raw1715step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1715step1 raw1715step1Labels raw1715step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1996 node1996Labels := by rfl

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

theorem canonical1743 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1743 raw1743Labels = mixedMoment B node4807 node4807Labels := by
  calc
    mixedMoment B raw1743 raw1743Labels = mixedMoment B raw1743step0 raw1743step0Labels := by
      have ha : raw1743step0 = (fun i j => raw1743 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1743step0 raw1743; decide +kernel
      have hl : raw1743step0Labels = raw1743Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1743 raw1743Labels permutation32 permutation4
    mixedMoment B raw1743step0 raw1743step0Labels = mixedMoment B raw1743step1 raw1743step1Labels := by
      have ha : raw1743step1 = raw1743step0 := by apply Matrix.ext; unfold raw1743step1 raw1743step0; decide +kernel
      have hl : raw1743step0Labels = labelEmbedding7 ∘ raw1743step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1743step0 raw1743step0Labels raw1743step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4807 node4807Labels := by rfl

theorem canonical1744 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1744 raw1744Labels = mixedMoment B node2025 node2025Labels := by
  calc
    mixedMoment B raw1744 raw1744Labels = mixedMoment B raw1744step0 raw1744step0Labels := by
      have ha : raw1744step0 = (fun i j => raw1744 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1744step0 raw1744; decide +kernel
      have hl : raw1744step0Labels = raw1744Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1744 raw1744Labels permutation32 permutation4
    _ = mixedMoment B node2025 node2025Labels := by rfl

theorem canonical1745 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1745 raw1745Labels = mixedMoment B node2224 node2224Labels := by
  calc
    mixedMoment B raw1745 raw1745Labels = mixedMoment B raw1745step0 raw1745step0Labels := by
      have ha : raw1745step0 = (fun i j => raw1745 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1745step0 raw1745; decide +kernel
      have hl : raw1745step0Labels = raw1745Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1745 raw1745Labels permutation32 permutation6
    mixedMoment B raw1745step0 raw1745step0Labels = mixedMoment B raw1745step1 raw1745step1Labels := by
      have ha : raw1745step1 = -raw1745step0 := by apply Matrix.ext; change ∀ i j, raw1745step1 i j = -(raw1745step0 i j); unfold raw1745step1 raw1745step0; decide +kernel
      have hl : raw1745step1Labels = raw1745step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1745step1 raw1745step1Labels = mixedMoment B raw1745step2 raw1745step2Labels := by
      have ha : raw1745step2 = raw1745step1 := by apply Matrix.ext; unfold raw1745step2 raw1745step1; decide +kernel
      have hl : raw1745step1Labels = labelEmbedding1 ∘ raw1745step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1745step1 raw1745step1Labels raw1745step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2224 node2224Labels := by rfl

theorem canonical1773 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1773 raw1773Labels = mixedMoment B node4843 node4843Labels := by
  calc
    mixedMoment B raw1773 raw1773Labels = mixedMoment B raw1773step0 raw1773step0Labels := by
      have ha : raw1773step0 = (fun i j => raw1773 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1773step0 raw1773; decide +kernel
      have hl : raw1773step0Labels = raw1773Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1773 raw1773Labels permutation8 permutation4
    mixedMoment B raw1773step0 raw1773step0Labels = mixedMoment B raw1773step1 raw1773step1Labels := by
      have ha : raw1773step1 = raw1773step0 := by apply Matrix.ext; unfold raw1773step1 raw1773step0; decide +kernel
      have hl : raw1773step0Labels = labelEmbedding7 ∘ raw1773step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1773step0 raw1773step0Labels raw1773step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4843 node4843Labels := by rfl

theorem canonical1774 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1774 raw1774Labels = mixedMoment B node2062 node2062Labels := by
  calc
    mixedMoment B raw1774 raw1774Labels = mixedMoment B raw1774step0 raw1774step0Labels := by
      have ha : raw1774step0 = (fun i j => raw1774 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1774step0 raw1774; decide +kernel
      have hl : raw1774step0Labels = raw1774Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1774 raw1774Labels permutation8 permutation4
    _ = mixedMoment B node2062 node2062Labels := by rfl

theorem canonical1775 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1775 raw1775Labels = mixedMoment B node2230 node2230Labels := by
  calc
    mixedMoment B raw1775 raw1775Labels = mixedMoment B raw1775step0 raw1775step0Labels := by
      have ha : raw1775step0 = (fun i j => raw1775 (permutation9 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1775step0 raw1775; decide +kernel
      have hl : raw1775step0Labels = raw1775Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1775 raw1775Labels permutation9 permutation6
    mixedMoment B raw1775step0 raw1775step0Labels = mixedMoment B raw1775step1 raw1775step1Labels := by
      have ha : raw1775step1 = -raw1775step0 := by apply Matrix.ext; change ∀ i j, raw1775step1 i j = -(raw1775step0 i j); unfold raw1775step1 raw1775step0; decide +kernel
      have hl : raw1775step1Labels = raw1775step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1775step1 raw1775step1Labels = mixedMoment B raw1775step2 raw1775step2Labels := by
      have ha : raw1775step2 = raw1775step1 := by apply Matrix.ext; unfold raw1775step2 raw1775step1; decide +kernel
      have hl : raw1775step1Labels = labelEmbedding1 ∘ raw1775step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1775step1 raw1775step1Labels raw1775step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2230 node2230Labels := by rfl

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

theorem canonical1803 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1803 raw1803Labels = mixedMoment B node4871 node4871Labels := by
  calc
    mixedMoment B raw1803 raw1803Labels = mixedMoment B raw1803step0 raw1803step0Labels := by
      have ha : raw1803step0 = (fun i j => raw1803 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1803step0 raw1803; decide +kernel
      have hl : raw1803step0Labels = raw1803Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1803 raw1803Labels permutation8 permutation4
    mixedMoment B raw1803step0 raw1803step0Labels = mixedMoment B raw1803step1 raw1803step1Labels := by
      have ha : raw1803step1 = raw1803step0 := by apply Matrix.ext; unfold raw1803step1 raw1803step0; decide +kernel
      have hl : raw1803step0Labels = labelEmbedding7 ∘ raw1803step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1803step0 raw1803step0Labels raw1803step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4871 node4871Labels := by rfl

theorem canonical1804 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1804 raw1804Labels = mixedMoment B node2112 node2112Labels := by
  calc
    mixedMoment B raw1804 raw1804Labels = mixedMoment B raw1804step0 raw1804step0Labels := by
      have ha : raw1804step0 = (fun i j => raw1804 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1804step0 raw1804; decide +kernel
      have hl : raw1804step0Labels = raw1804Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1804 raw1804Labels permutation8 permutation4
    _ = mixedMoment B node2112 node2112Labels := by rfl

theorem canonical1805 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1805 raw1805Labels = mixedMoment B node2287 node2287Labels := by
  calc
    mixedMoment B raw1805 raw1805Labels = mixedMoment B raw1805step0 raw1805step0Labels := by
      have ha : raw1805step0 = (fun i j => raw1805 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1805step0 raw1805; decide +kernel
      have hl : raw1805step0Labels = raw1805Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1805 raw1805Labels permutation8 permutation6
    mixedMoment B raw1805step0 raw1805step0Labels = mixedMoment B raw1805step1 raw1805step1Labels := by
      have ha : raw1805step1 = -raw1805step0 := by apply Matrix.ext; change ∀ i j, raw1805step1 i j = -(raw1805step0 i j); unfold raw1805step1 raw1805step0; decide +kernel
      have hl : raw1805step1Labels = raw1805step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1805step1 raw1805step1Labels = mixedMoment B raw1805step2 raw1805step2Labels := by
      have ha : raw1805step2 = raw1805step1 := by apply Matrix.ext; unfold raw1805step2 raw1805step1; decide +kernel
      have hl : raw1805step1Labels = labelEmbedding1 ∘ raw1805step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1805step1 raw1805step1Labels raw1805step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2287 node2287Labels := by rfl

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

theorem canonical2103 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2103 raw2103Labels = mixedMoment B node5078 node5078Labels := by
  calc
    mixedMoment B raw2103 raw2103Labels = mixedMoment B raw2103step0 raw2103step0Labels := by
      have ha : raw2103step0 = (fun i j => raw2103 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2103step0 raw2103; decide +kernel
      have hl : raw2103step0Labels = raw2103Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2103 raw2103Labels permutation32 permutation4
    mixedMoment B raw2103step0 raw2103step0Labels = mixedMoment B raw2103step1 raw2103step1Labels := by
      have ha : raw2103step1 = raw2103step0 := by apply Matrix.ext; unfold raw2103step1 raw2103step0; decide +kernel
      have hl : raw2103step0Labels = labelEmbedding7 ∘ raw2103step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2103step0 raw2103step0Labels raw2103step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5078 node5078Labels := by rfl

theorem canonical2104 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2104 raw2104Labels = mixedMoment B node2485 node2485Labels := by
  calc
    mixedMoment B raw2104 raw2104Labels = mixedMoment B raw2104step0 raw2104step0Labels := by
      have ha : raw2104step0 = (fun i j => raw2104 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2104step0 raw2104; decide +kernel
      have hl : raw2104step0Labels = raw2104Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2104 raw2104Labels permutation32 permutation4
    _ = mixedMoment B node2485 node2485Labels := by rfl

theorem canonical2105 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2105 raw2105Labels = mixedMoment B node3481 node3481Labels := by
  calc
    mixedMoment B raw2105 raw2105Labels = mixedMoment B raw2105step0 raw2105step0Labels := by
      have ha : raw2105step0 = (fun i j => raw2105 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2105step0 raw2105; decide +kernel
      have hl : raw2105step0Labels = raw2105Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2105 raw2105Labels permutation32 permutation6
    mixedMoment B raw2105step0 raw2105step0Labels = mixedMoment B raw2105step1 raw2105step1Labels := by
      have ha : raw2105step1 = -raw2105step0 := by apply Matrix.ext; change ∀ i j, raw2105step1 i j = -(raw2105step0 i j); unfold raw2105step1 raw2105step0; decide +kernel
      have hl : raw2105step1Labels = raw2105step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2105step1 raw2105step1Labels = mixedMoment B raw2105step2 raw2105step2Labels := by
      have ha : raw2105step2 = raw2105step1 := by apply Matrix.ext; unfold raw2105step2 raw2105step1; decide +kernel
      have hl : raw2105step1Labels = labelEmbedding1 ∘ raw2105step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2105step1 raw2105step1Labels raw2105step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3481 node3481Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical215
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical27642 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27642 raw27642Labels = mixedMoment B node4841 node4841Labels := by
  calc
    mixedMoment B raw27642 raw27642Labels = mixedMoment B raw27642step0 raw27642step0Labels := by
      have hz : ∀ j, raw27642 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27642step0 = (fun i j => raw27642 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27642step0 raw27642; decide +kernel
      have hl : raw27642step0Labels = raw27642Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27642 raw27642Labels permutation434 hz
    mixedMoment B raw27642step0 raw27642step0Labels = mixedMoment B raw27642step1 raw27642step1Labels := by
      have hz : ∀ j, raw27642step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw27642step1 = (fun i j => raw27642step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw27642step1 raw27642step0; decide +kernel
      have hl : raw27642step1Labels = raw27642step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27642step0 raw27642step0Labels permutation80 hz
    mixedMoment B raw27642step1 raw27642step1Labels = mixedMoment B raw27642step2 raw27642step2Labels := by
      have ha : raw27642step2 = (fun i j => raw27642step1 (permutation31 i) (permutation7 j)) := by apply Matrix.ext; unfold raw27642step2 raw27642step1; decide +kernel
      have hl : raw27642step2Labels = raw27642step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27642step1 raw27642step1Labels permutation31 permutation7
    mixedMoment B raw27642step2 raw27642step2Labels = mixedMoment B raw27642step3 raw27642step3Labels := by
      have ha : raw27642step3 = -raw27642step2 := by apply Matrix.ext; change ∀ i j, raw27642step3 i j = -(raw27642step2 i j); unfold raw27642step3 raw27642step2; decide +kernel
      have hl : raw27642step3Labels = raw27642step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw27642step3 raw27642step3Labels = mixedMoment B raw27642step4 raw27642step4Labels := by
      have ha : raw27642step4 = raw27642step3 := by apply Matrix.ext; unfold raw27642step4 raw27642step3; decide +kernel
      have hl : raw27642step3Labels = labelEmbedding10 ∘ raw27642step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27642step3 raw27642step3Labels raw27642step4Labels labelEmbedding10 hl
    _ = mixedMoment B node4841 node4841Labels := by rfl

theorem canonical27647 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27647 raw27647Labels = mixedMoment B node4843 node4843Labels := by
  calc
    mixedMoment B raw27647 raw27647Labels = mixedMoment B raw27647step0 raw27647step0Labels := by
      have hz : ∀ j, raw27647 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27647step0 = (fun i j => raw27647 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27647step0 raw27647; decide +kernel
      have hl : raw27647step0Labels = raw27647Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27647 raw27647Labels permutation434 hz
    mixedMoment B raw27647step0 raw27647step0Labels = mixedMoment B raw27647step1 raw27647step1Labels := by
      have hz : ∀ j, raw27647step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw27647step1 = (fun i j => raw27647step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw27647step1 raw27647step0; decide +kernel
      have hl : raw27647step1Labels = raw27647step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27647step0 raw27647step0Labels permutation80 hz
    mixedMoment B raw27647step1 raw27647step1Labels = mixedMoment B raw27647step2 raw27647step2Labels := by
      have ha : raw27647step2 = (fun i j => raw27647step1 (permutation31 i) (permutation7 j)) := by apply Matrix.ext; unfold raw27647step2 raw27647step1; decide +kernel
      have hl : raw27647step2Labels = raw27647step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27647step1 raw27647step1Labels permutation31 permutation7
    mixedMoment B raw27647step2 raw27647step2Labels = mixedMoment B raw27647step3 raw27647step3Labels := by
      have ha : raw27647step3 = -raw27647step2 := by apply Matrix.ext; change ∀ i j, raw27647step3 i j = -(raw27647step2 i j); unfold raw27647step3 raw27647step2; decide +kernel
      have hl : raw27647step3Labels = raw27647step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw27647step3 raw27647step3Labels = mixedMoment B raw27647step4 raw27647step4Labels := by
      have ha : raw27647step4 = raw27647step3 := by apply Matrix.ext; unfold raw27647step4 raw27647step3; decide +kernel
      have hl : raw27647step3Labels = labelEmbedding10 ∘ raw27647step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27647step3 raw27647step3Labels raw27647step4Labels labelEmbedding10 hl
    _ = mixedMoment B node4843 node4843Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical216
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical27652 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27652 raw27652Labels = mixedMoment B node4807 node4807Labels := by
  calc
    mixedMoment B raw27652 raw27652Labels = mixedMoment B raw27652step0 raw27652step0Labels := by
      have hz : ∀ j, raw27652 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27652step0 = (fun i j => raw27652 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27652step0 raw27652; decide +kernel
      have hl : raw27652step0Labels = raw27652Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27652 raw27652Labels permutation434 hz
    mixedMoment B raw27652step0 raw27652step0Labels = mixedMoment B raw27652step1 raw27652step1Labels := by
      have ha : raw27652step1 = (fun i j => raw27652step0 (permutation151 i) (permutation7 j)) := by apply Matrix.ext; unfold raw27652step1 raw27652step0; decide +kernel
      have hl : raw27652step1Labels = raw27652step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27652step0 raw27652step0Labels permutation151 permutation7
    mixedMoment B raw27652step1 raw27652step1Labels = mixedMoment B raw27652step2 raw27652step2Labels := by
      have ha : raw27652step2 = -raw27652step1 := by apply Matrix.ext; change ∀ i j, raw27652step2 i j = -(raw27652step1 i j); unfold raw27652step2 raw27652step1; decide +kernel
      have hl : raw27652step2Labels = raw27652step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw27652step2 raw27652step2Labels = mixedMoment B raw27652step3 raw27652step3Labels := by
      have ha : raw27652step3 = raw27652step2 := by apply Matrix.ext; unfold raw27652step3 raw27652step2; decide +kernel
      have hl : raw27652step2Labels = labelEmbedding10 ∘ raw27652step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27652step2 raw27652step2Labels raw27652step3Labels labelEmbedding10 hl
    _ = mixedMoment B node4807 node4807Labels := by rfl

theorem canonical27653 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27653 raw27653Labels = mixedMoment B node4807 node4807Labels := by
  calc
    mixedMoment B raw27653 raw27653Labels = mixedMoment B raw27653step0 raw27653step0Labels := by
      have hz : ∀ j, raw27653 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27653step0 = (fun i j => raw27653 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27653step0 raw27653; decide +kernel
      have hl : raw27653step0Labels = raw27653Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27653 raw27653Labels permutation346 hz
    mixedMoment B raw27653step0 raw27653step0Labels = mixedMoment B raw27653step1 raw27653step1Labels := by
      have ha : raw27653step1 = (fun i j => raw27653step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw27653step1 raw27653step0; decide +kernel
      have hl : raw27653step1Labels = raw27653step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27653step0 raw27653step0Labels permutation32 permutation6
    mixedMoment B raw27653step1 raw27653step1Labels = mixedMoment B raw27653step2 raw27653step2Labels := by
      have ha : raw27653step2 = raw27653step1 := by apply Matrix.ext; unfold raw27653step2 raw27653step1; decide +kernel
      have hl : raw27653step1Labels = labelEmbedding9 ∘ raw27653step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27653step1 raw27653step1Labels raw27653step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4807 node4807Labels := by rfl

theorem canonical27654 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27654 raw27654Labels = mixedMoment B node5078 node5078Labels := by
  calc
    mixedMoment B raw27654 raw27654Labels = mixedMoment B raw27654step0 raw27654step0Labels := by
      have hz : ∀ j, raw27654 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27654step0 = (fun i j => raw27654 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27654step0 raw27654; decide +kernel
      have hl : raw27654step0Labels = raw27654Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27654 raw27654Labels permutation346 hz
    mixedMoment B raw27654step0 raw27654step0Labels = mixedMoment B raw27654step1 raw27654step1Labels := by
      have ha : raw27654step1 = (fun i j => raw27654step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw27654step1 raw27654step0; decide +kernel
      have hl : raw27654step1Labels = raw27654step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27654step0 raw27654step0Labels permutation32 permutation6
    mixedMoment B raw27654step1 raw27654step1Labels = mixedMoment B raw27654step2 raw27654step2Labels := by
      have ha : raw27654step2 = raw27654step1 := by apply Matrix.ext; unfold raw27654step2 raw27654step1; decide +kernel
      have hl : raw27654step1Labels = labelEmbedding9 ∘ raw27654step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27654step1 raw27654step1Labels raw27654step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5078 node5078Labels := by rfl

theorem canonical27655 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27655 raw27655Labels = mixedMoment B node5128 node5128Labels := by
  calc
    mixedMoment B raw27655 raw27655Labels = mixedMoment B raw27655step0 raw27655step0Labels := by
      have ha : raw27655step0 = (fun i j => raw27655 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw27655step0 raw27655; decide +kernel
      have hl : raw27655step0Labels = raw27655Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27655 raw27655Labels permutation152 permutation6
    mixedMoment B raw27655step0 raw27655step0Labels = mixedMoment B raw27655step1 raw27655step1Labels := by
      have ha : raw27655step1 = raw27655step0 := by apply Matrix.ext; unfold raw27655step1 raw27655step0; decide +kernel
      have hl : raw27655step0Labels = labelEmbedding9 ∘ raw27655step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27655step0 raw27655step0Labels raw27655step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5128 node5128Labels := by rfl

theorem canonical27656 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27656 raw27656Labels = mixedMoment B node5078 node5078Labels := by
  calc
    mixedMoment B raw27656 raw27656Labels = mixedMoment B raw27656step0 raw27656step0Labels := by
      have hz : ∀ j, raw27656 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27656step0 = (fun i j => raw27656 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27656step0 raw27656; decide +kernel
      have hl : raw27656step0Labels = raw27656Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27656 raw27656Labels permutation346 hz
    mixedMoment B raw27656step0 raw27656step0Labels = mixedMoment B raw27656step1 raw27656step1Labels := by
      have ha : raw27656step1 = (fun i j => raw27656step0 (permutation151 i) (permutation7 j)) := by apply Matrix.ext; unfold raw27656step1 raw27656step0; decide +kernel
      have hl : raw27656step1Labels = raw27656step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27656step0 raw27656step0Labels permutation151 permutation7
    mixedMoment B raw27656step1 raw27656step1Labels = mixedMoment B raw27656step2 raw27656step2Labels := by
      have ha : raw27656step2 = -raw27656step1 := by apply Matrix.ext; change ∀ i j, raw27656step2 i j = -(raw27656step1 i j); unfold raw27656step2 raw27656step1; decide +kernel
      have hl : raw27656step2Labels = raw27656step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw27656step2 raw27656step2Labels = mixedMoment B raw27656step3 raw27656step3Labels := by
      have ha : raw27656step3 = raw27656step2 := by apply Matrix.ext; unfold raw27656step3 raw27656step2; decide +kernel
      have hl : raw27656step2Labels = labelEmbedding10 ∘ raw27656step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27656step2 raw27656step2Labels raw27656step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5078 node5078Labels := by rfl

theorem canonical27662 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27662 raw27662Labels = mixedMoment B node4871 node4871Labels := by
  calc
    mixedMoment B raw27662 raw27662Labels = mixedMoment B raw27662step0 raw27662step0Labels := by
      have hz : ∀ j, raw27662 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27662step0 = (fun i j => raw27662 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27662step0 raw27662; decide +kernel
      have hl : raw27662step0Labels = raw27662Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27662 raw27662Labels permutation434 hz
    mixedMoment B raw27662step0 raw27662step0Labels = mixedMoment B raw27662step1 raw27662step1Labels := by
      have hz : ∀ j, raw27662step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw27662step1 = (fun i j => raw27662step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw27662step1 raw27662step0; decide +kernel
      have hl : raw27662step1Labels = raw27662step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27662step0 raw27662step0Labels permutation80 hz
    mixedMoment B raw27662step1 raw27662step1Labels = mixedMoment B raw27662step2 raw27662step2Labels := by
      have ha : raw27662step2 = (fun i j => raw27662step1 (permutation31 i) (permutation7 j)) := by apply Matrix.ext; unfold raw27662step2 raw27662step1; decide +kernel
      have hl : raw27662step2Labels = raw27662step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27662step1 raw27662step1Labels permutation31 permutation7
    mixedMoment B raw27662step2 raw27662step2Labels = mixedMoment B raw27662step3 raw27662step3Labels := by
      have ha : raw27662step3 = -raw27662step2 := by apply Matrix.ext; change ∀ i j, raw27662step3 i j = -(raw27662step2 i j); unfold raw27662step3 raw27662step2; decide +kernel
      have hl : raw27662step3Labels = raw27662step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw27662step3 raw27662step3Labels = mixedMoment B raw27662step4 raw27662step4Labels := by
      have ha : raw27662step4 = raw27662step3 := by apply Matrix.ext; unfold raw27662step4 raw27662step3; decide +kernel
      have hl : raw27662step3Labels = labelEmbedding10 ∘ raw27662step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27662step3 raw27662step3Labels raw27662step4Labels labelEmbedding10 hl
    _ = mixedMoment B node4871 node4871Labels := by rfl

theorem canonical27771 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27771 raw27771Labels = mixedMoment B node4808 node4808Labels := by
  calc
    mixedMoment B raw27771 raw27771Labels = mixedMoment B raw27771step0 raw27771step0Labels := by
      have hz : ∀ j, raw27771 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27771step0 = (fun i j => raw27771 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27771step0 raw27771; decide +kernel
      have hl : raw27771step0Labels = raw27771Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27771 raw27771Labels permutation346 hz
    mixedMoment B raw27771step0 raw27771step0Labels = mixedMoment B raw27771step1 raw27771step1Labels := by
      have ha : raw27771step1 = (fun i j => raw27771step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw27771step1 raw27771step0; decide +kernel
      have hl : raw27771step1Labels = raw27771step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27771step0 raw27771step0Labels permutation32 permutation6
    mixedMoment B raw27771step1 raw27771step1Labels = mixedMoment B raw27771step2 raw27771step2Labels := by
      have ha : raw27771step2 = raw27771step1 := by apply Matrix.ext; unfold raw27771step2 raw27771step1; decide +kernel
      have hl : raw27771step1Labels = labelEmbedding9 ∘ raw27771step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27771step1 raw27771step1Labels raw27771step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4808 node4808Labels := by rfl

theorem canonical27772 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27772 raw27772Labels = mixedMoment B node4853 node4853Labels := by
  calc
    mixedMoment B raw27772 raw27772Labels = mixedMoment B raw27772step0 raw27772step0Labels := by
      have hz : ∀ j, raw27772 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27772step0 = (fun i j => raw27772 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27772step0 raw27772; decide +kernel
      have hl : raw27772step0Labels = raw27772Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27772 raw27772Labels permutation346 hz
    mixedMoment B raw27772step0 raw27772step0Labels = mixedMoment B raw27772step1 raw27772step1Labels := by
      have ha : raw27772step1 = (fun i j => raw27772step0 (permutation151 i) (permutation7 j)) := by apply Matrix.ext; unfold raw27772step1 raw27772step0; decide +kernel
      have hl : raw27772step1Labels = raw27772step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27772step0 raw27772step0Labels permutation151 permutation7
    mixedMoment B raw27772step1 raw27772step1Labels = mixedMoment B raw27772step2 raw27772step2Labels := by
      have ha : raw27772step2 = -raw27772step1 := by apply Matrix.ext; change ∀ i j, raw27772step2 i j = -(raw27772step1 i j); unfold raw27772step2 raw27772step1; decide +kernel
      have hl : raw27772step2Labels = raw27772step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw27772step2 raw27772step2Labels = mixedMoment B raw27772step3 raw27772step3Labels := by
      have ha : raw27772step3 = raw27772step2 := by apply Matrix.ext; unfold raw27772step3 raw27772step2; decide +kernel
      have hl : raw27772step2Labels = labelEmbedding10 ∘ raw27772step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27772step2 raw27772step2Labels raw27772step3Labels labelEmbedding10 hl
    _ = mixedMoment B node4853 node4853Labels := by rfl

theorem canonical27773 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27773 raw27773Labels = mixedMoment B node4824 node4824Labels := by
  calc
    mixedMoment B raw27773 raw27773Labels = mixedMoment B raw27773step0 raw27773step0Labels := by
      have ha : raw27773step0 = (fun i j => raw27773 (permutation646 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27773step0 raw27773; decide +kernel
      have hl : raw27773step0Labels = raw27773Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27773 raw27773Labels permutation646 permutation2
    _ = mixedMoment B node4824 node4824Labels := by rfl

theorem canonical27774 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27774 raw27774Labels = mixedMoment B node4486 node4486Labels := by
  calc
    mixedMoment B raw27774 raw27774Labels = mixedMoment B raw27774step0 raw27774step0Labels := by
      have hz : ∀ j, raw27774 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27774step0 = (fun i j => raw27774 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27774step0 raw27774; decide +kernel
      have hl : raw27774step0Labels = raw27774Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27774 raw27774Labels permutation346 hz
    mixedMoment B raw27774step0 raw27774step0Labels = mixedMoment B raw27774step1 raw27774step1Labels := by
      have ha : raw27774step1 = (fun i j => raw27774step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27774step1 raw27774step0; decide +kernel
      have hl : raw27774step1Labels = raw27774step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27774step0 raw27774step0Labels permutation151 permutation2
    _ = mixedMoment B node4486 node4486Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical217
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical27780 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27780 raw27780Labels = mixedMoment B node5174 node5174Labels := by
  calc
    mixedMoment B raw27780 raw27780Labels = mixedMoment B raw27780step0 raw27780step0Labels := by
      have hz : ∀ j, raw27780 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27780step0 = (fun i j => raw27780 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27780step0 raw27780; decide +kernel
      have hl : raw27780step0Labels = raw27780Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27780 raw27780Labels permutation434 hz
    mixedMoment B raw27780step0 raw27780step0Labels = mixedMoment B raw27780step1 raw27780step1Labels := by
      have hz : ∀ j, raw27780step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw27780step1 = (fun i j => raw27780step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw27780step1 raw27780step0; decide +kernel
      have hl : raw27780step1Labels = raw27780step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27780step0 raw27780step0Labels permutation80 hz
    mixedMoment B raw27780step1 raw27780step1Labels = mixedMoment B raw27780step2 raw27780step2Labels := by
      have ha : raw27780step2 = (fun i j => raw27780step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw27780step2 raw27780step1; decide +kernel
      have hl : raw27780step2Labels = raw27780step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27780step1 raw27780step1Labels permutation8 permutation6
    mixedMoment B raw27780step2 raw27780step2Labels = mixedMoment B raw27780step3 raw27780step3Labels := by
      have ha : raw27780step3 = raw27780step2 := by apply Matrix.ext; unfold raw27780step3 raw27780step2; decide +kernel
      have hl : raw27780step2Labels = labelEmbedding9 ∘ raw27780step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27780step2 raw27780step2Labels raw27780step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5174 node5174Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical218
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical27954 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27954 raw27954Labels = mixedMoment B node4741 node4741Labels := by
  calc
    mixedMoment B raw27954 raw27954Labels = mixedMoment B raw27954step0 raw27954step0Labels := by
      have hz : ∀ j, raw27954 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27954step0 = (fun i j => raw27954 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27954step0 raw27954; decide +kernel
      have hl : raw27954step0Labels = raw27954Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27954 raw27954Labels permutation346 hz
    mixedMoment B raw27954step0 raw27954step0Labels = mixedMoment B raw27954step1 raw27954step1Labels := by
      have ha : raw27954step1 = (fun i j => raw27954step0 (permutation151 i) (permutation7 j)) := by apply Matrix.ext; unfold raw27954step1 raw27954step0; decide +kernel
      have hl : raw27954step1Labels = raw27954step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27954step0 raw27954step0Labels permutation151 permutation7
    mixedMoment B raw27954step1 raw27954step1Labels = mixedMoment B raw27954step2 raw27954step2Labels := by
      have ha : raw27954step2 = -raw27954step1 := by apply Matrix.ext; change ∀ i j, raw27954step2 i j = -(raw27954step1 i j); unfold raw27954step2 raw27954step1; decide +kernel
      have hl : raw27954step2Labels = raw27954step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw27954step2 raw27954step2Labels = mixedMoment B raw27954step3 raw27954step3Labels := by
      have ha : raw27954step3 = raw27954step2 := by apply Matrix.ext; unfold raw27954step3 raw27954step2; decide +kernel
      have hl : raw27954step2Labels = labelEmbedding10 ∘ raw27954step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27954step2 raw27954step2Labels raw27954step3Labels labelEmbedding10 hl
    _ = mixedMoment B node4741 node4741Labels := by rfl

theorem canonical27958 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27958 raw27958Labels = mixedMoment B node4742 node4742Labels := by
  calc
    mixedMoment B raw27958 raw27958Labels = mixedMoment B raw27958step0 raw27958step0Labels := by
      have hz : ∀ j, raw27958 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27958step0 = (fun i j => raw27958 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27958step0 raw27958; decide +kernel
      have hl : raw27958step0Labels = raw27958Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27958 raw27958Labels permutation346 hz
    mixedMoment B raw27958step0 raw27958step0Labels = mixedMoment B raw27958step1 raw27958step1Labels := by
      have ha : raw27958step1 = (fun i j => raw27958step0 (permutation151 i) (permutation7 j)) := by apply Matrix.ext; unfold raw27958step1 raw27958step0; decide +kernel
      have hl : raw27958step1Labels = raw27958step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27958step0 raw27958step0Labels permutation151 permutation7
    mixedMoment B raw27958step1 raw27958step1Labels = mixedMoment B raw27958step2 raw27958step2Labels := by
      have ha : raw27958step2 = -raw27958step1 := by apply Matrix.ext; change ∀ i j, raw27958step2 i j = -(raw27958step1 i j); unfold raw27958step2 raw27958step1; decide +kernel
      have hl : raw27958step2Labels = raw27958step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw27958step2 raw27958step2Labels = mixedMoment B raw27958step3 raw27958step3Labels := by
      have ha : raw27958step3 = raw27958step2 := by apply Matrix.ext; unfold raw27958step3 raw27958step2; decide +kernel
      have hl : raw27958step2Labels = labelEmbedding10 ∘ raw27958step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27958step2 raw27958step2Labels raw27958step3Labels labelEmbedding10 hl
    _ = mixedMoment B node4742 node4742Labels := by rfl

theorem canonical27962 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27962 raw27962Labels = mixedMoment B node4729 node4729Labels := by
  calc
    mixedMoment B raw27962 raw27962Labels = mixedMoment B raw27962step0 raw27962step0Labels := by
      have ha : raw27962step0 = (fun i j => raw27962 (permutation682 i) (permutation7 j)) := by apply Matrix.ext; unfold raw27962step0 raw27962; decide +kernel
      have hl : raw27962step0Labels = raw27962Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27962 raw27962Labels permutation682 permutation7
    mixedMoment B raw27962step0 raw27962step0Labels = mixedMoment B raw27962step1 raw27962step1Labels := by
      have ha : raw27962step1 = -raw27962step0 := by apply Matrix.ext; change ∀ i j, raw27962step1 i j = -(raw27962step0 i j); unfold raw27962step1 raw27962step0; decide +kernel
      have hl : raw27962step1Labels = raw27962step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw27962step1 raw27962step1Labels = mixedMoment B raw27962step2 raw27962step2Labels := by
      have ha : raw27962step2 = raw27962step1 := by apply Matrix.ext; unfold raw27962step2 raw27962step1; decide +kernel
      have hl : raw27962step1Labels = labelEmbedding10 ∘ raw27962step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27962step1 raw27962step1Labels raw27962step2Labels labelEmbedding10 hl
    _ = mixedMoment B node4729 node4729Labels := by rfl

theorem canonical27967 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27967 raw27967Labels = mixedMoment B node4747 node4747Labels := by
  calc
    mixedMoment B raw27967 raw27967Labels = mixedMoment B raw27967step0 raw27967step0Labels := by
      have hz : ∀ j, raw27967 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27967step0 = (fun i j => raw27967 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27967step0 raw27967; decide +kernel
      have hl : raw27967step0Labels = raw27967Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27967 raw27967Labels permutation346 hz
    mixedMoment B raw27967step0 raw27967step0Labels = mixedMoment B raw27967step1 raw27967step1Labels := by
      have ha : raw27967step1 = (fun i j => raw27967step0 (permutation151 i) (permutation7 j)) := by apply Matrix.ext; unfold raw27967step1 raw27967step0; decide +kernel
      have hl : raw27967step1Labels = raw27967step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27967step0 raw27967step0Labels permutation151 permutation7
    mixedMoment B raw27967step1 raw27967step1Labels = mixedMoment B raw27967step2 raw27967step2Labels := by
      have ha : raw27967step2 = -raw27967step1 := by apply Matrix.ext; change ∀ i j, raw27967step2 i j = -(raw27967step1 i j); unfold raw27967step2 raw27967step1; decide +kernel
      have hl : raw27967step2Labels = raw27967step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw27967step2 raw27967step2Labels = mixedMoment B raw27967step3 raw27967step3Labels := by
      have ha : raw27967step3 = raw27967step2 := by apply Matrix.ext; unfold raw27967step3 raw27967step2; decide +kernel
      have hl : raw27967step2Labels = labelEmbedding10 ∘ raw27967step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27967step2 raw27967step2Labels raw27967step3Labels labelEmbedding10 hl
    _ = mixedMoment B node4747 node4747Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical219
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical28125 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28125 raw28125Labels = mixedMoment B node4804 node4804Labels := by
  calc
    mixedMoment B raw28125 raw28125Labels = mixedMoment B raw28125step0 raw28125step0Labels := by
      have hz : ∀ j, raw28125 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28125step0 = (fun i j => raw28125 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28125step0 raw28125; decide +kernel
      have hl : raw28125step0Labels = raw28125Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28125 raw28125Labels permutation346 hz
    mixedMoment B raw28125step0 raw28125step0Labels = mixedMoment B raw28125step1 raw28125step1Labels := by
      have ha : raw28125step1 = (fun i j => raw28125step0 (permutation151 i) (permutation7 j)) := by apply Matrix.ext; unfold raw28125step1 raw28125step0; decide +kernel
      have hl : raw28125step1Labels = raw28125step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28125step0 raw28125step0Labels permutation151 permutation7
    mixedMoment B raw28125step1 raw28125step1Labels = mixedMoment B raw28125step2 raw28125step2Labels := by
      have ha : raw28125step2 = -raw28125step1 := by apply Matrix.ext; change ∀ i j, raw28125step2 i j = -(raw28125step1 i j); unfold raw28125step2 raw28125step1; decide +kernel
      have hl : raw28125step2Labels = raw28125step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw28125step2 raw28125step2Labels = mixedMoment B raw28125step3 raw28125step3Labels := by
      have ha : raw28125step3 = raw28125step2 := by apply Matrix.ext; unfold raw28125step3 raw28125step2; decide +kernel
      have hl : raw28125step2Labels = labelEmbedding10 ∘ raw28125step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28125step2 raw28125step2Labels raw28125step3Labels labelEmbedding10 hl
    _ = mixedMoment B node4804 node4804Labels := by rfl

theorem canonical28126 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28126 raw28126Labels = mixedMoment B node4779 node4779Labels := by
  calc
    mixedMoment B raw28126 raw28126Labels = mixedMoment B raw28126step0 raw28126step0Labels := by
      have ha : raw28126step0 = (fun i j => raw28126 (permutation682 i) (permutation7 j)) := by apply Matrix.ext; unfold raw28126step0 raw28126; decide +kernel
      have hl : raw28126step0Labels = raw28126Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28126 raw28126Labels permutation682 permutation7
    mixedMoment B raw28126step0 raw28126step0Labels = mixedMoment B raw28126step1 raw28126step1Labels := by
      have ha : raw28126step1 = -raw28126step0 := by apply Matrix.ext; change ∀ i j, raw28126step1 i j = -(raw28126step0 i j); unfold raw28126step1 raw28126step0; decide +kernel
      have hl : raw28126step1Labels = raw28126step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw28126step1 raw28126step1Labels = mixedMoment B raw28126step2 raw28126step2Labels := by
      have ha : raw28126step2 = raw28126step1 := by apply Matrix.ext; unfold raw28126step2 raw28126step1; decide +kernel
      have hl : raw28126step1Labels = labelEmbedding10 ∘ raw28126step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28126step1 raw28126step1Labels raw28126step2Labels labelEmbedding10 hl
    _ = mixedMoment B node4779 node4779Labels := by rfl

theorem canonical28127 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28127 raw28127Labels = mixedMoment B node4418 node4418Labels := by
  calc
    mixedMoment B raw28127 raw28127Labels = mixedMoment B raw28127step0 raw28127step0Labels := by
      have hz : ∀ j, raw28127 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28127step0 = (fun i j => raw28127 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28127step0 raw28127; decide +kernel
      have hl : raw28127step0Labels = raw28127Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28127 raw28127Labels permutation346 hz
    mixedMoment B raw28127step0 raw28127step0Labels = mixedMoment B raw28127step1 raw28127step1Labels := by
      have ha : raw28127step1 = (fun i j => raw28127step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28127step1 raw28127step0; decide +kernel
      have hl : raw28127step1Labels = raw28127step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28127step0 raw28127step0Labels permutation151 permutation2
    _ = mixedMoment B node4418 node4418Labels := by rfl

theorem canonical28128 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28128 raw28128Labels = mixedMoment B node4808 node4808Labels := by
  calc
    mixedMoment B raw28128 raw28128Labels = mixedMoment B raw28128step0 raw28128step0Labels := by
      have hz : ∀ j, raw28128 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28128step0 = (fun i j => raw28128 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28128step0 raw28128; decide +kernel
      have hl : raw28128step0Labels = raw28128Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28128 raw28128Labels permutation346 hz
    mixedMoment B raw28128step0 raw28128step0Labels = mixedMoment B raw28128step1 raw28128step1Labels := by
      have ha : raw28128step1 = (fun i j => raw28128step0 (permutation151 i) (permutation7 j)) := by apply Matrix.ext; unfold raw28128step1 raw28128step0; decide +kernel
      have hl : raw28128step1Labels = raw28128step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28128step0 raw28128step0Labels permutation151 permutation7
    mixedMoment B raw28128step1 raw28128step1Labels = mixedMoment B raw28128step2 raw28128step2Labels := by
      have ha : raw28128step2 = -raw28128step1 := by apply Matrix.ext; change ∀ i j, raw28128step2 i j = -(raw28128step1 i j); unfold raw28128step2 raw28128step1; decide +kernel
      have hl : raw28128step2Labels = raw28128step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw28128step2 raw28128step2Labels = mixedMoment B raw28128step3 raw28128step3Labels := by
      have ha : raw28128step3 = raw28128step2 := by apply Matrix.ext; unfold raw28128step3 raw28128step2; decide +kernel
      have hl : raw28128step2Labels = labelEmbedding10 ∘ raw28128step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28128step2 raw28128step2Labels raw28128step3Labels labelEmbedding10 hl
    _ = mixedMoment B node4808 node4808Labels := by rfl

theorem canonical28129 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28129 raw28129Labels = mixedMoment B node4780 node4780Labels := by
  calc
    mixedMoment B raw28129 raw28129Labels = mixedMoment B raw28129step0 raw28129step0Labels := by
      have ha : raw28129step0 = (fun i j => raw28129 (permutation682 i) (permutation7 j)) := by apply Matrix.ext; unfold raw28129step0 raw28129; decide +kernel
      have hl : raw28129step0Labels = raw28129Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28129 raw28129Labels permutation682 permutation7
    mixedMoment B raw28129step0 raw28129step0Labels = mixedMoment B raw28129step1 raw28129step1Labels := by
      have ha : raw28129step1 = -raw28129step0 := by apply Matrix.ext; change ∀ i j, raw28129step1 i j = -(raw28129step0 i j); unfold raw28129step1 raw28129step0; decide +kernel
      have hl : raw28129step1Labels = raw28129step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw28129step1 raw28129step1Labels = mixedMoment B raw28129step2 raw28129step2Labels := by
      have ha : raw28129step2 = raw28129step1 := by apply Matrix.ext; unfold raw28129step2 raw28129step1; decide +kernel
      have hl : raw28129step1Labels = labelEmbedding10 ∘ raw28129step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28129step1 raw28129step1Labels raw28129step2Labels labelEmbedding10 hl
    _ = mixedMoment B node4780 node4780Labels := by rfl

theorem canonical28130 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28130 raw28130Labels = mixedMoment B node4420 node4420Labels := by
  calc
    mixedMoment B raw28130 raw28130Labels = mixedMoment B raw28130step0 raw28130step0Labels := by
      have hz : ∀ j, raw28130 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28130step0 = (fun i j => raw28130 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28130step0 raw28130; decide +kernel
      have hl : raw28130step0Labels = raw28130Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28130 raw28130Labels permutation346 hz
    mixedMoment B raw28130step0 raw28130step0Labels = mixedMoment B raw28130step1 raw28130step1Labels := by
      have ha : raw28130step1 = (fun i j => raw28130step0 (permutation150 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28130step1 raw28130step0; decide +kernel
      have hl : raw28130step1Labels = raw28130step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28130step0 raw28130step0Labels permutation150 permutation2
    _ = mixedMoment B node4420 node4420Labels := by rfl

theorem canonical28131 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28131 raw28131Labels = mixedMoment B node4793 node4793Labels := by
  calc
    mixedMoment B raw28131 raw28131Labels = mixedMoment B raw28131step0 raw28131step0Labels := by
      have ha : raw28131step0 = (fun i j => raw28131 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw28131step0 raw28131; decide +kernel
      have hl : raw28131step0Labels = raw28131Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28131 raw28131Labels permutation152 permutation6
    mixedMoment B raw28131step0 raw28131step0Labels = mixedMoment B raw28131step1 raw28131step1Labels := by
      have ha : raw28131step1 = raw28131step0 := by apply Matrix.ext; unfold raw28131step1 raw28131step0; decide +kernel
      have hl : raw28131step0Labels = labelEmbedding9 ∘ raw28131step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28131step0 raw28131step0Labels raw28131step1Labels labelEmbedding9 hl
    _ = mixedMoment B node4793 node4793Labels := by rfl

theorem canonical28132 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28132 raw28132Labels = mixedMoment B node4792 node4792Labels := by
  calc
    mixedMoment B raw28132 raw28132Labels = mixedMoment B raw28132step0 raw28132step0Labels := by
      have ha : raw28132step0 = (fun i j => raw28132 (permutation682 i) (permutation7 j)) := by apply Matrix.ext; unfold raw28132step0 raw28132; decide +kernel
      have hl : raw28132step0Labels = raw28132Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28132 raw28132Labels permutation682 permutation7
    mixedMoment B raw28132step0 raw28132step0Labels = mixedMoment B raw28132step1 raw28132step1Labels := by
      have ha : raw28132step1 = -raw28132step0 := by apply Matrix.ext; change ∀ i j, raw28132step1 i j = -(raw28132step0 i j); unfold raw28132step1 raw28132step0; decide +kernel
      have hl : raw28132step1Labels = raw28132step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw28132step1 raw28132step1Labels = mixedMoment B raw28132step2 raw28132step2Labels := by
      have ha : raw28132step2 = raw28132step1 := by apply Matrix.ext; unfold raw28132step2 raw28132step1; decide +kernel
      have hl : raw28132step1Labels = labelEmbedding10 ∘ raw28132step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28132step1 raw28132step1Labels raw28132step2Labels labelEmbedding10 hl
    _ = mixedMoment B node4792 node4792Labels := by rfl

theorem canonical28133 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28133 raw28133Labels = mixedMoment B node4414 node4414Labels := by
  calc
    mixedMoment B raw28133 raw28133Labels = mixedMoment B raw28133step0 raw28133step0Labels := by
      have ha : raw28133step0 = (fun i j => raw28133 (permutation682 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28133step0 raw28133; decide +kernel
      have hl : raw28133step0Labels = raw28133Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28133 raw28133Labels permutation682 permutation2
    _ = mixedMoment B node4414 node4414Labels := by rfl

theorem canonical28134 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28134 raw28134Labels = mixedMoment B node4819 node4819Labels := by
  calc
    mixedMoment B raw28134 raw28134Labels = mixedMoment B raw28134step0 raw28134step0Labels := by
      have hz : ∀ j, raw28134 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28134step0 = (fun i j => raw28134 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28134step0 raw28134; decide +kernel
      have hl : raw28134step0Labels = raw28134Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28134 raw28134Labels permutation346 hz
    mixedMoment B raw28134step0 raw28134step0Labels = mixedMoment B raw28134step1 raw28134step1Labels := by
      have ha : raw28134step1 = (fun i j => raw28134step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw28134step1 raw28134step0; decide +kernel
      have hl : raw28134step1Labels = raw28134step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28134step0 raw28134step0Labels permutation32 permutation6
    mixedMoment B raw28134step1 raw28134step1Labels = mixedMoment B raw28134step2 raw28134step2Labels := by
      have ha : raw28134step2 = raw28134step1 := by apply Matrix.ext; unfold raw28134step2 raw28134step1; decide +kernel
      have hl : raw28134step1Labels = labelEmbedding9 ∘ raw28134step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28134step1 raw28134step1Labels raw28134step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4819 node4819Labels := by rfl

theorem canonical28135 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28135 raw28135Labels = mixedMoment B node4817 node4817Labels := by
  calc
    mixedMoment B raw28135 raw28135Labels = mixedMoment B raw28135step0 raw28135step0Labels := by
      have hz : ∀ j, raw28135 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28135step0 = (fun i j => raw28135 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28135step0 raw28135; decide +kernel
      have hl : raw28135step0Labels = raw28135Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28135 raw28135Labels permutation346 hz
    mixedMoment B raw28135step0 raw28135step0Labels = mixedMoment B raw28135step1 raw28135step1Labels := by
      have ha : raw28135step1 = (fun i j => raw28135step0 (permutation151 i) (permutation7 j)) := by apply Matrix.ext; unfold raw28135step1 raw28135step0; decide +kernel
      have hl : raw28135step1Labels = raw28135step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28135step0 raw28135step0Labels permutation151 permutation7
    mixedMoment B raw28135step1 raw28135step1Labels = mixedMoment B raw28135step2 raw28135step2Labels := by
      have ha : raw28135step2 = -raw28135step1 := by apply Matrix.ext; change ∀ i j, raw28135step2 i j = -(raw28135step1 i j); unfold raw28135step2 raw28135step1; decide +kernel
      have hl : raw28135step2Labels = raw28135step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw28135step2 raw28135step2Labels = mixedMoment B raw28135step3 raw28135step3Labels := by
      have ha : raw28135step3 = raw28135step2 := by apply Matrix.ext; unfold raw28135step3 raw28135step2; decide +kernel
      have hl : raw28135step2Labels = labelEmbedding10 ∘ raw28135step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28135step2 raw28135step2Labels raw28135step3Labels labelEmbedding10 hl
    _ = mixedMoment B node4817 node4817Labels := by rfl

theorem canonical28136 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28136 raw28136Labels = mixedMoment B node4783 node4783Labels := by
  calc
    mixedMoment B raw28136 raw28136Labels = mixedMoment B raw28136step0 raw28136step0Labels := by
      have ha : raw28136step0 = (fun i j => raw28136 (permutation682 i) (permutation7 j)) := by apply Matrix.ext; unfold raw28136step0 raw28136; decide +kernel
      have hl : raw28136step0Labels = raw28136Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28136 raw28136Labels permutation682 permutation7
    mixedMoment B raw28136step0 raw28136step0Labels = mixedMoment B raw28136step1 raw28136step1Labels := by
      have ha : raw28136step1 = -raw28136step0 := by apply Matrix.ext; change ∀ i j, raw28136step1 i j = -(raw28136step0 i j); unfold raw28136step1 raw28136step0; decide +kernel
      have hl : raw28136step1Labels = raw28136step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw28136step1 raw28136step1Labels = mixedMoment B raw28136step2 raw28136step2Labels := by
      have ha : raw28136step2 = raw28136step1 := by apply Matrix.ext; unfold raw28136step2 raw28136step1; decide +kernel
      have hl : raw28136step1Labels = labelEmbedding10 ∘ raw28136step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28136step1 raw28136step1Labels raw28136step2Labels labelEmbedding10 hl
    _ = mixedMoment B node4783 node4783Labels := by rfl

theorem canonical28137 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28137 raw28137Labels = mixedMoment B node4425 node4425Labels := by
  calc
    mixedMoment B raw28137 raw28137Labels = mixedMoment B raw28137step0 raw28137step0Labels := by
      have hz : ∀ j, raw28137 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28137step0 = (fun i j => raw28137 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28137step0 raw28137; decide +kernel
      have hl : raw28137step0Labels = raw28137Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28137 raw28137Labels permutation346 hz
    mixedMoment B raw28137step0 raw28137step0Labels = mixedMoment B raw28137step1 raw28137step1Labels := by
      have ha : raw28137step1 = (fun i j => raw28137step0 (permutation148 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28137step1 raw28137step0; decide +kernel
      have hl : raw28137step1Labels = raw28137step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28137step0 raw28137step0Labels permutation148 permutation2
    _ = mixedMoment B node4425 node4425Labels := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons73
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singleton4729 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4729 node4729Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1898 node1898Labels + mixedMoment B node1940 node1940Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1644 singletonSmall4729
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4729) = raw1644Labels := by decide +kernel
  rw [hl, canonical1644 B hB] at h
  have hc0 : mixedMoment B raw1644 (Fin.cases (0 : Fin 2) singletonSmall4729) =
      mixedMoment B node1898 node1898Labels := by
    have ha : raw1644 = raw1645 := by apply Matrix.ext; unfold raw1644 raw1645; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4729 = raw1645Labels := by decide +kernel
    rw [ha, hj, canonical1645 B hB]
  have hc1 : mixedMoment B raw1644 (Fin.cases (1 : Fin 2) singletonSmall4729) =
      mixedMoment B node1940 node1940Labels := by
    have ha : raw1644 = raw1646 := by apply Matrix.ext; unfold raw1644 raw1646; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4729 = raw1646Labels := by decide +kernel
    rw [ha, hj, canonical1646 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons74
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singleton4742 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4742 node4742Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1915 node1915Labels + mixedMoment B node1946 node1946Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1659 singletonSmall4742
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4742) = raw1659Labels := by decide +kernel
  rw [hl, canonical1659 B hB] at h
  have hc0 : mixedMoment B raw1659 (Fin.cases (0 : Fin 2) singletonSmall4742) =
      mixedMoment B node1915 node1915Labels := by
    have ha : raw1659 = raw1660 := by apply Matrix.ext; unfold raw1659 raw1660; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4742 = raw1660Labels := by decide +kernel
    rw [ha, hj, canonical1660 B hB]
  have hc1 : mixedMoment B raw1659 (Fin.cases (1 : Fin 2) singletonSmall4742) =
      mixedMoment B node1946 node1946Labels := by
    have ha : raw1659 = raw1661 := by apply Matrix.ext; unfold raw1659 raw1661; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4742 = raw1661Labels := by decide +kernel
    rw [ha, hj, canonical1661 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4747 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4747 node4747Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1926 node1926Labels + mixedMoment B node1948 node1948Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1668 singletonSmall4747
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4747) = raw1668Labels := by decide +kernel
  rw [hl, canonical1668 B hB] at h
  have hc0 : mixedMoment B raw1668 (Fin.cases (0 : Fin 2) singletonSmall4747) =
      mixedMoment B node1926 node1926Labels := by
    have ha : raw1668 = raw1669 := by apply Matrix.ext; unfold raw1668 raw1669; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4747 = raw1669Labels := by decide +kernel
    rw [ha, hj, canonical1669 B hB]
  have hc1 : mixedMoment B raw1668 (Fin.cases (1 : Fin 2) singletonSmall4747) =
      mixedMoment B node1948 node1948Labels := by
    have ha : raw1668 = raw1670 := by apply Matrix.ext; unfold raw1668 raw1670; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4747 = raw1670Labels := by decide +kernel
    rw [ha, hj, canonical1670 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4779 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4779 node4779Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1987 node1987Labels + mixedMoment B node1996 node1996Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1713 singletonSmall4779
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4779) = raw1713Labels := by decide +kernel
  rw [hl, canonical1713 B hB] at h
  have hc0 : mixedMoment B raw1713 (Fin.cases (0 : Fin 2) singletonSmall4779) =
      mixedMoment B node1987 node1987Labels := by
    have ha : raw1713 = raw1714 := by apply Matrix.ext; unfold raw1713 raw1714; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4779 = raw1714Labels := by decide +kernel
    rw [ha, hj, canonical1714 B hB]
  have hc1 : mixedMoment B raw1713 (Fin.cases (1 : Fin 2) singletonSmall4779) =
      mixedMoment B node1996 node1996Labels := by
    have ha : raw1713 = raw1715 := by apply Matrix.ext; unfold raw1713 raw1715; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4779 = raw1715Labels := by decide +kernel
    rw [ha, hj, canonical1715 B hB]
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

theorem singleton4807 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4807 node4807Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2025 node2025Labels + mixedMoment B node2224 node2224Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1743 singletonSmall4807
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4807) = raw1743Labels := by decide +kernel
  rw [hl, canonical1743 B hB] at h
  have hc0 : mixedMoment B raw1743 (Fin.cases (0 : Fin 2) singletonSmall4807) =
      mixedMoment B node2025 node2025Labels := by
    have ha : raw1743 = raw1744 := by apply Matrix.ext; unfold raw1743 raw1744; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4807 = raw1744Labels := by decide +kernel
    rw [ha, hj, canonical1744 B hB]
  have hc1 : mixedMoment B raw1743 (Fin.cases (1 : Fin 2) singletonSmall4807) =
      mixedMoment B node2224 node2224Labels := by
    have ha : raw1743 = raw1745 := by apply Matrix.ext; unfold raw1743 raw1745; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4807 = raw1745Labels := by decide +kernel
    rw [ha, hj, canonical1745 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4843 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4843 node4843Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2062 node2062Labels + mixedMoment B node2230 node2230Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1773 singletonSmall4843
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4843) = raw1773Labels := by decide +kernel
  rw [hl, canonical1773 B hB] at h
  have hc0 : mixedMoment B raw1773 (Fin.cases (0 : Fin 2) singletonSmall4843) =
      mixedMoment B node2062 node2062Labels := by
    have ha : raw1773 = raw1774 := by apply Matrix.ext; unfold raw1773 raw1774; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4843 = raw1774Labels := by decide +kernel
    rw [ha, hj, canonical1774 B hB]
  have hc1 : mixedMoment B raw1773 (Fin.cases (1 : Fin 2) singletonSmall4843) =
      mixedMoment B node2230 node2230Labels := by
    have ha : raw1773 = raw1775 := by apply Matrix.ext; unfold raw1773 raw1775; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4843 = raw1775Labels := by decide +kernel
    rw [ha, hj, canonical1775 B hB]
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

theorem singleton4871 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4871 node4871Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2112 node2112Labels + mixedMoment B node2287 node2287Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1803 singletonSmall4871
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4871) = raw1803Labels := by decide +kernel
  rw [hl, canonical1803 B hB] at h
  have hc0 : mixedMoment B raw1803 (Fin.cases (0 : Fin 2) singletonSmall4871) =
      mixedMoment B node2112 node2112Labels := by
    have ha : raw1803 = raw1804 := by apply Matrix.ext; unfold raw1803 raw1804; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4871 = raw1804Labels := by decide +kernel
    rw [ha, hj, canonical1804 B hB]
  have hc1 : mixedMoment B raw1803 (Fin.cases (1 : Fin 2) singletonSmall4871) =
      mixedMoment B node2287 node2287Labels := by
    have ha : raw1803 = raw1805 := by apply Matrix.ext; unfold raw1803 raw1805; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4871 = raw1805Labels := by decide +kernel
    rw [ha, hj, canonical1805 B hB]
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

theorem singleton5078 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5078 node5078Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2485 node2485Labels + mixedMoment B node3481 node3481Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2103 singletonSmall5078
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5078) = raw2103Labels := by decide +kernel
  rw [hl, canonical2103 B hB] at h
  have hc0 : mixedMoment B raw2103 (Fin.cases (0 : Fin 2) singletonSmall5078) =
      mixedMoment B node2485 node2485Labels := by
    have ha : raw2103 = raw2104 := by apply Matrix.ext; unfold raw2103 raw2104; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5078 = raw2104Labels := by decide +kernel
    rw [ha, hj, canonical2104 B hB]
  have hc1 : mixedMoment B raw2103 (Fin.cases (1 : Fin 2) singletonSmall5078) =
      mixedMoment B node3481 node3481Labels := by
    have ha : raw2103 = raw2105 := by apply Matrix.ext; unfold raw2103 raw2105; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5078 = raw2105Labels := by decide +kernel
    rw [ha, hj, canonical2105 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

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

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound29
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound1898 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1898 node1898Labels = Sparse.eval nodeValue1898 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1898) = mixedMoment B node1898 node1898Labels := rfl
  simpa [nodeValue1898, Sparse.eval] using hc.symm

theorem sound1915 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1915 node1915Labels = Sparse.eval nodeValue1915 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1915) = mixedMoment B node1915 node1915Labels := rfl
  simpa [nodeValue1915, Sparse.eval] using hc.symm

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

theorem sound1926 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1926 node1926Labels = Sparse.eval nodeValue1926 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1926) = mixedMoment B node1926 node1926Labels := rfl
  simpa [nodeValue1926, Sparse.eval] using hc.symm

theorem sound1940 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1940 node1940Labels = Sparse.eval nodeValue1940 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1940) = mixedMoment B node1940 node1940Labels := rfl
  simpa [nodeValue1940, Sparse.eval] using hc.symm

theorem sound1946 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1946 node1946Labels = Sparse.eval nodeValue1946 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1946) = mixedMoment B node1946 node1946Labels := rfl
  simpa [nodeValue1946, Sparse.eval] using hc.symm

theorem sound1948 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1948 node1948Labels = Sparse.eval nodeValue1948 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1948) = mixedMoment B node1948 node1948Labels := rfl
  simpa [nodeValue1948, Sparse.eval] using hc.symm

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

theorem sound1987 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1987 node1987Labels = Sparse.eval nodeValue1987 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1987) = mixedMoment B node1987 node1987Labels := rfl
  simpa [nodeValue1987, Sparse.eval] using hc.symm

theorem sound1996 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1996 node1996Labels = Sparse.eval nodeValue1996 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1996) = mixedMoment B node1996 node1996Labels := rfl
  simpa [nodeValue1996, Sparse.eval] using hc.symm

theorem sound2022 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2022 node2022Labels = Sparse.eval nodeValue2022 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2022) = mixedMoment B node2022 node2022Labels := rfl
  simpa [nodeValue2022, Sparse.eval] using hc.symm

theorem sound2025 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2025 node2025Labels = Sparse.eval nodeValue2025 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2025) = mixedMoment B node2025 node2025Labels := rfl
  simpa [nodeValue2025, Sparse.eval] using hc.symm

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

theorem sound2062 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2062 node2062Labels = Sparse.eval nodeValue2062 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2062) = mixedMoment B node2062 node2062Labels := rfl
  simpa [nodeValue2062, Sparse.eval] using hc.symm

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

theorem sound2112 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2112 node2112Labels = Sparse.eval nodeValue2112 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2112) = mixedMoment B node2112 node2112Labels := rfl
  simpa [nodeValue2112, Sparse.eval] using hc.symm

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

theorem sound2224 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2224 node2224Labels = Sparse.eval nodeValue2224 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2224) = mixedMoment B node2224 node2224Labels := rfl
  simpa [nodeValue2224, Sparse.eval] using hc.symm

theorem sound2230 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2230 node2230Labels = Sparse.eval nodeValue2230 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2230) = mixedMoment B node2230 node2230Labels := rfl
  simpa [nodeValue2230, Sparse.eval] using hc.symm

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

theorem sound2287 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2287 node2287Labels = Sparse.eval nodeValue2287 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2287) = mixedMoment B node2287 node2287Labels := rfl
  simpa [nodeValue2287, Sparse.eval] using hc.symm

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

theorem sound2485 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2485 node2485Labels = Sparse.eval nodeValue2485 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2485) = mixedMoment B node2485 node2485Labels := rfl
  simpa [nodeValue2485, Sparse.eval] using hc.symm

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

theorem sound3481 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3481 node3481Labels = Sparse.eval nodeValue3481 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3481) = mixedMoment B node3481 node3481Labels := rfl
  simpa [nodeValue3481, Sparse.eval] using hc.symm

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

theorem sound4414 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4414 node4414Labels = Sparse.eval nodeValue4414 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4414) = mixedMoment B node4414 node4414Labels := rfl
  simpa [nodeValue4414, Sparse.eval] using hc.symm

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

theorem sound4420 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4420 node4420Labels = Sparse.eval nodeValue4420 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4420) = mixedMoment B node4420 node4420Labels := rfl
  simpa [nodeValue4420, Sparse.eval] using hc.symm

theorem sound4425 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4425 node4425Labels = Sparse.eval nodeValue4425 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4425) = mixedMoment B node4425 node4425Labels := rfl
  simpa [nodeValue4425, Sparse.eval] using hc.symm

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

theorem sound4486 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4486 node4486Labels = Sparse.eval nodeValue4486 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4486) = mixedMoment B node4486 node4486Labels := rfl
  simpa [nodeValue4486, Sparse.eval] using hc.symm

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

theorem sound4729 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4729 node4729Labels = Sparse.eval nodeValue4729 (mixedVector B) := by
  have h := singleton4729 B _hB
  rw [sound1898 B _hB _hF, sound1940 B _hB _hF] at h
  norm_num [nodeValue4729, nodeValue1898, nodeValue1940, Sparse.eval] at h ⊢
  linarith only [h]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros74
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero4741 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4741 node4741Labels = 0 := by
  exact mixedMoment_order_one B hB node4741 node4741Labels 1
    (by decide +kernel) (by decide +kernel)

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound74
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound4741 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4741 node4741Labels = Sparse.eval nodeValue4741 (mixedVector B) := by
  simpa only [nodeValue4741, Sparse.eval_nil] using zero4741 B _hB _hF

theorem sound4742 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4742 node4742Labels = Sparse.eval nodeValue4742 (mixedVector B) := by
  have h := singleton4742 B _hB
  rw [sound1915 B _hB _hF, sound1946 B _hB _hF] at h
  norm_num [nodeValue4742, nodeValue1915, nodeValue1946, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4747 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4747 node4747Labels = Sparse.eval nodeValue4747 (mixedVector B) := by
  have h := singleton4747 B _hB
  rw [sound1926 B _hB _hF, sound1948 B _hB _hF] at h
  norm_num [nodeValue4747, nodeValue1926, nodeValue1948, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4779 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4779 node4779Labels = Sparse.eval nodeValue4779 (mixedVector B) := by
  have h := singleton4779 B _hB
  rw [sound1987 B _hB _hF, sound1996 B _hB _hF] at h
  norm_num [nodeValue4779, nodeValue1987, nodeValue1996, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4780 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4780 node4780Labels = Sparse.eval nodeValue4780 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4780) = mixedMoment B node4780 node4780Labels := rfl
  simpa [nodeValue4780, Sparse.eval] using hc.symm

theorem sound4783 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4783 node4783Labels = Sparse.eval nodeValue4783 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4783) = mixedMoment B node4783 node4783Labels := rfl
  simpa [nodeValue4783, Sparse.eval] using hc.symm

theorem sound4792 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4792 node4792Labels = Sparse.eval nodeValue4792 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4792) = mixedMoment B node4792 node4792Labels := rfl
  simpa [nodeValue4792, Sparse.eval] using hc.symm

theorem sound4793 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4793 node4793Labels = Sparse.eval nodeValue4793 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4793) = mixedMoment B node4793 node4793Labels := rfl
  simpa [nodeValue4793, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros75
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero4841 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4841 node4841Labels = 0 := by
  exact mixedMoment_order_one B hB node4841 node4841Labels 1
    (by decide +kernel) (by decide +kernel)

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

theorem sound4807 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4807 node4807Labels = Sparse.eval nodeValue4807 (mixedVector B) := by
  have h := singleton4807 B _hB
  rw [sound2025 B _hB _hF, sound2224 B _hB _hF] at h
  norm_num [nodeValue4807, nodeValue2025, nodeValue2224, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4808 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4808 node4808Labels = Sparse.eval nodeValue4808 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4808) = mixedMoment B node4808 node4808Labels := rfl
  simpa [nodeValue4808, Sparse.eval] using hc.symm

theorem sound4817 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4817 node4817Labels = Sparse.eval nodeValue4817 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4817) = mixedMoment B node4817 node4817Labels := rfl
  simpa [nodeValue4817, Sparse.eval] using hc.symm

theorem sound4819 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4819 node4819Labels = Sparse.eval nodeValue4819 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4819) = mixedMoment B node4819 node4819Labels := rfl
  simpa [nodeValue4819, Sparse.eval] using hc.symm

theorem sound4824 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4824 node4824Labels = Sparse.eval nodeValue4824 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4824) = mixedMoment B node4824 node4824Labels := rfl
  simpa [nodeValue4824, Sparse.eval] using hc.symm

theorem sound4841 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4841 node4841Labels = Sparse.eval nodeValue4841 (mixedVector B) := by
  simpa only [nodeValue4841, Sparse.eval_nil] using zero4841 B _hB _hF

theorem sound4843 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4843 node4843Labels = Sparse.eval nodeValue4843 (mixedVector B) := by
  have h := singleton4843 B _hB
  rw [sound2062 B _hB _hF, sound2230 B _hB _hF] at h
  norm_num [nodeValue4843, nodeValue2062, nodeValue2230, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4853 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4853 node4853Labels = Sparse.eval nodeValue4853 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4853) = mixedMoment B node4853 node4853Labels := rfl
  simpa [nodeValue4853, Sparse.eval] using hc.symm

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

theorem sound4871 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4871 node4871Labels = Sparse.eval nodeValue4871 (mixedVector B) := by
  have h := singleton4871 B _hB
  rw [sound2112 B _hB _hF, sound2287 B _hB _hF] at h
  norm_num [nodeValue4871, nodeValue2112, nodeValue2287, Sparse.eval] at h ⊢
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

theorem sound5078 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5078 node5078Labels = Sparse.eval nodeValue5078 (mixedVector B) := by
  have h := singleton5078 B _hB
  rw [sound2485 B _hB _hF, sound3481 B _hB _hF] at h
  norm_num [nodeValue5078, nodeValue2485, nodeValue3481, Sparse.eval] at h ⊢
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

theorem sound5128 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5128 node5128Labels = Sparse.eval nodeValue5128 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5128) = mixedMoment B node5128 node5128Labels := rfl
  simpa [nodeValue5128, Sparse.eval] using hc.symm

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources61
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sourceEq1979 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1979 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1979 + difference 0 1) (sourceB1979 + difference 1 0) sourceC1979) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4804) := by
    have ha : (tripleCharges (sourceA1979 + difference 0 1) (sourceB1979 + difference 1 0) sourceC1979) = raw28125 := by
      apply Matrix.ext; unfold tripleCharges sourceA1979 sourceB1979 sourceC1979 difference raw28125; decide +kernel
    rw [ha]
    exact (canonical28125 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1979 + difference 0 2) (sourceB1979 + difference 2 0) sourceC1979) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4779) := by
    have ha : (tripleCharges (sourceA1979 + difference 0 2) (sourceB1979 + difference 2 0) sourceC1979) = raw28126 := by
      apply Matrix.ext; unfold tripleCharges sourceA1979 sourceB1979 sourceC1979 difference raw28126; decide +kernel
    rw [ha]
    exact (canonical28126 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1979 + difference 0 3) (sourceB1979 + difference 3 0) sourceC1979) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4841) := by
    have ha : (tripleCharges (sourceA1979 + difference 0 3) (sourceB1979 + difference 3 0) sourceC1979) = raw27642 := by
      apply Matrix.ext; unfold tripleCharges sourceA1979 sourceB1979 sourceC1979 difference raw27642; decide +kernel
    rw [ha]
    exact (canonical27642 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1979 + difference 0 4) (sourceB1979 + difference 4 0) sourceC1979) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4741) := by
    have ha : (tripleCharges (sourceA1979 + difference 0 4) (sourceB1979 + difference 4 0) sourceC1979) = raw27954 := by
      apply Matrix.ext; unfold tripleCharges sourceA1979 sourceB1979 sourceC1979 difference raw27954; decide +kernel
    rw [ha]
    exact (canonical27954 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1979 + difference 0 5) (sourceB1979 + difference 5 0) sourceC1979) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4418) := by
    have ha : (tripleCharges (sourceA1979 + difference 0 5) (sourceB1979 + difference 5 0) sourceC1979) = raw28127 := by
      apply Matrix.ext; unfold tripleCharges sourceA1979 sourceB1979 sourceC1979 difference raw28127; decide +kernel
    rw [ha]
    exact (canonical28127 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1979 + difference 1 0) (sourceB1979 + difference 0 1) sourceC1979) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4808) := by
    have ha : (tripleCharges (sourceA1979 + difference 1 0) (sourceB1979 + difference 0 1) sourceC1979) = raw28128 := by
      apply Matrix.ext; unfold tripleCharges sourceA1979 sourceB1979 sourceC1979 difference raw28128; decide +kernel
    rw [ha]
    exact (canonical28128 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1979 + difference 1 2) (sourceB1979 + difference 2 1) sourceC1979) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4780) := by
    have ha : (tripleCharges (sourceA1979 + difference 1 2) (sourceB1979 + difference 2 1) sourceC1979) = raw28129 := by
      apply Matrix.ext; unfold tripleCharges sourceA1979 sourceB1979 sourceC1979 difference raw28129; decide +kernel
    rw [ha]
    exact (canonical28129 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1979 + difference 1 3) (sourceB1979 + difference 3 1) sourceC1979) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4843) := by
    have ha : (tripleCharges (sourceA1979 + difference 1 3) (sourceB1979 + difference 3 1) sourceC1979) = raw27647 := by
      apply Matrix.ext; unfold tripleCharges sourceA1979 sourceB1979 sourceC1979 difference raw27647; decide +kernel
    rw [ha]
    exact (canonical27647 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1979 + difference 1 4) (sourceB1979 + difference 4 1) sourceC1979) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4742) := by
    have ha : (tripleCharges (sourceA1979 + difference 1 4) (sourceB1979 + difference 4 1) sourceC1979) = raw27958 := by
      apply Matrix.ext; unfold tripleCharges sourceA1979 sourceB1979 sourceC1979 difference raw27958; decide +kernel
    rw [ha]
    exact (canonical27958 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1979 + difference 1 5) (sourceB1979 + difference 5 1) sourceC1979) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4420) := by
    have ha : (tripleCharges (sourceA1979 + difference 1 5) (sourceB1979 + difference 5 1) sourceC1979) = raw28130 := by
      apply Matrix.ext; unfold tripleCharges sourceA1979 sourceB1979 sourceC1979 difference raw28130; decide +kernel
    rw [ha]
    exact (canonical28130 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1979 + difference 2 0) (sourceB1979 + difference 0 2) sourceC1979) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4793) := by
    have ha : (tripleCharges (sourceA1979 + difference 2 0) (sourceB1979 + difference 0 2) sourceC1979) = raw28131 := by
      apply Matrix.ext; unfold tripleCharges sourceA1979 sourceB1979 sourceC1979 difference raw28131; decide +kernel
    rw [ha]
    exact (canonical28131 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1979 + difference 2 1) (sourceB1979 + difference 1 2) sourceC1979) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4792) := by
    have ha : (tripleCharges (sourceA1979 + difference 2 1) (sourceB1979 + difference 1 2) sourceC1979) = raw28132 := by
      apply Matrix.ext; unfold tripleCharges sourceA1979 sourceB1979 sourceC1979 difference raw28132; decide +kernel
    rw [ha]
    exact (canonical28132 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1979 + difference 2 3) (sourceB1979 + difference 3 2) sourceC1979) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4807) := by
    have ha : (tripleCharges (sourceA1979 + difference 2 3) (sourceB1979 + difference 3 2) sourceC1979) = raw27652 := by
      apply Matrix.ext; unfold tripleCharges sourceA1979 sourceB1979 sourceC1979 difference raw27652; decide +kernel
    rw [ha]
    exact (canonical27652 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1979 + difference 2 4) (sourceB1979 + difference 4 2) sourceC1979) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4729) := by
    have ha : (tripleCharges (sourceA1979 + difference 2 4) (sourceB1979 + difference 4 2) sourceC1979) = raw27962 := by
      apply Matrix.ext; unfold tripleCharges sourceA1979 sourceB1979 sourceC1979 difference raw27962; decide +kernel
    rw [ha]
    exact (canonical27962 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1979 + difference 2 5) (sourceB1979 + difference 5 2) sourceC1979) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4414) := by
    have ha : (tripleCharges (sourceA1979 + difference 2 5) (sourceB1979 + difference 5 2) sourceC1979) = raw28133 := by
      apply Matrix.ext; unfold tripleCharges sourceA1979 sourceB1979 sourceC1979 difference raw28133; decide +kernel
    rw [ha]
    exact (canonical28133 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1979 + difference 3 0) (sourceB1979 + difference 0 3) sourceC1979) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4819) := by
    have ha : (tripleCharges (sourceA1979 + difference 3 0) (sourceB1979 + difference 0 3) sourceC1979) = raw28134 := by
      apply Matrix.ext; unfold tripleCharges sourceA1979 sourceB1979 sourceC1979 difference raw28134; decide +kernel
    rw [ha]
    exact (canonical28134 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1979 + difference 3 1) (sourceB1979 + difference 1 3) sourceC1979) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4817) := by
    have ha : (tripleCharges (sourceA1979 + difference 3 1) (sourceB1979 + difference 1 3) sourceC1979) = raw28135 := by
      apply Matrix.ext; unfold tripleCharges sourceA1979 sourceB1979 sourceC1979 difference raw28135; decide +kernel
    rw [ha]
    exact (canonical28135 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1979 + difference 3 2) (sourceB1979 + difference 2 3) sourceC1979) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4783) := by
    have ha : (tripleCharges (sourceA1979 + difference 3 2) (sourceB1979 + difference 2 3) sourceC1979) = raw28136 := by
      apply Matrix.ext; unfold tripleCharges sourceA1979 sourceB1979 sourceC1979 difference raw28136; decide +kernel
    rw [ha]
    exact (canonical28136 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1979 + difference 3 4) (sourceB1979 + difference 4 3) sourceC1979) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4747) := by
    have ha : (tripleCharges (sourceA1979 + difference 3 4) (sourceB1979 + difference 4 3) sourceC1979) = raw27967 := by
      apply Matrix.ext; unfold tripleCharges sourceA1979 sourceB1979 sourceC1979 difference raw27967; decide +kernel
    rw [ha]
    exact (canonical27967 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1979 + difference 3 5) (sourceB1979 + difference 5 3) sourceC1979) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4425) := by
    have ha : (tripleCharges (sourceA1979 + difference 3 5) (sourceB1979 + difference 5 3) sourceC1979) = raw28137 := by
      apply Matrix.ext; unfold tripleCharges sourceA1979 sourceB1979 sourceC1979 difference raw28137; decide +kernel
    rw [ha]
    exact (canonical28137 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1979 + difference 4 0) (sourceB1979 + difference 0 4) sourceC1979) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4808) := by
    have ha : (tripleCharges (sourceA1979 + difference 4 0) (sourceB1979 + difference 0 4) sourceC1979) = raw27771 := by
      apply Matrix.ext; unfold tripleCharges sourceA1979 sourceB1979 sourceC1979 difference raw27771; decide +kernel
    rw [ha]
    exact (canonical27771 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1979 + difference 4 1) (sourceB1979 + difference 1 4) sourceC1979) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4853) := by
    have ha : (tripleCharges (sourceA1979 + difference 4 1) (sourceB1979 + difference 1 4) sourceC1979) = raw27772 := by
      apply Matrix.ext; unfold tripleCharges sourceA1979 sourceB1979 sourceC1979 difference raw27772; decide +kernel
    rw [ha]
    exact (canonical27772 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1979 + difference 4 2) (sourceB1979 + difference 2 4) sourceC1979) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4824) := by
    have ha : (tripleCharges (sourceA1979 + difference 4 2) (sourceB1979 + difference 2 4) sourceC1979) = raw27773 := by
      apply Matrix.ext; unfold tripleCharges sourceA1979 sourceB1979 sourceC1979 difference raw27773; decide +kernel
    rw [ha]
    exact (canonical27773 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1979 + difference 4 3) (sourceB1979 + difference 3 4) sourceC1979) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4871) := by
    have ha : (tripleCharges (sourceA1979 + difference 4 3) (sourceB1979 + difference 3 4) sourceC1979) = raw27662 := by
      apply Matrix.ext; unfold tripleCharges sourceA1979 sourceB1979 sourceC1979 difference raw27662; decide +kernel
    rw [ha]
    exact (canonical27662 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1979 + difference 4 5) (sourceB1979 + difference 5 4) sourceC1979) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4486) := by
    have ha : (tripleCharges (sourceA1979 + difference 4 5) (sourceB1979 + difference 5 4) sourceC1979) = raw27774 := by
      apply Matrix.ext; unfold tripleCharges sourceA1979 sourceB1979 sourceC1979 difference raw27774; decide +kernel
    rw [ha]
    exact (canonical27774 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1979 + difference 5 0) (sourceB1979 + difference 0 5) sourceC1979) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4807) := by
    have ha : (tripleCharges (sourceA1979 + difference 5 0) (sourceB1979 + difference 0 5) sourceC1979) = raw27653 := by
      apply Matrix.ext; unfold tripleCharges sourceA1979 sourceB1979 sourceC1979 difference raw27653; decide +kernel
    rw [ha]
    exact (canonical27653 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1979 + difference 5 1) (sourceB1979 + difference 1 5) sourceC1979) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5078) := by
    have ha : (tripleCharges (sourceA1979 + difference 5 1) (sourceB1979 + difference 1 5) sourceC1979) = raw27654 := by
      apply Matrix.ext; unfold tripleCharges sourceA1979 sourceB1979 sourceC1979 difference raw27654; decide +kernel
    rw [ha]
    exact (canonical27654 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1979 + difference 5 2) (sourceB1979 + difference 2 5) sourceC1979) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5128) := by
    have ha : (tripleCharges (sourceA1979 + difference 5 2) (sourceB1979 + difference 2 5) sourceC1979) = raw27655 := by
      apply Matrix.ext; unfold tripleCharges sourceA1979 sourceB1979 sourceC1979 difference raw27655; decide +kernel
    rw [ha]
    exact (canonical27655 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1979 + difference 5 3) (sourceB1979 + difference 3 5) sourceC1979) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5174) := by
    have ha : (tripleCharges (sourceA1979 + difference 5 3) (sourceB1979 + difference 3 5) sourceC1979) = raw27780 := by
      apply Matrix.ext; unfold tripleCharges sourceA1979 sourceB1979 sourceC1979 difference raw27780; decide +kernel
    rw [ha]
    exact (canonical27780 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1979 + difference 5 4) (sourceB1979 + difference 4 5) sourceC1979) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5078) := by
    have ha : (tripleCharges (sourceA1979 + difference 5 4) (sourceB1979 + difference 4 5) sourceC1979) = raw27656 := by
      apply Matrix.ext; unfold tripleCharges sourceA1979 sourceB1979 sourceC1979 difference raw27656; decide +kernel
    rw [ha]
    exact (canonical27656 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1979 sourceB1979 sourceC1979
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1979, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic104
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reindexCheck1679 : Integer.Sparse.reindex keyMap MixedData.row1679 = numericRow1679 := by decide +kernel

theorem numericCheck1679 (x : Master → ℝ) : Integer.Sparse.eval numericRow1679 x =
    (8640 : ℝ) * reducedSource1679 x := by
  norm_num [numericRow1679, reducedSource1679, Integer.Sparse.eval, Sparse.eval, nodeValue4414, nodeValue4418, nodeValue4420, nodeValue4425, nodeValue4486, nodeValue4729, nodeValue4741, nodeValue4742, nodeValue4747, nodeValue4779, nodeValue4780, nodeValue4783, nodeValue4792, nodeValue4793, nodeValue4804, nodeValue4807, nodeValue4808, nodeValue4817, nodeValue4819, nodeValue4824, nodeValue4841, nodeValue4843, nodeValue4853, nodeValue4871, nodeValue5078, nodeValue5128, nodeValue5174]
  ring

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Rows104
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero1679 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1679 (mixedVector B) = 0 := by
  have h4414 : mixedVector B (Sum.inr 4414) = Sparse.eval nodeValue4414 (mixedVector B) := by
    change mixedMoment B node4414 node4414Labels = _
    exact sound4414 B hB hF
  have h4418 : mixedVector B (Sum.inr 4418) = Sparse.eval nodeValue4418 (mixedVector B) := by
    change mixedMoment B node4418 node4418Labels = _
    exact sound4418 B hB hF
  have h4420 : mixedVector B (Sum.inr 4420) = Sparse.eval nodeValue4420 (mixedVector B) := by
    change mixedMoment B node4420 node4420Labels = _
    exact sound4420 B hB hF
  have h4425 : mixedVector B (Sum.inr 4425) = Sparse.eval nodeValue4425 (mixedVector B) := by
    change mixedMoment B node4425 node4425Labels = _
    exact sound4425 B hB hF
  have h4486 : mixedVector B (Sum.inr 4486) = Sparse.eval nodeValue4486 (mixedVector B) := by
    change mixedMoment B node4486 node4486Labels = _
    exact sound4486 B hB hF
  have h4729 : mixedVector B (Sum.inr 4729) = Sparse.eval nodeValue4729 (mixedVector B) := by
    change mixedMoment B node4729 node4729Labels = _
    exact sound4729 B hB hF
  have h4741 : mixedVector B (Sum.inr 4741) = Sparse.eval nodeValue4741 (mixedVector B) := by
    change mixedMoment B node4741 node4741Labels = _
    exact sound4741 B hB hF
  have h4742 : mixedVector B (Sum.inr 4742) = Sparse.eval nodeValue4742 (mixedVector B) := by
    change mixedMoment B node4742 node4742Labels = _
    exact sound4742 B hB hF
  have h4747 : mixedVector B (Sum.inr 4747) = Sparse.eval nodeValue4747 (mixedVector B) := by
    change mixedMoment B node4747 node4747Labels = _
    exact sound4747 B hB hF
  have h4779 : mixedVector B (Sum.inr 4779) = Sparse.eval nodeValue4779 (mixedVector B) := by
    change mixedMoment B node4779 node4779Labels = _
    exact sound4779 B hB hF
  have h4780 : mixedVector B (Sum.inr 4780) = Sparse.eval nodeValue4780 (mixedVector B) := by
    change mixedMoment B node4780 node4780Labels = _
    exact sound4780 B hB hF
  have h4783 : mixedVector B (Sum.inr 4783) = Sparse.eval nodeValue4783 (mixedVector B) := by
    change mixedMoment B node4783 node4783Labels = _
    exact sound4783 B hB hF
  have h4792 : mixedVector B (Sum.inr 4792) = Sparse.eval nodeValue4792 (mixedVector B) := by
    change mixedMoment B node4792 node4792Labels = _
    exact sound4792 B hB hF
  have h4793 : mixedVector B (Sum.inr 4793) = Sparse.eval nodeValue4793 (mixedVector B) := by
    change mixedMoment B node4793 node4793Labels = _
    exact sound4793 B hB hF
  have h4804 : mixedVector B (Sum.inr 4804) = Sparse.eval nodeValue4804 (mixedVector B) := by
    change mixedMoment B node4804 node4804Labels = _
    exact sound4804 B hB hF
  have h4807 : mixedVector B (Sum.inr 4807) = Sparse.eval nodeValue4807 (mixedVector B) := by
    change mixedMoment B node4807 node4807Labels = _
    exact sound4807 B hB hF
  have h4808 : mixedVector B (Sum.inr 4808) = Sparse.eval nodeValue4808 (mixedVector B) := by
    change mixedMoment B node4808 node4808Labels = _
    exact sound4808 B hB hF
  have h4817 : mixedVector B (Sum.inr 4817) = Sparse.eval nodeValue4817 (mixedVector B) := by
    change mixedMoment B node4817 node4817Labels = _
    exact sound4817 B hB hF
  have h4819 : mixedVector B (Sum.inr 4819) = Sparse.eval nodeValue4819 (mixedVector B) := by
    change mixedMoment B node4819 node4819Labels = _
    exact sound4819 B hB hF
  have h4824 : mixedVector B (Sum.inr 4824) = Sparse.eval nodeValue4824 (mixedVector B) := by
    change mixedMoment B node4824 node4824Labels = _
    exact sound4824 B hB hF
  have h4841 : mixedVector B (Sum.inr 4841) = Sparse.eval nodeValue4841 (mixedVector B) := by
    change mixedMoment B node4841 node4841Labels = _
    exact sound4841 B hB hF
  have h4843 : mixedVector B (Sum.inr 4843) = Sparse.eval nodeValue4843 (mixedVector B) := by
    change mixedMoment B node4843 node4843Labels = _
    exact sound4843 B hB hF
  have h4853 : mixedVector B (Sum.inr 4853) = Sparse.eval nodeValue4853 (mixedVector B) := by
    change mixedMoment B node4853 node4853Labels = _
    exact sound4853 B hB hF
  have h4871 : mixedVector B (Sum.inr 4871) = Sparse.eval nodeValue4871 (mixedVector B) := by
    change mixedMoment B node4871 node4871Labels = _
    exact sound4871 B hB hF
  have h5078 : mixedVector B (Sum.inr 5078) = Sparse.eval nodeValue5078 (mixedVector B) := by
    change mixedMoment B node5078 node5078Labels = _
    exact sound5078 B hB hF
  have h5128 : mixedVector B (Sum.inr 5128) = Sparse.eval nodeValue5128 (mixedVector B) := by
    change mixedMoment B node5128 node5128Labels = _
    exact sound5128 B hB hF
  have h5174 : mixedVector B (Sum.inr 5174) = Sparse.eval nodeValue5174 (mixedVector B) := by
    change mixedMoment B node5174 node5174Labels = _
    exact sound5174_e B hB hF
  simpa only [sourceForm1979, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4414, h4418, h4420, h4425, h4486, h4729, h4741, h4742, h4747, h4779, h4780, h4783, h4792, h4793, h4804, h4807, h4808, h4817, h4819, h4824, h4841, h4843, h4853, h4871, h5078, h5128, h5174, reducedSource1679] using sourceEq1979 B hB

theorem rowSound1679_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1679 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1679, numericCheck1679, reducedZero1679 B hB hF, mul_zero]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedSourceBridge.rowSound1679_e_oai := @OAI.MUB6.Certificate.MixedSourceBridge.rowSound1679_e_oai
