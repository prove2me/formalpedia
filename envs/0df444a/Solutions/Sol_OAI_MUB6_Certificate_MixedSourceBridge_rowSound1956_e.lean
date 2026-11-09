-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedSourceBridge.rowSound1956_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-08T22:26:09.534224+00:00
-- url     : https://prove2.me/submissions/d43b7777-31d6-4415-aa46-05d92af60779

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E070
import Definitions.Def_OAIQ106E086
import Definitions.Def_OAIQ106E088
import Definitions.Def_OAIQ106E089
import Definitions.Def_OAIQ106E090
import Definitions.Def_OAIQ106E095
import Definitions.Def_OAIQ106E097
import Definitions.Def_OAIQ106E190
import Definitions.Def_OAIQ106E192
import Definitions.Def_OAIQ106E194
import Definitions.Def_OAIQ106E107
import Definitions.Def_OAIQ106E119
import Definitions.Def_OAIQ106E120
import Definitions.Def_OAIQ106E125
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical10
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical1362 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1362 raw1362Labels = mixedMoment B node4541 node4541Labels := by
  calc
    mixedMoment B raw1362 raw1362Labels = mixedMoment B raw1362step0 raw1362step0Labels := by
      have ha : raw1362step0 = (fun i j => raw1362 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1362step0 raw1362; decide +kernel
      have hl : raw1362step0Labels = raw1362Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1362 raw1362Labels permutation152 permutation4
    mixedMoment B raw1362step0 raw1362step0Labels = mixedMoment B raw1362step1 raw1362step1Labels := by
      have ha : raw1362step1 = raw1362step0 := by apply Matrix.ext; unfold raw1362step1 raw1362step0; decide +kernel
      have hl : raw1362step0Labels = labelEmbedding7 ∘ raw1362step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1362step0 raw1362step0Labels raw1362step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4541 node4541Labels := by rfl

theorem canonical1363 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1363 raw1363Labels = mixedMoment B node1126 node1126Labels := by
  calc
    mixedMoment B raw1363 raw1363Labels = mixedMoment B raw1363step0 raw1363step0Labels := by
      have ha : raw1363step0 = (fun i j => raw1363 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1363step0 raw1363; decide +kernel
      have hl : raw1363step0Labels = raw1363Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1363 raw1363Labels permutation152 permutation4
    _ = mixedMoment B node1126 node1126Labels := by rfl

theorem canonical1364 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1364 raw1364Labels = mixedMoment B node3256 node3256Labels := by
  calc
    mixedMoment B raw1364 raw1364Labels = mixedMoment B raw1364step0 raw1364step0Labels := by
      have ha : raw1364step0 = (fun i j => raw1364 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1364step0 raw1364; decide +kernel
      have hl : raw1364step0Labels = raw1364Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1364 raw1364Labels permutation152 permutation6
    mixedMoment B raw1364step0 raw1364step0Labels = mixedMoment B raw1364step1 raw1364step1Labels := by
      have ha : raw1364step1 = -raw1364step0 := by apply Matrix.ext; change ∀ i j, raw1364step1 i j = -(raw1364step0 i j); unfold raw1364step1 raw1364step0; decide +kernel
      have hl : raw1364step1Labels = raw1364step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1364step1 raw1364step1Labels = mixedMoment B raw1364step2 raw1364step2Labels := by
      have ha : raw1364step2 = raw1364step1 := by apply Matrix.ext; unfold raw1364step2 raw1364step1; decide +kernel
      have hl : raw1364step1Labels = labelEmbedding1 ∘ raw1364step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1364step1 raw1364step1Labels raw1364step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3256 node3256Labels := by rfl

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

theorem canonical1902 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1902 raw1902Labels = mixedMoment B node4939 node4939Labels := by
  calc
    mixedMoment B raw1902 raw1902Labels = mixedMoment B raw1902step0 raw1902step0Labels := by
      have ha : raw1902step0 = (fun i j => raw1902 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1902step0 raw1902; decide +kernel
      have hl : raw1902step0Labels = raw1902Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1902 raw1902Labels permutation152 permutation4
    mixedMoment B raw1902step0 raw1902step0Labels = mixedMoment B raw1902step1 raw1902step1Labels := by
      have ha : raw1902step1 = raw1902step0 := by apply Matrix.ext; unfold raw1902step1 raw1902step0; decide +kernel
      have hl : raw1902step0Labels = labelEmbedding7 ∘ raw1902step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1902step0 raw1902step0Labels raw1902step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4939 node4939Labels := by rfl

theorem canonical1903 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1903 raw1903Labels = mixedMoment B node2330 node2330Labels := by
  calc
    mixedMoment B raw1903 raw1903Labels = mixedMoment B raw1903step0 raw1903step0Labels := by
      have ha : raw1903step0 = (fun i j => raw1903 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1903step0 raw1903; decide +kernel
      have hl : raw1903step0Labels = raw1903Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1903 raw1903Labels permutation152 permutation4
    _ = mixedMoment B node2330 node2330Labels := by rfl

theorem canonical1904 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1904 raw1904Labels = mixedMoment B node3404 node3404Labels := by
  calc
    mixedMoment B raw1904 raw1904Labels = mixedMoment B raw1904step0 raw1904step0Labels := by
      have ha : raw1904step0 = (fun i j => raw1904 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1904step0 raw1904; decide +kernel
      have hl : raw1904step0Labels = raw1904Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1904 raw1904Labels permutation152 permutation6
    mixedMoment B raw1904step0 raw1904step0Labels = mixedMoment B raw1904step1 raw1904step1Labels := by
      have ha : raw1904step1 = -raw1904step0 := by apply Matrix.ext; change ∀ i j, raw1904step1 i j = -(raw1904step0 i j); unfold raw1904step1 raw1904step0; decide +kernel
      have hl : raw1904step1Labels = raw1904step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1904step1 raw1904step1Labels = mixedMoment B raw1904step2 raw1904step2Labels := by
      have ha : raw1904step2 = raw1904step1 := by apply Matrix.ext; unfold raw1904step2 raw1904step1; decide +kernel
      have hl : raw1904step1Labels = labelEmbedding1 ∘ raw1904step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1904step1 raw1904step1Labels raw1904step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3404 node3404Labels := by rfl

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

theorem canonical2121 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2121 raw2121Labels = mixedMoment B node5098 node5098Labels := by
  calc
    mixedMoment B raw2121 raw2121Labels = mixedMoment B raw2121step0 raw2121step0Labels := by
      have ha : raw2121step0 = (fun i j => raw2121 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2121step0 raw2121; decide +kernel
      have hl : raw2121step0Labels = raw2121Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2121 raw2121Labels permutation152 permutation4
    mixedMoment B raw2121step0 raw2121step0Labels = mixedMoment B raw2121step1 raw2121step1Labels := by
      have ha : raw2121step1 = raw2121step0 := by apply Matrix.ext; unfold raw2121step1 raw2121step0; decide +kernel
      have hl : raw2121step0Labels = labelEmbedding7 ∘ raw2121step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2121step0 raw2121step0Labels raw2121step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5098 node5098Labels := by rfl

theorem canonical2122 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2122 raw2122Labels = mixedMoment B node2508 node2508Labels := by
  calc
    mixedMoment B raw2122 raw2122Labels = mixedMoment B raw2122step0 raw2122step0Labels := by
      have ha : raw2122step0 = (fun i j => raw2122 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2122step0 raw2122; decide +kernel
      have hl : raw2122step0Labels = raw2122Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2122 raw2122Labels permutation152 permutation4
    _ = mixedMoment B node2508 node2508Labels := by rfl

theorem canonical2123 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2123 raw2123Labels = mixedMoment B node3460 node3460Labels := by
  calc
    mixedMoment B raw2123 raw2123Labels = mixedMoment B raw2123step0 raw2123step0Labels := by
      have ha : raw2123step0 = (fun i j => raw2123 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2123step0 raw2123; decide +kernel
      have hl : raw2123step0Labels = raw2123Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2123 raw2123Labels permutation152 permutation6
    mixedMoment B raw2123step0 raw2123step0Labels = mixedMoment B raw2123step1 raw2123step1Labels := by
      have ha : raw2123step1 = -raw2123step0 := by apply Matrix.ext; change ∀ i j, raw2123step1 i j = -(raw2123step0 i j); unfold raw2123step1 raw2123step0; decide +kernel
      have hl : raw2123step1Labels = raw2123step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2123step1 raw2123step1Labels = mixedMoment B raw2123step2 raw2123step2Labels := by
      have ha : raw2123step2 = raw2123step1 := by apply Matrix.ext; unfold raw2123step2 raw2123step1; decide +kernel
      have hl : raw2123step1Labels = labelEmbedding1 ∘ raw2123step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2123step1 raw2123step1Labels raw2123step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3460 node3460Labels := by rfl

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

theorem canonical2472 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2472 raw2472Labels = mixedMoment B node5400 node5400Labels := by
  calc
    mixedMoment B raw2472 raw2472Labels = mixedMoment B raw2472step0 raw2472step0Labels := by
      have ha : raw2472step0 = (fun i j => raw2472 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2472step0 raw2472; decide +kernel
      have hl : raw2472step0Labels = raw2472Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2472 raw2472Labels permutation152 permutation4
    mixedMoment B raw2472step0 raw2472step0Labels = mixedMoment B raw2472step1 raw2472step1Labels := by
      have ha : raw2472step1 = raw2472step0 := by apply Matrix.ext; unfold raw2472step1 raw2472step0; decide +kernel
      have hl : raw2472step0Labels = labelEmbedding7 ∘ raw2472step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2472step0 raw2472step0Labels raw2472step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5400 node5400Labels := by rfl

theorem canonical2473 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2473 raw2473Labels = mixedMoment B node3786 node3786Labels := by
  calc
    mixedMoment B raw2473 raw2473Labels = mixedMoment B raw2473step0 raw2473step0Labels := by
      have ha : raw2473step0 = (fun i j => raw2473 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2473step0 raw2473; decide +kernel
      have hl : raw2473step0Labels = raw2473Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2473 raw2473Labels permutation152 permutation4
    _ = mixedMoment B node3786 node3786Labels := by rfl

theorem canonical2474 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2474 raw2474Labels = mixedMoment B node3799 node3799Labels := by
  calc
    mixedMoment B raw2474 raw2474Labels = mixedMoment B raw2474step0 raw2474step0Labels := by
      have ha : raw2474step0 = (fun i j => raw2474 (permutation160 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2474step0 raw2474; decide +kernel
      have hl : raw2474step0Labels = raw2474Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2474 raw2474Labels permutation160 permutation6
    mixedMoment B raw2474step0 raw2474step0Labels = mixedMoment B raw2474step1 raw2474step1Labels := by
      have ha : raw2474step1 = -raw2474step0 := by apply Matrix.ext; change ∀ i j, raw2474step1 i j = -(raw2474step0 i j); unfold raw2474step1 raw2474step0; decide +kernel
      have hl : raw2474step1Labels = raw2474step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2474step1 raw2474step1Labels = mixedMoment B raw2474step2 raw2474step2Labels := by
      have ha : raw2474step2 = raw2474step1 := by apply Matrix.ext; unfold raw2474step2 raw2474step1; decide +kernel
      have hl : raw2474step1Labels = labelEmbedding1 ∘ raw2474step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2474step1 raw2474step1Labels raw2474step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3799 node3799Labels := by rfl

theorem canonical2484 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2484 raw2484Labels = mixedMoment B node5405 node5405Labels := by
  calc
    mixedMoment B raw2484 raw2484Labels = mixedMoment B raw2484step0 raw2484step0Labels := by
      have ha : raw2484step0 = (fun i j => raw2484 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2484step0 raw2484; decide +kernel
      have hl : raw2484step0Labels = raw2484Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2484 raw2484Labels permutation152 permutation4
    mixedMoment B raw2484step0 raw2484step0Labels = mixedMoment B raw2484step1 raw2484step1Labels := by
      have ha : raw2484step1 = raw2484step0 := by apply Matrix.ext; unfold raw2484step1 raw2484step0; decide +kernel
      have hl : raw2484step0Labels = labelEmbedding7 ∘ raw2484step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2484step0 raw2484step0Labels raw2484step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5405 node5405Labels := by rfl

theorem canonical2485 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2485 raw2485Labels = mixedMoment B node3800 node3800Labels := by
  calc
    mixedMoment B raw2485 raw2485Labels = mixedMoment B raw2485step0 raw2485step0Labels := by
      have ha : raw2485step0 = (fun i j => raw2485 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2485step0 raw2485; decide +kernel
      have hl : raw2485step0Labels = raw2485Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2485 raw2485Labels permutation152 permutation4
    _ = mixedMoment B node3800 node3800Labels := by rfl

theorem canonical2486 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2486 raw2486Labels = mixedMoment B node3805 node3805Labels := by
  calc
    mixedMoment B raw2486 raw2486Labels = mixedMoment B raw2486step0 raw2486step0Labels := by
      have ha : raw2486step0 = (fun i j => raw2486 (permutation164 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2486step0 raw2486; decide +kernel
      have hl : raw2486step0Labels = raw2486Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2486 raw2486Labels permutation164 permutation6
    mixedMoment B raw2486step0 raw2486step0Labels = mixedMoment B raw2486step1 raw2486step1Labels := by
      have ha : raw2486step1 = -raw2486step0 := by apply Matrix.ext; change ∀ i j, raw2486step1 i j = -(raw2486step0 i j); unfold raw2486step1 raw2486step0; decide +kernel
      have hl : raw2486step1Labels = raw2486step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2486step1 raw2486step1Labels = mixedMoment B raw2486step2 raw2486step2Labels := by
      have ha : raw2486step2 = raw2486step1 := by apply Matrix.ext; unfold raw2486step2 raw2486step1; decide +kernel
      have hl : raw2486step1Labels = labelEmbedding1 ∘ raw2486step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2486step1 raw2486step1Labels raw2486step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3805 node3805Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical259
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical33155 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33155 raw33155Labels = mixedMoment B node5351 node5351Labels := by
  calc
    _ = mixedMoment B node5351 node5351Labels := by rfl

theorem canonical33156 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33156 raw33156Labels = mixedMoment B node5400 node5400Labels := by
  calc
    _ = mixedMoment B node5400 node5400Labels := by rfl

theorem canonical33157 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33157 raw33157Labels = mixedMoment B node5409 node5409Labels := by
  calc
    mixedMoment B raw33157 raw33157Labels = mixedMoment B raw33157step0 raw33157step0Labels := by
      have hz : ∀ j, raw33157 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw33157step0 = (fun i j => raw33157 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw33157step0 raw33157; decide +kernel
      have hl : raw33157step0Labels = raw33157Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33157 raw33157Labels permutation434 hz
    _ = mixedMoment B node5409 node5409Labels := by rfl

theorem canonical33158 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33158 raw33158Labels = mixedMoment B node5409 node5409Labels := by
  calc
    mixedMoment B raw33158 raw33158Labels = mixedMoment B raw33158step0 raw33158step0Labels := by
      have hz : ∀ j, raw33158 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw33158step0 = (fun i j => raw33158 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw33158step0 raw33158; decide +kernel
      have hl : raw33158step0Labels = raw33158Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33158 raw33158Labels permutation520 hz
    _ = mixedMoment B node5409 node5409Labels := by rfl

theorem canonical33159 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33159 raw33159Labels = mixedMoment B node5256 node5256Labels := by
  calc
    _ = mixedMoment B node5256 node5256Labels := by rfl

theorem canonical33160 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33160 raw33160Labels = mixedMoment B node4541 node4541Labels := by
  calc
    mixedMoment B raw33160 raw33160Labels = mixedMoment B raw33160step0 raw33160step0Labels := by
      have ha : raw33160step0 = (fun i j => raw33160 (permutation160 i) (permutation2 j)) := by apply Matrix.ext; unfold raw33160step0 raw33160; decide +kernel
      have hl : raw33160step0Labels = raw33160Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33160 raw33160Labels permutation160 permutation2
    _ = mixedMoment B node4541 node4541Labels := by rfl

theorem canonical33161 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33161 raw33161Labels = mixedMoment B node4939 node4939Labels := by
  calc
    mixedMoment B raw33161 raw33161Labels = mixedMoment B raw33161step0 raw33161step0Labels := by
      have ha : raw33161step0 = (fun i j => raw33161 (permutation160 i) (permutation2 j)) := by apply Matrix.ext; unfold raw33161step0 raw33161; decide +kernel
      have hl : raw33161step0Labels = raw33161Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33161 raw33161Labels permutation160 permutation2
    _ = mixedMoment B node4939 node4939Labels := by rfl

theorem canonical33162 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33162 raw33162Labels = mixedMoment B node5101 node5101Labels := by
  calc
    mixedMoment B raw33162 raw33162Labels = mixedMoment B raw33162step0 raw33162step0Labels := by
      have hz : ∀ j, raw33162 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw33162step0 = (fun i j => raw33162 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw33162step0 raw33162; decide +kernel
      have hl : raw33162step0Labels = raw33162Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33162 raw33162Labels permutation434 hz
    mixedMoment B raw33162step0 raw33162step0Labels = mixedMoment B raw33162step1 raw33162step1Labels := by
      have ha : raw33162step1 = (fun i j => raw33162step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw33162step1 raw33162step0; decide +kernel
      have hl : raw33162step1Labels = raw33162step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33162step0 raw33162step0Labels permutation34 permutation2
    _ = mixedMoment B node5101 node5101Labels := by rfl

theorem canonical33163 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33163 raw33163Labels = mixedMoment B node5101 node5101Labels := by
  calc
    mixedMoment B raw33163 raw33163Labels = mixedMoment B raw33163step0 raw33163step0Labels := by
      have hz : ∀ j, raw33163 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw33163step0 = (fun i j => raw33163 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw33163step0 raw33163; decide +kernel
      have hl : raw33163step0Labels = raw33163Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33163 raw33163Labels permutation520 hz
    mixedMoment B raw33163step0 raw33163step0Labels = mixedMoment B raw33163step1 raw33163step1Labels := by
      have ha : raw33163step1 = (fun i j => raw33163step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw33163step1 raw33163step0; decide +kernel
      have hl : raw33163step1Labels = raw33163step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33163step0 raw33163step0Labels permutation34 permutation2
    _ = mixedMoment B node5101 node5101Labels := by rfl

theorem canonical33164 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33164 raw33164Labels = mixedMoment B node4529 node4529Labels := by
  calc
    mixedMoment B raw33164 raw33164Labels = mixedMoment B raw33164step0 raw33164step0Labels := by
      have ha : raw33164step0 = (fun i j => raw33164 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw33164step0 raw33164; decide +kernel
      have hl : raw33164step0Labels = raw33164Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33164 raw33164Labels permutation154 permutation2
    _ = mixedMoment B node4529 node4529Labels := by rfl

theorem canonical33165 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33165 raw33165Labels = mixedMoment B node4931 node4931Labels := by
  calc
    mixedMoment B raw33165 raw33165Labels = mixedMoment B raw33165step0 raw33165step0Labels := by
      have ha : raw33165step0 = (fun i j => raw33165 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw33165step0 raw33165; decide +kernel
      have hl : raw33165step0Labels = raw33165Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33165 raw33165Labels permutation154 permutation2
    _ = mixedMoment B node4931 node4931Labels := by rfl

theorem canonical33166 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33166 raw33166Labels = mixedMoment B node5042 node5042Labels := by
  calc
    mixedMoment B raw33166 raw33166Labels = mixedMoment B raw33166step0 raw33166step0Labels := by
      have ha : raw33166step0 = (fun i j => raw33166 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw33166step0 raw33166; decide +kernel
      have hl : raw33166step0Labels = raw33166Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33166 raw33166Labels permutation154 permutation2
    _ = mixedMoment B node5042 node5042Labels := by rfl

theorem canonical33167 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33167 raw33167Labels = mixedMoment B node5080 node5080Labels := by
  calc
    mixedMoment B raw33167 raw33167Labels = mixedMoment B raw33167step0 raw33167step0Labels := by
      have hz : ∀ j, raw33167 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw33167step0 = (fun i j => raw33167 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw33167step0 raw33167; decide +kernel
      have hl : raw33167step0Labels = raw33167Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33167 raw33167Labels permutation520 hz
    _ = mixedMoment B node5080 node5080Labels := by rfl

theorem canonical33168 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33168 raw33168Labels = mixedMoment B node4529 node4529Labels := by
  calc
    _ = mixedMoment B node4529 node4529Labels := by rfl

theorem canonical33169 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33169 raw33169Labels = mixedMoment B node4931 node4931Labels := by
  calc
    _ = mixedMoment B node4931 node4931Labels := by rfl

theorem canonical33170 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33170 raw33170Labels = mixedMoment B node5042 node5042Labels := by
  calc
    _ = mixedMoment B node5042 node5042Labels := by rfl

theorem canonical33171 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33171 raw33171Labels = mixedMoment B node5080 node5080Labels := by
  calc
    mixedMoment B raw33171 raw33171Labels = mixedMoment B raw33171step0 raw33171step0Labels := by
      have hz : ∀ j, raw33171 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw33171step0 = (fun i j => raw33171 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw33171step0 raw33171; decide +kernel
      have hl : raw33171step0Labels = raw33171Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33171 raw33171Labels permutation434 hz
    _ = mixedMoment B node5080 node5080Labels := by rfl

theorem canonical33172 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33172 raw33172Labels = mixedMoment B node4527 node4527Labels := by
  calc
    _ = mixedMoment B node4527 node4527Labels := by rfl

theorem canonical33173 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33173 raw33173Labels = mixedMoment B node4929 node4929Labels := by
  calc
    _ = mixedMoment B node4929 node4929Labels := by rfl

theorem canonical33174 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33174 raw33174Labels = mixedMoment B node5041 node5041Labels := by
  calc
    _ = mixedMoment B node5041 node5041Labels := by rfl

theorem canonical33175 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33175 raw33175Labels = mixedMoment B node5075 node5075Labels := by
  calc
    mixedMoment B raw33175 raw33175Labels = mixedMoment B raw33175step0 raw33175step0Labels := by
      have hz : ∀ j, raw33175 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw33175step0 = (fun i j => raw33175 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw33175step0 raw33175; decide +kernel
      have hl : raw33175step0Labels = raw33175Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33175 raw33175Labels permutation434 hz
    _ = mixedMoment B node5075 node5075Labels := by rfl

theorem canonical33176 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33176 raw33176Labels = mixedMoment B node5075 node5075Labels := by
  calc
    mixedMoment B raw33176 raw33176Labels = mixedMoment B raw33176step0 raw33176step0Labels := by
      have hz : ∀ j, raw33176 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw33176step0 = (fun i j => raw33176 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw33176step0 raw33176; decide +kernel
      have hl : raw33176step0Labels = raw33176Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33176 raw33176Labels permutation520 hz
    _ = mixedMoment B node5075 node5075Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical90
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical11544 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11544 raw11544Labels = mixedMoment B node5405 node5405Labels := by
  calc
    mixedMoment B raw11544 raw11544Labels = mixedMoment B raw11544step0 raw11544step0Labels := by
      have ha : raw11544step0 = (fun i j => raw11544 (permutation160 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11544step0 raw11544; decide +kernel
      have hl : raw11544step0Labels = raw11544Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11544 raw11544Labels permutation160 permutation7
    mixedMoment B raw11544step0 raw11544step0Labels = mixedMoment B raw11544step1 raw11544step1Labels := by
      have ha : raw11544step1 = -raw11544step0 := by apply Matrix.ext; change ∀ i j, raw11544step1 i j = -(raw11544step0 i j); unfold raw11544step1 raw11544step0; decide +kernel
      have hl : raw11544step1Labels = raw11544step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11544step1 raw11544step1Labels = mixedMoment B raw11544step2 raw11544step2Labels := by
      have ha : raw11544step2 = raw11544step1 := by apply Matrix.ext; unfold raw11544step2 raw11544step1; decide +kernel
      have hl : raw11544step1Labels = labelEmbedding10 ∘ raw11544step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11544step1 raw11544step1Labels raw11544step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5405 node5405Labels := by rfl

theorem canonical11555 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11555 raw11555Labels = mixedMoment B node5098 node5098Labels := by
  calc
    mixedMoment B raw11555 raw11555Labels = mixedMoment B raw11555step0 raw11555step0Labels := by
      have ha : raw11555step0 = (fun i j => raw11555 (permutation160 i) (permutation2 j)) := by apply Matrix.ext; unfold raw11555step0 raw11555; decide +kernel
      have hl : raw11555step0Labels = raw11555Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11555 raw11555Labels permutation160 permutation2
    _ = mixedMoment B node5098 node5098Labels := by rfl

theorem canonical11560 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11560 raw11560Labels = mixedMoment B node5074 node5074Labels := by
  calc
    mixedMoment B raw11560 raw11560Labels = mixedMoment B raw11560step0 raw11560step0Labels := by
      have ha : raw11560step0 = (fun i j => raw11560 (permutation155 i) (permutation2 j)) := by apply Matrix.ext; unfold raw11560step0 raw11560; decide +kernel
      have hl : raw11560step0Labels = raw11560Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11560 raw11560Labels permutation155 permutation2
    _ = mixedMoment B node5074 node5074Labels := by rfl

theorem canonical11565 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11565 raw11565Labels = mixedMoment B node5074 node5074Labels := by
  calc
    mixedMoment B raw11565 raw11565Labels = mixedMoment B raw11565step0 raw11565step0Labels := by
      have ha : raw11565step0 = (fun i j => raw11565 (permutation153 i) (permutation2 j)) := by apply Matrix.ext; unfold raw11565step0 raw11565; decide +kernel
      have hl : raw11565step0Labels = raw11565Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11565 raw11565Labels permutation153 permutation2
    _ = mixedMoment B node5074 node5074Labels := by rfl

theorem canonical11569 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11569 raw11569Labels = mixedMoment B node4589 node4589Labels := by
  calc
    _ = mixedMoment B node4589 node4589Labels := by rfl

theorem canonical11571 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11571 raw11571Labels = mixedMoment B node5184 node5184Labels := by
  calc
    mixedMoment B raw11571 raw11571Labels = mixedMoment B raw11571step0 raw11571step0Labels := by
      have ha : raw11571step0 = (fun i j => raw11571 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw11571step0 raw11571; decide +kernel
      have hl : raw11571step0Labels = raw11571Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11571 raw11571Labels permutation176 permutation2
    _ = mixedMoment B node5184 node5184Labels := by rfl

theorem canonical11572 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11572 raw11572Labels = mixedMoment B node5258 node5258Labels := by
  calc
    mixedMoment B raw11572 raw11572Labels = mixedMoment B raw11572step0 raw11572step0Labels := by
      have hz : ∀ j, raw11572 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11572step0 = (fun i j => raw11572 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11572step0 raw11572; decide +kernel
      have hl : raw11572step0Labels = raw11572Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11572 raw11572Labels permutation434 hz
    _ = mixedMoment B node5258 node5258Labels := by rfl

theorem canonical11573 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11573 raw11573Labels = mixedMoment B node5258 node5258Labels := by
  calc
    mixedMoment B raw11573 raw11573Labels = mixedMoment B raw11573step0 raw11573step0Labels := by
      have hz : ∀ j, raw11573 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw11573step0 = (fun i j => raw11573 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw11573step0 raw11573; decide +kernel
      have hl : raw11573step0Labels = raw11573Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11573 raw11573Labels permutation520 hz
    _ = mixedMoment B node5258 node5258Labels := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons70
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singleton4541 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4541 node4541Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1126 node1126Labels + mixedMoment B node3256 node3256Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1362 singletonSmall4541
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4541) = raw1362Labels := by decide +kernel
  rw [hl, canonical1362 B hB] at h
  have hc0 : mixedMoment B raw1362 (Fin.cases (0 : Fin 2) singletonSmall4541) =
      mixedMoment B node1126 node1126Labels := by
    have ha : raw1362 = raw1363 := by apply Matrix.ext; unfold raw1362 raw1363; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4541 = raw1363Labels := by decide +kernel
    rw [ha, hj, canonical1363 B hB]
  have hc1 : mixedMoment B raw1362 (Fin.cases (1 : Fin 2) singletonSmall4541) =
      mixedMoment B node3256 node3256Labels := by
    have ha : raw1362 = raw1364 := by apply Matrix.ext; unfold raw1362 raw1364; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4541 = raw1364Labels := by decide +kernel
    rw [ha, hj, canonical1364 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

end MUB6.Certificate.MixedSemantics

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

theorem singleton4939 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4939 node4939Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2330 node2330Labels + mixedMoment B node3404 node3404Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1902 singletonSmall4939
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4939) = raw1902Labels := by decide +kernel
  rw [hl, canonical1902 B hB] at h
  have hc0 : mixedMoment B raw1902 (Fin.cases (0 : Fin 2) singletonSmall4939) =
      mixedMoment B node2330 node2330Labels := by
    have ha : raw1902 = raw1903 := by apply Matrix.ext; unfold raw1902 raw1903; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4939 = raw1903Labels := by decide +kernel
    rw [ha, hj, canonical1903 B hB]
  have hc1 : mixedMoment B raw1902 (Fin.cases (1 : Fin 2) singletonSmall4939) =
      mixedMoment B node3404 node3404Labels := by
    have ha : raw1902 = raw1904 := by apply Matrix.ext; unfold raw1902 raw1904; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4939 = raw1904Labels := by decide +kernel
    rw [ha, hj, canonical1904 B hB]
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

theorem singleton5098 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5098 node5098Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2508 node2508Labels + mixedMoment B node3460 node3460Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2121 singletonSmall5098
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5098) = raw2121Labels := by decide +kernel
  rw [hl, canonical2121 B hB] at h
  have hc0 : mixedMoment B raw2121 (Fin.cases (0 : Fin 2) singletonSmall5098) =
      mixedMoment B node2508 node2508Labels := by
    have ha : raw2121 = raw2122 := by apply Matrix.ext; unfold raw2121 raw2122; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5098 = raw2122Labels := by decide +kernel
    rw [ha, hj, canonical2122 B hB]
  have hc1 : mixedMoment B raw2121 (Fin.cases (1 : Fin 2) singletonSmall5098) =
      mixedMoment B node3460 node3460Labels := by
    have ha : raw2121 = raw2123 := by apply Matrix.ext; unfold raw2121 raw2123; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5098 = raw2123Labels := by decide +kernel
    rw [ha, hj, canonical2123 B hB]
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

theorem singleton5400 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5400 node5400Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3786 node3786Labels + mixedMoment B node3799 node3799Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2472 singletonSmall5400
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5400) = raw2472Labels := by decide +kernel
  rw [hl, canonical2472 B hB] at h
  have hc0 : mixedMoment B raw2472 (Fin.cases (0 : Fin 2) singletonSmall5400) =
      mixedMoment B node3786 node3786Labels := by
    have ha : raw2472 = raw2473 := by apply Matrix.ext; unfold raw2472 raw2473; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5400 = raw2473Labels := by decide +kernel
    rw [ha, hj, canonical2473 B hB]
  have hc1 : mixedMoment B raw2472 (Fin.cases (1 : Fin 2) singletonSmall5400) =
      mixedMoment B node3799 node3799Labels := by
    have ha : raw2472 = raw2474 := by apply Matrix.ext; unfold raw2472 raw2474; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5400 = raw2474Labels := by decide +kernel
    rw [ha, hj, canonical2474 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton5405 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5405 node5405Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3800 node3800Labels + mixedMoment B node3805 node3805Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2484 singletonSmall5405
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5405) = raw2484Labels := by decide +kernel
  rw [hl, canonical2484 B hB] at h
  have hc0 : mixedMoment B raw2484 (Fin.cases (0 : Fin 2) singletonSmall5405) =
      mixedMoment B node3800 node3800Labels := by
    have ha : raw2484 = raw2485 := by apply Matrix.ext; unfold raw2484 raw2485; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5405 = raw2485Labels := by decide +kernel
    rw [ha, hj, canonical2485 B hB]
  have hc1 : mixedMoment B raw2484 (Fin.cases (1 : Fin 2) singletonSmall5405) =
      mixedMoment B node3805 node3805Labels := by
    have ha : raw2484 = raw2486 := by apply Matrix.ext; unfold raw2484 raw2486; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5405 = raw2486Labels := by decide +kernel
    rw [ha, hj, canonical2486 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

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

theorem sound1126 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1126 node1126Labels = Sparse.eval nodeValue1126 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1126) = mixedMoment B node1126 node1126Labels := rfl
  simpa [nodeValue1126, Sparse.eval] using hc.symm

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

theorem sound2330 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2330 node2330Labels = Sparse.eval nodeValue2330 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2330) = mixedMoment B node2330 node2330Labels := rfl
  simpa [nodeValue2330, Sparse.eval] using hc.symm

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

theorem sound2488 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2488 node2488Labels = Sparse.eval nodeValue2488 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2488) = mixedMoment B node2488 node2488Labels := rfl
  simpa [nodeValue2488, Sparse.eval] using hc.symm

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

theorem sound2508 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2508 node2508Labels = Sparse.eval nodeValue2508 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2508) = mixedMoment B node2508 node2508Labels := rfl
  simpa [nodeValue2508, Sparse.eval] using hc.symm

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

theorem sound3256 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3256 node3256Labels = Sparse.eval nodeValue3256 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3256) = mixedMoment B node3256 node3256Labels := rfl
  simpa [nodeValue3256, Sparse.eval] using hc.symm

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

theorem sound3404 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3404 node3404Labels = Sparse.eval nodeValue3404 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3404) = mixedMoment B node3404 node3404Labels := rfl
  simpa [nodeValue3404, Sparse.eval] using hc.symm

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

theorem sound3460 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3460 node3460Labels = Sparse.eval nodeValue3460 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3460) = mixedMoment B node3460 node3460Labels := rfl
  simpa [nodeValue3460, Sparse.eval] using hc.symm

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

theorem sound3689 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3689 node3689Labels = Sparse.eval nodeValue3689 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3689) = mixedMoment B node3689 node3689Labels := rfl
  simpa [nodeValue3689, Sparse.eval] using hc.symm

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

theorem sound3757 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3757 node3757Labels = Sparse.eval nodeValue3757 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3757) = mixedMoment B node3757 node3757Labels := rfl
  simpa [nodeValue3757, Sparse.eval] using hc.symm

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

theorem sound3786 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3786 node3786Labels = Sparse.eval nodeValue3786 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3786) = mixedMoment B node3786 node3786Labels := rfl
  simpa [nodeValue3786, Sparse.eval] using hc.symm

theorem sound3799 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3799 node3799Labels = Sparse.eval nodeValue3799 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3799) = mixedMoment B node3799 node3799Labels := rfl
  simpa [nodeValue3799, Sparse.eval] using hc.symm

theorem sound3800 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3800 node3800Labels = Sparse.eval nodeValue3800 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3800) = mixedMoment B node3800 node3800Labels := rfl
  simpa [nodeValue3800, Sparse.eval] using hc.symm

theorem sound3805 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3805 node3805Labels = Sparse.eval nodeValue3805 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3805) = mixedMoment B node3805 node3805Labels := rfl
  simpa [nodeValue3805, Sparse.eval] using hc.symm

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

theorem sound4527 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4527 node4527Labels = Sparse.eval nodeValue4527 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4527) = mixedMoment B node4527 node4527Labels := rfl
  simpa [nodeValue4527, Sparse.eval] using hc.symm

theorem sound4529 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4529 node4529Labels = Sparse.eval nodeValue4529 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4529) = mixedMoment B node4529 node4529Labels := rfl
  simpa [nodeValue4529, Sparse.eval] using hc.symm

theorem sound4541 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4541 node4541Labels = Sparse.eval nodeValue4541 (mixedVector B) := by
  have h := singleton4541 B _hB
  rw [sound1126 B _hB _hF, sound3256 B _hB _hF] at h
  norm_num [nodeValue4541, nodeValue1126, nodeValue3256, Sparse.eval] at h ⊢
  linarith only [h]

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

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros77
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero4929 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node4929 node4929Labels = 0 := by
  exact mixedMoment_alpha B hF node4929 node4929Labels 1 permutation152
    (by decide +kernel)

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

theorem sound4929 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4929 node4929Labels = Sparse.eval nodeValue4929 (mixedVector B) := by
  simpa only [nodeValue4929, Sparse.eval_nil] using zero4929 B _hB _hF

theorem sound4931 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4931 node4931Labels = Sparse.eval nodeValue4931 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4931) = mixedMoment B node4931 node4931Labels := rfl
  simpa [nodeValue4931, Sparse.eval] using hc.symm

theorem sound4939 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4939 node4939Labels = Sparse.eval nodeValue4939 (mixedVector B) := by
  have h := singleton4939 B _hB
  rw [sound2330 B _hB _hF, sound3404 B _hB _hF] at h
  norm_num [nodeValue4939, nodeValue2330, nodeValue3404, Sparse.eval] at h ⊢
  linarith only [h]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound78
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound5041 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5041 node5041Labels = Sparse.eval nodeValue5041 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5041) = mixedMoment B node5041 node5041Labels := rfl
  simpa [nodeValue5041, Sparse.eval] using hc.symm

theorem sound5042 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5042 node5042Labels = Sparse.eval nodeValue5042 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5042) = mixedMoment B node5042 node5042Labels := rfl
  simpa [nodeValue5042, Sparse.eval] using hc.symm

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

theorem sound5074 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5074 node5074Labels = Sparse.eval nodeValue5074 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5074) = mixedMoment B node5074 node5074Labels := rfl
  simpa [nodeValue5074, Sparse.eval] using hc.symm

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

theorem sound5098 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5098 node5098Labels = Sparse.eval nodeValue5098 (mixedVector B) := by
  have h := singleton5098 B _hB
  rw [sound2508 B _hB _hF, sound3460 B _hB _hF] at h
  norm_num [nodeValue5098, nodeValue2508, nodeValue3460, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5101 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5101 node5101Labels = Sparse.eval nodeValue5101 (mixedVector B) := by
  simpa only [nodeValue5101, Sparse.eval_nil] using zero5101 B _hB _hF

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

theorem sound5351 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5351 node5351Labels = Sparse.eval nodeValue5351 (mixedVector B) := by
  have h := singleton5351 B _hB
  rw [sound3689 B _hB _hF, sound3757 B _hB _hF] at h
  norm_num [nodeValue5351, nodeValue3689, nodeValue3757, Sparse.eval] at h ⊢
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

theorem sound5400 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5400 node5400Labels = Sparse.eval nodeValue5400 (mixedVector B) := by
  have h := singleton5400 B _hB
  rw [sound3786 B _hB _hF, sound3799 B _hB _hF] at h
  norm_num [nodeValue5400, nodeValue3786, nodeValue3799, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5405 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5405 node5405Labels = Sparse.eval nodeValue5405 (mixedVector B) := by
  have h := singleton5405 B _hB
  rw [sound3800 B _hB _hF, sound3805 B _hB _hF] at h
  norm_num [nodeValue5405, nodeValue3800, nodeValue3805, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5409 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5409 node5409Labels = Sparse.eval nodeValue5409 (mixedVector B) := by
  simpa only [nodeValue5409, Sparse.eval_nil] using zero5409 B _hB _hF

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources75
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sourceEq2416 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2416 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2416 + difference 0 1) (sourceB2416 + difference 1 0) sourceC2416) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5351) := by
    have ha : (tripleCharges (sourceA2416 + difference 0 1) (sourceB2416 + difference 1 0) sourceC2416) = raw33155 := by
      apply Matrix.ext; unfold tripleCharges sourceA2416 sourceB2416 sourceC2416 difference raw33155; decide +kernel
    rw [ha]
    exact (canonical33155 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2416 + difference 0 2) (sourceB2416 + difference 2 0) sourceC2416) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5400) := by
    have ha : (tripleCharges (sourceA2416 + difference 0 2) (sourceB2416 + difference 2 0) sourceC2416) = raw33156 := by
      apply Matrix.ext; unfold tripleCharges sourceA2416 sourceB2416 sourceC2416 difference raw33156; decide +kernel
    rw [ha]
    exact (canonical33156 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2416 + difference 0 3) (sourceB2416 + difference 3 0) sourceC2416) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5409) := by
    have ha : (tripleCharges (sourceA2416 + difference 0 3) (sourceB2416 + difference 3 0) sourceC2416) = raw33157 := by
      apply Matrix.ext; unfold tripleCharges sourceA2416 sourceB2416 sourceC2416 difference raw33157; decide +kernel
    rw [ha]
    exact (canonical33157 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2416 + difference 0 4) (sourceB2416 + difference 4 0) sourceC2416) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5409) := by
    have ha : (tripleCharges (sourceA2416 + difference 0 4) (sourceB2416 + difference 4 0) sourceC2416) = raw33158 := by
      apply Matrix.ext; unfold tripleCharges sourceA2416 sourceB2416 sourceC2416 difference raw33158; decide +kernel
    rw [ha]
    exact (canonical33158 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2416 + difference 0 5) (sourceB2416 + difference 5 0) sourceC2416) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5405) := by
    have ha : (tripleCharges (sourceA2416 + difference 0 5) (sourceB2416 + difference 5 0) sourceC2416) = raw11544 := by
      apply Matrix.ext; unfold tripleCharges sourceA2416 sourceB2416 sourceC2416 difference raw11544; decide +kernel
    rw [ha]
    exact (canonical11544 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2416 + difference 1 0) (sourceB2416 + difference 0 1) sourceC2416) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4589) := by
    have ha : (tripleCharges (sourceA2416 + difference 1 0) (sourceB2416 + difference 0 1) sourceC2416) = raw11569 := by
      apply Matrix.ext; unfold tripleCharges sourceA2416 sourceB2416 sourceC2416 difference raw11569; decide +kernel
    rw [ha]
    exact (canonical11569 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2416 + difference 1 2) (sourceB2416 + difference 2 1) sourceC2416) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5184) := by
    have ha : (tripleCharges (sourceA2416 + difference 1 2) (sourceB2416 + difference 2 1) sourceC2416) = raw11571 := by
      apply Matrix.ext; unfold tripleCharges sourceA2416 sourceB2416 sourceC2416 difference raw11571; decide +kernel
    rw [ha]
    exact (canonical11571 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2416 + difference 1 3) (sourceB2416 + difference 3 1) sourceC2416) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5258) := by
    have ha : (tripleCharges (sourceA2416 + difference 1 3) (sourceB2416 + difference 3 1) sourceC2416) = raw11572 := by
      apply Matrix.ext; unfold tripleCharges sourceA2416 sourceB2416 sourceC2416 difference raw11572; decide +kernel
    rw [ha]
    exact (canonical11572 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2416 + difference 1 4) (sourceB2416 + difference 4 1) sourceC2416) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5258) := by
    have ha : (tripleCharges (sourceA2416 + difference 1 4) (sourceB2416 + difference 4 1) sourceC2416) = raw11573 := by
      apply Matrix.ext; unfold tripleCharges sourceA2416 sourceB2416 sourceC2416 difference raw11573; decide +kernel
    rw [ha]
    exact (canonical11573 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2416 + difference 1 5) (sourceB2416 + difference 5 1) sourceC2416) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5256) := by
    have ha : (tripleCharges (sourceA2416 + difference 1 5) (sourceB2416 + difference 5 1) sourceC2416) = raw33159 := by
      apply Matrix.ext; unfold tripleCharges sourceA2416 sourceB2416 sourceC2416 difference raw33159; decide +kernel
    rw [ha]
    exact (canonical33159 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2416 + difference 2 0) (sourceB2416 + difference 0 2) sourceC2416) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4541) := by
    have ha : (tripleCharges (sourceA2416 + difference 2 0) (sourceB2416 + difference 0 2) sourceC2416) = raw33160 := by
      apply Matrix.ext; unfold tripleCharges sourceA2416 sourceB2416 sourceC2416 difference raw33160; decide +kernel
    rw [ha]
    exact (canonical33160 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2416 + difference 2 1) (sourceB2416 + difference 1 2) sourceC2416) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4939) := by
    have ha : (tripleCharges (sourceA2416 + difference 2 1) (sourceB2416 + difference 1 2) sourceC2416) = raw33161 := by
      apply Matrix.ext; unfold tripleCharges sourceA2416 sourceB2416 sourceC2416 difference raw33161; decide +kernel
    rw [ha]
    exact (canonical33161 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2416 + difference 2 3) (sourceB2416 + difference 3 2) sourceC2416) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5101) := by
    have ha : (tripleCharges (sourceA2416 + difference 2 3) (sourceB2416 + difference 3 2) sourceC2416) = raw33162 := by
      apply Matrix.ext; unfold tripleCharges sourceA2416 sourceB2416 sourceC2416 difference raw33162; decide +kernel
    rw [ha]
    exact (canonical33162 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2416 + difference 2 4) (sourceB2416 + difference 4 2) sourceC2416) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5101) := by
    have ha : (tripleCharges (sourceA2416 + difference 2 4) (sourceB2416 + difference 4 2) sourceC2416) = raw33163 := by
      apply Matrix.ext; unfold tripleCharges sourceA2416 sourceB2416 sourceC2416 difference raw33163; decide +kernel
    rw [ha]
    exact (canonical33163 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2416 + difference 2 5) (sourceB2416 + difference 5 2) sourceC2416) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5098) := by
    have ha : (tripleCharges (sourceA2416 + difference 2 5) (sourceB2416 + difference 5 2) sourceC2416) = raw11555 := by
      apply Matrix.ext; unfold tripleCharges sourceA2416 sourceB2416 sourceC2416 difference raw11555; decide +kernel
    rw [ha]
    exact (canonical11555 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2416 + difference 3 0) (sourceB2416 + difference 0 3) sourceC2416) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4529) := by
    have ha : (tripleCharges (sourceA2416 + difference 3 0) (sourceB2416 + difference 0 3) sourceC2416) = raw33164 := by
      apply Matrix.ext; unfold tripleCharges sourceA2416 sourceB2416 sourceC2416 difference raw33164; decide +kernel
    rw [ha]
    exact (canonical33164 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2416 + difference 3 1) (sourceB2416 + difference 1 3) sourceC2416) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4931) := by
    have ha : (tripleCharges (sourceA2416 + difference 3 1) (sourceB2416 + difference 1 3) sourceC2416) = raw33165 := by
      apply Matrix.ext; unfold tripleCharges sourceA2416 sourceB2416 sourceC2416 difference raw33165; decide +kernel
    rw [ha]
    exact (canonical33165 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2416 + difference 3 2) (sourceB2416 + difference 2 3) sourceC2416) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5042) := by
    have ha : (tripleCharges (sourceA2416 + difference 3 2) (sourceB2416 + difference 2 3) sourceC2416) = raw33166 := by
      apply Matrix.ext; unfold tripleCharges sourceA2416 sourceB2416 sourceC2416 difference raw33166; decide +kernel
    rw [ha]
    exact (canonical33166 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2416 + difference 3 4) (sourceB2416 + difference 4 3) sourceC2416) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5080) := by
    have ha : (tripleCharges (sourceA2416 + difference 3 4) (sourceB2416 + difference 4 3) sourceC2416) = raw33167 := by
      apply Matrix.ext; unfold tripleCharges sourceA2416 sourceB2416 sourceC2416 difference raw33167; decide +kernel
    rw [ha]
    exact (canonical33167 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2416 + difference 3 5) (sourceB2416 + difference 5 3) sourceC2416) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5074) := by
    have ha : (tripleCharges (sourceA2416 + difference 3 5) (sourceB2416 + difference 5 3) sourceC2416) = raw11560 := by
      apply Matrix.ext; unfold tripleCharges sourceA2416 sourceB2416 sourceC2416 difference raw11560; decide +kernel
    rw [ha]
    exact (canonical11560 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2416 + difference 4 0) (sourceB2416 + difference 0 4) sourceC2416) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4529) := by
    have ha : (tripleCharges (sourceA2416 + difference 4 0) (sourceB2416 + difference 0 4) sourceC2416) = raw33168 := by
      apply Matrix.ext; unfold tripleCharges sourceA2416 sourceB2416 sourceC2416 difference raw33168; decide +kernel
    rw [ha]
    exact (canonical33168 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2416 + difference 4 1) (sourceB2416 + difference 1 4) sourceC2416) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4931) := by
    have ha : (tripleCharges (sourceA2416 + difference 4 1) (sourceB2416 + difference 1 4) sourceC2416) = raw33169 := by
      apply Matrix.ext; unfold tripleCharges sourceA2416 sourceB2416 sourceC2416 difference raw33169; decide +kernel
    rw [ha]
    exact (canonical33169 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2416 + difference 4 2) (sourceB2416 + difference 2 4) sourceC2416) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5042) := by
    have ha : (tripleCharges (sourceA2416 + difference 4 2) (sourceB2416 + difference 2 4) sourceC2416) = raw33170 := by
      apply Matrix.ext; unfold tripleCharges sourceA2416 sourceB2416 sourceC2416 difference raw33170; decide +kernel
    rw [ha]
    exact (canonical33170 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2416 + difference 4 3) (sourceB2416 + difference 3 4) sourceC2416) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5080) := by
    have ha : (tripleCharges (sourceA2416 + difference 4 3) (sourceB2416 + difference 3 4) sourceC2416) = raw33171 := by
      apply Matrix.ext; unfold tripleCharges sourceA2416 sourceB2416 sourceC2416 difference raw33171; decide +kernel
    rw [ha]
    exact (canonical33171 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2416 + difference 4 5) (sourceB2416 + difference 5 4) sourceC2416) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5074) := by
    have ha : (tripleCharges (sourceA2416 + difference 4 5) (sourceB2416 + difference 5 4) sourceC2416) = raw11565 := by
      apply Matrix.ext; unfold tripleCharges sourceA2416 sourceB2416 sourceC2416 difference raw11565; decide +kernel
    rw [ha]
    exact (canonical11565 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2416 + difference 5 0) (sourceB2416 + difference 0 5) sourceC2416) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4527) := by
    have ha : (tripleCharges (sourceA2416 + difference 5 0) (sourceB2416 + difference 0 5) sourceC2416) = raw33172 := by
      apply Matrix.ext; unfold tripleCharges sourceA2416 sourceB2416 sourceC2416 difference raw33172; decide +kernel
    rw [ha]
    exact (canonical33172 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2416 + difference 5 1) (sourceB2416 + difference 1 5) sourceC2416) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4929) := by
    have ha : (tripleCharges (sourceA2416 + difference 5 1) (sourceB2416 + difference 1 5) sourceC2416) = raw33173 := by
      apply Matrix.ext; unfold tripleCharges sourceA2416 sourceB2416 sourceC2416 difference raw33173; decide +kernel
    rw [ha]
    exact (canonical33173 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2416 + difference 5 2) (sourceB2416 + difference 2 5) sourceC2416) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5041) := by
    have ha : (tripleCharges (sourceA2416 + difference 5 2) (sourceB2416 + difference 2 5) sourceC2416) = raw33174 := by
      apply Matrix.ext; unfold tripleCharges sourceA2416 sourceB2416 sourceC2416 difference raw33174; decide +kernel
    rw [ha]
    exact (canonical33174 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2416 + difference 5 3) (sourceB2416 + difference 3 5) sourceC2416) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5075) := by
    have ha : (tripleCharges (sourceA2416 + difference 5 3) (sourceB2416 + difference 3 5) sourceC2416) = raw33175 := by
      apply Matrix.ext; unfold tripleCharges sourceA2416 sourceB2416 sourceC2416 difference raw33175; decide +kernel
    rw [ha]
    exact (canonical33175 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2416 + difference 5 4) (sourceB2416 + difference 4 5) sourceC2416) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5075) := by
    have ha : (tripleCharges (sourceA2416 + difference 5 4) (sourceB2416 + difference 4 5) sourceC2416) = raw33176 := by
      apply Matrix.ext; unfold tripleCharges sourceA2416 sourceB2416 sourceC2416 difference raw33176; decide +kernel
    rw [ha]
    exact (canonical33176 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2416 sourceB2416 sourceC2416
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2416, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic122
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reindexCheck1956 : Integer.Sparse.reindex keyMap MixedData.row1956 = numericRow1956 := by decide +kernel

theorem numericCheck1956 (x : Master → ℝ) : Integer.Sparse.eval numericRow1956 x =
    (4 : ℝ) * reducedSource1956 x := by
  norm_num [numericRow1956, reducedSource1956, Integer.Sparse.eval, Sparse.eval, nodeValue4527, nodeValue4529, nodeValue4541, nodeValue4589, nodeValue4929, nodeValue4931, nodeValue4939, nodeValue5041, nodeValue5042, nodeValue5074, nodeValue5075, nodeValue5080, nodeValue5098, nodeValue5101, nodeValue5184, nodeValue5256, nodeValue5258, nodeValue5351, nodeValue5400, nodeValue5405, nodeValue5409]
  ring

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Rows122
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero1956 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1956 (mixedVector B) = 0 := by
  have h4527 : mixedVector B (Sum.inr 4527) = Sparse.eval nodeValue4527 (mixedVector B) := by
    change mixedMoment B node4527 node4527Labels = _
    exact sound4527 B hB hF
  have h4529 : mixedVector B (Sum.inr 4529) = Sparse.eval nodeValue4529 (mixedVector B) := by
    change mixedMoment B node4529 node4529Labels = _
    exact sound4529 B hB hF
  have h4541 : mixedVector B (Sum.inr 4541) = Sparse.eval nodeValue4541 (mixedVector B) := by
    change mixedMoment B node4541 node4541Labels = _
    exact sound4541 B hB hF
  have h4589 : mixedVector B (Sum.inr 4589) = Sparse.eval nodeValue4589 (mixedVector B) := by
    change mixedMoment B node4589 node4589Labels = _
    exact sound4589 B hB hF
  have h4929 : mixedVector B (Sum.inr 4929) = Sparse.eval nodeValue4929 (mixedVector B) := by
    change mixedMoment B node4929 node4929Labels = _
    exact sound4929 B hB hF
  have h4931 : mixedVector B (Sum.inr 4931) = Sparse.eval nodeValue4931 (mixedVector B) := by
    change mixedMoment B node4931 node4931Labels = _
    exact sound4931 B hB hF
  have h4939 : mixedVector B (Sum.inr 4939) = Sparse.eval nodeValue4939 (mixedVector B) := by
    change mixedMoment B node4939 node4939Labels = _
    exact sound4939 B hB hF
  have h5041 : mixedVector B (Sum.inr 5041) = Sparse.eval nodeValue5041 (mixedVector B) := by
    change mixedMoment B node5041 node5041Labels = _
    exact sound5041 B hB hF
  have h5042 : mixedVector B (Sum.inr 5042) = Sparse.eval nodeValue5042 (mixedVector B) := by
    change mixedMoment B node5042 node5042Labels = _
    exact sound5042 B hB hF
  have h5074 : mixedVector B (Sum.inr 5074) = Sparse.eval nodeValue5074 (mixedVector B) := by
    change mixedMoment B node5074 node5074Labels = _
    exact sound5074 B hB hF
  have h5075 : mixedVector B (Sum.inr 5075) = Sparse.eval nodeValue5075 (mixedVector B) := by
    change mixedMoment B node5075 node5075Labels = _
    exact sound5075 B hB hF
  have h5080 : mixedVector B (Sum.inr 5080) = Sparse.eval nodeValue5080 (mixedVector B) := by
    change mixedMoment B node5080 node5080Labels = _
    exact sound5080 B hB hF
  have h5098 : mixedVector B (Sum.inr 5098) = Sparse.eval nodeValue5098 (mixedVector B) := by
    change mixedMoment B node5098 node5098Labels = _
    exact sound5098 B hB hF
  have h5101 : mixedVector B (Sum.inr 5101) = Sparse.eval nodeValue5101 (mixedVector B) := by
    change mixedMoment B node5101 node5101Labels = _
    exact sound5101 B hB hF
  have h5184 : mixedVector B (Sum.inr 5184) = Sparse.eval nodeValue5184 (mixedVector B) := by
    change mixedMoment B node5184 node5184Labels = _
    exact sound5184 B hB hF
  have h5256 : mixedVector B (Sum.inr 5256) = Sparse.eval nodeValue5256 (mixedVector B) := by
    change mixedMoment B node5256 node5256Labels = _
    exact sound5256 B hB hF
  have h5258 : mixedVector B (Sum.inr 5258) = Sparse.eval nodeValue5258 (mixedVector B) := by
    change mixedMoment B node5258 node5258Labels = _
    exact sound5258 B hB hF
  have h5351 : mixedVector B (Sum.inr 5351) = Sparse.eval nodeValue5351 (mixedVector B) := by
    change mixedMoment B node5351 node5351Labels = _
    exact sound5351 B hB hF
  have h5400 : mixedVector B (Sum.inr 5400) = Sparse.eval nodeValue5400 (mixedVector B) := by
    change mixedMoment B node5400 node5400Labels = _
    exact sound5400 B hB hF
  have h5405 : mixedVector B (Sum.inr 5405) = Sparse.eval nodeValue5405 (mixedVector B) := by
    change mixedMoment B node5405 node5405Labels = _
    exact sound5405 B hB hF
  have h5409 : mixedVector B (Sum.inr 5409) = Sparse.eval nodeValue5409 (mixedVector B) := by
    change mixedMoment B node5409 node5409Labels = _
    exact sound5409 B hB hF
  simpa only [sourceForm2416, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4527, h4529, h4541, h4589, h4929, h4931, h4939, h5041, h5042, h5074, h5075, h5080, h5098, h5101, h5184, h5256, h5258, h5351, h5400, h5405, h5409, reducedSource1956] using sourceEq2416 B hB

theorem rowSound1956_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1956 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1956, numericCheck1956, reducedZero1956 B hB hF, mul_zero]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedSourceBridge.rowSound1956_e_oai := @OAI.MUB6.Certificate.MixedSourceBridge.rowSound1956_e_oai
