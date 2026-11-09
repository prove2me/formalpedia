-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedSourceBridge.rowSound1508_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-08T21:11:14.585481+00:00
-- url     : https://prove2.me/submissions/e809af3b-d772-4eb1-afaf-37530288e4c7

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E070
import Definitions.Def_OAIQ106E086
import Definitions.Def_OAIQ106E088
import Definitions.Def_OAIQ106E089
import Definitions.Def_OAIQ106E093
import Definitions.Def_OAIQ106E094
import Definitions.Def_OAIQ106E101
import Definitions.Def_OAIQ106E117
import Definitions.Def_OAIQ106E119
import Definitions.Def_OAIQ106E120
import Definitions.Def_OAIQ106E124
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

theorem canonical1299 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1299 raw1299Labels = mixedMoment B node4499 node4499Labels := by
  calc
    mixedMoment B raw1299 raw1299Labels = mixedMoment B raw1299step0 raw1299step0Labels := by
      have ha : raw1299step0 = (fun i j => raw1299 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1299step0 raw1299; decide +kernel
      have hl : raw1299step0Labels = raw1299Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1299 raw1299Labels permutation8 permutation4
    mixedMoment B raw1299step0 raw1299step0Labels = mixedMoment B raw1299step1 raw1299step1Labels := by
      have ha : raw1299step1 = raw1299step0 := by apply Matrix.ext; unfold raw1299step1 raw1299step0; decide +kernel
      have hl : raw1299step0Labels = labelEmbedding7 ∘ raw1299step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1299step0 raw1299step0Labels raw1299step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4499 node4499Labels := by rfl

theorem canonical1300 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1300 raw1300Labels = mixedMoment B node1083 node1083Labels := by
  calc
    mixedMoment B raw1300 raw1300Labels = mixedMoment B raw1300step0 raw1300step0Labels := by
      have ha : raw1300step0 = (fun i j => raw1300 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1300step0 raw1300; decide +kernel
      have hl : raw1300step0Labels = raw1300Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1300 raw1300Labels permutation8 permutation4
    _ = mixedMoment B node1083 node1083Labels := by rfl

theorem canonical1301 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1301 raw1301Labels = mixedMoment B node1728 node1728Labels := by
  calc
    mixedMoment B raw1301 raw1301Labels = mixedMoment B raw1301step0 raw1301step0Labels := by
      have ha : raw1301step0 = (fun i j => raw1301 (permutation9 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1301step0 raw1301; decide +kernel
      have hl : raw1301step0Labels = raw1301Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1301 raw1301Labels permutation9 permutation6
    mixedMoment B raw1301step0 raw1301step0Labels = mixedMoment B raw1301step1 raw1301step1Labels := by
      have ha : raw1301step1 = -raw1301step0 := by apply Matrix.ext; change ∀ i j, raw1301step1 i j = -(raw1301step0 i j); unfold raw1301step1 raw1301step0; decide +kernel
      have hl : raw1301step1Labels = raw1301step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1301step1 raw1301step1Labels = mixedMoment B raw1301step2 raw1301step2Labels := by
      have ha : raw1301step2 = raw1301step1 := by apply Matrix.ext; unfold raw1301step2 raw1301step1; decide +kernel
      have hl : raw1301step1Labels = labelEmbedding1 ∘ raw1301step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1301step1 raw1301step1Labels raw1301step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1728 node1728Labels := by rfl

theorem canonical1302 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1302 raw1302Labels = mixedMoment B node4503 node4503Labels := by
  calc
    mixedMoment B raw1302 raw1302Labels = mixedMoment B raw1302step0 raw1302step0Labels := by
      have ha : raw1302step0 = (fun i j => raw1302 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1302step0 raw1302; decide +kernel
      have hl : raw1302step0Labels = raw1302Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1302 raw1302Labels permutation8 permutation4
    mixedMoment B raw1302step0 raw1302step0Labels = mixedMoment B raw1302step1 raw1302step1Labels := by
      have ha : raw1302step1 = raw1302step0 := by apply Matrix.ext; unfold raw1302step1 raw1302step0; decide +kernel
      have hl : raw1302step0Labels = labelEmbedding7 ∘ raw1302step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1302step0 raw1302step0Labels raw1302step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4503 node4503Labels := by rfl

theorem canonical1303 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1303 raw1303Labels = mixedMoment B node1087 node1087Labels := by
  calc
    mixedMoment B raw1303 raw1303Labels = mixedMoment B raw1303step0 raw1303step0Labels := by
      have ha : raw1303step0 = (fun i j => raw1303 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1303step0 raw1303; decide +kernel
      have hl : raw1303step0Labels = raw1303Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1303 raw1303Labels permutation8 permutation4
    _ = mixedMoment B node1087 node1087Labels := by rfl

theorem canonical1304 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1304 raw1304Labels = mixedMoment B node1739 node1739Labels := by
  calc
    mixedMoment B raw1304 raw1304Labels = mixedMoment B raw1304step0 raw1304step0Labels := by
      have ha : raw1304step0 = (fun i j => raw1304 (permutation12 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1304step0 raw1304; decide +kernel
      have hl : raw1304step0Labels = raw1304Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1304 raw1304Labels permutation12 permutation6
    mixedMoment B raw1304step0 raw1304step0Labels = mixedMoment B raw1304step1 raw1304step1Labels := by
      have ha : raw1304step1 = -raw1304step0 := by apply Matrix.ext; change ∀ i j, raw1304step1 i j = -(raw1304step0 i j); unfold raw1304step1 raw1304step0; decide +kernel
      have hl : raw1304step1Labels = raw1304step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1304step1 raw1304step1Labels = mixedMoment B raw1304step2 raw1304step2Labels := by
      have ha : raw1304step2 = raw1304step1 := by apply Matrix.ext; unfold raw1304step2 raw1304step1; decide +kernel
      have hl : raw1304step1Labels = labelEmbedding1 ∘ raw1304step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1304step1 raw1304step1Labels raw1304step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1739 node1739Labels := by rfl

theorem canonical1305 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1305 raw1305Labels = mixedMoment B node4507 node4507Labels := by
  calc
    mixedMoment B raw1305 raw1305Labels = mixedMoment B raw1305step0 raw1305step0Labels := by
      have ha : raw1305step0 = (fun i j => raw1305 (permutation2 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1305step0 raw1305; decide +kernel
      have hl : raw1305step0Labels = raw1305Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1305 raw1305Labels permutation2 permutation4
    mixedMoment B raw1305step0 raw1305step0Labels = mixedMoment B raw1305step1 raw1305step1Labels := by
      have ha : raw1305step1 = raw1305step0 := by apply Matrix.ext; unfold raw1305step1 raw1305step0; decide +kernel
      have hl : raw1305step0Labels = labelEmbedding7 ∘ raw1305step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1305step0 raw1305step0Labels raw1305step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4507 node4507Labels := by rfl

theorem canonical1306 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1306 raw1306Labels = mixedMoment B node1091 node1091Labels := by
  calc
    mixedMoment B raw1306 raw1306Labels = mixedMoment B raw1306step0 raw1306step0Labels := by
      have ha : raw1306step0 = (fun i j => raw1306 (permutation2 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1306step0 raw1306; decide +kernel
      have hl : raw1306step0Labels = raw1306Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1306 raw1306Labels permutation2 permutation4
    _ = mixedMoment B node1091 node1091Labels := by rfl

theorem canonical1307 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1307 raw1307Labels = mixedMoment B node1756 node1756Labels := by
  calc
    mixedMoment B raw1307 raw1307Labels = mixedMoment B raw1307step0 raw1307step0Labels := by
      have ha : raw1307step0 = (fun i j => raw1307 (permutation3 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1307step0 raw1307; decide +kernel
      have hl : raw1307step0Labels = raw1307Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1307 raw1307Labels permutation3 permutation6
    mixedMoment B raw1307step0 raw1307step0Labels = mixedMoment B raw1307step1 raw1307step1Labels := by
      have ha : raw1307step1 = -raw1307step0 := by apply Matrix.ext; change ∀ i j, raw1307step1 i j = -(raw1307step0 i j); unfold raw1307step1 raw1307step0; decide +kernel
      have hl : raw1307step1Labels = raw1307step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1307step1 raw1307step1Labels = mixedMoment B raw1307step2 raw1307step2Labels := by
      have ha : raw1307step2 = raw1307step1 := by apply Matrix.ext; unfold raw1307step2 raw1307step1; decide +kernel
      have hl : raw1307step1Labels = labelEmbedding1 ∘ raw1307step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1307step1 raw1307step1Labels raw1307step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1756 node1756Labels := by rfl

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

theorem canonical1767 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1767 raw1767Labels = mixedMoment B node4835 node4835Labels := by
  calc
    mixedMoment B raw1767 raw1767Labels = mixedMoment B raw1767step0 raw1767step0Labels := by
      have ha : raw1767step0 = (fun i j => raw1767 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1767step0 raw1767; decide +kernel
      have hl : raw1767step0Labels = raw1767Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1767 raw1767Labels permutation32 permutation4
    mixedMoment B raw1767step0 raw1767step0Labels = mixedMoment B raw1767step1 raw1767step1Labels := by
      have ha : raw1767step1 = raw1767step0 := by apply Matrix.ext; unfold raw1767step1 raw1767step0; decide +kernel
      have hl : raw1767step0Labels = labelEmbedding7 ∘ raw1767step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1767step0 raw1767step0Labels raw1767step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4835 node4835Labels := by rfl

theorem canonical1768 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1768 raw1768Labels = mixedMoment B node2054 node2054Labels := by
  calc
    mixedMoment B raw1768 raw1768Labels = mixedMoment B raw1768step0 raw1768step0Labels := by
      have ha : raw1768step0 = (fun i j => raw1768 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1768step0 raw1768; decide +kernel
      have hl : raw1768step0Labels = raw1768Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1768 raw1768Labels permutation32 permutation4
    _ = mixedMoment B node2054 node2054Labels := by rfl

theorem canonical1769 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1769 raw1769Labels = mixedMoment B node2206 node2206Labels := by
  calc
    mixedMoment B raw1769 raw1769Labels = mixedMoment B raw1769step0 raw1769step0Labels := by
      have ha : raw1769step0 = (fun i j => raw1769 (permutation33 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1769step0 raw1769; decide +kernel
      have hl : raw1769step0Labels = raw1769Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1769 raw1769Labels permutation33 permutation6
    mixedMoment B raw1769step0 raw1769step0Labels = mixedMoment B raw1769step1 raw1769step1Labels := by
      have ha : raw1769step1 = -raw1769step0 := by apply Matrix.ext; change ∀ i j, raw1769step1 i j = -(raw1769step0 i j); unfold raw1769step1 raw1769step0; decide +kernel
      have hl : raw1769step1Labels = raw1769step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1769step1 raw1769step1Labels = mixedMoment B raw1769step2 raw1769step2Labels := by
      have ha : raw1769step2 = raw1769step1 := by apply Matrix.ext; unfold raw1769step2 raw1769step1; decide +kernel
      have hl : raw1769step1Labels = labelEmbedding1 ∘ raw1769step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1769step1 raw1769step1Labels raw1769step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2206 node2206Labels := by rfl

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

theorem canonical1824 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1824 raw1824Labels = mixedMoment B node4896 node4896Labels := by
  calc
    mixedMoment B raw1824 raw1824Labels = mixedMoment B raw1824step0 raw1824step0Labels := by
      have ha : raw1824step0 = (fun i j => raw1824 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1824step0 raw1824; decide +kernel
      have hl : raw1824step0Labels = raw1824Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1824 raw1824Labels permutation8 permutation4
    mixedMoment B raw1824step0 raw1824step0Labels = mixedMoment B raw1824step1 raw1824step1Labels := by
      have ha : raw1824step1 = raw1824step0 := by apply Matrix.ext; unfold raw1824step1 raw1824step0; decide +kernel
      have hl : raw1824step0Labels = labelEmbedding7 ∘ raw1824step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1824step0 raw1824step0Labels raw1824step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4896 node4896Labels := by rfl

theorem canonical1825 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1825 raw1825Labels = mixedMoment B node2266 node2266Labels := by
  calc
    mixedMoment B raw1825 raw1825Labels = mixedMoment B raw1825step0 raw1825step0Labels := by
      have ha : raw1825step0 = (fun i j => raw1825 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1825step0 raw1825; decide +kernel
      have hl : raw1825step0Labels = raw1825Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1825 raw1825Labels permutation8 permutation4
    _ = mixedMoment B node2266 node2266Labels := by rfl

theorem canonical1826 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1826 raw1826Labels = mixedMoment B node2278 node2278Labels := by
  calc
    mixedMoment B raw1826 raw1826Labels = mixedMoment B raw1826step0 raw1826step0Labels := by
      have ha : raw1826step0 = (fun i j => raw1826 (permutation12 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1826step0 raw1826; decide +kernel
      have hl : raw1826step0Labels = raw1826Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1826 raw1826Labels permutation12 permutation6
    mixedMoment B raw1826step0 raw1826step0Labels = mixedMoment B raw1826step1 raw1826step1Labels := by
      have ha : raw1826step1 = -raw1826step0 := by apply Matrix.ext; change ∀ i j, raw1826step1 i j = -(raw1826step0 i j); unfold raw1826step1 raw1826step0; decide +kernel
      have hl : raw1826step1Labels = raw1826step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1826step1 raw1826step1Labels = mixedMoment B raw1826step2 raw1826step2Labels := by
      have ha : raw1826step2 = raw1826step1 := by apply Matrix.ext; unfold raw1826step2 raw1826step1; decide +kernel
      have hl : raw1826step1Labels = labelEmbedding1 ∘ raw1826step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1826step1 raw1826step1Labels raw1826step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2278 node2278Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical201
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical25733 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25733 raw25733Labels = mixedMoment B node4835 node4835Labels := by
  calc
    mixedMoment B raw25733 raw25733Labels = mixedMoment B raw25733step0 raw25733step0Labels := by
      have hz : ∀ j, raw25733 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25733step0 = (fun i j => raw25733 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25733step0 raw25733; decide +kernel
      have hl : raw25733step0Labels = raw25733Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25733 raw25733Labels permutation346 hz
    mixedMoment B raw25733step0 raw25733step0Labels = mixedMoment B raw25733step1 raw25733step1Labels := by
      have ha : raw25733step1 = (fun i j => raw25733step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25733step1 raw25733step0; decide +kernel
      have hl : raw25733step1Labels = raw25733step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25733step0 raw25733step0Labels permutation34 permutation2
    _ = mixedMoment B node4835 node4835Labels := by rfl

theorem canonical25734 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25734 raw25734Labels = mixedMoment B node4835 node4835Labels := by
  calc
    mixedMoment B raw25734 raw25734Labels = mixedMoment B raw25734step0 raw25734step0Labels := by
      have hz : ∀ j, raw25734 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw25734step0 = (fun i j => raw25734 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw25734step0 raw25734; decide +kernel
      have hl : raw25734step0Labels = raw25734Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25734 raw25734Labels permutation265 hz
    mixedMoment B raw25734step0 raw25734step0Labels = mixedMoment B raw25734step1 raw25734step1Labels := by
      have ha : raw25734step1 = (fun i j => raw25734step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25734step1 raw25734step0; decide +kernel
      have hl : raw25734step1Labels = raw25734step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25734step0 raw25734step0Labels permutation34 permutation2
    _ = mixedMoment B node4835 node4835Labels := by rfl

theorem canonical25735 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25735 raw25735Labels = mixedMoment B node4896 node4896Labels := by
  calc
    mixedMoment B raw25735 raw25735Labels = mixedMoment B raw25735step0 raw25735step0Labels := by
      have hz : ∀ j, raw25735 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25735step0 = (fun i j => raw25735 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25735step0 raw25735; decide +kernel
      have hl : raw25735step0Labels = raw25735Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25735 raw25735Labels permutation346 hz
    mixedMoment B raw25735step0 raw25735step0Labels = mixedMoment B raw25735step1 raw25735step1Labels := by
      have hz : ∀ j, raw25735step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw25735step1 = (fun i j => raw25735step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw25735step1 raw25735step0; decide +kernel
      have hl : raw25735step1Labels = raw25735step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25735step0 raw25735step0Labels permutation56 hz
    mixedMoment B raw25735step1 raw25735step1Labels = mixedMoment B raw25735step2 raw25735step2Labels := by
      have ha : raw25735step2 = (fun i j => raw25735step1 (permutation11 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25735step2 raw25735step1; decide +kernel
      have hl : raw25735step2Labels = raw25735step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25735step1 raw25735step1Labels permutation11 permutation7
    mixedMoment B raw25735step2 raw25735step2Labels = mixedMoment B raw25735step3 raw25735step3Labels := by
      have ha : raw25735step3 = -raw25735step2 := by apply Matrix.ext; change ∀ i j, raw25735step3 i j = -(raw25735step2 i j); unfold raw25735step3 raw25735step2; decide +kernel
      have hl : raw25735step3Labels = raw25735step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25735step3 raw25735step3Labels = mixedMoment B raw25735step4 raw25735step4Labels := by
      have ha : raw25735step4 = raw25735step3 := by apply Matrix.ext; unfold raw25735step4 raw25735step3; decide +kernel
      have hl : raw25735step3Labels = labelEmbedding10 ∘ raw25735step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25735step3 raw25735step3Labels raw25735step4Labels labelEmbedding10 hl
    _ = mixedMoment B node4896 node4896Labels := by rfl

theorem canonical25736 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25736 raw25736Labels = mixedMoment B node4901 node4901Labels := by
  calc
    mixedMoment B raw25736 raw25736Labels = mixedMoment B raw25736step0 raw25736step0Labels := by
      have hz : ∀ j, raw25736 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw25736step0 = (fun i j => raw25736 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw25736step0 raw25736; decide +kernel
      have hl : raw25736step0Labels = raw25736Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25736 raw25736Labels permutation520 hz
    mixedMoment B raw25736step0 raw25736step0Labels = mixedMoment B raw25736step1 raw25736step1Labels := by
      have hz : ∀ j, raw25736step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw25736step1 = (fun i j => raw25736step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw25736step1 raw25736step0; decide +kernel
      have hl : raw25736step1Labels = raw25736step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25736step0 raw25736step0Labels permutation80 hz
    mixedMoment B raw25736step1 raw25736step1Labels = mixedMoment B raw25736step2 raw25736step2Labels := by
      have hz : ∀ j, raw25736step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw25736step2 = (fun i j => raw25736step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw25736step2 raw25736step1; decide +kernel
      have hl : raw25736step2Labels = raw25736step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25736step1 raw25736step1Labels permutation14 hz
    _ = mixedMoment B node4901 node4901Labels := by rfl

theorem canonical25737 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25737 raw25737Labels = mixedMoment B node4895 node4895Labels := by
  calc
    mixedMoment B raw25737 raw25737Labels = mixedMoment B raw25737step0 raw25737step0Labels := by
      have hz : ∀ j, raw25737 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25737step0 = (fun i j => raw25737 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25737step0 raw25737; decide +kernel
      have hl : raw25737step0Labels = raw25737Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25737 raw25737Labels permutation346 hz
    mixedMoment B raw25737step0 raw25737step0Labels = mixedMoment B raw25737step1 raw25737step1Labels := by
      have hz : ∀ j, raw25737step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw25737step1 = (fun i j => raw25737step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw25737step1 raw25737step0; decide +kernel
      have hl : raw25737step1Labels = raw25737step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25737step0 raw25737step0Labels permutation56 hz
    mixedMoment B raw25737step1 raw25737step1Labels = mixedMoment B raw25737step2 raw25737step2Labels := by
      have ha : raw25737step2 = (fun i j => raw25737step1 (permutation11 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25737step2 raw25737step1; decide +kernel
      have hl : raw25737step2Labels = raw25737step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25737step1 raw25737step1Labels permutation11 permutation7
    mixedMoment B raw25737step2 raw25737step2Labels = mixedMoment B raw25737step3 raw25737step3Labels := by
      have ha : raw25737step3 = -raw25737step2 := by apply Matrix.ext; change ∀ i j, raw25737step3 i j = -(raw25737step2 i j); unfold raw25737step3 raw25737step2; decide +kernel
      have hl : raw25737step3Labels = raw25737step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25737step3 raw25737step3Labels = mixedMoment B raw25737step4 raw25737step4Labels := by
      have ha : raw25737step4 = raw25737step3 := by apply Matrix.ext; unfold raw25737step4 raw25737step3; decide +kernel
      have hl : raw25737step3Labels = labelEmbedding10 ∘ raw25737step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25737step3 raw25737step3Labels raw25737step4Labels labelEmbedding10 hl
    _ = mixedMoment B node4895 node4895Labels := by rfl

theorem canonical25738 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25738 raw25738Labels = mixedMoment B node4173 node4173Labels := by
  calc
    mixedMoment B raw25738 raw25738Labels = mixedMoment B raw25738step0 raw25738step0Labels := by
      have hz : ∀ j, raw25738 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25738step0 = (fun i j => raw25738 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25738step0 raw25738; decide +kernel
      have hl : raw25738step0Labels = raw25738Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25738 raw25738Labels permutation346 hz
    mixedMoment B raw25738step0 raw25738step0Labels = mixedMoment B raw25738step1 raw25738step1Labels := by
      have ha : raw25738step1 = (fun i j => raw25738step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25738step1 raw25738step0; decide +kernel
      have hl : raw25738step1Labels = raw25738step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25738step0 raw25738step0Labels permutation34 permutation2
    _ = mixedMoment B node4173 node4173Labels := by rfl

theorem canonical25739 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25739 raw25739Labels = mixedMoment B node4342 node4342Labels := by
  calc
    mixedMoment B raw25739 raw25739Labels = mixedMoment B raw25739step0 raw25739step0Labels := by
      have ha : raw25739step0 = (fun i j => raw25739 (permutation178 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25739step0 raw25739; decide +kernel
      have hl : raw25739step0Labels = raw25739Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25739 raw25739Labels permutation178 permutation2
    _ = mixedMoment B node4342 node4342Labels := by rfl

theorem canonical25740 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25740 raw25740Labels = mixedMoment B node4474 node4474Labels := by
  calc
    mixedMoment B raw25740 raw25740Labels = mixedMoment B raw25740step0 raw25740step0Labels := by
      have hz : ∀ j, raw25740 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25740step0 = (fun i j => raw25740 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25740step0 raw25740; decide +kernel
      have hl : raw25740step0Labels = raw25740Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25740 raw25740Labels permutation346 hz
    mixedMoment B raw25740step0 raw25740step0Labels = mixedMoment B raw25740step1 raw25740step1Labels := by
      have ha : raw25740step1 = (fun i j => raw25740step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25740step1 raw25740step0; decide +kernel
      have hl : raw25740step1Labels = raw25740step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25740step0 raw25740step0Labels permutation38 permutation2
    _ = mixedMoment B node4474 node4474Labels := by rfl

theorem canonical25741 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25741 raw25741Labels = mixedMoment B node4499 node4499Labels := by
  calc
    mixedMoment B raw25741 raw25741Labels = mixedMoment B raw25741step0 raw25741step0Labels := by
      have hz : ∀ j, raw25741 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw25741step0 = (fun i j => raw25741 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw25741step0 raw25741; decide +kernel
      have hl : raw25741step0Labels = raw25741Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25741 raw25741Labels permutation520 hz
    mixedMoment B raw25741step0 raw25741step0Labels = mixedMoment B raw25741step1 raw25741step1Labels := by
      have hz : ∀ j, raw25741step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw25741step1 = (fun i j => raw25741step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw25741step1 raw25741step0; decide +kernel
      have hl : raw25741step1Labels = raw25741step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25741step0 raw25741step0Labels permutation80 hz
    _ = mixedMoment B node4499 node4499Labels := by rfl

theorem canonical25742 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25742 raw25742Labels = mixedMoment B node4495 node4495Labels := by
  calc
    mixedMoment B raw25742 raw25742Labels = mixedMoment B raw25742step0 raw25742step0Labels := by
      have hz : ∀ j, raw25742 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25742step0 = (fun i j => raw25742 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25742step0 raw25742; decide +kernel
      have hl : raw25742step0Labels = raw25742Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25742 raw25742Labels permutation346 hz
    mixedMoment B raw25742step0 raw25742step0Labels = mixedMoment B raw25742step1 raw25742step1Labels := by
      have ha : raw25742step1 = (fun i j => raw25742step0 (permutation35 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25742step1 raw25742step0; decide +kernel
      have hl : raw25742step1Labels = raw25742step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25742step0 raw25742step0Labels permutation35 permutation2
    _ = mixedMoment B node4495 node4495Labels := by rfl

theorem canonical25743 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25743 raw25743Labels = mixedMoment B node4173 node4173Labels := by
  calc
    mixedMoment B raw25743 raw25743Labels = mixedMoment B raw25743step0 raw25743step0Labels := by
      have hz : ∀ j, raw25743 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw25743step0 = (fun i j => raw25743 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw25743step0 raw25743; decide +kernel
      have hl : raw25743step0Labels = raw25743Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25743 raw25743Labels permutation265 hz
    mixedMoment B raw25743step0 raw25743step0Labels = mixedMoment B raw25743step1 raw25743step1Labels := by
      have ha : raw25743step1 = (fun i j => raw25743step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25743step1 raw25743step0; decide +kernel
      have hl : raw25743step1Labels = raw25743step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25743step0 raw25743step0Labels permutation34 permutation2
    _ = mixedMoment B node4173 node4173Labels := by rfl

theorem canonical25744 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25744 raw25744Labels = mixedMoment B node4342 node4342Labels := by
  calc
    mixedMoment B raw25744 raw25744Labels = mixedMoment B raw25744step0 raw25744step0Labels := by
      have ha : raw25744step0 = (fun i j => raw25744 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25744step0 raw25744; decide +kernel
      have hl : raw25744step0Labels = raw25744Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25744 raw25744Labels permutation154 permutation2
    _ = mixedMoment B node4342 node4342Labels := by rfl

theorem canonical25745 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25745 raw25745Labels = mixedMoment B node4474 node4474Labels := by
  calc
    mixedMoment B raw25745 raw25745Labels = mixedMoment B raw25745step0 raw25745step0Labels := by
      have hz : ∀ j, raw25745 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw25745step0 = (fun i j => raw25745 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw25745step0 raw25745; decide +kernel
      have hl : raw25745step0Labels = raw25745Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25745 raw25745Labels permutation265 hz
    mixedMoment B raw25745step0 raw25745step0Labels = mixedMoment B raw25745step1 raw25745step1Labels := by
      have ha : raw25745step1 = (fun i j => raw25745step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25745step1 raw25745step0; decide +kernel
      have hl : raw25745step1Labels = raw25745step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25745step0 raw25745step0Labels permutation38 permutation2
    _ = mixedMoment B node4474 node4474Labels := by rfl

theorem canonical25746 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25746 raw25746Labels = mixedMoment B node4499 node4499Labels := by
  calc
    mixedMoment B raw25746 raw25746Labels = mixedMoment B raw25746step0 raw25746step0Labels := by
      have hz : ∀ j, raw25746 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw25746step0 = (fun i j => raw25746 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw25746step0 raw25746; decide +kernel
      have hl : raw25746step0Labels = raw25746Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25746 raw25746Labels permutation520 hz
    mixedMoment B raw25746step0 raw25746step0Labels = mixedMoment B raw25746step1 raw25746step1Labels := by
      have hz : ∀ j, raw25746step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw25746step1 = (fun i j => raw25746step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw25746step1 raw25746step0; decide +kernel
      have hl : raw25746step1Labels = raw25746step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25746step0 raw25746step0Labels permutation56 hz
    _ = mixedMoment B node4499 node4499Labels := by rfl

theorem canonical25747 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25747 raw25747Labels = mixedMoment B node4495 node4495Labels := by
  calc
    mixedMoment B raw25747 raw25747Labels = mixedMoment B raw25747step0 raw25747step0Labels := by
      have hz : ∀ j, raw25747 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw25747step0 = (fun i j => raw25747 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw25747step0 raw25747; decide +kernel
      have hl : raw25747step0Labels = raw25747Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25747 raw25747Labels permutation265 hz
    mixedMoment B raw25747step0 raw25747step0Labels = mixedMoment B raw25747step1 raw25747step1Labels := by
      have ha : raw25747step1 = (fun i j => raw25747step0 (permutation35 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25747step1 raw25747step0; decide +kernel
      have hl : raw25747step1Labels = raw25747step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25747step0 raw25747step0Labels permutation35 permutation2
    _ = mixedMoment B node4495 node4495Labels := by rfl

theorem canonical25748 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25748 raw25748Labels = mixedMoment B node4180 node4180Labels := by
  calc
    mixedMoment B raw25748 raw25748Labels = mixedMoment B raw25748step0 raw25748step0Labels := by
      have hz : ∀ j, raw25748 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25748step0 = (fun i j => raw25748 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25748step0 raw25748; decide +kernel
      have hl : raw25748step0Labels = raw25748Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25748 raw25748Labels permutation346 hz
    mixedMoment B raw25748step0 raw25748step0Labels = mixedMoment B raw25748step1 raw25748step1Labels := by
      have hz : ∀ j, raw25748step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw25748step1 = (fun i j => raw25748step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw25748step1 raw25748step0; decide +kernel
      have hl : raw25748step1Labels = raw25748step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25748step0 raw25748step0Labels permutation56 hz
    mixedMoment B raw25748step1 raw25748step1Labels = mixedMoment B raw25748step2 raw25748step2Labels := by
      have ha : raw25748step2 = (fun i j => raw25748step1 (permutation11 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25748step2 raw25748step1; decide +kernel
      have hl : raw25748step2Labels = raw25748step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25748step1 raw25748step1Labels permutation11 permutation2
    _ = mixedMoment B node4180 node4180Labels := by rfl

theorem canonical25749 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25749 raw25749Labels = mixedMoment B node4349 node4349Labels := by
  calc
    mixedMoment B raw25749 raw25749Labels = mixedMoment B raw25749step0 raw25749step0Labels := by
      have hz : ∀ j, raw25749 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25749step0 = (fun i j => raw25749 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25749step0 raw25749; decide +kernel
      have hl : raw25749step0Labels = raw25749Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25749 raw25749Labels permutation346 hz
    mixedMoment B raw25749step0 raw25749step0Labels = mixedMoment B raw25749step1 raw25749step1Labels := by
      have ha : raw25749step1 = (fun i j => raw25749step0 (permutation35 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25749step1 raw25749step0; decide +kernel
      have hl : raw25749step1Labels = raw25749step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25749step0 raw25749step0Labels permutation35 permutation2
    _ = mixedMoment B node4349 node4349Labels := by rfl

theorem canonical25750 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25750 raw25750Labels = mixedMoment B node4349 node4349Labels := by
  calc
    mixedMoment B raw25750 raw25750Labels = mixedMoment B raw25750step0 raw25750step0Labels := by
      have hz : ∀ j, raw25750 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw25750step0 = (fun i j => raw25750 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw25750step0 raw25750; decide +kernel
      have hl : raw25750step0Labels = raw25750Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25750 raw25750Labels permutation265 hz
    mixedMoment B raw25750step0 raw25750step0Labels = mixedMoment B raw25750step1 raw25750step1Labels := by
      have ha : raw25750step1 = (fun i j => raw25750step0 (permutation35 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25750step1 raw25750step0; decide +kernel
      have hl : raw25750step1Labels = raw25750step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25750step0 raw25750step0Labels permutation35 permutation2
    _ = mixedMoment B node4349 node4349Labels := by rfl

theorem canonical25751 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25751 raw25751Labels = mixedMoment B node4511 node4511Labels := by
  calc
    mixedMoment B raw25751 raw25751Labels = mixedMoment B raw25751step0 raw25751step0Labels := by
      have hz : ∀ j, raw25751 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw25751step0 = (fun i j => raw25751 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw25751step0 raw25751; decide +kernel
      have hl : raw25751step0Labels = raw25751Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25751 raw25751Labels permutation520 hz
    mixedMoment B raw25751step0 raw25751step0Labels = mixedMoment B raw25751step1 raw25751step1Labels := by
      have hz : ∀ j, raw25751step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw25751step1 = (fun i j => raw25751step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw25751step1 raw25751step0; decide +kernel
      have hl : raw25751step1Labels = raw25751step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25751step0 raw25751step0Labels permutation80 hz
    mixedMoment B raw25751step1 raw25751step1Labels = mixedMoment B raw25751step2 raw25751step2Labels := by
      have hz : ∀ j, raw25751step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw25751step2 = (fun i j => raw25751step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw25751step2 raw25751step1; decide +kernel
      have hl : raw25751step2Labels = raw25751step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25751step1 raw25751step1Labels permutation14 hz
    mixedMoment B raw25751step2 raw25751step2Labels = mixedMoment B raw25751step3 raw25751step3Labels := by
      have ha : raw25751step3 = (fun i j => raw25751step2 (permutation3 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25751step3 raw25751step2; decide +kernel
      have hl : raw25751step3Labels = raw25751step2Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25751step2 raw25751step2Labels permutation3 permutation2
    _ = mixedMoment B node4511 node4511Labels := by rfl

theorem canonical25752 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25752 raw25752Labels = mixedMoment B node4498 node4498Labels := by
  calc
    mixedMoment B raw25752 raw25752Labels = mixedMoment B raw25752step0 raw25752step0Labels := by
      have hz : ∀ j, raw25752 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25752step0 = (fun i j => raw25752 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25752step0 raw25752; decide +kernel
      have hl : raw25752step0Labels = raw25752Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25752 raw25752Labels permutation346 hz
    mixedMoment B raw25752step0 raw25752step0Labels = mixedMoment B raw25752step1 raw25752step1Labels := by
      have hz : ∀ j, raw25752step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw25752step1 = (fun i j => raw25752step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw25752step1 raw25752step0; decide +kernel
      have hl : raw25752step1Labels = raw25752step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25752step0 raw25752step0Labels permutation56 hz
    mixedMoment B raw25752step1 raw25752step1Labels = mixedMoment B raw25752step2 raw25752step2Labels := by
      have ha : raw25752step2 = (fun i j => raw25752step1 (permutation11 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25752step2 raw25752step1; decide +kernel
      have hl : raw25752step2Labels = raw25752step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25752step1 raw25752step1Labels permutation11 permutation2
    _ = mixedMoment B node4498 node4498Labels := by rfl

theorem canonical25753 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25753 raw25753Labels = mixedMoment B node4188 node4188Labels := by
  calc
    mixedMoment B raw25753 raw25753Labels = mixedMoment B raw25753step0 raw25753step0Labels := by
      have hz : ∀ j, raw25753 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25753step0 = (fun i j => raw25753 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25753step0 raw25753; decide +kernel
      have hl : raw25753step0Labels = raw25753Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25753 raw25753Labels permutation346 hz
    mixedMoment B raw25753step0 raw25753step0Labels = mixedMoment B raw25753step1 raw25753step1Labels := by
      have hz : ∀ j, raw25753step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw25753step1 = (fun i j => raw25753step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw25753step1 raw25753step0; decide +kernel
      have hl : raw25753step1Labels = raw25753step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25753step0 raw25753step0Labels permutation56 hz
    _ = mixedMoment B node4188 node4188Labels := by rfl

theorem canonical25754 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25754 raw25754Labels = mixedMoment B node4357 node4357Labels := by
  calc
    mixedMoment B raw25754 raw25754Labels = mixedMoment B raw25754step0 raw25754step0Labels := by
      have hz : ∀ j, raw25754 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25754step0 = (fun i j => raw25754 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25754step0 raw25754; decide +kernel
      have hl : raw25754step0Labels = raw25754Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25754 raw25754Labels permutation346 hz
    _ = mixedMoment B node4357 node4357Labels := by rfl

theorem canonical25755 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25755 raw25755Labels = mixedMoment B node4357 node4357Labels := by
  calc
    mixedMoment B raw25755 raw25755Labels = mixedMoment B raw25755step0 raw25755step0Labels := by
      have hz : ∀ j, raw25755 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw25755step0 = (fun i j => raw25755 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw25755step0 raw25755; decide +kernel
      have hl : raw25755step0Labels = raw25755Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25755 raw25755Labels permutation265 hz
    _ = mixedMoment B node4357 node4357Labels := by rfl

theorem canonical25756 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25756 raw25756Labels = mixedMoment B node4480 node4480Labels := by
  calc
    mixedMoment B raw25756 raw25756Labels = mixedMoment B raw25756step0 raw25756step0Labels := by
      have hz : ∀ j, raw25756 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25756step0 = (fun i j => raw25756 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25756step0 raw25756; decide +kernel
      have hl : raw25756step0Labels = raw25756Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25756 raw25756Labels permutation346 hz
    mixedMoment B raw25756step0 raw25756step0Labels = mixedMoment B raw25756step1 raw25756step1Labels := by
      have hz : ∀ j, raw25756step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw25756step1 = (fun i j => raw25756step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw25756step1 raw25756step0; decide +kernel
      have hl : raw25756step1Labels = raw25756step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25756step0 raw25756step0Labels permutation56 hz
    _ = mixedMoment B node4480 node4480Labels := by rfl

theorem canonical25757 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25757 raw25757Labels = mixedMoment B node4503 node4503Labels := by
  calc
    mixedMoment B raw25757 raw25757Labels = mixedMoment B raw25757step0 raw25757step0Labels := by
      have hz : ∀ j, raw25757 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25757step0 = (fun i j => raw25757 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25757step0 raw25757; decide +kernel
      have hl : raw25757step0Labels = raw25757Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25757 raw25757Labels permutation346 hz
    mixedMoment B raw25757step0 raw25757step0Labels = mixedMoment B raw25757step1 raw25757step1Labels := by
      have hz : ∀ j, raw25757step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw25757step1 = (fun i j => raw25757step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw25757step1 raw25757step0; decide +kernel
      have hl : raw25757step1Labels = raw25757step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25757step0 raw25757step0Labels permutation56 hz
    mixedMoment B raw25757step1 raw25757step1Labels = mixedMoment B raw25757step2 raw25757step2Labels := by
      have ha : raw25757step2 = (fun i j => raw25757step1 (permutation12 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25757step2 raw25757step1; decide +kernel
      have hl : raw25757step2Labels = raw25757step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25757step1 raw25757step1Labels permutation12 permutation2
    _ = mixedMoment B node4503 node4503Labels := by rfl

theorem canonical25758 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25758 raw25758Labels = mixedMoment B node4178 node4178Labels := by
  calc
    mixedMoment B raw25758 raw25758Labels = mixedMoment B raw25758step0 raw25758step0Labels := by
      have hz : ∀ j, raw25758 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25758step0 = (fun i j => raw25758 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25758step0 raw25758; decide +kernel
      have hl : raw25758step0Labels = raw25758Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25758 raw25758Labels permutation346 hz
    mixedMoment B raw25758step0 raw25758step0Labels = mixedMoment B raw25758step1 raw25758step1Labels := by
      have hz : ∀ j, raw25758step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw25758step1 = (fun i j => raw25758step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw25758step1 raw25758step0; decide +kernel
      have hl : raw25758step1Labels = raw25758step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25758step0 raw25758step0Labels permutation56 hz
    mixedMoment B raw25758step1 raw25758step1Labels = mixedMoment B raw25758step2 raw25758step2Labels := by
      have ha : raw25758step2 = (fun i j => raw25758step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25758step2 raw25758step1; decide +kernel
      have hl : raw25758step2Labels = raw25758step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25758step1 raw25758step1Labels permutation10 permutation2
    _ = mixedMoment B node4178 node4178Labels := by rfl

theorem canonical25759 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25759 raw25759Labels = mixedMoment B node4347 node4347Labels := by
  calc
    mixedMoment B raw25759 raw25759Labels = mixedMoment B raw25759step0 raw25759step0Labels := by
      have hz : ∀ j, raw25759 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25759step0 = (fun i j => raw25759 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25759step0 raw25759; decide +kernel
      have hl : raw25759step0Labels = raw25759Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25759 raw25759Labels permutation346 hz
    mixedMoment B raw25759step0 raw25759step0Labels = mixedMoment B raw25759step1 raw25759step1Labels := by
      have ha : raw25759step1 = (fun i j => raw25759step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25759step1 raw25759step0; decide +kernel
      have hl : raw25759step1Labels = raw25759step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25759step0 raw25759step0Labels permutation34 permutation2
    _ = mixedMoment B node4347 node4347Labels := by rfl

theorem canonical25760 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25760 raw25760Labels = mixedMoment B node4347 node4347Labels := by
  calc
    mixedMoment B raw25760 raw25760Labels = mixedMoment B raw25760step0 raw25760step0Labels := by
      have hz : ∀ j, raw25760 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw25760step0 = (fun i j => raw25760 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw25760step0 raw25760; decide +kernel
      have hl : raw25760step0Labels = raw25760Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25760 raw25760Labels permutation265 hz
    mixedMoment B raw25760step0 raw25760step0Labels = mixedMoment B raw25760step1 raw25760step1Labels := by
      have ha : raw25760step1 = (fun i j => raw25760step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25760step1 raw25760step0; decide +kernel
      have hl : raw25760step1Labels = raw25760step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25760step0 raw25760step0Labels permutation34 permutation2
    _ = mixedMoment B node4347 node4347Labels := by rfl

theorem canonical25761 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25761 raw25761Labels = mixedMoment B node4476 node4476Labels := by
  calc
    mixedMoment B raw25761 raw25761Labels = mixedMoment B raw25761step0 raw25761step0Labels := by
      have hz : ∀ j, raw25761 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25761step0 = (fun i j => raw25761 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25761step0 raw25761; decide +kernel
      have hl : raw25761step0Labels = raw25761Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25761 raw25761Labels permutation346 hz
    mixedMoment B raw25761step0 raw25761step0Labels = mixedMoment B raw25761step1 raw25761step1Labels := by
      have hz : ∀ j, raw25761step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw25761step1 = (fun i j => raw25761step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw25761step1 raw25761step0; decide +kernel
      have hl : raw25761step1Labels = raw25761step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25761step0 raw25761step0Labels permutation56 hz
    _ = mixedMoment B node4476 node4476Labels := by rfl

theorem canonical25762 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25762 raw25762Labels = mixedMoment B node4507 node4507Labels := by
  calc
    mixedMoment B raw25762 raw25762Labels = mixedMoment B raw25762step0 raw25762step0Labels := by
      have hz : ∀ j, raw25762 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw25762step0 = (fun i j => raw25762 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw25762step0 raw25762; decide +kernel
      have hl : raw25762step0Labels = raw25762Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25762 raw25762Labels permutation520 hz
    mixedMoment B raw25762step0 raw25762step0Labels = mixedMoment B raw25762step1 raw25762step1Labels := by
      have hz : ∀ j, raw25762step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw25762step1 = (fun i j => raw25762step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw25762step1 raw25762step0; decide +kernel
      have hl : raw25762step1Labels = raw25762step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25762step0 raw25762step0Labels permutation80 hz
    mixedMoment B raw25762step1 raw25762step1Labels = mixedMoment B raw25762step2 raw25762step2Labels := by
      have hz : ∀ j, raw25762step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw25762step2 = (fun i j => raw25762step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw25762step2 raw25762step1; decide +kernel
      have hl : raw25762step2Labels = raw25762step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25762step1 raw25762step1Labels permutation14 hz
    _ = mixedMoment B node4507 node4507Labels := by rfl

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

theorem canonical816 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw816 raw816Labels = mixedMoment B node4180 node4180Labels := by
  calc
    mixedMoment B raw816 raw816Labels = mixedMoment B raw816step0 raw816step0Labels := by
      have ha : raw816step0 = (fun i j => raw816 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw816step0 raw816; decide +kernel
      have hl : raw816step0Labels = raw816Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw816 raw816Labels permutation8 permutation4
    mixedMoment B raw816step0 raw816step0Labels = mixedMoment B raw816step1 raw816step1Labels := by
      have ha : raw816step1 = raw816step0 := by apply Matrix.ext; unfold raw816step1 raw816step0; decide +kernel
      have hl : raw816step0Labels = labelEmbedding7 ∘ raw816step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw816step0 raw816step0Labels raw816step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4180 node4180Labels := by rfl

theorem canonical817 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw817 raw817Labels = mixedMoment B node608 node608Labels := by
  calc
    mixedMoment B raw817 raw817Labels = mixedMoment B raw817step0 raw817step0Labels := by
      have ha : raw817step0 = (fun i j => raw817 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw817step0 raw817; decide +kernel
      have hl : raw817step0Labels = raw817Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw817 raw817Labels permutation8 permutation4
    _ = mixedMoment B node608 node608Labels := by rfl

theorem canonical818 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw818 raw818Labels = mixedMoment B node1519 node1519Labels := by
  calc
    mixedMoment B raw818 raw818Labels = mixedMoment B raw818step0 raw818step0Labels := by
      have ha : raw818step0 = (fun i j => raw818 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw818step0 raw818; decide +kernel
      have hl : raw818step0Labels = raw818Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw818 raw818Labels permutation8 permutation6
    mixedMoment B raw818step0 raw818step0Labels = mixedMoment B raw818step1 raw818step1Labels := by
      have ha : raw818step1 = -raw818step0 := by apply Matrix.ext; change ∀ i j, raw818step1 i j = -(raw818step0 i j); unfold raw818step1 raw818step0; decide +kernel
      have hl : raw818step1Labels = raw818step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw818step1 raw818step1Labels = mixedMoment B raw818step2 raw818step2Labels := by
      have ha : raw818step2 = raw818step1 := by apply Matrix.ext; unfold raw818step2 raw818step1; decide +kernel
      have hl : raw818step1Labels = labelEmbedding1 ∘ raw818step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw818step1 raw818step1Labels raw818step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1519 node1519Labels := by rfl

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

theorem canonical1134 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1134 raw1134Labels = mixedMoment B node4349 node4349Labels := by
  calc
    mixedMoment B raw1134 raw1134Labels = mixedMoment B raw1134step0 raw1134step0Labels := by
      have ha : raw1134step0 = (fun i j => raw1134 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1134step0 raw1134; decide +kernel
      have hl : raw1134step0Labels = raw1134Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1134 raw1134Labels permutation32 permutation4
    mixedMoment B raw1134step0 raw1134step0Labels = mixedMoment B raw1134step1 raw1134step1Labels := by
      have ha : raw1134step1 = raw1134step0 := by apply Matrix.ext; unfold raw1134step1 raw1134step0; decide +kernel
      have hl : raw1134step0Labels = labelEmbedding7 ∘ raw1134step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1134step0 raw1134step0Labels raw1134step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4349 node4349Labels := by rfl

theorem canonical1135 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1135 raw1135Labels = mixedMoment B node927 node927Labels := by
  calc
    mixedMoment B raw1135 raw1135Labels = mixedMoment B raw1135step0 raw1135step0Labels := by
      have ha : raw1135step0 = (fun i j => raw1135 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1135step0 raw1135; decide +kernel
      have hl : raw1135step0Labels = raw1135Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1135 raw1135Labels permutation32 permutation4
    _ = mixedMoment B node927 node927Labels := by rfl

theorem canonical1136 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1136 raw1136Labels = mixedMoment B node1675 node1675Labels := by
  calc
    mixedMoment B raw1136 raw1136Labels = mixedMoment B raw1136step0 raw1136step0Labels := by
      have ha : raw1136step0 = (fun i j => raw1136 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1136step0 raw1136; decide +kernel
      have hl : raw1136step0Labels = raw1136Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1136 raw1136Labels permutation32 permutation6
    mixedMoment B raw1136step0 raw1136step0Labels = mixedMoment B raw1136step1 raw1136step1Labels := by
      have ha : raw1136step1 = -raw1136step0 := by apply Matrix.ext; change ∀ i j, raw1136step1 i j = -(raw1136step0 i j); unfold raw1136step1 raw1136step0; decide +kernel
      have hl : raw1136step1Labels = raw1136step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1136step1 raw1136step1Labels = mixedMoment B raw1136step2 raw1136step2Labels := by
      have ha : raw1136step2 = raw1136step1 := by apply Matrix.ext; unfold raw1136step2 raw1136step1; decide +kernel
      have hl : raw1136step1Labels = labelEmbedding1 ∘ raw1136step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1136step1 raw1136step1Labels raw1136step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1675 node1675Labels := by rfl

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

theorem singleton4180 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4180 node4180Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node608 node608Labels + mixedMoment B node1519 node1519Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw816 singletonSmall4180
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4180) = raw816Labels := by decide +kernel
  rw [hl, canonical816 B hB] at h
  have hc0 : mixedMoment B raw816 (Fin.cases (0 : Fin 2) singletonSmall4180) =
      mixedMoment B node608 node608Labels := by
    have ha : raw816 = raw817 := by apply Matrix.ext; unfold raw816 raw817; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4180 = raw817Labels := by decide +kernel
    rw [ha, hj, canonical817 B hB]
  have hc1 : mixedMoment B raw816 (Fin.cases (1 : Fin 2) singletonSmall4180) =
      mixedMoment B node1519 node1519Labels := by
    have ha : raw816 = raw818 := by apply Matrix.ext; unfold raw816 raw818; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4180 = raw818Labels := by decide +kernel
    rw [ha, hj, canonical818 B hB]
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

theorem singleton4349 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4349 node4349Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node927 node927Labels + mixedMoment B node1675 node1675Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1134 singletonSmall4349
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4349) = raw1134Labels := by decide +kernel
  rw [hl, canonical1134 B hB] at h
  have hc0 : mixedMoment B raw1134 (Fin.cases (0 : Fin 2) singletonSmall4349) =
      mixedMoment B node927 node927Labels := by
    have ha : raw1134 = raw1135 := by apply Matrix.ext; unfold raw1134 raw1135; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4349 = raw1135Labels := by decide +kernel
    rw [ha, hj, canonical1135 B hB]
  have hc1 : mixedMoment B raw1134 (Fin.cases (1 : Fin 2) singletonSmall4349) =
      mixedMoment B node1675 node1675Labels := by
    have ha : raw1134 = raw1136 := by apply Matrix.ext; unfold raw1134 raw1136; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4349 = raw1136Labels := by decide +kernel
    rw [ha, hj, canonical1136 B hB]
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

theorem singleton4499 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4499 node4499Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1083 node1083Labels + mixedMoment B node1728 node1728Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1299 singletonSmall4499
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4499) = raw1299Labels := by decide +kernel
  rw [hl, canonical1299 B hB] at h
  have hc0 : mixedMoment B raw1299 (Fin.cases (0 : Fin 2) singletonSmall4499) =
      mixedMoment B node1083 node1083Labels := by
    have ha : raw1299 = raw1300 := by apply Matrix.ext; unfold raw1299 raw1300; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4499 = raw1300Labels := by decide +kernel
    rw [ha, hj, canonical1300 B hB]
  have hc1 : mixedMoment B raw1299 (Fin.cases (1 : Fin 2) singletonSmall4499) =
      mixedMoment B node1728 node1728Labels := by
    have ha : raw1299 = raw1301 := by apply Matrix.ext; unfold raw1299 raw1301; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4499 = raw1301Labels := by decide +kernel
    rw [ha, hj, canonical1301 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4503 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4503 node4503Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1087 node1087Labels + mixedMoment B node1739 node1739Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1302 singletonSmall4503
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4503) = raw1302Labels := by decide +kernel
  rw [hl, canonical1302 B hB] at h
  have hc0 : mixedMoment B raw1302 (Fin.cases (0 : Fin 2) singletonSmall4503) =
      mixedMoment B node1087 node1087Labels := by
    have ha : raw1302 = raw1303 := by apply Matrix.ext; unfold raw1302 raw1303; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4503 = raw1303Labels := by decide +kernel
    rw [ha, hj, canonical1303 B hB]
  have hc1 : mixedMoment B raw1302 (Fin.cases (1 : Fin 2) singletonSmall4503) =
      mixedMoment B node1739 node1739Labels := by
    have ha : raw1302 = raw1304 := by apply Matrix.ext; unfold raw1302 raw1304; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4503 = raw1304Labels := by decide +kernel
    rw [ha, hj, canonical1304 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4507 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4507 node4507Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1091 node1091Labels + mixedMoment B node1756 node1756Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1305 singletonSmall4507
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4507) = raw1305Labels := by decide +kernel
  rw [hl, canonical1305 B hB] at h
  have hc0 : mixedMoment B raw1305 (Fin.cases (0 : Fin 2) singletonSmall4507) =
      mixedMoment B node1091 node1091Labels := by
    have ha : raw1305 = raw1306 := by apply Matrix.ext; unfold raw1305 raw1306; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4507 = raw1306Labels := by decide +kernel
    rw [ha, hj, canonical1306 B hB]
  have hc1 : mixedMoment B raw1305 (Fin.cases (1 : Fin 2) singletonSmall4507) =
      mixedMoment B node1756 node1756Labels := by
    have ha : raw1305 = raw1307 := by apply Matrix.ext; unfold raw1305 raw1307; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4507 = raw1307Labels := by decide +kernel
    rw [ha, hj, canonical1307 B hB]
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

theorem singleton4835 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4835 node4835Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2054 node2054Labels + mixedMoment B node2206 node2206Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1767 singletonSmall4835
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4835) = raw1767Labels := by decide +kernel
  rw [hl, canonical1767 B hB] at h
  have hc0 : mixedMoment B raw1767 (Fin.cases (0 : Fin 2) singletonSmall4835) =
      mixedMoment B node2054 node2054Labels := by
    have ha : raw1767 = raw1768 := by apply Matrix.ext; unfold raw1767 raw1768; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4835 = raw1768Labels := by decide +kernel
    rw [ha, hj, canonical1768 B hB]
  have hc1 : mixedMoment B raw1767 (Fin.cases (1 : Fin 2) singletonSmall4835) =
      mixedMoment B node2206 node2206Labels := by
    have ha : raw1767 = raw1769 := by apply Matrix.ext; unfold raw1767 raw1769; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4835 = raw1769Labels := by decide +kernel
    rw [ha, hj, canonical1769 B hB]
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

theorem singleton4896 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4896 node4896Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2266 node2266Labels + mixedMoment B node2278 node2278Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1824 singletonSmall4896
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4896) = raw1824Labels := by decide +kernel
  rw [hl, canonical1824 B hB] at h
  have hc0 : mixedMoment B raw1824 (Fin.cases (0 : Fin 2) singletonSmall4896) =
      mixedMoment B node2266 node2266Labels := by
    have ha : raw1824 = raw1825 := by apply Matrix.ext; unfold raw1824 raw1825; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4896 = raw1825Labels := by decide +kernel
    rw [ha, hj, canonical1825 B hB]
  have hc1 : mixedMoment B raw1824 (Fin.cases (1 : Fin 2) singletonSmall4896) =
      mixedMoment B node2278 node2278Labels := by
    have ha : raw1824 = raw1826 := by apply Matrix.ext; unfold raw1824 raw1826; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4896 = raw1826Labels := by decide +kernel
    rw [ha, hj, canonical1826 B hB]
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

theorem sound927 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node927 node927Labels = Sparse.eval nodeValue927 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 927) = mixedMoment B node927 node927Labels := rfl
  simpa [nodeValue927, Sparse.eval] using hc.symm

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

theorem sound1079 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1079 node1079Labels = Sparse.eval nodeValue1079 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1079) = mixedMoment B node1079 node1079Labels := rfl
  simpa [nodeValue1079, Sparse.eval] using hc.symm

theorem sound1083 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1083 node1083Labels = Sparse.eval nodeValue1083 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1083) = mixedMoment B node1083 node1083Labels := rfl
  simpa [nodeValue1083, Sparse.eval] using hc.symm

theorem sound1087 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1087 node1087Labels = Sparse.eval nodeValue1087 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1087) = mixedMoment B node1087 node1087Labels := rfl
  simpa [nodeValue1087, Sparse.eval] using hc.symm

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

theorem sound1091 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1091 node1091Labels = Sparse.eval nodeValue1091 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1091) = mixedMoment B node1091 node1091Labels := rfl
  simpa [nodeValue1091, Sparse.eval] using hc.symm

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

theorem sound1519 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1519 node1519Labels = Sparse.eval nodeValue1519 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1519) = mixedMoment B node1519 node1519Labels := rfl
  simpa [nodeValue1519, Sparse.eval] using hc.symm

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

theorem sound1675 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1675 node1675Labels = Sparse.eval nodeValue1675 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1675) = mixedMoment B node1675 node1675Labels := rfl
  simpa [nodeValue1675, Sparse.eval] using hc.symm

theorem sound1708 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1708 node1708Labels = Sparse.eval nodeValue1708 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1708) = mixedMoment B node1708 node1708Labels := rfl
  simpa [nodeValue1708, Sparse.eval] using hc.symm

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

theorem sound1739 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1739 node1739Labels = Sparse.eval nodeValue1739 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1739) = mixedMoment B node1739 node1739Labels := rfl
  simpa [nodeValue1739, Sparse.eval] using hc.symm

theorem sound1756 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1756 node1756Labels = Sparse.eval nodeValue1756 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1756) = mixedMoment B node1756 node1756Labels := rfl
  simpa [nodeValue1756, Sparse.eval] using hc.symm

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

theorem sound2054 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2054 node2054Labels = Sparse.eval nodeValue2054 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2054) = mixedMoment B node2054 node2054Labels := rfl
  simpa [nodeValue2054, Sparse.eval] using hc.symm

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

theorem sound2206 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2206 node2206Labels = Sparse.eval nodeValue2206 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2206) = mixedMoment B node2206 node2206Labels := rfl
  simpa [nodeValue2206, Sparse.eval] using hc.symm

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

theorem sound2266 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2266 node2266Labels = Sparse.eval nodeValue2266 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2266) = mixedMoment B node2266 node2266Labels := rfl
  simpa [nodeValue2266, Sparse.eval] using hc.symm

theorem sound2278 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2278 node2278Labels = Sparse.eval nodeValue2278 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2278) = mixedMoment B node2278 node2278Labels := rfl
  simpa [nodeValue2278, Sparse.eval] using hc.symm

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

theorem sound608 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node608 node608Labels = Sparse.eval nodeValue608 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 608) = mixedMoment B node608 node608Labels := rfl
  simpa [nodeValue608, Sparse.eval] using hc.symm

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

theorem sound4173 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4173 node4173Labels = Sparse.eval nodeValue4173 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4173) = mixedMoment B node4173 node4173Labels := rfl
  simpa [nodeValue4173, Sparse.eval] using hc.symm

theorem sound4178 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4178 node4178Labels = Sparse.eval nodeValue4178 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4178) = mixedMoment B node4178 node4178Labels := rfl
  simpa [nodeValue4178, Sparse.eval] using hc.symm

theorem sound4180 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4180 node4180Labels = Sparse.eval nodeValue4180 (mixedVector B) := by
  have h := singleton4180 B _hB
  rw [sound608 B _hB _hF, sound1519 B _hB _hF] at h
  norm_num [nodeValue4180, nodeValue608, nodeValue1519, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4188 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4188 node4188Labels = Sparse.eval nodeValue4188 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4188) = mixedMoment B node4188 node4188Labels := rfl
  simpa [nodeValue4188, Sparse.eval] using hc.symm

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

theorem zero4342 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node4342 node4342Labels = 0 := by
  exact mixedMoment_alpha B hF node4342 node4342Labels 1 permutation160
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

theorem sound4342 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4342 node4342Labels = Sparse.eval nodeValue4342 (mixedVector B) := by
  simpa only [nodeValue4342, Sparse.eval_nil] using zero4342 B _hB _hF

theorem sound4347 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4347 node4347Labels = Sparse.eval nodeValue4347 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4347) = mixedMoment B node4347 node4347Labels := rfl
  simpa [nodeValue4347, Sparse.eval] using hc.symm

theorem sound4349 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4349 node4349Labels = Sparse.eval nodeValue4349 (mixedVector B) := by
  have h := singleton4349 B _hB
  rw [sound927 B _hB _hF, sound1675 B _hB _hF] at h
  norm_num [nodeValue4349, nodeValue927, nodeValue1675, Sparse.eval] at h ⊢
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

theorem sound4357 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4357 node4357Labels = Sparse.eval nodeValue4357 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4357) = mixedMoment B node4357 node4357Labels := rfl
  simpa [nodeValue4357, Sparse.eval] using hc.symm

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

theorem sound4474 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4474 node4474Labels = Sparse.eval nodeValue4474 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4474) = mixedMoment B node4474 node4474Labels := rfl
  simpa [nodeValue4474, Sparse.eval] using hc.symm

theorem sound4476 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4476 node4476Labels = Sparse.eval nodeValue4476 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4476) = mixedMoment B node4476 node4476Labels := rfl
  simpa [nodeValue4476, Sparse.eval] using hc.symm

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

theorem zero4511 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4511 node4511Labels = 0 := by
  exact mixedMoment_order_one B hB node4511 node4511Labels 1
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

theorem sound4480 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4480 node4480Labels = Sparse.eval nodeValue4480 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4480) = mixedMoment B node4480 node4480Labels := rfl
  simpa [nodeValue4480, Sparse.eval] using hc.symm

theorem sound4495 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4495 node4495Labels = Sparse.eval nodeValue4495 (mixedVector B) := by
  have h := singleton4495 B _hB
  rw [sound1079 B _hB _hF, sound1708 B _hB _hF] at h
  norm_num [nodeValue4495, nodeValue1079, nodeValue1708, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4498 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4498 node4498Labels = Sparse.eval nodeValue4498 (mixedVector B) := by
  simpa only [nodeValue4498, Sparse.eval_nil] using zero4498 B _hB _hF

theorem sound4499 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4499 node4499Labels = Sparse.eval nodeValue4499 (mixedVector B) := by
  have h := singleton4499 B _hB
  rw [sound1083 B _hB _hF, sound1728 B _hB _hF] at h
  norm_num [nodeValue4499, nodeValue1083, nodeValue1728, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4503 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4503 node4503Labels = Sparse.eval nodeValue4503 (mixedVector B) := by
  have h := singleton4503 B _hB
  rw [sound1087 B _hB _hF, sound1739 B _hB _hF] at h
  norm_num [nodeValue4503, nodeValue1087, nodeValue1739, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4507 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4507 node4507Labels = Sparse.eval nodeValue4507 (mixedVector B) := by
  have h := singleton4507 B _hB
  rw [sound1091 B _hB _hF, sound1756 B _hB _hF] at h
  norm_num [nodeValue4507, nodeValue1091, nodeValue1756, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4511 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4511 node4511Labels = Sparse.eval nodeValue4511 (mixedVector B) := by
  simpa only [nodeValue4511, Sparse.eval_nil] using zero4511 B _hB _hF

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

theorem sound4835 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4835 node4835Labels = Sparse.eval nodeValue4835 (mixedVector B) := by
  have h := singleton4835 B _hB
  rw [sound2054 B _hB _hF, sound2206 B _hB _hF] at h
  norm_num [nodeValue4835, nodeValue2054, nodeValue2206, Sparse.eval] at h ⊢
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

theorem zero4895 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4895 node4895Labels = 0 := by
  exact mixedMoment_order_one B hB node4895 node4895Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero4901 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4901 node4901Labels = 0 := by
  exact mixedMoment_order_one B hB node4901 node4901Labels 1
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

theorem sound4895 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4895 node4895Labels = Sparse.eval nodeValue4895 (mixedVector B) := by
  simpa only [nodeValue4895, Sparse.eval_nil] using zero4895 B _hB _hF

theorem sound4896 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4896 node4896Labels = Sparse.eval nodeValue4896 (mixedVector B) := by
  have h := singleton4896 B _hB
  rw [sound2266 B _hB _hF, sound2278 B _hB _hF] at h
  norm_num [nodeValue4896, nodeValue2266, nodeValue2278, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4901 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4901 node4901Labels = Sparse.eval nodeValue4901 (mixedVector B) := by
  simpa only [nodeValue4901, Sparse.eval_nil] using zero4901 B _hB _hF

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources55
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sourceEq1775 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1775 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1775 + difference 0 1) (sourceB1775 + difference 1 0) sourceC1775) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4835) := by
    have ha : (tripleCharges (sourceA1775 + difference 0 1) (sourceB1775 + difference 1 0) sourceC1775) = raw25733 := by
      apply Matrix.ext; unfold tripleCharges sourceA1775 sourceB1775 sourceC1775 difference raw25733; decide +kernel
    rw [ha]
    exact (canonical25733 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1775 + difference 0 2) (sourceB1775 + difference 2 0) sourceC1775) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4835) := by
    have ha : (tripleCharges (sourceA1775 + difference 0 2) (sourceB1775 + difference 2 0) sourceC1775) = raw25734 := by
      apply Matrix.ext; unfold tripleCharges sourceA1775 sourceB1775 sourceC1775 difference raw25734; decide +kernel
    rw [ha]
    exact (canonical25734 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1775 + difference 0 3) (sourceB1775 + difference 3 0) sourceC1775) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4896) := by
    have ha : (tripleCharges (sourceA1775 + difference 0 3) (sourceB1775 + difference 3 0) sourceC1775) = raw25735 := by
      apply Matrix.ext; unfold tripleCharges sourceA1775 sourceB1775 sourceC1775 difference raw25735; decide +kernel
    rw [ha]
    exact (canonical25735 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1775 + difference 0 4) (sourceB1775 + difference 4 0) sourceC1775) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4901) := by
    have ha : (tripleCharges (sourceA1775 + difference 0 4) (sourceB1775 + difference 4 0) sourceC1775) = raw25736 := by
      apply Matrix.ext; unfold tripleCharges sourceA1775 sourceB1775 sourceC1775 difference raw25736; decide +kernel
    rw [ha]
    exact (canonical25736 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1775 + difference 0 5) (sourceB1775 + difference 5 0) sourceC1775) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4895) := by
    have ha : (tripleCharges (sourceA1775 + difference 0 5) (sourceB1775 + difference 5 0) sourceC1775) = raw25737 := by
      apply Matrix.ext; unfold tripleCharges sourceA1775 sourceB1775 sourceC1775 difference raw25737; decide +kernel
    rw [ha]
    exact (canonical25737 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1775 + difference 1 0) (sourceB1775 + difference 0 1) sourceC1775) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4173) := by
    have ha : (tripleCharges (sourceA1775 + difference 1 0) (sourceB1775 + difference 0 1) sourceC1775) = raw25738 := by
      apply Matrix.ext; unfold tripleCharges sourceA1775 sourceB1775 sourceC1775 difference raw25738; decide +kernel
    rw [ha]
    exact (canonical25738 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1775 + difference 1 2) (sourceB1775 + difference 2 1) sourceC1775) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4342) := by
    have ha : (tripleCharges (sourceA1775 + difference 1 2) (sourceB1775 + difference 2 1) sourceC1775) = raw25739 := by
      apply Matrix.ext; unfold tripleCharges sourceA1775 sourceB1775 sourceC1775 difference raw25739; decide +kernel
    rw [ha]
    exact (canonical25739 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1775 + difference 1 3) (sourceB1775 + difference 3 1) sourceC1775) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4474) := by
    have ha : (tripleCharges (sourceA1775 + difference 1 3) (sourceB1775 + difference 3 1) sourceC1775) = raw25740 := by
      apply Matrix.ext; unfold tripleCharges sourceA1775 sourceB1775 sourceC1775 difference raw25740; decide +kernel
    rw [ha]
    exact (canonical25740 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1775 + difference 1 4) (sourceB1775 + difference 4 1) sourceC1775) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4499) := by
    have ha : (tripleCharges (sourceA1775 + difference 1 4) (sourceB1775 + difference 4 1) sourceC1775) = raw25741 := by
      apply Matrix.ext; unfold tripleCharges sourceA1775 sourceB1775 sourceC1775 difference raw25741; decide +kernel
    rw [ha]
    exact (canonical25741 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1775 + difference 1 5) (sourceB1775 + difference 5 1) sourceC1775) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4495) := by
    have ha : (tripleCharges (sourceA1775 + difference 1 5) (sourceB1775 + difference 5 1) sourceC1775) = raw25742 := by
      apply Matrix.ext; unfold tripleCharges sourceA1775 sourceB1775 sourceC1775 difference raw25742; decide +kernel
    rw [ha]
    exact (canonical25742 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1775 + difference 2 0) (sourceB1775 + difference 0 2) sourceC1775) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4173) := by
    have ha : (tripleCharges (sourceA1775 + difference 2 0) (sourceB1775 + difference 0 2) sourceC1775) = raw25743 := by
      apply Matrix.ext; unfold tripleCharges sourceA1775 sourceB1775 sourceC1775 difference raw25743; decide +kernel
    rw [ha]
    exact (canonical25743 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1775 + difference 2 1) (sourceB1775 + difference 1 2) sourceC1775) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4342) := by
    have ha : (tripleCharges (sourceA1775 + difference 2 1) (sourceB1775 + difference 1 2) sourceC1775) = raw25744 := by
      apply Matrix.ext; unfold tripleCharges sourceA1775 sourceB1775 sourceC1775 difference raw25744; decide +kernel
    rw [ha]
    exact (canonical25744 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1775 + difference 2 3) (sourceB1775 + difference 3 2) sourceC1775) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4474) := by
    have ha : (tripleCharges (sourceA1775 + difference 2 3) (sourceB1775 + difference 3 2) sourceC1775) = raw25745 := by
      apply Matrix.ext; unfold tripleCharges sourceA1775 sourceB1775 sourceC1775 difference raw25745; decide +kernel
    rw [ha]
    exact (canonical25745 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1775 + difference 2 4) (sourceB1775 + difference 4 2) sourceC1775) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4499) := by
    have ha : (tripleCharges (sourceA1775 + difference 2 4) (sourceB1775 + difference 4 2) sourceC1775) = raw25746 := by
      apply Matrix.ext; unfold tripleCharges sourceA1775 sourceB1775 sourceC1775 difference raw25746; decide +kernel
    rw [ha]
    exact (canonical25746 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1775 + difference 2 5) (sourceB1775 + difference 5 2) sourceC1775) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4495) := by
    have ha : (tripleCharges (sourceA1775 + difference 2 5) (sourceB1775 + difference 5 2) sourceC1775) = raw25747 := by
      apply Matrix.ext; unfold tripleCharges sourceA1775 sourceB1775 sourceC1775 difference raw25747; decide +kernel
    rw [ha]
    exact (canonical25747 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1775 + difference 3 0) (sourceB1775 + difference 0 3) sourceC1775) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4180) := by
    have ha : (tripleCharges (sourceA1775 + difference 3 0) (sourceB1775 + difference 0 3) sourceC1775) = raw25748 := by
      apply Matrix.ext; unfold tripleCharges sourceA1775 sourceB1775 sourceC1775 difference raw25748; decide +kernel
    rw [ha]
    exact (canonical25748 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1775 + difference 3 1) (sourceB1775 + difference 1 3) sourceC1775) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4349) := by
    have ha : (tripleCharges (sourceA1775 + difference 3 1) (sourceB1775 + difference 1 3) sourceC1775) = raw25749 := by
      apply Matrix.ext; unfold tripleCharges sourceA1775 sourceB1775 sourceC1775 difference raw25749; decide +kernel
    rw [ha]
    exact (canonical25749 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1775 + difference 3 2) (sourceB1775 + difference 2 3) sourceC1775) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4349) := by
    have ha : (tripleCharges (sourceA1775 + difference 3 2) (sourceB1775 + difference 2 3) sourceC1775) = raw25750 := by
      apply Matrix.ext; unfold tripleCharges sourceA1775 sourceB1775 sourceC1775 difference raw25750; decide +kernel
    rw [ha]
    exact (canonical25750 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1775 + difference 3 4) (sourceB1775 + difference 4 3) sourceC1775) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4511) := by
    have ha : (tripleCharges (sourceA1775 + difference 3 4) (sourceB1775 + difference 4 3) sourceC1775) = raw25751 := by
      apply Matrix.ext; unfold tripleCharges sourceA1775 sourceB1775 sourceC1775 difference raw25751; decide +kernel
    rw [ha]
    exact (canonical25751 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1775 + difference 3 5) (sourceB1775 + difference 5 3) sourceC1775) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4498) := by
    have ha : (tripleCharges (sourceA1775 + difference 3 5) (sourceB1775 + difference 5 3) sourceC1775) = raw25752 := by
      apply Matrix.ext; unfold tripleCharges sourceA1775 sourceB1775 sourceC1775 difference raw25752; decide +kernel
    rw [ha]
    exact (canonical25752 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1775 + difference 4 0) (sourceB1775 + difference 0 4) sourceC1775) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4188) := by
    have ha : (tripleCharges (sourceA1775 + difference 4 0) (sourceB1775 + difference 0 4) sourceC1775) = raw25753 := by
      apply Matrix.ext; unfold tripleCharges sourceA1775 sourceB1775 sourceC1775 difference raw25753; decide +kernel
    rw [ha]
    exact (canonical25753 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1775 + difference 4 1) (sourceB1775 + difference 1 4) sourceC1775) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4357) := by
    have ha : (tripleCharges (sourceA1775 + difference 4 1) (sourceB1775 + difference 1 4) sourceC1775) = raw25754 := by
      apply Matrix.ext; unfold tripleCharges sourceA1775 sourceB1775 sourceC1775 difference raw25754; decide +kernel
    rw [ha]
    exact (canonical25754 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1775 + difference 4 2) (sourceB1775 + difference 2 4) sourceC1775) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4357) := by
    have ha : (tripleCharges (sourceA1775 + difference 4 2) (sourceB1775 + difference 2 4) sourceC1775) = raw25755 := by
      apply Matrix.ext; unfold tripleCharges sourceA1775 sourceB1775 sourceC1775 difference raw25755; decide +kernel
    rw [ha]
    exact (canonical25755 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1775 + difference 4 3) (sourceB1775 + difference 3 4) sourceC1775) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4480) := by
    have ha : (tripleCharges (sourceA1775 + difference 4 3) (sourceB1775 + difference 3 4) sourceC1775) = raw25756 := by
      apply Matrix.ext; unfold tripleCharges sourceA1775 sourceB1775 sourceC1775 difference raw25756; decide +kernel
    rw [ha]
    exact (canonical25756 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1775 + difference 4 5) (sourceB1775 + difference 5 4) sourceC1775) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4503) := by
    have ha : (tripleCharges (sourceA1775 + difference 4 5) (sourceB1775 + difference 5 4) sourceC1775) = raw25757 := by
      apply Matrix.ext; unfold tripleCharges sourceA1775 sourceB1775 sourceC1775 difference raw25757; decide +kernel
    rw [ha]
    exact (canonical25757 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1775 + difference 5 0) (sourceB1775 + difference 0 5) sourceC1775) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4178) := by
    have ha : (tripleCharges (sourceA1775 + difference 5 0) (sourceB1775 + difference 0 5) sourceC1775) = raw25758 := by
      apply Matrix.ext; unfold tripleCharges sourceA1775 sourceB1775 sourceC1775 difference raw25758; decide +kernel
    rw [ha]
    exact (canonical25758 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1775 + difference 5 1) (sourceB1775 + difference 1 5) sourceC1775) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4347) := by
    have ha : (tripleCharges (sourceA1775 + difference 5 1) (sourceB1775 + difference 1 5) sourceC1775) = raw25759 := by
      apply Matrix.ext; unfold tripleCharges sourceA1775 sourceB1775 sourceC1775 difference raw25759; decide +kernel
    rw [ha]
    exact (canonical25759 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1775 + difference 5 2) (sourceB1775 + difference 2 5) sourceC1775) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4347) := by
    have ha : (tripleCharges (sourceA1775 + difference 5 2) (sourceB1775 + difference 2 5) sourceC1775) = raw25760 := by
      apply Matrix.ext; unfold tripleCharges sourceA1775 sourceB1775 sourceC1775 difference raw25760; decide +kernel
    rw [ha]
    exact (canonical25760 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1775 + difference 5 3) (sourceB1775 + difference 3 5) sourceC1775) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4476) := by
    have ha : (tripleCharges (sourceA1775 + difference 5 3) (sourceB1775 + difference 3 5) sourceC1775) = raw25761 := by
      apply Matrix.ext; unfold tripleCharges sourceA1775 sourceB1775 sourceC1775 difference raw25761; decide +kernel
    rw [ha]
    exact (canonical25761 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1775 + difference 5 4) (sourceB1775 + difference 4 5) sourceC1775) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4507) := by
    have ha : (tripleCharges (sourceA1775 + difference 5 4) (sourceB1775 + difference 4 5) sourceC1775) = raw25762 := by
      apply Matrix.ext; unfold tripleCharges sourceA1775 sourceB1775 sourceC1775 difference raw25762; decide +kernel
    rw [ha]
    exact (canonical25762 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1775 sourceB1775 sourceC1775
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1775, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic94
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reindexCheck1508 : Integer.Sparse.reindex keyMap MixedData.row1508 = numericRow1508 := by decide +kernel

theorem numericCheck1508 (x : Master → ℝ) : Integer.Sparse.eval numericRow1508 x =
    (4 : ℝ) * reducedSource1508 x := by
  norm_num [numericRow1508, reducedSource1508, Integer.Sparse.eval, Sparse.eval, nodeValue4173, nodeValue4178, nodeValue4180, nodeValue4188, nodeValue4342, nodeValue4347, nodeValue4349, nodeValue4357, nodeValue4474, nodeValue4476, nodeValue4480, nodeValue4495, nodeValue4498, nodeValue4499, nodeValue4503, nodeValue4507, nodeValue4511, nodeValue4835, nodeValue4895, nodeValue4896, nodeValue4901]
  ring

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Rows94
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero1508 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1508 (mixedVector B) = 0 := by
  have h4173 : mixedVector B (Sum.inr 4173) = Sparse.eval nodeValue4173 (mixedVector B) := by
    change mixedMoment B node4173 node4173Labels = _
    exact sound4173 B hB hF
  have h4178 : mixedVector B (Sum.inr 4178) = Sparse.eval nodeValue4178 (mixedVector B) := by
    change mixedMoment B node4178 node4178Labels = _
    exact sound4178 B hB hF
  have h4180 : mixedVector B (Sum.inr 4180) = Sparse.eval nodeValue4180 (mixedVector B) := by
    change mixedMoment B node4180 node4180Labels = _
    exact sound4180 B hB hF
  have h4188 : mixedVector B (Sum.inr 4188) = Sparse.eval nodeValue4188 (mixedVector B) := by
    change mixedMoment B node4188 node4188Labels = _
    exact sound4188 B hB hF
  have h4342 : mixedVector B (Sum.inr 4342) = Sparse.eval nodeValue4342 (mixedVector B) := by
    change mixedMoment B node4342 node4342Labels = _
    exact sound4342 B hB hF
  have h4347 : mixedVector B (Sum.inr 4347) = Sparse.eval nodeValue4347 (mixedVector B) := by
    change mixedMoment B node4347 node4347Labels = _
    exact sound4347 B hB hF
  have h4349 : mixedVector B (Sum.inr 4349) = Sparse.eval nodeValue4349 (mixedVector B) := by
    change mixedMoment B node4349 node4349Labels = _
    exact sound4349 B hB hF
  have h4357 : mixedVector B (Sum.inr 4357) = Sparse.eval nodeValue4357 (mixedVector B) := by
    change mixedMoment B node4357 node4357Labels = _
    exact sound4357 B hB hF
  have h4474 : mixedVector B (Sum.inr 4474) = Sparse.eval nodeValue4474 (mixedVector B) := by
    change mixedMoment B node4474 node4474Labels = _
    exact sound4474 B hB hF
  have h4476 : mixedVector B (Sum.inr 4476) = Sparse.eval nodeValue4476 (mixedVector B) := by
    change mixedMoment B node4476 node4476Labels = _
    exact sound4476 B hB hF
  have h4480 : mixedVector B (Sum.inr 4480) = Sparse.eval nodeValue4480 (mixedVector B) := by
    change mixedMoment B node4480 node4480Labels = _
    exact sound4480 B hB hF
  have h4495 : mixedVector B (Sum.inr 4495) = Sparse.eval nodeValue4495 (mixedVector B) := by
    change mixedMoment B node4495 node4495Labels = _
    exact sound4495 B hB hF
  have h4498 : mixedVector B (Sum.inr 4498) = Sparse.eval nodeValue4498 (mixedVector B) := by
    change mixedMoment B node4498 node4498Labels = _
    exact sound4498 B hB hF
  have h4499 : mixedVector B (Sum.inr 4499) = Sparse.eval nodeValue4499 (mixedVector B) := by
    change mixedMoment B node4499 node4499Labels = _
    exact sound4499 B hB hF
  have h4503 : mixedVector B (Sum.inr 4503) = Sparse.eval nodeValue4503 (mixedVector B) := by
    change mixedMoment B node4503 node4503Labels = _
    exact sound4503 B hB hF
  have h4507 : mixedVector B (Sum.inr 4507) = Sparse.eval nodeValue4507 (mixedVector B) := by
    change mixedMoment B node4507 node4507Labels = _
    exact sound4507 B hB hF
  have h4511 : mixedVector B (Sum.inr 4511) = Sparse.eval nodeValue4511 (mixedVector B) := by
    change mixedMoment B node4511 node4511Labels = _
    exact sound4511 B hB hF
  have h4835 : mixedVector B (Sum.inr 4835) = Sparse.eval nodeValue4835 (mixedVector B) := by
    change mixedMoment B node4835 node4835Labels = _
    exact sound4835 B hB hF
  have h4895 : mixedVector B (Sum.inr 4895) = Sparse.eval nodeValue4895 (mixedVector B) := by
    change mixedMoment B node4895 node4895Labels = _
    exact sound4895 B hB hF
  have h4896 : mixedVector B (Sum.inr 4896) = Sparse.eval nodeValue4896 (mixedVector B) := by
    change mixedMoment B node4896 node4896Labels = _
    exact sound4896 B hB hF
  have h4901 : mixedVector B (Sum.inr 4901) = Sparse.eval nodeValue4901 (mixedVector B) := by
    change mixedMoment B node4901 node4901Labels = _
    exact sound4901 B hB hF
  simpa only [sourceForm1775, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4173, h4178, h4180, h4188, h4342, h4347, h4349, h4357, h4474, h4476, h4480, h4495, h4498, h4499, h4503, h4507, h4511, h4835, h4895, h4896, h4901, reducedSource1508] using sourceEq1775 B hB

theorem rowSound1508_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1508 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1508, numericCheck1508, reducedZero1508 B hB hF, mul_zero]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedSourceBridge.rowSound1508_e_oai := @OAI.MUB6.Certificate.MixedSourceBridge.rowSound1508_e_oai
