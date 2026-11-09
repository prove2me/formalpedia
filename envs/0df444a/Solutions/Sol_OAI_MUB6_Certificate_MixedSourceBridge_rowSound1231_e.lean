-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedSourceBridge.rowSound1231_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-08T20:16:40.294205+00:00
-- url     : https://prove2.me/submissions/5acdad3e-8132-4e3e-9215-bf0acb364fe6

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E184
import Definitions.Def_OAIQ106E086
import Definitions.Def_OAIQ106E088
import Definitions.Def_OAIQ106E089
import Definitions.Def_OAIQ106E098
import Definitions.Def_OAIQ106E116
import Definitions.Def_OAIQ106E117
import Definitions.Def_OAIQ106E118
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical173
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical22221 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22221 raw22221Labels = mixedMoment B node4454 node4454Labels := by
  calc
    mixedMoment B raw22221 raw22221Labels = mixedMoment B raw22221step0 raw22221step0Labels := by
      have hz : ∀ j, raw22221 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22221step0 = (fun i j => raw22221 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22221step0 raw22221; decide +kernel
      have hl : raw22221step0Labels = raw22221Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22221 raw22221Labels permutation434 hz
    mixedMoment B raw22221step0 raw22221step0Labels = mixedMoment B raw22221step1 raw22221step1Labels := by
      have hz : ∀ j, raw22221step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22221step1 = (fun i j => raw22221step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22221step1 raw22221step0; decide +kernel
      have hl : raw22221step1Labels = raw22221step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22221step0 raw22221step0Labels permutation80 hz
    mixedMoment B raw22221step1 raw22221step1Labels = mixedMoment B raw22221step2 raw22221step2Labels := by
      have ha : raw22221step2 = (fun i j => raw22221step1 (permutation10 i) (permutation7 j)) := by apply Matrix.ext; unfold raw22221step2 raw22221step1; decide +kernel
      have hl : raw22221step2Labels = raw22221step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22221step1 raw22221step1Labels permutation10 permutation7
    mixedMoment B raw22221step2 raw22221step2Labels = mixedMoment B raw22221step3 raw22221step3Labels := by
      have ha : raw22221step3 = -raw22221step2 := by apply Matrix.ext; change ∀ i j, raw22221step3 i j = -(raw22221step2 i j); unfold raw22221step3 raw22221step2; decide +kernel
      have hl : raw22221step3Labels = raw22221step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw22221step3 raw22221step3Labels = mixedMoment B raw22221step4 raw22221step4Labels := by
      have ha : raw22221step4 = raw22221step3 := by apply Matrix.ext; unfold raw22221step4 raw22221step3; decide +kernel
      have hl : raw22221step3Labels = labelEmbedding10 ∘ raw22221step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22221step3 raw22221step3Labels raw22221step4Labels labelEmbedding10 hl
    _ = mixedMoment B node4454 node4454Labels := by rfl

theorem canonical22222 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22222 raw22222Labels = mixedMoment B node4398 node4398Labels := by
  calc
    mixedMoment B raw22222 raw22222Labels = mixedMoment B raw22222step0 raw22222step0Labels := by
      have hz : ∀ j, raw22222 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22222step0 = (fun i j => raw22222 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22222step0 raw22222; decide +kernel
      have hl : raw22222step0Labels = raw22222Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22222 raw22222Labels permutation434 hz
    mixedMoment B raw22222step0 raw22222step0Labels = mixedMoment B raw22222step1 raw22222step1Labels := by
      have ha : raw22222step1 = (fun i j => raw22222step0 (permutation40 i) (permutation7 j)) := by apply Matrix.ext; unfold raw22222step1 raw22222step0; decide +kernel
      have hl : raw22222step1Labels = raw22222step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22222step0 raw22222step0Labels permutation40 permutation7
    mixedMoment B raw22222step1 raw22222step1Labels = mixedMoment B raw22222step2 raw22222step2Labels := by
      have ha : raw22222step2 = -raw22222step1 := by apply Matrix.ext; change ∀ i j, raw22222step2 i j = -(raw22222step1 i j); unfold raw22222step2 raw22222step1; decide +kernel
      have hl : raw22222step2Labels = raw22222step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw22222step2 raw22222step2Labels = mixedMoment B raw22222step3 raw22222step3Labels := by
      have ha : raw22222step3 = raw22222step2 := by apply Matrix.ext; unfold raw22222step3 raw22222step2; decide +kernel
      have hl : raw22222step2Labels = labelEmbedding10 ∘ raw22222step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22222step2 raw22222step2Labels raw22222step3Labels labelEmbedding10 hl
    _ = mixedMoment B node4398 node4398Labels := by rfl

theorem canonical22223 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22223 raw22223Labels = mixedMoment B node4398 node4398Labels := by
  calc
    mixedMoment B raw22223 raw22223Labels = mixedMoment B raw22223step0 raw22223step0Labels := by
      have hz : ∀ j, raw22223 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22223step0 = (fun i j => raw22223 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22223step0 raw22223; decide +kernel
      have hl : raw22223step0Labels = raw22223Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22223 raw22223Labels permutation346 hz
    mixedMoment B raw22223step0 raw22223step0Labels = mixedMoment B raw22223step1 raw22223step1Labels := by
      have ha : raw22223step1 = (fun i j => raw22223step0 (permutation40 i) (permutation7 j)) := by apply Matrix.ext; unfold raw22223step1 raw22223step0; decide +kernel
      have hl : raw22223step1Labels = raw22223step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22223step0 raw22223step0Labels permutation40 permutation7
    mixedMoment B raw22223step1 raw22223step1Labels = mixedMoment B raw22223step2 raw22223step2Labels := by
      have ha : raw22223step2 = -raw22223step1 := by apply Matrix.ext; change ∀ i j, raw22223step2 i j = -(raw22223step1 i j); unfold raw22223step2 raw22223step1; decide +kernel
      have hl : raw22223step2Labels = raw22223step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw22223step2 raw22223step2Labels = mixedMoment B raw22223step3 raw22223step3Labels := by
      have ha : raw22223step3 = raw22223step2 := by apply Matrix.ext; unfold raw22223step3 raw22223step2; decide +kernel
      have hl : raw22223step2Labels = labelEmbedding10 ∘ raw22223step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22223step2 raw22223step2Labels raw22223step3Labels labelEmbedding10 hl
    _ = mixedMoment B node4398 node4398Labels := by rfl

theorem canonical22224 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22224 raw22224Labels = mixedMoment B node4501 node4501Labels := by
  calc
    mixedMoment B raw22224 raw22224Labels = mixedMoment B raw22224step0 raw22224step0Labels := by
      have hz : ∀ j, raw22224 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw22224step0 = (fun i j => raw22224 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw22224step0 raw22224; decide +kernel
      have hl : raw22224step0Labels = raw22224Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22224 raw22224Labels permutation520 hz
    mixedMoment B raw22224step0 raw22224step0Labels = mixedMoment B raw22224step1 raw22224step1Labels := by
      have hz : ∀ j, raw22224step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw22224step1 = (fun i j => raw22224step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw22224step1 raw22224step0; decide +kernel
      have hl : raw22224step1Labels = raw22224step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22224step0 raw22224step0Labels permutation104 hz
    mixedMoment B raw22224step1 raw22224step1Labels = mixedMoment B raw22224step2 raw22224step2Labels := by
      have hz : ∀ j, raw22224step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw22224step2 = (fun i j => raw22224step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw22224step2 raw22224step1; decide +kernel
      have hl : raw22224step2Labels = raw22224step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22224step1 raw22224step1Labels permutation20 hz
    mixedMoment B raw22224step2 raw22224step2Labels = mixedMoment B raw22224step3 raw22224step3Labels := by
      have ha : raw22224step3 = (fun i j => raw22224step2 (permutation2 i) (permutation7 j)) := by apply Matrix.ext; unfold raw22224step3 raw22224step2; decide +kernel
      have hl : raw22224step3Labels = raw22224step2Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22224step2 raw22224step2Labels permutation2 permutation7
    mixedMoment B raw22224step3 raw22224step3Labels = mixedMoment B raw22224step4 raw22224step4Labels := by
      have ha : raw22224step4 = -raw22224step3 := by apply Matrix.ext; change ∀ i j, raw22224step4 i j = -(raw22224step3 i j); unfold raw22224step4 raw22224step3; decide +kernel
      have hl : raw22224step4Labels = raw22224step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw22224step4 raw22224step4Labels = mixedMoment B raw22224step5 raw22224step5Labels := by
      have ha : raw22224step5 = raw22224step4 := by apply Matrix.ext; unfold raw22224step5 raw22224step4; decide +kernel
      have hl : raw22224step4Labels = labelEmbedding10 ∘ raw22224step5Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22224step4 raw22224step4Labels raw22224step5Labels labelEmbedding10 hl
    _ = mixedMoment B node4501 node4501Labels := by rfl

theorem canonical22225 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22225 raw22225Labels = mixedMoment B node4460 node4460Labels := by
  calc
    mixedMoment B raw22225 raw22225Labels = mixedMoment B raw22225step0 raw22225step0Labels := by
      have hz : ∀ j, raw22225 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22225step0 = (fun i j => raw22225 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22225step0 raw22225; decide +kernel
      have hl : raw22225step0Labels = raw22225Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22225 raw22225Labels permutation434 hz
    mixedMoment B raw22225step0 raw22225step0Labels = mixedMoment B raw22225step1 raw22225step1Labels := by
      have hz : ∀ j, raw22225step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22225step1 = (fun i j => raw22225step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22225step1 raw22225step0; decide +kernel
      have hl : raw22225step1Labels = raw22225step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22225step0 raw22225step0Labels permutation80 hz
    mixedMoment B raw22225step1 raw22225step1Labels = mixedMoment B raw22225step2 raw22225step2Labels := by
      have ha : raw22225step2 = (fun i j => raw22225step1 (permutation10 i) (permutation7 j)) := by apply Matrix.ext; unfold raw22225step2 raw22225step1; decide +kernel
      have hl : raw22225step2Labels = raw22225step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22225step1 raw22225step1Labels permutation10 permutation7
    mixedMoment B raw22225step2 raw22225step2Labels = mixedMoment B raw22225step3 raw22225step3Labels := by
      have ha : raw22225step3 = -raw22225step2 := by apply Matrix.ext; change ∀ i j, raw22225step3 i j = -(raw22225step2 i j); unfold raw22225step3 raw22225step2; decide +kernel
      have hl : raw22225step3Labels = raw22225step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw22225step3 raw22225step3Labels = mixedMoment B raw22225step4 raw22225step4Labels := by
      have ha : raw22225step4 = raw22225step3 := by apply Matrix.ext; unfold raw22225step4 raw22225step3; decide +kernel
      have hl : raw22225step3Labels = labelEmbedding10 ∘ raw22225step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22225step3 raw22225step3Labels raw22225step4Labels labelEmbedding10 hl
    _ = mixedMoment B node4460 node4460Labels := by rfl

theorem canonical22226 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22226 raw22226Labels = mixedMoment B node4120 node4120Labels := by
  calc
    mixedMoment B raw22226 raw22226Labels = mixedMoment B raw22226step0 raw22226step0Labels := by
      have hz : ∀ j, raw22226 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22226step0 = (fun i j => raw22226 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22226step0 raw22226; decide +kernel
      have hl : raw22226step0Labels = raw22226Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22226 raw22226Labels permutation434 hz
    mixedMoment B raw22226step0 raw22226step0Labels = mixedMoment B raw22226step1 raw22226step1Labels := by
      have hz : ∀ j, raw22226step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22226step1 = (fun i j => raw22226step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22226step1 raw22226step0; decide +kernel
      have hl : raw22226step1Labels = raw22226step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22226step0 raw22226step0Labels permutation80 hz
    mixedMoment B raw22226step1 raw22226step1Labels = mixedMoment B raw22226step2 raw22226step2Labels := by
      have ha : raw22226step2 = (fun i j => raw22226step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22226step2 raw22226step1; decide +kernel
      have hl : raw22226step2Labels = raw22226step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22226step1 raw22226step1Labels permutation10 permutation2
    _ = mixedMoment B node4120 node4120Labels := by rfl

theorem canonical22227 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22227 raw22227Labels = mixedMoment B node4211 node4211Labels := by
  calc
    mixedMoment B raw22227 raw22227Labels = mixedMoment B raw22227step0 raw22227step0Labels := by
      have hz : ∀ j, raw22227 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22227step0 = (fun i j => raw22227 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22227step0 raw22227; decide +kernel
      have hl : raw22227step0Labels = raw22227Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22227 raw22227Labels permutation434 hz
    mixedMoment B raw22227step0 raw22227step0Labels = mixedMoment B raw22227step1 raw22227step1Labels := by
      have ha : raw22227step1 = (fun i j => raw22227step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22227step1 raw22227step0; decide +kernel
      have hl : raw22227step1Labels = raw22227step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22227step0 raw22227step0Labels permutation40 permutation2
    _ = mixedMoment B node4211 node4211Labels := by rfl

theorem canonical22228 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22228 raw22228Labels = mixedMoment B node4211 node4211Labels := by
  calc
    mixedMoment B raw22228 raw22228Labels = mixedMoment B raw22228step0 raw22228step0Labels := by
      have hz : ∀ j, raw22228 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22228step0 = (fun i j => raw22228 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22228step0 raw22228; decide +kernel
      have hl : raw22228step0Labels = raw22228Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22228 raw22228Labels permutation346 hz
    mixedMoment B raw22228step0 raw22228step0Labels = mixedMoment B raw22228step1 raw22228step1Labels := by
      have ha : raw22228step1 = (fun i j => raw22228step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22228step1 raw22228step0; decide +kernel
      have hl : raw22228step1Labels = raw22228step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22228step0 raw22228step0Labels permutation40 permutation2
    _ = mixedMoment B node4211 node4211Labels := by rfl

theorem canonical22229 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22229 raw22229Labels = mixedMoment B node4070 node4070Labels := by
  calc
    mixedMoment B raw22229 raw22229Labels = mixedMoment B raw22229step0 raw22229step0Labels := by
      have hz : ∀ j, raw22229 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw22229step0 = (fun i j => raw22229 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw22229step0 raw22229; decide +kernel
      have hl : raw22229step0Labels = raw22229Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22229 raw22229Labels permutation520 hz
    mixedMoment B raw22229step0 raw22229step0Labels = mixedMoment B raw22229step1 raw22229step1Labels := by
      have hz : ∀ j, raw22229step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw22229step1 = (fun i j => raw22229step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw22229step1 raw22229step0; decide +kernel
      have hl : raw22229step1Labels = raw22229step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22229step0 raw22229step0Labels permutation104 hz
    mixedMoment B raw22229step1 raw22229step1Labels = mixedMoment B raw22229step2 raw22229step2Labels := by
      have hz : ∀ j, raw22229step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw22229step2 = (fun i j => raw22229step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw22229step2 raw22229step1; decide +kernel
      have hl : raw22229step2Labels = raw22229step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22229step1 raw22229step1Labels permutation20 hz
    mixedMoment B raw22229step2 raw22229step2Labels = mixedMoment B raw22229step3 raw22229step3Labels := by
      have hz : ∀ i, raw22229step2 i (permutation4 0) = 0 := by decide +kernel
      have ha : raw22229step3 = (fun i j => raw22229step2 i (permutation4 j.succ)) := by apply Matrix.ext; unfold raw22229step3 raw22229step2; decide +kernel
      have hl : raw22229step3Labels = (fun j => raw22229step2Labels (permutation4 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw22229step2 raw22229step2Labels permutation4 hz
    mixedMoment B raw22229step3 raw22229step3Labels = mixedMoment B raw22229step4 raw22229step4Labels := by
      have ha : raw22229step4 = raw22229step3 := by apply Matrix.ext; unfold raw22229step4 raw22229step3; decide +kernel
      have hl : raw22229step3Labels = labelEmbedding2 ∘ raw22229step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22229step3 raw22229step3Labels raw22229step4Labels labelEmbedding2 hl
    _ = mixedMoment B node4070 node4070Labels := by rfl

theorem canonical22230 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22230 raw22230Labels = mixedMoment B node4269 node4269Labels := by
  calc
    mixedMoment B raw22230 raw22230Labels = mixedMoment B raw22230step0 raw22230step0Labels := by
      have hz : ∀ j, raw22230 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22230step0 = (fun i j => raw22230 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22230step0 raw22230; decide +kernel
      have hl : raw22230step0Labels = raw22230Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22230 raw22230Labels permutation434 hz
    mixedMoment B raw22230step0 raw22230step0Labels = mixedMoment B raw22230step1 raw22230step1Labels := by
      have hz : ∀ j, raw22230step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22230step1 = (fun i j => raw22230step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22230step1 raw22230step0; decide +kernel
      have hl : raw22230step1Labels = raw22230step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22230step0 raw22230step0Labels permutation80 hz
    mixedMoment B raw22230step1 raw22230step1Labels = mixedMoment B raw22230step2 raw22230step2Labels := by
      have ha : raw22230step2 = (fun i j => raw22230step1 (permutation10 i) (permutation7 j)) := by apply Matrix.ext; unfold raw22230step2 raw22230step1; decide +kernel
      have hl : raw22230step2Labels = raw22230step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22230step1 raw22230step1Labels permutation10 permutation7
    mixedMoment B raw22230step2 raw22230step2Labels = mixedMoment B raw22230step3 raw22230step3Labels := by
      have ha : raw22230step3 = -raw22230step2 := by apply Matrix.ext; change ∀ i j, raw22230step3 i j = -(raw22230step2 i j); unfold raw22230step3 raw22230step2; decide +kernel
      have hl : raw22230step3Labels = raw22230step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw22230step3 raw22230step3Labels = mixedMoment B raw22230step4 raw22230step4Labels := by
      have ha : raw22230step4 = raw22230step3 := by apply Matrix.ext; unfold raw22230step4 raw22230step3; decide +kernel
      have hl : raw22230step3Labels = labelEmbedding10 ∘ raw22230step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22230step3 raw22230step3Labels raw22230step4Labels labelEmbedding10 hl
    _ = mixedMoment B node4269 node4269Labels := by rfl

theorem canonical22231 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22231 raw22231Labels = mixedMoment B node4099 node4099Labels := by
  calc
    mixedMoment B raw22231 raw22231Labels = mixedMoment B raw22231step0 raw22231step0Labels := by
      have hz : ∀ j, raw22231 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22231step0 = (fun i j => raw22231 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22231step0 raw22231; decide +kernel
      have hl : raw22231step0Labels = raw22231Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22231 raw22231Labels permutation434 hz
    _ = mixedMoment B node4099 node4099Labels := by rfl

theorem canonical22232 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22232 raw22232Labels = mixedMoment B node4231 node4231Labels := by
  calc
    mixedMoment B raw22232 raw22232Labels = mixedMoment B raw22232step0 raw22232step0Labels := by
      have hz : ∀ j, raw22232 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22232step0 = (fun i j => raw22232 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22232step0 raw22232; decide +kernel
      have hl : raw22232step0Labels = raw22232Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22232 raw22232Labels permutation434 hz
    _ = mixedMoment B node4231 node4231Labels := by rfl

theorem canonical22233 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22233 raw22233Labels = mixedMoment B node4195 node4195Labels := by
  calc
    mixedMoment B raw22233 raw22233Labels = mixedMoment B raw22233step0 raw22233step0Labels := by
      have ha : raw22233step0 = (fun i j => raw22233 (permutation200 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22233step0 raw22233; decide +kernel
      have hl : raw22233step0Labels = raw22233Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22233 raw22233Labels permutation200 permutation2
    _ = mixedMoment B node4195 node4195Labels := by rfl

theorem canonical22234 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22234 raw22234Labels = mixedMoment B node4266 node4266Labels := by
  calc
    mixedMoment B raw22234 raw22234Labels = mixedMoment B raw22234step0 raw22234step0Labels := by
      have hz : ∀ j, raw22234 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw22234step0 = (fun i j => raw22234 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw22234step0 raw22234; decide +kernel
      have hl : raw22234step0Labels = raw22234Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22234 raw22234Labels permutation520 hz
    mixedMoment B raw22234step0 raw22234step0Labels = mixedMoment B raw22234step1 raw22234step1Labels := by
      have hz : ∀ j, raw22234step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw22234step1 = (fun i j => raw22234step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw22234step1 raw22234step0; decide +kernel
      have hl : raw22234step1Labels = raw22234step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22234step0 raw22234step0Labels permutation104 hz
    _ = mixedMoment B node4266 node4266Labels := by rfl

theorem canonical22235 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22235 raw22235Labels = mixedMoment B node4251 node4251Labels := by
  calc
    mixedMoment B raw22235 raw22235Labels = mixedMoment B raw22235step0 raw22235step0Labels := by
      have hz : ∀ j, raw22235 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22235step0 = (fun i j => raw22235 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22235step0 raw22235; decide +kernel
      have hl : raw22235step0Labels = raw22235Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22235 raw22235Labels permutation434 hz
    mixedMoment B raw22235step0 raw22235step0Labels = mixedMoment B raw22235step1 raw22235step1Labels := by
      have ha : raw22235step1 = (fun i j => raw22235step0 (permutation40 i) (permutation7 j)) := by apply Matrix.ext; unfold raw22235step1 raw22235step0; decide +kernel
      have hl : raw22235step1Labels = raw22235step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22235step0 raw22235step0Labels permutation40 permutation7
    mixedMoment B raw22235step1 raw22235step1Labels = mixedMoment B raw22235step2 raw22235step2Labels := by
      have ha : raw22235step2 = -raw22235step1 := by apply Matrix.ext; change ∀ i j, raw22235step2 i j = -(raw22235step1 i j); unfold raw22235step2 raw22235step1; decide +kernel
      have hl : raw22235step2Labels = raw22235step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw22235step2 raw22235step2Labels = mixedMoment B raw22235step3 raw22235step3Labels := by
      have ha : raw22235step3 = raw22235step2 := by apply Matrix.ext; unfold raw22235step3 raw22235step2; decide +kernel
      have hl : raw22235step2Labels = labelEmbedding10 ∘ raw22235step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22235step2 raw22235step2Labels raw22235step3Labels labelEmbedding10 hl
    _ = mixedMoment B node4251 node4251Labels := by rfl

theorem canonical22236 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22236 raw22236Labels = mixedMoment B node4099 node4099Labels := by
  calc
    mixedMoment B raw22236 raw22236Labels = mixedMoment B raw22236step0 raw22236step0Labels := by
      have hz : ∀ j, raw22236 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22236step0 = (fun i j => raw22236 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22236step0 raw22236; decide +kernel
      have hl : raw22236step0Labels = raw22236Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22236 raw22236Labels permutation346 hz
    _ = mixedMoment B node4099 node4099Labels := by rfl

theorem canonical22237 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22237 raw22237Labels = mixedMoment B node4231 node4231Labels := by
  calc
    mixedMoment B raw22237 raw22237Labels = mixedMoment B raw22237step0 raw22237step0Labels := by
      have hz : ∀ j, raw22237 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22237step0 = (fun i j => raw22237 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22237step0 raw22237; decide +kernel
      have hl : raw22237step0Labels = raw22237Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22237 raw22237Labels permutation346 hz
    _ = mixedMoment B node4231 node4231Labels := by rfl

theorem canonical22238 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22238 raw22238Labels = mixedMoment B node4195 node4195Labels := by
  calc
    mixedMoment B raw22238 raw22238Labels = mixedMoment B raw22238step0 raw22238step0Labels := by
      have ha : raw22238step0 = (fun i j => raw22238 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22238step0 raw22238; decide +kernel
      have hl : raw22238step0Labels = raw22238Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22238 raw22238Labels permutation176 permutation2
    _ = mixedMoment B node4195 node4195Labels := by rfl

theorem canonical22239 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22239 raw22239Labels = mixedMoment B node4266 node4266Labels := by
  calc
    mixedMoment B raw22239 raw22239Labels = mixedMoment B raw22239step0 raw22239step0Labels := by
      have hz : ∀ j, raw22239 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw22239step0 = (fun i j => raw22239 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw22239step0 raw22239; decide +kernel
      have hl : raw22239step0Labels = raw22239Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22239 raw22239Labels permutation520 hz
    mixedMoment B raw22239step0 raw22239step0Labels = mixedMoment B raw22239step1 raw22239step1Labels := by
      have hz : ∀ j, raw22239step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22239step1 = (fun i j => raw22239step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22239step1 raw22239step0; decide +kernel
      have hl : raw22239step1Labels = raw22239step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22239step0 raw22239step0Labels permutation80 hz
    _ = mixedMoment B node4266 node4266Labels := by rfl

theorem canonical22240 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22240 raw22240Labels = mixedMoment B node4251 node4251Labels := by
  calc
    mixedMoment B raw22240 raw22240Labels = mixedMoment B raw22240step0 raw22240step0Labels := by
      have hz : ∀ j, raw22240 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22240step0 = (fun i j => raw22240 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22240step0 raw22240; decide +kernel
      have hl : raw22240step0Labels = raw22240Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22240 raw22240Labels permutation346 hz
    mixedMoment B raw22240step0 raw22240step0Labels = mixedMoment B raw22240step1 raw22240step1Labels := by
      have ha : raw22240step1 = (fun i j => raw22240step0 (permutation40 i) (permutation7 j)) := by apply Matrix.ext; unfold raw22240step1 raw22240step0; decide +kernel
      have hl : raw22240step1Labels = raw22240step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22240step0 raw22240step0Labels permutation40 permutation7
    mixedMoment B raw22240step1 raw22240step1Labels = mixedMoment B raw22240step2 raw22240step2Labels := by
      have ha : raw22240step2 = -raw22240step1 := by apply Matrix.ext; change ∀ i j, raw22240step2 i j = -(raw22240step1 i j); unfold raw22240step2 raw22240step1; decide +kernel
      have hl : raw22240step2Labels = raw22240step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw22240step2 raw22240step2Labels = mixedMoment B raw22240step3 raw22240step3Labels := by
      have ha : raw22240step3 = raw22240step2 := by apply Matrix.ext; unfold raw22240step3 raw22240step2; decide +kernel
      have hl : raw22240step2Labels = labelEmbedding10 ∘ raw22240step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22240step2 raw22240step2Labels raw22240step3Labels labelEmbedding10 hl
    _ = mixedMoment B node4251 node4251Labels := by rfl

theorem canonical22241 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22241 raw22241Labels = mixedMoment B node4109 node4109Labels := by
  calc
    mixedMoment B raw22241 raw22241Labels = mixedMoment B raw22241step0 raw22241step0Labels := by
      have hz : ∀ j, raw22241 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22241step0 = (fun i j => raw22241 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22241step0 raw22241; decide +kernel
      have hl : raw22241step0Labels = raw22241Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22241 raw22241Labels permutation434 hz
    mixedMoment B raw22241step0 raw22241step0Labels = mixedMoment B raw22241step1 raw22241step1Labels := by
      have hz : ∀ j, raw22241step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22241step1 = (fun i j => raw22241step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22241step1 raw22241step0; decide +kernel
      have hl : raw22241step1Labels = raw22241step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22241step0 raw22241step0Labels permutation80 hz
    _ = mixedMoment B node4109 node4109Labels := by rfl

theorem canonical22242 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22242 raw22242Labels = mixedMoment B node4241 node4241Labels := by
  calc
    mixedMoment B raw22242 raw22242Labels = mixedMoment B raw22242step0 raw22242step0Labels := by
      have hz : ∀ j, raw22242 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22242step0 = (fun i j => raw22242 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22242step0 raw22242; decide +kernel
      have hl : raw22242step0Labels = raw22242Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22242 raw22242Labels permutation434 hz
    mixedMoment B raw22242step0 raw22242step0Labels = mixedMoment B raw22242step1 raw22242step1Labels := by
      have hz : ∀ j, raw22242step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22242step1 = (fun i j => raw22242step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22242step1 raw22242step0; decide +kernel
      have hl : raw22242step1Labels = raw22242step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22242step0 raw22242step0Labels permutation80 hz
    _ = mixedMoment B node4241 node4241Labels := by rfl

theorem canonical22243 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22243 raw22243Labels = mixedMoment B node4203 node4203Labels := by
  calc
    mixedMoment B raw22243 raw22243Labels = mixedMoment B raw22243step0 raw22243step0Labels := by
      have hz : ∀ j, raw22243 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22243step0 = (fun i j => raw22243 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22243step0 raw22243; decide +kernel
      have hl : raw22243step0Labels = raw22243Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22243 raw22243Labels permutation434 hz
    mixedMoment B raw22243step0 raw22243step0Labels = mixedMoment B raw22243step1 raw22243step1Labels := by
      have ha : raw22243step1 = (fun i j => raw22243step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22243step1 raw22243step0; decide +kernel
      have hl : raw22243step1Labels = raw22243step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22243step0 raw22243step0Labels permutation38 permutation2
    _ = mixedMoment B node4203 node4203Labels := by rfl

theorem canonical22244 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22244 raw22244Labels = mixedMoment B node4203 node4203Labels := by
  calc
    mixedMoment B raw22244 raw22244Labels = mixedMoment B raw22244step0 raw22244step0Labels := by
      have hz : ∀ j, raw22244 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22244step0 = (fun i j => raw22244 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22244step0 raw22244; decide +kernel
      have hl : raw22244step0Labels = raw22244Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22244 raw22244Labels permutation346 hz
    mixedMoment B raw22244step0 raw22244step0Labels = mixedMoment B raw22244step1 raw22244step1Labels := by
      have ha : raw22244step1 = (fun i j => raw22244step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22244step1 raw22244step0; decide +kernel
      have hl : raw22244step1Labels = raw22244step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22244step0 raw22244step0Labels permutation38 permutation2
    _ = mixedMoment B node4203 node4203Labels := by rfl

theorem canonical22245 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22245 raw22245Labels = mixedMoment B node4272 node4272Labels := by
  calc
    mixedMoment B raw22245 raw22245Labels = mixedMoment B raw22245step0 raw22245step0Labels := by
      have hz : ∀ j, raw22245 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22245step0 = (fun i j => raw22245 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22245step0 raw22245; decide +kernel
      have hl : raw22245step0Labels = raw22245Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22245 raw22245Labels permutation434 hz
    mixedMoment B raw22245step0 raw22245step0Labels = mixedMoment B raw22245step1 raw22245step1Labels := by
      have hz : ∀ j, raw22245step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22245step1 = (fun i j => raw22245step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22245step1 raw22245step0; decide +kernel
      have hl : raw22245step1Labels = raw22245step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22245step0 raw22245step0Labels permutation80 hz
    _ = mixedMoment B node4272 node4272Labels := by rfl

theorem canonical22246 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22246 raw22246Labels = mixedMoment B node4103 node4103Labels := by
  calc
    mixedMoment B raw22246 raw22246Labels = mixedMoment B raw22246step0 raw22246step0Labels := by
      have hz : ∀ j, raw22246 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22246step0 = (fun i j => raw22246 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22246step0 raw22246; decide +kernel
      have hl : raw22246step0Labels = raw22246Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22246 raw22246Labels permutation434 hz
    mixedMoment B raw22246step0 raw22246step0Labels = mixedMoment B raw22246step1 raw22246step1Labels := by
      have hz : ∀ j, raw22246step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22246step1 = (fun i j => raw22246step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22246step1 raw22246step0; decide +kernel
      have hl : raw22246step1Labels = raw22246step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22246step0 raw22246step0Labels permutation80 hz
    _ = mixedMoment B node4103 node4103Labels := by rfl

theorem canonical22247 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22247 raw22247Labels = mixedMoment B node4235 node4235Labels := by
  calc
    mixedMoment B raw22247 raw22247Labels = mixedMoment B raw22247step0 raw22247step0Labels := by
      have hz : ∀ j, raw22247 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22247step0 = (fun i j => raw22247 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22247step0 raw22247; decide +kernel
      have hl : raw22247step0Labels = raw22247Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22247 raw22247Labels permutation434 hz
    mixedMoment B raw22247step0 raw22247step0Labels = mixedMoment B raw22247step1 raw22247step1Labels := by
      have hz : ∀ j, raw22247step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22247step1 = (fun i j => raw22247step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22247step1 raw22247step0; decide +kernel
      have hl : raw22247step1Labels = raw22247step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22247step0 raw22247step0Labels permutation80 hz
    _ = mixedMoment B node4235 node4235Labels := by rfl

theorem canonical22248 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22248 raw22248Labels = mixedMoment B node4198 node4198Labels := by
  calc
    mixedMoment B raw22248 raw22248Labels = mixedMoment B raw22248step0 raw22248step0Labels := by
      have hz : ∀ j, raw22248 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22248step0 = (fun i j => raw22248 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22248step0 raw22248; decide +kernel
      have hl : raw22248step0Labels = raw22248Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22248 raw22248Labels permutation434 hz
    mixedMoment B raw22248step0 raw22248step0Labels = mixedMoment B raw22248step1 raw22248step1Labels := by
      have ha : raw22248step1 = (fun i j => raw22248step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22248step1 raw22248step0; decide +kernel
      have hl : raw22248step1Labels = raw22248step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22248step0 raw22248step0Labels permutation38 permutation2
    _ = mixedMoment B node4198 node4198Labels := by rfl

theorem canonical22249 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22249 raw22249Labels = mixedMoment B node4198 node4198Labels := by
  calc
    mixedMoment B raw22249 raw22249Labels = mixedMoment B raw22249step0 raw22249step0Labels := by
      have hz : ∀ j, raw22249 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22249step0 = (fun i j => raw22249 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22249step0 raw22249; decide +kernel
      have hl : raw22249step0Labels = raw22249Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22249 raw22249Labels permutation346 hz
    mixedMoment B raw22249step0 raw22249step0Labels = mixedMoment B raw22249step1 raw22249step1Labels := by
      have ha : raw22249step1 = (fun i j => raw22249step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22249step1 raw22249step0; decide +kernel
      have hl : raw22249step1Labels = raw22249step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22249step0 raw22249step0Labels permutation38 permutation2
    _ = mixedMoment B node4198 node4198Labels := by rfl

theorem canonical22250 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22250 raw22250Labels = mixedMoment B node4274 node4274Labels := by
  calc
    mixedMoment B raw22250 raw22250Labels = mixedMoment B raw22250step0 raw22250step0Labels := by
      have hz : ∀ j, raw22250 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw22250step0 = (fun i j => raw22250 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw22250step0 raw22250; decide +kernel
      have hl : raw22250step0Labels = raw22250Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22250 raw22250Labels permutation520 hz
    mixedMoment B raw22250step0 raw22250step0Labels = mixedMoment B raw22250step1 raw22250step1Labels := by
      have hz : ∀ j, raw22250step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw22250step1 = (fun i j => raw22250step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw22250step1 raw22250step0; decide +kernel
      have hl : raw22250step1Labels = raw22250step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22250step0 raw22250step0Labels permutation104 hz
    mixedMoment B raw22250step1 raw22250step1Labels = mixedMoment B raw22250step2 raw22250step2Labels := by
      have hz : ∀ j, raw22250step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw22250step2 = (fun i j => raw22250step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw22250step2 raw22250step1; decide +kernel
      have hl : raw22250step2Labels = raw22250step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22250step1 raw22250step1Labels permutation20 hz
    _ = mixedMoment B node4274 node4274Labels := by rfl

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

theorem canonical669 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw669 raw669Labels = mixedMoment B node4099 node4099Labels := by
  calc
    mixedMoment B raw669 raw669Labels = mixedMoment B raw669step0 raw669step0Labels := by
      have ha : raw669step0 = (fun i j => raw669 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw669step0 raw669; decide +kernel
      have hl : raw669step0Labels = raw669Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw669 raw669Labels permutation32 permutation4
    mixedMoment B raw669step0 raw669step0Labels = mixedMoment B raw669step1 raw669step1Labels := by
      have ha : raw669step1 = raw669step0 := by apply Matrix.ext; unfold raw669step1 raw669step0; decide +kernel
      have hl : raw669step0Labels = labelEmbedding7 ∘ raw669step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw669step0 raw669step0Labels raw669step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4099 node4099Labels := by rfl

theorem canonical670 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw670 raw670Labels = mixedMoment B node536 node536Labels := by
  calc
    mixedMoment B raw670 raw670Labels = mixedMoment B raw670step0 raw670step0Labels := by
      have ha : raw670step0 = (fun i j => raw670 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw670step0 raw670; decide +kernel
      have hl : raw670step0Labels = raw670Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw670 raw670Labels permutation32 permutation4
    _ = mixedMoment B node536 node536Labels := by rfl

theorem canonical671 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw671 raw671Labels = mixedMoment B node657 node657Labels := by
  calc
    mixedMoment B raw671 raw671Labels = mixedMoment B raw671step0 raw671step0Labels := by
      have ha : raw671step0 = (fun i j => raw671 (permutation40 i) (permutation6 j)) := by apply Matrix.ext; unfold raw671step0 raw671; decide +kernel
      have hl : raw671step0Labels = raw671Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw671 raw671Labels permutation40 permutation6
    mixedMoment B raw671step0 raw671step0Labels = mixedMoment B raw671step1 raw671step1Labels := by
      have ha : raw671step1 = -raw671step0 := by apply Matrix.ext; change ∀ i j, raw671step1 i j = -(raw671step0 i j); unfold raw671step1 raw671step0; decide +kernel
      have hl : raw671step1Labels = raw671step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw671step1 raw671step1Labels = mixedMoment B raw671step2 raw671step2Labels := by
      have ha : raw671step2 = raw671step1 := by apply Matrix.ext; unfold raw671step2 raw671step1; decide +kernel
      have hl : raw671step1Labels = labelEmbedding1 ∘ raw671step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw671step1 raw671step1Labels raw671step2Labels labelEmbedding1 hl
    _ = mixedMoment B node657 node657Labels := by rfl

theorem canonical681 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw681 raw681Labels = mixedMoment B node4103 node4103Labels := by
  calc
    mixedMoment B raw681 raw681Labels = mixedMoment B raw681step0 raw681step0Labels := by
      have ha : raw681step0 = (fun i j => raw681 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw681step0 raw681; decide +kernel
      have hl : raw681step0Labels = raw681Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw681 raw681Labels permutation8 permutation4
    mixedMoment B raw681step0 raw681step0Labels = mixedMoment B raw681step1 raw681step1Labels := by
      have ha : raw681step1 = raw681step0 := by apply Matrix.ext; unfold raw681step1 raw681step0; decide +kernel
      have hl : raw681step0Labels = labelEmbedding7 ∘ raw681step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw681step0 raw681step0Labels raw681step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4103 node4103Labels := by rfl

theorem canonical682 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw682 raw682Labels = mixedMoment B node540 node540Labels := by
  calc
    mixedMoment B raw682 raw682Labels = mixedMoment B raw682step0 raw682step0Labels := by
      have ha : raw682step0 = (fun i j => raw682 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw682step0 raw682; decide +kernel
      have hl : raw682step0Labels = raw682Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw682 raw682Labels permutation8 permutation4
    _ = mixedMoment B node540 node540Labels := by rfl

theorem canonical683 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw683 raw683Labels = mixedMoment B node665 node665Labels := by
  calc
    mixedMoment B raw683 raw683Labels = mixedMoment B raw683step0 raw683step0Labels := by
      have ha : raw683step0 = (fun i j => raw683 (permutation10 i) (permutation6 j)) := by apply Matrix.ext; unfold raw683step0 raw683; decide +kernel
      have hl : raw683step0Labels = raw683Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw683 raw683Labels permutation10 permutation6
    mixedMoment B raw683step0 raw683step0Labels = mixedMoment B raw683step1 raw683step1Labels := by
      have ha : raw683step1 = -raw683step0 := by apply Matrix.ext; change ∀ i j, raw683step1 i j = -(raw683step0 i j); unfold raw683step1 raw683step0; decide +kernel
      have hl : raw683step1Labels = raw683step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw683step1 raw683step1Labels = mixedMoment B raw683step2 raw683step2Labels := by
      have ha : raw683step2 = raw683step1 := by apply Matrix.ext; unfold raw683step2 raw683step1; decide +kernel
      have hl : raw683step1Labels = labelEmbedding1 ∘ raw683step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw683step1 raw683step1Labels raw683step2Labels labelEmbedding1 hl
    _ = mixedMoment B node665 node665Labels := by rfl

theorem canonical699 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw699 raw699Labels = mixedMoment B node4109 node4109Labels := by
  calc
    mixedMoment B raw699 raw699Labels = mixedMoment B raw699step0 raw699step0Labels := by
      have ha : raw699step0 = (fun i j => raw699 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw699step0 raw699; decide +kernel
      have hl : raw699step0Labels = raw699Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw699 raw699Labels permutation8 permutation4
    mixedMoment B raw699step0 raw699step0Labels = mixedMoment B raw699step1 raw699step1Labels := by
      have ha : raw699step1 = raw699step0 := by apply Matrix.ext; unfold raw699step1 raw699step0; decide +kernel
      have hl : raw699step0Labels = labelEmbedding7 ∘ raw699step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw699step0 raw699step0Labels raw699step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4109 node4109Labels := by rfl

theorem canonical700 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw700 raw700Labels = mixedMoment B node546 node546Labels := by
  calc
    mixedMoment B raw700 raw700Labels = mixedMoment B raw700step0 raw700step0Labels := by
      have ha : raw700step0 = (fun i j => raw700 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw700step0 raw700; decide +kernel
      have hl : raw700step0Labels = raw700Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw700 raw700Labels permutation8 permutation4
    _ = mixedMoment B node546 node546Labels := by rfl

theorem canonical701 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw701 raw701Labels = mixedMoment B node676 node676Labels := by
  calc
    mixedMoment B raw701 raw701Labels = mixedMoment B raw701step0 raw701step0Labels := by
      have ha : raw701step0 = (fun i j => raw701 (permutation10 i) (permutation6 j)) := by apply Matrix.ext; unfold raw701step0 raw701; decide +kernel
      have hl : raw701step0Labels = raw701Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw701 raw701Labels permutation10 permutation6
    mixedMoment B raw701step0 raw701step0Labels = mixedMoment B raw701step1 raw701step1Labels := by
      have ha : raw701step1 = -raw701step0 := by apply Matrix.ext; change ∀ i j, raw701step1 i j = -(raw701step0 i j); unfold raw701step1 raw701step0; decide +kernel
      have hl : raw701step1Labels = raw701step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw701step1 raw701step1Labels = mixedMoment B raw701step2 raw701step2Labels := by
      have ha : raw701step2 = raw701step1 := by apply Matrix.ext; unfold raw701step2 raw701step1; decide +kernel
      have hl : raw701step1Labels = labelEmbedding1 ∘ raw701step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw701step1 raw701step1Labels raw701step2Labels labelEmbedding1 hl
    _ = mixedMoment B node676 node676Labels := by rfl

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

theorem canonical849 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw849 raw849Labels = mixedMoment B node4195 node4195Labels := by
  calc
    mixedMoment B raw849 raw849Labels = mixedMoment B raw849step0 raw849step0Labels := by
      have ha : raw849step0 = (fun i j => raw849 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw849step0 raw849; decide +kernel
      have hl : raw849step0Labels = raw849Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw849 raw849Labels permutation152 permutation4
    mixedMoment B raw849step0 raw849step0Labels = mixedMoment B raw849step1 raw849step1Labels := by
      have ha : raw849step1 = raw849step0 := by apply Matrix.ext; unfold raw849step1 raw849step0; decide +kernel
      have hl : raw849step0Labels = labelEmbedding7 ∘ raw849step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw849step0 raw849step0Labels raw849step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4195 node4195Labels := by rfl

theorem canonical850 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw850 raw850Labels = mixedMoment B node698 node698Labels := by
  calc
    mixedMoment B raw850 raw850Labels = mixedMoment B raw850step0 raw850step0Labels := by
      have ha : raw850step0 = (fun i j => raw850 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw850step0 raw850; decide +kernel
      have hl : raw850step0Labels = raw850Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw850 raw850Labels permutation152 permutation4
    _ = mixedMoment B node698 node698Labels := by rfl

theorem canonical851 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw851 raw851Labels = mixedMoment B node744 node744Labels := by
  calc
    mixedMoment B raw851 raw851Labels = mixedMoment B raw851step0 raw851step0Labels := by
      have ha : raw851step0 = (fun i j => raw851 (permutation160 i) (permutation6 j)) := by apply Matrix.ext; unfold raw851step0 raw851; decide +kernel
      have hl : raw851step0Labels = raw851Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw851 raw851Labels permutation160 permutation6
    mixedMoment B raw851step0 raw851step0Labels = mixedMoment B raw851step1 raw851step1Labels := by
      have ha : raw851step1 = -raw851step0 := by apply Matrix.ext; change ∀ i j, raw851step1 i j = -(raw851step0 i j); unfold raw851step1 raw851step0; decide +kernel
      have hl : raw851step1Labels = raw851step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw851step1 raw851step1Labels = mixedMoment B raw851step2 raw851step2Labels := by
      have ha : raw851step2 = raw851step1 := by apply Matrix.ext; unfold raw851step2 raw851step1; decide +kernel
      have hl : raw851step1Labels = labelEmbedding1 ∘ raw851step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw851step1 raw851step1Labels raw851step2Labels labelEmbedding1 hl
    _ = mixedMoment B node744 node744Labels := by rfl

theorem canonical858 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw858 raw858Labels = mixedMoment B node4198 node4198Labels := by
  calc
    mixedMoment B raw858 raw858Labels = mixedMoment B raw858step0 raw858step0Labels := by
      have ha : raw858step0 = (fun i j => raw858 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw858step0 raw858; decide +kernel
      have hl : raw858step0Labels = raw858Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw858 raw858Labels permutation32 permutation4
    mixedMoment B raw858step0 raw858step0Labels = mixedMoment B raw858step1 raw858step1Labels := by
      have ha : raw858step1 = raw858step0 := by apply Matrix.ext; unfold raw858step1 raw858step0; decide +kernel
      have hl : raw858step0Labels = labelEmbedding7 ∘ raw858step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw858step0 raw858step0Labels raw858step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4198 node4198Labels := by rfl

theorem canonical859 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw859 raw859Labels = mixedMoment B node701 node701Labels := by
  calc
    mixedMoment B raw859 raw859Labels = mixedMoment B raw859step0 raw859step0Labels := by
      have ha : raw859step0 = (fun i j => raw859 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw859step0 raw859; decide +kernel
      have hl : raw859step0Labels = raw859Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw859 raw859Labels permutation32 permutation4
    _ = mixedMoment B node701 node701Labels := by rfl

theorem canonical860 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw860 raw860Labels = mixedMoment B node750 node750Labels := by
  calc
    mixedMoment B raw860 raw860Labels = mixedMoment B raw860step0 raw860step0Labels := by
      have ha : raw860step0 = (fun i j => raw860 (permutation34 i) (permutation6 j)) := by apply Matrix.ext; unfold raw860step0 raw860; decide +kernel
      have hl : raw860step0Labels = raw860Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw860 raw860Labels permutation34 permutation6
    mixedMoment B raw860step0 raw860step0Labels = mixedMoment B raw860step1 raw860step1Labels := by
      have ha : raw860step1 = -raw860step0 := by apply Matrix.ext; change ∀ i j, raw860step1 i j = -(raw860step0 i j); unfold raw860step1 raw860step0; decide +kernel
      have hl : raw860step1Labels = raw860step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw860step1 raw860step1Labels = mixedMoment B raw860step2 raw860step2Labels := by
      have ha : raw860step2 = raw860step1 := by apply Matrix.ext; unfold raw860step2 raw860step1; decide +kernel
      have hl : raw860step1Labels = labelEmbedding1 ∘ raw860step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw860step1 raw860step1Labels raw860step2Labels labelEmbedding1 hl
    _ = mixedMoment B node750 node750Labels := by rfl

theorem canonical873 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw873 raw873Labels = mixedMoment B node4203 node4203Labels := by
  calc
    mixedMoment B raw873 raw873Labels = mixedMoment B raw873step0 raw873step0Labels := by
      have ha : raw873step0 = (fun i j => raw873 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw873step0 raw873; decide +kernel
      have hl : raw873step0Labels = raw873Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw873 raw873Labels permutation32 permutation4
    mixedMoment B raw873step0 raw873step0Labels = mixedMoment B raw873step1 raw873step1Labels := by
      have ha : raw873step1 = raw873step0 := by apply Matrix.ext; unfold raw873step1 raw873step0; decide +kernel
      have hl : raw873step0Labels = labelEmbedding7 ∘ raw873step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw873step0 raw873step0Labels raw873step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4203 node4203Labels := by rfl

theorem canonical874 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw874 raw874Labels = mixedMoment B node706 node706Labels := by
  calc
    mixedMoment B raw874 raw874Labels = mixedMoment B raw874step0 raw874step0Labels := by
      have ha : raw874step0 = (fun i j => raw874 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw874step0 raw874; decide +kernel
      have hl : raw874step0Labels = raw874Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw874 raw874Labels permutation32 permutation4
    _ = mixedMoment B node706 node706Labels := by rfl

theorem canonical875 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw875 raw875Labels = mixedMoment B node755 node755Labels := by
  calc
    mixedMoment B raw875 raw875Labels = mixedMoment B raw875step0 raw875step0Labels := by
      have ha : raw875step0 = (fun i j => raw875 (permutation34 i) (permutation6 j)) := by apply Matrix.ext; unfold raw875step0 raw875; decide +kernel
      have hl : raw875step0Labels = raw875Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw875 raw875Labels permutation34 permutation6
    mixedMoment B raw875step0 raw875step0Labels = mixedMoment B raw875step1 raw875step1Labels := by
      have ha : raw875step1 = -raw875step0 := by apply Matrix.ext; change ∀ i j, raw875step1 i j = -(raw875step0 i j); unfold raw875step1 raw875step0; decide +kernel
      have hl : raw875step1Labels = raw875step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw875step1 raw875step1Labels = mixedMoment B raw875step2 raw875step2Labels := by
      have ha : raw875step2 = raw875step1 := by apply Matrix.ext; unfold raw875step2 raw875step1; decide +kernel
      have hl : raw875step1Labels = labelEmbedding1 ∘ raw875step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw875step1 raw875step1Labels raw875step2Labels labelEmbedding1 hl
    _ = mixedMoment B node755 node755Labels := by rfl

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

theorem canonical927 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw927 raw927Labels = mixedMoment B node4231 node4231Labels := by
  calc
    mixedMoment B raw927 raw927Labels = mixedMoment B raw927step0 raw927step0Labels := by
      have ha : raw927step0 = (fun i j => raw927 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw927step0 raw927; decide +kernel
      have hl : raw927step0Labels = raw927Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw927 raw927Labels permutation32 permutation4
    mixedMoment B raw927step0 raw927step0Labels = mixedMoment B raw927step1 raw927step1Labels := by
      have ha : raw927step1 = raw927step0 := by apply Matrix.ext; unfold raw927step1 raw927step0; decide +kernel
      have hl : raw927step0Labels = labelEmbedding7 ∘ raw927step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw927step0 raw927step0Labels raw927step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4231 node4231Labels := by rfl

theorem canonical928 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw928 raw928Labels = mixedMoment B node731 node731Labels := by
  calc
    mixedMoment B raw928 raw928Labels = mixedMoment B raw928step0 raw928step0Labels := by
      have ha : raw928step0 = (fun i j => raw928 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw928step0 raw928; decide +kernel
      have hl : raw928step0Labels = raw928Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw928 raw928Labels permutation32 permutation4
    _ = mixedMoment B node731 node731Labels := by rfl

theorem canonical929 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw929 raw929Labels = mixedMoment B node781 node781Labels := by
  calc
    mixedMoment B raw929 raw929Labels = mixedMoment B raw929step0 raw929step0Labels := by
      have ha : raw929step0 = (fun i j => raw929 (permutation40 i) (permutation6 j)) := by apply Matrix.ext; unfold raw929step0 raw929; decide +kernel
      have hl : raw929step0Labels = raw929Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw929 raw929Labels permutation40 permutation6
    mixedMoment B raw929step0 raw929step0Labels = mixedMoment B raw929step1 raw929step1Labels := by
      have ha : raw929step1 = -raw929step0 := by apply Matrix.ext; change ∀ i j, raw929step1 i j = -(raw929step0 i j); unfold raw929step1 raw929step0; decide +kernel
      have hl : raw929step1Labels = raw929step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw929step1 raw929step1Labels = mixedMoment B raw929step2 raw929step2Labels := by
      have ha : raw929step2 = raw929step1 := by apply Matrix.ext; unfold raw929step2 raw929step1; decide +kernel
      have hl : raw929step1Labels = labelEmbedding1 ∘ raw929step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw929step1 raw929step1Labels raw929step2Labels labelEmbedding1 hl
    _ = mixedMoment B node781 node781Labels := by rfl

theorem canonical939 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw939 raw939Labels = mixedMoment B node4235 node4235Labels := by
  calc
    mixedMoment B raw939 raw939Labels = mixedMoment B raw939step0 raw939step0Labels := by
      have ha : raw939step0 = (fun i j => raw939 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw939step0 raw939; decide +kernel
      have hl : raw939step0Labels = raw939Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw939 raw939Labels permutation8 permutation4
    mixedMoment B raw939step0 raw939step0Labels = mixedMoment B raw939step1 raw939step1Labels := by
      have ha : raw939step1 = raw939step0 := by apply Matrix.ext; unfold raw939step1 raw939step0; decide +kernel
      have hl : raw939step0Labels = labelEmbedding7 ∘ raw939step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw939step0 raw939step0Labels raw939step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4235 node4235Labels := by rfl

theorem canonical940 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw940 raw940Labels = mixedMoment B node735 node735Labels := by
  calc
    mixedMoment B raw940 raw940Labels = mixedMoment B raw940step0 raw940step0Labels := by
      have ha : raw940step0 = (fun i j => raw940 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw940step0 raw940; decide +kernel
      have hl : raw940step0Labels = raw940Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw940 raw940Labels permutation8 permutation4
    _ = mixedMoment B node735 node735Labels := by rfl

theorem canonical941 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw941 raw941Labels = mixedMoment B node801 node801Labels := by
  calc
    mixedMoment B raw941 raw941Labels = mixedMoment B raw941step0 raw941step0Labels := by
      have ha : raw941step0 = (fun i j => raw941 (permutation10 i) (permutation6 j)) := by apply Matrix.ext; unfold raw941step0 raw941; decide +kernel
      have hl : raw941step0Labels = raw941Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw941 raw941Labels permutation10 permutation6
    mixedMoment B raw941step0 raw941step0Labels = mixedMoment B raw941step1 raw941step1Labels := by
      have ha : raw941step1 = -raw941step0 := by apply Matrix.ext; change ∀ i j, raw941step1 i j = -(raw941step0 i j); unfold raw941step1 raw941step0; decide +kernel
      have hl : raw941step1Labels = raw941step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw941step1 raw941step1Labels = mixedMoment B raw941step2 raw941step2Labels := by
      have ha : raw941step2 = raw941step1 := by apply Matrix.ext; unfold raw941step2 raw941step1; decide +kernel
      have hl : raw941step1Labels = labelEmbedding1 ∘ raw941step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw941step1 raw941step1Labels raw941step2Labels labelEmbedding1 hl
    _ = mixedMoment B node801 node801Labels := by rfl

theorem canonical957 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw957 raw957Labels = mixedMoment B node4241 node4241Labels := by
  calc
    mixedMoment B raw957 raw957Labels = mixedMoment B raw957step0 raw957step0Labels := by
      have ha : raw957step0 = (fun i j => raw957 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw957step0 raw957; decide +kernel
      have hl : raw957step0Labels = raw957Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw957 raw957Labels permutation8 permutation4
    mixedMoment B raw957step0 raw957step0Labels = mixedMoment B raw957step1 raw957step1Labels := by
      have ha : raw957step1 = raw957step0 := by apply Matrix.ext; unfold raw957step1 raw957step0; decide +kernel
      have hl : raw957step0Labels = labelEmbedding7 ∘ raw957step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw957step0 raw957step0Labels raw957step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4241 node4241Labels := by rfl

theorem canonical958 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw958 raw958Labels = mixedMoment B node741 node741Labels := by
  calc
    mixedMoment B raw958 raw958Labels = mixedMoment B raw958step0 raw958step0Labels := by
      have ha : raw958step0 = (fun i j => raw958 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw958step0 raw958; decide +kernel
      have hl : raw958step0Labels = raw958Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw958 raw958Labels permutation8 permutation4
    _ = mixedMoment B node741 node741Labels := by rfl

theorem canonical959 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw959 raw959Labels = mixedMoment B node820 node820Labels := by
  calc
    mixedMoment B raw959 raw959Labels = mixedMoment B raw959step0 raw959step0Labels := by
      have ha : raw959step0 = (fun i j => raw959 (permutation10 i) (permutation6 j)) := by apply Matrix.ext; unfold raw959step0 raw959; decide +kernel
      have hl : raw959step0Labels = raw959Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw959 raw959Labels permutation10 permutation6
    mixedMoment B raw959step0 raw959step0Labels = mixedMoment B raw959step1 raw959step1Labels := by
      have ha : raw959step1 = -raw959step0 := by apply Matrix.ext; change ∀ i j, raw959step1 i j = -(raw959step0 i j); unfold raw959step1 raw959step0; decide +kernel
      have hl : raw959step1Labels = raw959step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw959step1 raw959step1Labels = mixedMoment B raw959step2 raw959step2Labels := by
      have ha : raw959step2 = raw959step1 := by apply Matrix.ext; unfold raw959step2 raw959step1; decide +kernel
      have hl : raw959step1Labels = labelEmbedding1 ∘ raw959step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw959step1 raw959step1Labels raw959step2Labels labelEmbedding1 hl
    _ = mixedMoment B node820 node820Labels := by rfl

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

theorem canonical999 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw999 raw999Labels = mixedMoment B node4272 node4272Labels := by
  calc
    mixedMoment B raw999 raw999Labels = mixedMoment B raw999step0 raw999step0Labels := by
      have ha : raw999step0 = (fun i j => raw999 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw999step0 raw999; decide +kernel
      have hl : raw999step0Labels = raw999Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw999 raw999Labels permutation8 permutation4
    mixedMoment B raw999step0 raw999step0Labels = mixedMoment B raw999step1 raw999step1Labels := by
      have ha : raw999step1 = raw999step0 := by apply Matrix.ext; unfold raw999step1 raw999step0; decide +kernel
      have hl : raw999step0Labels = labelEmbedding7 ∘ raw999step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw999step0 raw999step0Labels raw999step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4272 node4272Labels := by rfl

theorem canonical1000 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1000 raw1000Labels = mixedMoment B node815 node815Labels := by
  calc
    mixedMoment B raw1000 raw1000Labels = mixedMoment B raw1000step0 raw1000step0Labels := by
      have ha : raw1000step0 = (fun i j => raw1000 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1000step0 raw1000; decide +kernel
      have hl : raw1000step0Labels = raw1000Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1000 raw1000Labels permutation8 permutation4
    _ = mixedMoment B node815 node815Labels := by rfl

theorem canonical1001 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1001 raw1001Labels = mixedMoment B node826 node826Labels := by
  calc
    mixedMoment B raw1001 raw1001Labels = mixedMoment B raw1001step0 raw1001step0Labels := by
      have ha : raw1001step0 = (fun i j => raw1001 (permutation10 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1001step0 raw1001; decide +kernel
      have hl : raw1001step0Labels = raw1001Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1001 raw1001Labels permutation10 permutation6
    mixedMoment B raw1001step0 raw1001step0Labels = mixedMoment B raw1001step1 raw1001step1Labels := by
      have ha : raw1001step1 = -raw1001step0 := by apply Matrix.ext; change ∀ i j, raw1001step1 i j = -(raw1001step0 i j); unfold raw1001step1 raw1001step0; decide +kernel
      have hl : raw1001step1Labels = raw1001step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1001step1 raw1001step1Labels = mixedMoment B raw1001step2 raw1001step2Labels := by
      have ha : raw1001step2 = raw1001step1 := by apply Matrix.ext; unfold raw1001step2 raw1001step1; decide +kernel
      have hl : raw1001step1Labels = labelEmbedding1 ∘ raw1001step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1001step1 raw1001step1Labels raw1001step2Labels labelEmbedding1 hl
    _ = mixedMoment B node826 node826Labels := by rfl

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

theorem canonical1209 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1209 raw1209Labels = mixedMoment B node4398 node4398Labels := by
  calc
    mixedMoment B raw1209 raw1209Labels = mixedMoment B raw1209step0 raw1209step0Labels := by
      have ha : raw1209step0 = (fun i j => raw1209 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1209step0 raw1209; decide +kernel
      have hl : raw1209step0Labels = raw1209Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1209 raw1209Labels permutation32 permutation4
    mixedMoment B raw1209step0 raw1209step0Labels = mixedMoment B raw1209step1 raw1209step1Labels := by
      have ha : raw1209step1 = raw1209step0 := by apply Matrix.ext; unfold raw1209step1 raw1209step0; decide +kernel
      have hl : raw1209step0Labels = labelEmbedding7 ∘ raw1209step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1209step0 raw1209step0Labels raw1209step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4398 node4398Labels := by rfl

theorem canonical1210 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1210 raw1210Labels = mixedMoment B node979 node979Labels := by
  calc
    mixedMoment B raw1210 raw1210Labels = mixedMoment B raw1210step0 raw1210step0Labels := by
      have ha : raw1210step0 = (fun i j => raw1210 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1210step0 raw1210; decide +kernel
      have hl : raw1210step0Labels = raw1210Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1210 raw1210Labels permutation32 permutation4
    _ = mixedMoment B node979 node979Labels := by rfl

theorem canonical1211 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1211 raw1211Labels = mixedMoment B node1599 node1599Labels := by
  calc
    mixedMoment B raw1211 raw1211Labels = mixedMoment B raw1211step0 raw1211step0Labels := by
      have ha : raw1211step0 = (fun i j => raw1211 (permutation34 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1211step0 raw1211; decide +kernel
      have hl : raw1211step0Labels = raw1211Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1211 raw1211Labels permutation34 permutation6
    mixedMoment B raw1211step0 raw1211step0Labels = mixedMoment B raw1211step1 raw1211step1Labels := by
      have ha : raw1211step1 = -raw1211step0 := by apply Matrix.ext; change ∀ i j, raw1211step1 i j = -(raw1211step0 i j); unfold raw1211step1 raw1211step0; decide +kernel
      have hl : raw1211step1Labels = raw1211step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1211step1 raw1211step1Labels = mixedMoment B raw1211step2 raw1211step2Labels := by
      have ha : raw1211step2 = raw1211step1 := by apply Matrix.ext; unfold raw1211step2 raw1211step1; decide +kernel
      have hl : raw1211step1Labels = labelEmbedding1 ∘ raw1211step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1211step1 raw1211step1Labels raw1211step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1599 node1599Labels := by rfl

theorem canonical1251 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1251 raw1251Labels = mixedMoment B node4454 node4454Labels := by
  calc
    mixedMoment B raw1251 raw1251Labels = mixedMoment B raw1251step0 raw1251step0Labels := by
      have ha : raw1251step0 = (fun i j => raw1251 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1251step0 raw1251; decide +kernel
      have hl : raw1251step0Labels = raw1251Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1251 raw1251Labels permutation8 permutation4
    mixedMoment B raw1251step0 raw1251step0Labels = mixedMoment B raw1251step1 raw1251step1Labels := by
      have ha : raw1251step1 = raw1251step0 := by apply Matrix.ext; unfold raw1251step1 raw1251step0; decide +kernel
      have hl : raw1251step0Labels = labelEmbedding7 ∘ raw1251step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1251step0 raw1251step0Labels raw1251step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4454 node4454Labels := by rfl

theorem canonical1252 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1252 raw1252Labels = mixedMoment B node1037 node1037Labels := by
  calc
    mixedMoment B raw1252 raw1252Labels = mixedMoment B raw1252step0 raw1252step0Labels := by
      have ha : raw1252step0 = (fun i j => raw1252 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1252step0 raw1252; decide +kernel
      have hl : raw1252step0Labels = raw1252Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1252 raw1252Labels permutation8 permutation4
    _ = mixedMoment B node1037 node1037Labels := by rfl

theorem canonical1253 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1253 raw1253Labels = mixedMoment B node1647 node1647Labels := by
  calc
    mixedMoment B raw1253 raw1253Labels = mixedMoment B raw1253step0 raw1253step0Labels := by
      have ha : raw1253step0 = (fun i j => raw1253 (permutation10 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1253step0 raw1253; decide +kernel
      have hl : raw1253step0Labels = raw1253Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1253 raw1253Labels permutation10 permutation6
    mixedMoment B raw1253step0 raw1253step0Labels = mixedMoment B raw1253step1 raw1253step1Labels := by
      have ha : raw1253step1 = -raw1253step0 := by apply Matrix.ext; change ∀ i j, raw1253step1 i j = -(raw1253step0 i j); unfold raw1253step1 raw1253step0; decide +kernel
      have hl : raw1253step1Labels = raw1253step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1253step1 raw1253step1Labels = mixedMoment B raw1253step2 raw1253step2Labels := by
      have ha : raw1253step2 = raw1253step1 := by apply Matrix.ext; unfold raw1253step2 raw1253step1; decide +kernel
      have hl : raw1253step1Labels = labelEmbedding1 ∘ raw1253step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1253step1 raw1253step1Labels raw1253step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1647 node1647Labels := by rfl

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

theorem singleton4099 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4099 node4099Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node536 node536Labels + mixedMoment B node657 node657Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw669 singletonSmall4099
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4099) = raw669Labels := by decide +kernel
  rw [hl, canonical669 B hB] at h
  have hc0 : mixedMoment B raw669 (Fin.cases (0 : Fin 2) singletonSmall4099) =
      mixedMoment B node536 node536Labels := by
    have ha : raw669 = raw670 := by apply Matrix.ext; unfold raw669 raw670; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4099 = raw670Labels := by decide +kernel
    rw [ha, hj, canonical670 B hB]
  have hc1 : mixedMoment B raw669 (Fin.cases (1 : Fin 2) singletonSmall4099) =
      mixedMoment B node657 node657Labels := by
    have ha : raw669 = raw671 := by apply Matrix.ext; unfold raw669 raw671; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4099 = raw671Labels := by decide +kernel
    rw [ha, hj, canonical671 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4103 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4103 node4103Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node540 node540Labels + mixedMoment B node665 node665Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw681 singletonSmall4103
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4103) = raw681Labels := by decide +kernel
  rw [hl, canonical681 B hB] at h
  have hc0 : mixedMoment B raw681 (Fin.cases (0 : Fin 2) singletonSmall4103) =
      mixedMoment B node540 node540Labels := by
    have ha : raw681 = raw682 := by apply Matrix.ext; unfold raw681 raw682; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4103 = raw682Labels := by decide +kernel
    rw [ha, hj, canonical682 B hB]
  have hc1 : mixedMoment B raw681 (Fin.cases (1 : Fin 2) singletonSmall4103) =
      mixedMoment B node665 node665Labels := by
    have ha : raw681 = raw683 := by apply Matrix.ext; unfold raw681 raw683; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4103 = raw683Labels := by decide +kernel
    rw [ha, hj, canonical683 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4109 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4109 node4109Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node546 node546Labels + mixedMoment B node676 node676Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw699 singletonSmall4109
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4109) = raw699Labels := by decide +kernel
  rw [hl, canonical699 B hB] at h
  have hc0 : mixedMoment B raw699 (Fin.cases (0 : Fin 2) singletonSmall4109) =
      mixedMoment B node546 node546Labels := by
    have ha : raw699 = raw700 := by apply Matrix.ext; unfold raw699 raw700; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4109 = raw700Labels := by decide +kernel
    rw [ha, hj, canonical700 B hB]
  have hc1 : mixedMoment B raw699 (Fin.cases (1 : Fin 2) singletonSmall4109) =
      mixedMoment B node676 node676Labels := by
    have ha : raw699 = raw701 := by apply Matrix.ext; unfold raw699 raw701; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4109 = raw701Labels := by decide +kernel
    rw [ha, hj, canonical701 B hB]
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

theorem singleton4195 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4195 node4195Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node698 node698Labels + mixedMoment B node744 node744Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw849 singletonSmall4195
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4195) = raw849Labels := by decide +kernel
  rw [hl, canonical849 B hB] at h
  have hc0 : mixedMoment B raw849 (Fin.cases (0 : Fin 2) singletonSmall4195) =
      mixedMoment B node698 node698Labels := by
    have ha : raw849 = raw850 := by apply Matrix.ext; unfold raw849 raw850; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4195 = raw850Labels := by decide +kernel
    rw [ha, hj, canonical850 B hB]
  have hc1 : mixedMoment B raw849 (Fin.cases (1 : Fin 2) singletonSmall4195) =
      mixedMoment B node744 node744Labels := by
    have ha : raw849 = raw851 := by apply Matrix.ext; unfold raw849 raw851; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4195 = raw851Labels := by decide +kernel
    rw [ha, hj, canonical851 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4198 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4198 node4198Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node701 node701Labels + mixedMoment B node750 node750Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw858 singletonSmall4198
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4198) = raw858Labels := by decide +kernel
  rw [hl, canonical858 B hB] at h
  have hc0 : mixedMoment B raw858 (Fin.cases (0 : Fin 2) singletonSmall4198) =
      mixedMoment B node701 node701Labels := by
    have ha : raw858 = raw859 := by apply Matrix.ext; unfold raw858 raw859; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4198 = raw859Labels := by decide +kernel
    rw [ha, hj, canonical859 B hB]
  have hc1 : mixedMoment B raw858 (Fin.cases (1 : Fin 2) singletonSmall4198) =
      mixedMoment B node750 node750Labels := by
    have ha : raw858 = raw860 := by apply Matrix.ext; unfold raw858 raw860; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4198 = raw860Labels := by decide +kernel
    rw [ha, hj, canonical860 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4203 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4203 node4203Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node706 node706Labels + mixedMoment B node755 node755Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw873 singletonSmall4203
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4203) = raw873Labels := by decide +kernel
  rw [hl, canonical873 B hB] at h
  have hc0 : mixedMoment B raw873 (Fin.cases (0 : Fin 2) singletonSmall4203) =
      mixedMoment B node706 node706Labels := by
    have ha : raw873 = raw874 := by apply Matrix.ext; unfold raw873 raw874; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4203 = raw874Labels := by decide +kernel
    rw [ha, hj, canonical874 B hB]
  have hc1 : mixedMoment B raw873 (Fin.cases (1 : Fin 2) singletonSmall4203) =
      mixedMoment B node755 node755Labels := by
    have ha : raw873 = raw875 := by apply Matrix.ext; unfold raw873 raw875; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4203 = raw875Labels := by decide +kernel
    rw [ha, hj, canonical875 B hB]
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

theorem singleton4231 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4231 node4231Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node731 node731Labels + mixedMoment B node781 node781Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw927 singletonSmall4231
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4231) = raw927Labels := by decide +kernel
  rw [hl, canonical927 B hB] at h
  have hc0 : mixedMoment B raw927 (Fin.cases (0 : Fin 2) singletonSmall4231) =
      mixedMoment B node731 node731Labels := by
    have ha : raw927 = raw928 := by apply Matrix.ext; unfold raw927 raw928; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4231 = raw928Labels := by decide +kernel
    rw [ha, hj, canonical928 B hB]
  have hc1 : mixedMoment B raw927 (Fin.cases (1 : Fin 2) singletonSmall4231) =
      mixedMoment B node781 node781Labels := by
    have ha : raw927 = raw929 := by apply Matrix.ext; unfold raw927 raw929; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4231 = raw929Labels := by decide +kernel
    rw [ha, hj, canonical929 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4235 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4235 node4235Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node735 node735Labels + mixedMoment B node801 node801Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw939 singletonSmall4235
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4235) = raw939Labels := by decide +kernel
  rw [hl, canonical939 B hB] at h
  have hc0 : mixedMoment B raw939 (Fin.cases (0 : Fin 2) singletonSmall4235) =
      mixedMoment B node735 node735Labels := by
    have ha : raw939 = raw940 := by apply Matrix.ext; unfold raw939 raw940; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4235 = raw940Labels := by decide +kernel
    rw [ha, hj, canonical940 B hB]
  have hc1 : mixedMoment B raw939 (Fin.cases (1 : Fin 2) singletonSmall4235) =
      mixedMoment B node801 node801Labels := by
    have ha : raw939 = raw941 := by apply Matrix.ext; unfold raw939 raw941; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4235 = raw941Labels := by decide +kernel
    rw [ha, hj, canonical941 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4241 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4241 node4241Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node741 node741Labels + mixedMoment B node820 node820Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw957 singletonSmall4241
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4241) = raw957Labels := by decide +kernel
  rw [hl, canonical957 B hB] at h
  have hc0 : mixedMoment B raw957 (Fin.cases (0 : Fin 2) singletonSmall4241) =
      mixedMoment B node741 node741Labels := by
    have ha : raw957 = raw958 := by apply Matrix.ext; unfold raw957 raw958; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4241 = raw958Labels := by decide +kernel
    rw [ha, hj, canonical958 B hB]
  have hc1 : mixedMoment B raw957 (Fin.cases (1 : Fin 2) singletonSmall4241) =
      mixedMoment B node820 node820Labels := by
    have ha : raw957 = raw959 := by apply Matrix.ext; unfold raw957 raw959; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4241 = raw959Labels := by decide +kernel
    rw [ha, hj, canonical959 B hB]
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

theorem singleton4272 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4272 node4272Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node815 node815Labels + mixedMoment B node826 node826Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw999 singletonSmall4272
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4272) = raw999Labels := by decide +kernel
  rw [hl, canonical999 B hB] at h
  have hc0 : mixedMoment B raw999 (Fin.cases (0 : Fin 2) singletonSmall4272) =
      mixedMoment B node815 node815Labels := by
    have ha : raw999 = raw1000 := by apply Matrix.ext; unfold raw999 raw1000; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4272 = raw1000Labels := by decide +kernel
    rw [ha, hj, canonical1000 B hB]
  have hc1 : mixedMoment B raw999 (Fin.cases (1 : Fin 2) singletonSmall4272) =
      mixedMoment B node826 node826Labels := by
    have ha : raw999 = raw1001 := by apply Matrix.ext; unfold raw999 raw1001; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4272 = raw1001Labels := by decide +kernel
    rw [ha, hj, canonical1001 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons68
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singleton4398 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4398 node4398Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node979 node979Labels + mixedMoment B node1599 node1599Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1209 singletonSmall4398
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4398) = raw1209Labels := by decide +kernel
  rw [hl, canonical1209 B hB] at h
  have hc0 : mixedMoment B raw1209 (Fin.cases (0 : Fin 2) singletonSmall4398) =
      mixedMoment B node979 node979Labels := by
    have ha : raw1209 = raw1210 := by apply Matrix.ext; unfold raw1209 raw1210; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4398 = raw1210Labels := by decide +kernel
    rw [ha, hj, canonical1210 B hB]
  have hc1 : mixedMoment B raw1209 (Fin.cases (1 : Fin 2) singletonSmall4398) =
      mixedMoment B node1599 node1599Labels := by
    have ha : raw1209 = raw1211 := by apply Matrix.ext; unfold raw1209 raw1211; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4398 = raw1211Labels := by decide +kernel
    rw [ha, hj, canonical1211 B hB]
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

theorem singleton4454 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4454 node4454Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1037 node1037Labels + mixedMoment B node1647 node1647Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1251 singletonSmall4454
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4454) = raw1251Labels := by decide +kernel
  rw [hl, canonical1251 B hB] at h
  have hc0 : mixedMoment B raw1251 (Fin.cases (0 : Fin 2) singletonSmall4454) =
      mixedMoment B node1037 node1037Labels := by
    have ha : raw1251 = raw1252 := by apply Matrix.ext; unfold raw1251 raw1252; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4454 = raw1252Labels := by decide +kernel
    rw [ha, hj, canonical1252 B hB]
  have hc1 : mixedMoment B raw1251 (Fin.cases (1 : Fin 2) singletonSmall4454) =
      mixedMoment B node1647 node1647Labels := by
    have ha : raw1251 = raw1253 := by apply Matrix.ext; unfold raw1251 raw1253; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4454 = raw1253Labels := by decide +kernel
    rw [ha, hj, canonical1253 B hB]
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

theorem sound657 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node657 node657Labels = Sparse.eval nodeValue657 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 657) = mixedMoment B node657 node657Labels := rfl
  simpa [nodeValue657, Sparse.eval] using hc.symm

theorem sound665 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node665 node665Labels = Sparse.eval nodeValue665 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 665) = mixedMoment B node665 node665Labels := rfl
  simpa [nodeValue665, Sparse.eval] using hc.symm

theorem sound676 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node676 node676Labels = Sparse.eval nodeValue676 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 676) = mixedMoment B node676 node676Labels := rfl
  simpa [nodeValue676, Sparse.eval] using hc.symm

theorem sound698 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node698 node698Labels = Sparse.eval nodeValue698 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 698) = mixedMoment B node698 node698Labels := rfl
  simpa [nodeValue698, Sparse.eval] using hc.symm

theorem sound701 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node701 node701Labels = Sparse.eval nodeValue701 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 701) = mixedMoment B node701 node701Labels := rfl
  simpa [nodeValue701, Sparse.eval] using hc.symm

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

theorem sound706 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node706 node706Labels = Sparse.eval nodeValue706 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 706) = mixedMoment B node706 node706Labels := rfl
  simpa [nodeValue706, Sparse.eval] using hc.symm

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

theorem sound744 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node744 node744Labels = Sparse.eval nodeValue744 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 744) = mixedMoment B node744 node744Labels := rfl
  simpa [nodeValue744, Sparse.eval] using hc.symm

theorem sound750 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node750 node750Labels = Sparse.eval nodeValue750 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 750) = mixedMoment B node750 node750Labels := rfl
  simpa [nodeValue750, Sparse.eval] using hc.symm

theorem sound755 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node755 node755Labels = Sparse.eval nodeValue755 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 755) = mixedMoment B node755 node755Labels := rfl
  simpa [nodeValue755, Sparse.eval] using hc.symm

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

theorem sound781 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node781 node781Labels = Sparse.eval nodeValue781 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 781) = mixedMoment B node781 node781Labels := rfl
  simpa [nodeValue781, Sparse.eval] using hc.symm

theorem sound785 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node785 node785Labels = Sparse.eval nodeValue785 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 785) = mixedMoment B node785 node785Labels := rfl
  simpa [nodeValue785, Sparse.eval] using hc.symm

theorem sound801 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node801 node801Labels = Sparse.eval nodeValue801 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 801) = mixedMoment B node801 node801Labels := rfl
  simpa [nodeValue801, Sparse.eval] using hc.symm

theorem sound804 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node804 node804Labels = Sparse.eval nodeValue804 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 804) = mixedMoment B node804 node804Labels := rfl
  simpa [nodeValue804, Sparse.eval] using hc.symm

theorem sound815 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node815 node815Labels = Sparse.eval nodeValue815 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 815) = mixedMoment B node815 node815Labels := rfl
  simpa [nodeValue815, Sparse.eval] using hc.symm

theorem sound820 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node820 node820Labels = Sparse.eval nodeValue820 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 820) = mixedMoment B node820 node820Labels := rfl
  simpa [nodeValue820, Sparse.eval] using hc.symm

theorem sound826 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node826 node826Labels = Sparse.eval nodeValue826 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 826) = mixedMoment B node826 node826Labels := rfl
  simpa [nodeValue826, Sparse.eval] using hc.symm

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

theorem sound979 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node979 node979Labels = Sparse.eval nodeValue979 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 979) = mixedMoment B node979 node979Labels := rfl
  simpa [nodeValue979, Sparse.eval] using hc.symm

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

theorem sound1037 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1037 node1037Labels = Sparse.eval nodeValue1037 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1037) = mixedMoment B node1037 node1037Labels := rfl
  simpa [nodeValue1037, Sparse.eval] using hc.symm

theorem sound1043 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1043 node1043Labels = Sparse.eval nodeValue1043 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1043) = mixedMoment B node1043 node1043Labels := rfl
  simpa [nodeValue1043, Sparse.eval] using hc.symm

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

theorem sound1599 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1599 node1599Labels = Sparse.eval nodeValue1599 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1599) = mixedMoment B node1599 node1599Labels := rfl
  simpa [nodeValue1599, Sparse.eval] using hc.symm

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

theorem sound1725 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1725 node1725Labels = Sparse.eval nodeValue1725 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1725) = mixedMoment B node1725 node1725Labels := rfl
  simpa [nodeValue1725, Sparse.eval] using hc.symm

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

theorem sound540 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node540 node540Labels = Sparse.eval nodeValue540 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 540) = mixedMoment B node540 node540Labels := rfl
  simpa [nodeValue540, Sparse.eval] using hc.symm

theorem sound546 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node546 node546Labels = Sparse.eval nodeValue546 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 546) = mixedMoment B node546 node546Labels := rfl
  simpa [nodeValue546, Sparse.eval] using hc.symm

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

theorem zero4120 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4120 node4120Labels = 0 := by
  exact mixedMoment_order_one B hB node4120 node4120Labels 1
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

theorem sound4099 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4099 node4099Labels = Sparse.eval nodeValue4099 (mixedVector B) := by
  have h := singleton4099 B _hB
  rw [sound536 B _hB _hF, sound657 B _hB _hF] at h
  norm_num [nodeValue4099, nodeValue536, nodeValue657, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4103 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4103 node4103Labels = Sparse.eval nodeValue4103 (mixedVector B) := by
  have h := singleton4103 B _hB
  rw [sound540 B _hB _hF, sound665 B _hB _hF] at h
  norm_num [nodeValue4103, nodeValue540, nodeValue665, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4109 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4109 node4109Labels = Sparse.eval nodeValue4109 (mixedVector B) := by
  have h := singleton4109 B _hB
  rw [sound546 B _hB _hF, sound676 B _hB _hF] at h
  norm_num [nodeValue4109, nodeValue546, nodeValue676, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4120 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4120 node4120Labels = Sparse.eval nodeValue4120 (mixedVector B) := by
  simpa only [nodeValue4120, Sparse.eval_nil] using zero4120 B _hB _hF

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

theorem zero4211 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4211 node4211Labels = 0 := by
  exact mixedMoment_order_one B hB node4211 node4211Labels 1
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

theorem sound4195 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4195 node4195Labels = Sparse.eval nodeValue4195 (mixedVector B) := by
  have h := singleton4195 B _hB
  rw [sound698 B _hB _hF, sound744 B _hB _hF] at h
  norm_num [nodeValue4195, nodeValue698, nodeValue744, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4198 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4198 node4198Labels = Sparse.eval nodeValue4198 (mixedVector B) := by
  have h := singleton4198 B _hB
  rw [sound701 B _hB _hF, sound750 B _hB _hF] at h
  norm_num [nodeValue4198, nodeValue701, nodeValue750, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4203 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4203 node4203Labels = Sparse.eval nodeValue4203 (mixedVector B) := by
  have h := singleton4203 B _hB
  rw [sound706 B _hB _hF, sound755 B _hB _hF] at h
  norm_num [nodeValue4203, nodeValue706, nodeValue755, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4211 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4211 node4211Labels = Sparse.eval nodeValue4211 (mixedVector B) := by
  simpa only [nodeValue4211, Sparse.eval_nil] using zero4211 B _hB _hF

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

theorem zero4266 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4266 node4266Labels = 0 := by
  exact mixedMoment_order_one B hB node4266 node4266Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero4269 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4269 node4269Labels = 0 := by
  exact mixedMoment_order_one B hB node4269 node4269Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero4274 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4274 node4274Labels = 0 := by
  exact mixedMoment_order_one B hB node4274 node4274Labels 1
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

theorem sound4231 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4231 node4231Labels = Sparse.eval nodeValue4231 (mixedVector B) := by
  have h := singleton4231 B _hB
  rw [sound731 B _hB _hF, sound781 B _hB _hF] at h
  norm_num [nodeValue4231, nodeValue731, nodeValue781, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4235 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4235 node4235Labels = Sparse.eval nodeValue4235 (mixedVector B) := by
  have h := singleton4235 B _hB
  rw [sound735 B _hB _hF, sound801 B _hB _hF] at h
  norm_num [nodeValue4235, nodeValue735, nodeValue801, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4241 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4241 node4241Labels = Sparse.eval nodeValue4241 (mixedVector B) := by
  have h := singleton4241 B _hB
  rw [sound741 B _hB _hF, sound820 B _hB _hF] at h
  norm_num [nodeValue4241, nodeValue741, nodeValue820, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4251 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4251 node4251Labels = Sparse.eval nodeValue4251 (mixedVector B) := by
  have h := singleton4251 B _hB
  rw [sound785 B _hB _hF, sound804 B _hB _hF] at h
  norm_num [nodeValue4251, nodeValue785, nodeValue804, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4266 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4266 node4266Labels = Sparse.eval nodeValue4266 (mixedVector B) := by
  simpa only [nodeValue4266, Sparse.eval_nil] using zero4266 B _hB _hF

theorem sound4269 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4269 node4269Labels = Sparse.eval nodeValue4269 (mixedVector B) := by
  simpa only [nodeValue4269, Sparse.eval_nil] using zero4269 B _hB _hF

theorem sound4272 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4272 node4272Labels = Sparse.eval nodeValue4272 (mixedVector B) := by
  have h := singleton4272 B _hB
  rw [sound815 B _hB _hF, sound826 B _hB _hF] at h
  norm_num [nodeValue4272, nodeValue815, nodeValue826, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4274 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4274 node4274Labels = Sparse.eval nodeValue4274 (mixedVector B) := by
  simpa only [nodeValue4274, Sparse.eval_nil] using zero4274 B _hB _hF

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

theorem sound4398 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4398 node4398Labels = Sparse.eval nodeValue4398 (mixedVector B) := by
  have h := singleton4398 B _hB
  rw [sound979 B _hB _hF, sound1599 B _hB _hF] at h
  norm_num [nodeValue4398, nodeValue979, nodeValue1599, Sparse.eval] at h ⊢
  linarith only [h]

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

theorem sound4454 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4454 node4454Labels = Sparse.eval nodeValue4454 (mixedVector B) := by
  have h := singleton4454 B _hB
  rw [sound1037 B _hB _hF, sound1647 B _hB _hF] at h
  norm_num [nodeValue4454, nodeValue1037, nodeValue1647, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4460 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4460 node4460Labels = Sparse.eval nodeValue4460 (mixedVector B) := by
  have h := singleton4460 B _hB
  rw [sound1043 B _hB _hF, sound1725 B _hB _hF] at h
  norm_num [nodeValue4460, nodeValue1043, nodeValue1725, Sparse.eval] at h ⊢
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

theorem zero4501 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4501 node4501Labels = 0 := by
  exact mixedMoment_order_one B hB node4501 node4501Labels 1
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

theorem sound4501 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4501 node4501Labels = Sparse.eval nodeValue4501 (mixedVector B) := by
  simpa only [nodeValue4501, Sparse.eval_nil] using zero4501 B _hB _hF

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

theorem sourceEq1435 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1435 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1435 + difference 0 1) (sourceB1435 + difference 1 0) sourceC1435) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4454) := by
    have ha : (tripleCharges (sourceA1435 + difference 0 1) (sourceB1435 + difference 1 0) sourceC1435) = raw22221 := by
      apply Matrix.ext; unfold tripleCharges sourceA1435 sourceB1435 sourceC1435 difference raw22221; decide +kernel
    rw [ha]
    exact (canonical22221 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1435 + difference 0 2) (sourceB1435 + difference 2 0) sourceC1435) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4398) := by
    have ha : (tripleCharges (sourceA1435 + difference 0 2) (sourceB1435 + difference 2 0) sourceC1435) = raw22222 := by
      apply Matrix.ext; unfold tripleCharges sourceA1435 sourceB1435 sourceC1435 difference raw22222; decide +kernel
    rw [ha]
    exact (canonical22222 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1435 + difference 0 3) (sourceB1435 + difference 3 0) sourceC1435) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4398) := by
    have ha : (tripleCharges (sourceA1435 + difference 0 3) (sourceB1435 + difference 3 0) sourceC1435) = raw22223 := by
      apply Matrix.ext; unfold tripleCharges sourceA1435 sourceB1435 sourceC1435 difference raw22223; decide +kernel
    rw [ha]
    exact (canonical22223 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1435 + difference 0 4) (sourceB1435 + difference 4 0) sourceC1435) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4501) := by
    have ha : (tripleCharges (sourceA1435 + difference 0 4) (sourceB1435 + difference 4 0) sourceC1435) = raw22224 := by
      apply Matrix.ext; unfold tripleCharges sourceA1435 sourceB1435 sourceC1435 difference raw22224; decide +kernel
    rw [ha]
    exact (canonical22224 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1435 + difference 0 5) (sourceB1435 + difference 5 0) sourceC1435) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4460) := by
    have ha : (tripleCharges (sourceA1435 + difference 0 5) (sourceB1435 + difference 5 0) sourceC1435) = raw22225 := by
      apply Matrix.ext; unfold tripleCharges sourceA1435 sourceB1435 sourceC1435 difference raw22225; decide +kernel
    rw [ha]
    exact (canonical22225 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1435 + difference 1 0) (sourceB1435 + difference 0 1) sourceC1435) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4120) := by
    have ha : (tripleCharges (sourceA1435 + difference 1 0) (sourceB1435 + difference 0 1) sourceC1435) = raw22226 := by
      apply Matrix.ext; unfold tripleCharges sourceA1435 sourceB1435 sourceC1435 difference raw22226; decide +kernel
    rw [ha]
    exact (canonical22226 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1435 + difference 1 2) (sourceB1435 + difference 2 1) sourceC1435) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4211) := by
    have ha : (tripleCharges (sourceA1435 + difference 1 2) (sourceB1435 + difference 2 1) sourceC1435) = raw22227 := by
      apply Matrix.ext; unfold tripleCharges sourceA1435 sourceB1435 sourceC1435 difference raw22227; decide +kernel
    rw [ha]
    exact (canonical22227 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1435 + difference 1 3) (sourceB1435 + difference 3 1) sourceC1435) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4211) := by
    have ha : (tripleCharges (sourceA1435 + difference 1 3) (sourceB1435 + difference 3 1) sourceC1435) = raw22228 := by
      apply Matrix.ext; unfold tripleCharges sourceA1435 sourceB1435 sourceC1435 difference raw22228; decide +kernel
    rw [ha]
    exact (canonical22228 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1435 + difference 1 4) (sourceB1435 + difference 4 1) sourceC1435) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4070) := by
    have ha : (tripleCharges (sourceA1435 + difference 1 4) (sourceB1435 + difference 4 1) sourceC1435) = raw22229 := by
      apply Matrix.ext; unfold tripleCharges sourceA1435 sourceB1435 sourceC1435 difference raw22229; decide +kernel
    rw [ha]
    exact (canonical22229 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1435 + difference 1 5) (sourceB1435 + difference 5 1) sourceC1435) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4269) := by
    have ha : (tripleCharges (sourceA1435 + difference 1 5) (sourceB1435 + difference 5 1) sourceC1435) = raw22230 := by
      apply Matrix.ext; unfold tripleCharges sourceA1435 sourceB1435 sourceC1435 difference raw22230; decide +kernel
    rw [ha]
    exact (canonical22230 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1435 + difference 2 0) (sourceB1435 + difference 0 2) sourceC1435) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4099) := by
    have ha : (tripleCharges (sourceA1435 + difference 2 0) (sourceB1435 + difference 0 2) sourceC1435) = raw22231 := by
      apply Matrix.ext; unfold tripleCharges sourceA1435 sourceB1435 sourceC1435 difference raw22231; decide +kernel
    rw [ha]
    exact (canonical22231 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1435 + difference 2 1) (sourceB1435 + difference 1 2) sourceC1435) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4231) := by
    have ha : (tripleCharges (sourceA1435 + difference 2 1) (sourceB1435 + difference 1 2) sourceC1435) = raw22232 := by
      apply Matrix.ext; unfold tripleCharges sourceA1435 sourceB1435 sourceC1435 difference raw22232; decide +kernel
    rw [ha]
    exact (canonical22232 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1435 + difference 2 3) (sourceB1435 + difference 3 2) sourceC1435) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4195) := by
    have ha : (tripleCharges (sourceA1435 + difference 2 3) (sourceB1435 + difference 3 2) sourceC1435) = raw22233 := by
      apply Matrix.ext; unfold tripleCharges sourceA1435 sourceB1435 sourceC1435 difference raw22233; decide +kernel
    rw [ha]
    exact (canonical22233 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1435 + difference 2 4) (sourceB1435 + difference 4 2) sourceC1435) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4266) := by
    have ha : (tripleCharges (sourceA1435 + difference 2 4) (sourceB1435 + difference 4 2) sourceC1435) = raw22234 := by
      apply Matrix.ext; unfold tripleCharges sourceA1435 sourceB1435 sourceC1435 difference raw22234; decide +kernel
    rw [ha]
    exact (canonical22234 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1435 + difference 2 5) (sourceB1435 + difference 5 2) sourceC1435) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4251) := by
    have ha : (tripleCharges (sourceA1435 + difference 2 5) (sourceB1435 + difference 5 2) sourceC1435) = raw22235 := by
      apply Matrix.ext; unfold tripleCharges sourceA1435 sourceB1435 sourceC1435 difference raw22235; decide +kernel
    rw [ha]
    exact (canonical22235 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1435 + difference 3 0) (sourceB1435 + difference 0 3) sourceC1435) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4099) := by
    have ha : (tripleCharges (sourceA1435 + difference 3 0) (sourceB1435 + difference 0 3) sourceC1435) = raw22236 := by
      apply Matrix.ext; unfold tripleCharges sourceA1435 sourceB1435 sourceC1435 difference raw22236; decide +kernel
    rw [ha]
    exact (canonical22236 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1435 + difference 3 1) (sourceB1435 + difference 1 3) sourceC1435) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4231) := by
    have ha : (tripleCharges (sourceA1435 + difference 3 1) (sourceB1435 + difference 1 3) sourceC1435) = raw22237 := by
      apply Matrix.ext; unfold tripleCharges sourceA1435 sourceB1435 sourceC1435 difference raw22237; decide +kernel
    rw [ha]
    exact (canonical22237 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1435 + difference 3 2) (sourceB1435 + difference 2 3) sourceC1435) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4195) := by
    have ha : (tripleCharges (sourceA1435 + difference 3 2) (sourceB1435 + difference 2 3) sourceC1435) = raw22238 := by
      apply Matrix.ext; unfold tripleCharges sourceA1435 sourceB1435 sourceC1435 difference raw22238; decide +kernel
    rw [ha]
    exact (canonical22238 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1435 + difference 3 4) (sourceB1435 + difference 4 3) sourceC1435) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4266) := by
    have ha : (tripleCharges (sourceA1435 + difference 3 4) (sourceB1435 + difference 4 3) sourceC1435) = raw22239 := by
      apply Matrix.ext; unfold tripleCharges sourceA1435 sourceB1435 sourceC1435 difference raw22239; decide +kernel
    rw [ha]
    exact (canonical22239 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1435 + difference 3 5) (sourceB1435 + difference 5 3) sourceC1435) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4251) := by
    have ha : (tripleCharges (sourceA1435 + difference 3 5) (sourceB1435 + difference 5 3) sourceC1435) = raw22240 := by
      apply Matrix.ext; unfold tripleCharges sourceA1435 sourceB1435 sourceC1435 difference raw22240; decide +kernel
    rw [ha]
    exact (canonical22240 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1435 + difference 4 0) (sourceB1435 + difference 0 4) sourceC1435) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4109) := by
    have ha : (tripleCharges (sourceA1435 + difference 4 0) (sourceB1435 + difference 0 4) sourceC1435) = raw22241 := by
      apply Matrix.ext; unfold tripleCharges sourceA1435 sourceB1435 sourceC1435 difference raw22241; decide +kernel
    rw [ha]
    exact (canonical22241 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1435 + difference 4 1) (sourceB1435 + difference 1 4) sourceC1435) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4241) := by
    have ha : (tripleCharges (sourceA1435 + difference 4 1) (sourceB1435 + difference 1 4) sourceC1435) = raw22242 := by
      apply Matrix.ext; unfold tripleCharges sourceA1435 sourceB1435 sourceC1435 difference raw22242; decide +kernel
    rw [ha]
    exact (canonical22242 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1435 + difference 4 2) (sourceB1435 + difference 2 4) sourceC1435) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4203) := by
    have ha : (tripleCharges (sourceA1435 + difference 4 2) (sourceB1435 + difference 2 4) sourceC1435) = raw22243 := by
      apply Matrix.ext; unfold tripleCharges sourceA1435 sourceB1435 sourceC1435 difference raw22243; decide +kernel
    rw [ha]
    exact (canonical22243 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1435 + difference 4 3) (sourceB1435 + difference 3 4) sourceC1435) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4203) := by
    have ha : (tripleCharges (sourceA1435 + difference 4 3) (sourceB1435 + difference 3 4) sourceC1435) = raw22244 := by
      apply Matrix.ext; unfold tripleCharges sourceA1435 sourceB1435 sourceC1435 difference raw22244; decide +kernel
    rw [ha]
    exact (canonical22244 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1435 + difference 4 5) (sourceB1435 + difference 5 4) sourceC1435) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4272) := by
    have ha : (tripleCharges (sourceA1435 + difference 4 5) (sourceB1435 + difference 5 4) sourceC1435) = raw22245 := by
      apply Matrix.ext; unfold tripleCharges sourceA1435 sourceB1435 sourceC1435 difference raw22245; decide +kernel
    rw [ha]
    exact (canonical22245 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1435 + difference 5 0) (sourceB1435 + difference 0 5) sourceC1435) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4103) := by
    have ha : (tripleCharges (sourceA1435 + difference 5 0) (sourceB1435 + difference 0 5) sourceC1435) = raw22246 := by
      apply Matrix.ext; unfold tripleCharges sourceA1435 sourceB1435 sourceC1435 difference raw22246; decide +kernel
    rw [ha]
    exact (canonical22246 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1435 + difference 5 1) (sourceB1435 + difference 1 5) sourceC1435) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4235) := by
    have ha : (tripleCharges (sourceA1435 + difference 5 1) (sourceB1435 + difference 1 5) sourceC1435) = raw22247 := by
      apply Matrix.ext; unfold tripleCharges sourceA1435 sourceB1435 sourceC1435 difference raw22247; decide +kernel
    rw [ha]
    exact (canonical22247 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1435 + difference 5 2) (sourceB1435 + difference 2 5) sourceC1435) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4198) := by
    have ha : (tripleCharges (sourceA1435 + difference 5 2) (sourceB1435 + difference 2 5) sourceC1435) = raw22248 := by
      apply Matrix.ext; unfold tripleCharges sourceA1435 sourceB1435 sourceC1435 difference raw22248; decide +kernel
    rw [ha]
    exact (canonical22248 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1435 + difference 5 3) (sourceB1435 + difference 3 5) sourceC1435) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4198) := by
    have ha : (tripleCharges (sourceA1435 + difference 5 3) (sourceB1435 + difference 3 5) sourceC1435) = raw22249 := by
      apply Matrix.ext; unfold tripleCharges sourceA1435 sourceB1435 sourceC1435 difference raw22249; decide +kernel
    rw [ha]
    exact (canonical22249 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1435 + difference 5 4) (sourceB1435 + difference 4 5) sourceC1435) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4274) := by
    have ha : (tripleCharges (sourceA1435 + difference 5 4) (sourceB1435 + difference 4 5) sourceC1435) = raw22250 := by
      apply Matrix.ext; unfold tripleCharges sourceA1435 sourceB1435 sourceC1435 difference raw22250; decide +kernel
    rw [ha]
    exact (canonical22250 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1435 sourceB1435 sourceC1435
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1435, Integer.Sparse.eval]
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

theorem reindexCheck1231 : Integer.Sparse.reindex keyMap MixedData.row1231 = numericRow1231 := by decide +kernel

theorem numericCheck1231 (x : Master → ℝ) : Integer.Sparse.eval numericRow1231 x =
    (4 : ℝ) * reducedSource1231 x := by
  norm_num [numericRow1231, reducedSource1231, Integer.Sparse.eval, Sparse.eval, nodeValue4070, nodeValue4099, nodeValue4103, nodeValue4109, nodeValue4120, nodeValue4195, nodeValue4198, nodeValue4203, nodeValue4211, nodeValue4231, nodeValue4235, nodeValue4241, nodeValue4251, nodeValue4266, nodeValue4269, nodeValue4272, nodeValue4274, nodeValue4398, nodeValue4454, nodeValue4460, nodeValue4501]
  ring

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

theorem reducedZero1231 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1231 (mixedVector B) = 0 := by
  have h4070 : mixedVector B (Sum.inr 4070) = Sparse.eval nodeValue4070 (mixedVector B) := by
    change mixedMoment B node4070 node4070Labels = _
    exact sound4070 B hB hF
  have h4099 : mixedVector B (Sum.inr 4099) = Sparse.eval nodeValue4099 (mixedVector B) := by
    change mixedMoment B node4099 node4099Labels = _
    exact sound4099 B hB hF
  have h4103 : mixedVector B (Sum.inr 4103) = Sparse.eval nodeValue4103 (mixedVector B) := by
    change mixedMoment B node4103 node4103Labels = _
    exact sound4103 B hB hF
  have h4109 : mixedVector B (Sum.inr 4109) = Sparse.eval nodeValue4109 (mixedVector B) := by
    change mixedMoment B node4109 node4109Labels = _
    exact sound4109 B hB hF
  have h4120 : mixedVector B (Sum.inr 4120) = Sparse.eval nodeValue4120 (mixedVector B) := by
    change mixedMoment B node4120 node4120Labels = _
    exact sound4120 B hB hF
  have h4195 : mixedVector B (Sum.inr 4195) = Sparse.eval nodeValue4195 (mixedVector B) := by
    change mixedMoment B node4195 node4195Labels = _
    exact sound4195 B hB hF
  have h4198 : mixedVector B (Sum.inr 4198) = Sparse.eval nodeValue4198 (mixedVector B) := by
    change mixedMoment B node4198 node4198Labels = _
    exact sound4198 B hB hF
  have h4203 : mixedVector B (Sum.inr 4203) = Sparse.eval nodeValue4203 (mixedVector B) := by
    change mixedMoment B node4203 node4203Labels = _
    exact sound4203 B hB hF
  have h4211 : mixedVector B (Sum.inr 4211) = Sparse.eval nodeValue4211 (mixedVector B) := by
    change mixedMoment B node4211 node4211Labels = _
    exact sound4211 B hB hF
  have h4231 : mixedVector B (Sum.inr 4231) = Sparse.eval nodeValue4231 (mixedVector B) := by
    change mixedMoment B node4231 node4231Labels = _
    exact sound4231 B hB hF
  have h4235 : mixedVector B (Sum.inr 4235) = Sparse.eval nodeValue4235 (mixedVector B) := by
    change mixedMoment B node4235 node4235Labels = _
    exact sound4235 B hB hF
  have h4241 : mixedVector B (Sum.inr 4241) = Sparse.eval nodeValue4241 (mixedVector B) := by
    change mixedMoment B node4241 node4241Labels = _
    exact sound4241 B hB hF
  have h4251 : mixedVector B (Sum.inr 4251) = Sparse.eval nodeValue4251 (mixedVector B) := by
    change mixedMoment B node4251 node4251Labels = _
    exact sound4251 B hB hF
  have h4266 : mixedVector B (Sum.inr 4266) = Sparse.eval nodeValue4266 (mixedVector B) := by
    change mixedMoment B node4266 node4266Labels = _
    exact sound4266 B hB hF
  have h4269 : mixedVector B (Sum.inr 4269) = Sparse.eval nodeValue4269 (mixedVector B) := by
    change mixedMoment B node4269 node4269Labels = _
    exact sound4269 B hB hF
  have h4272 : mixedVector B (Sum.inr 4272) = Sparse.eval nodeValue4272 (mixedVector B) := by
    change mixedMoment B node4272 node4272Labels = _
    exact sound4272 B hB hF
  have h4274 : mixedVector B (Sum.inr 4274) = Sparse.eval nodeValue4274 (mixedVector B) := by
    change mixedMoment B node4274 node4274Labels = _
    exact sound4274 B hB hF
  have h4398 : mixedVector B (Sum.inr 4398) = Sparse.eval nodeValue4398 (mixedVector B) := by
    change mixedMoment B node4398 node4398Labels = _
    exact sound4398 B hB hF
  have h4454 : mixedVector B (Sum.inr 4454) = Sparse.eval nodeValue4454 (mixedVector B) := by
    change mixedMoment B node4454 node4454Labels = _
    exact sound4454 B hB hF
  have h4460 : mixedVector B (Sum.inr 4460) = Sparse.eval nodeValue4460 (mixedVector B) := by
    change mixedMoment B node4460 node4460Labels = _
    exact sound4460 B hB hF
  have h4501 : mixedVector B (Sum.inr 4501) = Sparse.eval nodeValue4501 (mixedVector B) := by
    change mixedMoment B node4501 node4501Labels = _
    exact sound4501 B hB hF
  simpa only [sourceForm1435, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4070, h4099, h4103, h4109, h4120, h4195, h4198, h4203, h4211, h4231, h4235, h4241, h4251, h4266, h4269, h4272, h4274, h4398, h4454, h4460, h4501, reducedSource1231] using sourceEq1435 B hB

theorem rowSound1231_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1231 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1231, numericCheck1231, reducedZero1231 B hB hF, mul_zero]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedSourceBridge.rowSound1231_e_oai := @OAI.MUB6.Certificate.MixedSourceBridge.rowSound1231_e_oai
