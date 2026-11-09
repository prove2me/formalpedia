-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedSourceBridge.rowSound2088_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-08T23:03:54.438774+00:00
-- url     : https://prove2.me/submissions/54831d95-a95a-4faa-bf92-ff8e28912242

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E070
import Definitions.Def_OAIQ106E086
import Definitions.Def_OAIQ106E095
import Definitions.Def_OAIQ106E097
import Definitions.Def_OAIQ106E192
import Definitions.Def_OAIQ106E193
import Definitions.Def_OAIQ106E100
import Definitions.Def_OAIQ106E194
import Definitions.Def_OAIQ106E101
import Definitions.Def_OAIQ106E109
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

theorem canonical2130 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2130 raw2130Labels = mixedMoment B node5105 node5105Labels := by
  calc
    mixedMoment B raw2130 raw2130Labels = mixedMoment B raw2130step0 raw2130step0Labels := by
      have ha : raw2130step0 = (fun i j => raw2130 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2130step0 raw2130; decide +kernel
      have hl : raw2130step0Labels = raw2130Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2130 raw2130Labels permutation32 permutation4
    mixedMoment B raw2130step0 raw2130step0Labels = mixedMoment B raw2130step1 raw2130step1Labels := by
      have ha : raw2130step1 = raw2130step0 := by apply Matrix.ext; unfold raw2130step1 raw2130step0; decide +kernel
      have hl : raw2130step0Labels = labelEmbedding7 ∘ raw2130step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2130step0 raw2130step0Labels raw2130step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5105 node5105Labels := by rfl

theorem canonical2131 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2131 raw2131Labels = mixedMoment B node2515 node2515Labels := by
  calc
    mixedMoment B raw2131 raw2131Labels = mixedMoment B raw2131step0 raw2131step0Labels := by
      have ha : raw2131step0 = (fun i j => raw2131 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2131step0 raw2131; decide +kernel
      have hl : raw2131step0Labels = raw2131Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2131 raw2131Labels permutation32 permutation4
    _ = mixedMoment B node2515 node2515Labels := by rfl

theorem canonical2132 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2132 raw2132Labels = mixedMoment B node3479 node3479Labels := by
  calc
    mixedMoment B raw2132 raw2132Labels = mixedMoment B raw2132step0 raw2132step0Labels := by
      have ha : raw2132step0 = (fun i j => raw2132 (permutation36 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2132step0 raw2132; decide +kernel
      have hl : raw2132step0Labels = raw2132Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2132 raw2132Labels permutation36 permutation6
    mixedMoment B raw2132step0 raw2132step0Labels = mixedMoment B raw2132step1 raw2132step1Labels := by
      have ha : raw2132step1 = -raw2132step0 := by apply Matrix.ext; change ∀ i j, raw2132step1 i j = -(raw2132step0 i j); unfold raw2132step1 raw2132step0; decide +kernel
      have hl : raw2132step1Labels = raw2132step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2132step1 raw2132step1Labels = mixedMoment B raw2132step2 raw2132step2Labels := by
      have ha : raw2132step2 = raw2132step1 := by apply Matrix.ext; unfold raw2132step2 raw2132step1; decide +kernel
      have hl : raw2132step1Labels = labelEmbedding1 ∘ raw2132step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2132step1 raw2132step1Labels raw2132step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3479 node3479Labels := by rfl

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

theorem canonical2400 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2400 raw2400Labels = mixedMoment B node5355 node5355Labels := by
  calc
    mixedMoment B raw2400 raw2400Labels = mixedMoment B raw2400step0 raw2400step0Labels := by
      have ha : raw2400step0 = (fun i j => raw2400 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2400step0 raw2400; decide +kernel
      have hl : raw2400step0Labels = raw2400Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2400 raw2400Labels permutation32 permutation4
    mixedMoment B raw2400step0 raw2400step0Labels = mixedMoment B raw2400step1 raw2400step1Labels := by
      have ha : raw2400step1 = raw2400step0 := by apply Matrix.ext; unfold raw2400step1 raw2400step0; decide +kernel
      have hl : raw2400step0Labels = labelEmbedding7 ∘ raw2400step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2400step0 raw2400step0Labels raw2400step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5355 node5355Labels := by rfl

theorem canonical2401 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2401 raw2401Labels = mixedMoment B node3693 node3693Labels := by
  calc
    mixedMoment B raw2401 raw2401Labels = mixedMoment B raw2401step0 raw2401step0Labels := by
      have ha : raw2401step0 = (fun i j => raw2401 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2401step0 raw2401; decide +kernel
      have hl : raw2401step0Labels = raw2401Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2401 raw2401Labels permutation32 permutation4
    _ = mixedMoment B node3693 node3693Labels := by rfl

theorem canonical2402 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2402 raw2402Labels = mixedMoment B node3770 node3770Labels := by
  calc
    mixedMoment B raw2402 raw2402Labels = mixedMoment B raw2402step0 raw2402step0Labels := by
      have ha : raw2402step0 = (fun i j => raw2402 (permutation34 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2402step0 raw2402; decide +kernel
      have hl : raw2402step0Labels = raw2402Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2402 raw2402Labels permutation34 permutation6
    mixedMoment B raw2402step0 raw2402step0Labels = mixedMoment B raw2402step1 raw2402step1Labels := by
      have ha : raw2402step1 = -raw2402step0 := by apply Matrix.ext; change ∀ i j, raw2402step1 i j = -(raw2402step0 i j); unfold raw2402step1 raw2402step0; decide +kernel
      have hl : raw2402step1Labels = raw2402step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2402step1 raw2402step1Labels = mixedMoment B raw2402step2 raw2402step2Labels := by
      have ha : raw2402step2 = raw2402step1 := by apply Matrix.ext; unfold raw2402step2 raw2402step1; decide +kernel
      have hl : raw2402step1Labels = labelEmbedding1 ∘ raw2402step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2402step1 raw2402step1Labels raw2402step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3770 node3770Labels := by rfl

theorem canonical2412 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2412 raw2412Labels = mixedMoment B node5365 node5365Labels := by
  calc
    mixedMoment B raw2412 raw2412Labels = mixedMoment B raw2412step0 raw2412step0Labels := by
      have ha : raw2412step0 = (fun i j => raw2412 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2412step0 raw2412; decide +kernel
      have hl : raw2412step0Labels = raw2412Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2412 raw2412Labels permutation152 permutation4
    mixedMoment B raw2412step0 raw2412step0Labels = mixedMoment B raw2412step1 raw2412step1Labels := by
      have ha : raw2412step1 = raw2412step0 := by apply Matrix.ext; unfold raw2412step1 raw2412step0; decide +kernel
      have hl : raw2412step0Labels = labelEmbedding7 ∘ raw2412step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2412step0 raw2412step0Labels raw2412step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5365 node5365Labels := by rfl

theorem canonical2413 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2413 raw2413Labels = mixedMoment B node3703 node3703Labels := by
  calc
    mixedMoment B raw2413 raw2413Labels = mixedMoment B raw2413step0 raw2413step0Labels := by
      have ha : raw2413step0 = (fun i j => raw2413 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2413step0 raw2413; decide +kernel
      have hl : raw2413step0Labels = raw2413Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2413 raw2413Labels permutation152 permutation4
    _ = mixedMoment B node3703 node3703Labels := by rfl

theorem canonical2414 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2414 raw2414Labels = mixedMoment B node3758 node3758Labels := by
  calc
    mixedMoment B raw2414 raw2414Labels = mixedMoment B raw2414step0 raw2414step0Labels := by
      have ha : raw2414step0 = (fun i j => raw2414 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2414step0 raw2414; decide +kernel
      have hl : raw2414step0Labels = raw2414Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2414 raw2414Labels permutation152 permutation6
    mixedMoment B raw2414step0 raw2414step0Labels = mixedMoment B raw2414step1 raw2414step1Labels := by
      have ha : raw2414step1 = -raw2414step0 := by apply Matrix.ext; change ∀ i j, raw2414step1 i j = -(raw2414step0 i j); unfold raw2414step1 raw2414step0; decide +kernel
      have hl : raw2414step1Labels = raw2414step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2414step1 raw2414step1Labels = mixedMoment B raw2414step2 raw2414step2Labels := by
      have ha : raw2414step2 = raw2414step1 := by apply Matrix.ext; unfold raw2414step2 raw2414step1; decide +kernel
      have hl : raw2414step1Labels = labelEmbedding1 ∘ raw2414step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2414step1 raw2414step1Labels raw2414step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3758 node3758Labels := by rfl

theorem canonical2415 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2415 raw2415Labels = mixedMoment B node5368 node5368Labels := by
  calc
    mixedMoment B raw2415 raw2415Labels = mixedMoment B raw2415step0 raw2415step0Labels := by
      have ha : raw2415step0 = (fun i j => raw2415 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2415step0 raw2415; decide +kernel
      have hl : raw2415step0Labels = raw2415Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2415 raw2415Labels permutation32 permutation4
    mixedMoment B raw2415step0 raw2415step0Labels = mixedMoment B raw2415step1 raw2415step1Labels := by
      have ha : raw2415step1 = raw2415step0 := by apply Matrix.ext; unfold raw2415step1 raw2415step0; decide +kernel
      have hl : raw2415step0Labels = labelEmbedding7 ∘ raw2415step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2415step0 raw2415step0Labels raw2415step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5368 node5368Labels := by rfl

theorem canonical2416 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2416 raw2416Labels = mixedMoment B node3705 node3705Labels := by
  calc
    mixedMoment B raw2416 raw2416Labels = mixedMoment B raw2416step0 raw2416step0Labels := by
      have ha : raw2416step0 = (fun i j => raw2416 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2416step0 raw2416; decide +kernel
      have hl : raw2416step0Labels = raw2416Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2416 raw2416Labels permutation32 permutation4
    _ = mixedMoment B node3705 node3705Labels := by rfl

theorem canonical2417 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2417 raw2417Labels = mixedMoment B node3767 node3767Labels := by
  calc
    mixedMoment B raw2417 raw2417Labels = mixedMoment B raw2417step0 raw2417step0Labels := by
      have ha : raw2417step0 = (fun i j => raw2417 (permutation33 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2417step0 raw2417; decide +kernel
      have hl : raw2417step0Labels = raw2417Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2417 raw2417Labels permutation33 permutation6
    mixedMoment B raw2417step0 raw2417step0Labels = mixedMoment B raw2417step1 raw2417step1Labels := by
      have ha : raw2417step1 = -raw2417step0 := by apply Matrix.ext; change ∀ i j, raw2417step1 i j = -(raw2417step0 i j); unfold raw2417step1 raw2417step0; decide +kernel
      have hl : raw2417step1Labels = raw2417step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2417step1 raw2417step1Labels = mixedMoment B raw2417step2 raw2417step2Labels := by
      have ha : raw2417step2 = raw2417step1 := by apply Matrix.ext; unfold raw2417step2 raw2417step1; decide +kernel
      have hl : raw2417step1Labels = labelEmbedding1 ∘ raw2417step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2417step1 raw2417step1Labels raw2417step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3767 node3767Labels := by rfl

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

theorem canonical2493 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2493 raw2493Labels = mixedMoment B node5412 node5412Labels := by
  calc
    mixedMoment B raw2493 raw2493Labels = mixedMoment B raw2493step0 raw2493step0Labels := by
      have ha : raw2493step0 = (fun i j => raw2493 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2493step0 raw2493; decide +kernel
      have hl : raw2493step0Labels = raw2493Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2493 raw2493Labels permutation32 permutation4
    mixedMoment B raw2493step0 raw2493step0Labels = mixedMoment B raw2493step1 raw2493step1Labels := by
      have ha : raw2493step1 = raw2493step0 := by apply Matrix.ext; unfold raw2493step1 raw2493step0; decide +kernel
      have hl : raw2493step0Labels = labelEmbedding7 ∘ raw2493step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2493step0 raw2493step0Labels raw2493step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5412 node5412Labels := by rfl

theorem canonical2494 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2494 raw2494Labels = mixedMoment B node3814 node3814Labels := by
  calc
    mixedMoment B raw2494 raw2494Labels = mixedMoment B raw2494step0 raw2494step0Labels := by
      have ha : raw2494step0 = (fun i j => raw2494 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2494step0 raw2494; decide +kernel
      have hl : raw2494step0Labels = raw2494Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2494 raw2494Labels permutation32 permutation4
    _ = mixedMoment B node3814 node3814Labels := by rfl

theorem canonical2495 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2495 raw2495Labels = mixedMoment B node3814 node3814Labels := by
  calc
    mixedMoment B raw2495 raw2495Labels = mixedMoment B raw2495step0 raw2495step0Labels := by
      have ha : raw2495step0 = (fun i j => raw2495 (permutation37 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2495step0 raw2495; decide +kernel
      have hl : raw2495step0Labels = raw2495Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2495 raw2495Labels permutation37 permutation6
    mixedMoment B raw2495step0 raw2495step0Labels = mixedMoment B raw2495step1 raw2495step1Labels := by
      have ha : raw2495step1 = -raw2495step0 := by apply Matrix.ext; change ∀ i j, raw2495step1 i j = -(raw2495step0 i j); unfold raw2495step1 raw2495step0; decide +kernel
      have hl : raw2495step1Labels = raw2495step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2495step1 raw2495step1Labels = mixedMoment B raw2495step2 raw2495step2Labels := by
      have ha : raw2495step2 = raw2495step1 := by apply Matrix.ext; unfold raw2495step2 raw2495step1; decide +kernel
      have hl : raw2495step1Labels = labelEmbedding1 ∘ raw2495step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2495step1 raw2495step1Labels raw2495step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3814 node3814Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical20
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical2589 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2589 raw2589Labels = mixedMoment B node5473 node5473Labels := by
  calc
    mixedMoment B raw2589 raw2589Labels = mixedMoment B raw2589step0 raw2589step0Labels := by
      have ha : raw2589step0 = (fun i j => raw2589 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2589step0 raw2589; decide +kernel
      have hl : raw2589step0Labels = raw2589Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2589 raw2589Labels permutation32 permutation4
    mixedMoment B raw2589step0 raw2589step0Labels = mixedMoment B raw2589step1 raw2589step1Labels := by
      have ha : raw2589step1 = raw2589step0 := by apply Matrix.ext; unfold raw2589step1 raw2589step0; decide +kernel
      have hl : raw2589step0Labels = labelEmbedding7 ∘ raw2589step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2589step0 raw2589step0Labels raw2589step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5473 node5473Labels := by rfl

theorem canonical2590 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2590 raw2590Labels = mixedMoment B node3958 node3958Labels := by
  calc
    mixedMoment B raw2590 raw2590Labels = mixedMoment B raw2590step0 raw2590step0Labels := by
      have ha : raw2590step0 = (fun i j => raw2590 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2590step0 raw2590; decide +kernel
      have hl : raw2590step0Labels = raw2590Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2590 raw2590Labels permutation32 permutation4
    _ = mixedMoment B node3958 node3958Labels := by rfl

theorem canonical2591 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2591 raw2591Labels = mixedMoment B node3961 node3961Labels := by
  calc
    mixedMoment B raw2591 raw2591Labels = mixedMoment B raw2591step0 raw2591step0Labels := by
      have ha : raw2591step0 = (fun i j => raw2591 (permutation56 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2591step0 raw2591; decide +kernel
      have hl : raw2591step0Labels = raw2591Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2591 raw2591Labels permutation56 permutation6
    mixedMoment B raw2591step0 raw2591step0Labels = mixedMoment B raw2591step1 raw2591step1Labels := by
      have ha : raw2591step1 = -raw2591step0 := by apply Matrix.ext; change ∀ i j, raw2591step1 i j = -(raw2591step0 i j); unfold raw2591step1 raw2591step0; decide +kernel
      have hl : raw2591step1Labels = raw2591step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2591step1 raw2591step1Labels = mixedMoment B raw2591step2 raw2591step2Labels := by
      have ha : raw2591step2 = raw2591step1 := by apply Matrix.ext; unfold raw2591step2 raw2591step1; decide +kernel
      have hl : raw2591step1Labels = labelEmbedding1 ∘ raw2591step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2591step1 raw2591step1Labels raw2591step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3961 node3961Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical285
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical36587 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36587 raw36587Labels = mixedMoment B node5105 node5105Labels := by
  calc
    mixedMoment B raw36587 raw36587Labels = mixedMoment B raw36587step0 raw36587step0Labels := by
      have hz : ∀ j, raw36587 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36587step0 = (fun i j => raw36587 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36587step0 raw36587; decide +kernel
      have hl : raw36587step0Labels = raw36587Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36587 raw36587Labels permutation346 hz
    mixedMoment B raw36587step0 raw36587step0Labels = mixedMoment B raw36587step1 raw36587step1Labels := by
      have ha : raw36587step1 = (fun i j => raw36587step0 (permutation58 i) (permutation2 j)) := by apply Matrix.ext; unfold raw36587step1 raw36587step0; decide +kernel
      have hl : raw36587step1Labels = raw36587step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36587step0 raw36587step0Labels permutation58 permutation2
    _ = mixedMoment B node5105 node5105Labels := by rfl

theorem canonical36588 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36588 raw36588Labels = mixedMoment B node5397 node5397Labels := by
  calc
    mixedMoment B raw36588 raw36588Labels = mixedMoment B raw36588step0 raw36588step0Labels := by
      have ha : raw36588step0 = (fun i j => raw36588 (permutation267 i) (permutation2 j)) := by apply Matrix.ext; unfold raw36588step0 raw36588; decide +kernel
      have hl : raw36588step0Labels = raw36588Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36588 raw36588Labels permutation267 permutation2
    _ = mixedMoment B node5397 node5397Labels := by rfl

theorem canonical36589 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36589 raw36589Labels = mixedMoment B node5412 node5412Labels := by
  calc
    mixedMoment B raw36589 raw36589Labels = mixedMoment B raw36589step0 raw36589step0Labels := by
      have hz : ∀ j, raw36589 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36589step0 = (fun i j => raw36589 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36589step0 raw36589; decide +kernel
      have hl : raw36589step0Labels = raw36589Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36589 raw36589Labels permutation346 hz
    mixedMoment B raw36589step0 raw36589step0Labels = mixedMoment B raw36589step1 raw36589step1Labels := by
      have ha : raw36589step1 = (fun i j => raw36589step0 (permutation56 i) (permutation2 j)) := by apply Matrix.ext; unfold raw36589step1 raw36589step0; decide +kernel
      have hl : raw36589step1Labels = raw36589step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36589step0 raw36589step0Labels permutation56 permutation2
    _ = mixedMoment B node5412 node5412Labels := by rfl

theorem canonical36590 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36590 raw36590Labels = mixedMoment B node5411 node5411Labels := by
  calc
    mixedMoment B raw36590 raw36590Labels = mixedMoment B raw36590step0 raw36590step0Labels := by
      have hz : ∀ j, raw36590 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36590step0 = (fun i j => raw36590 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36590step0 raw36590; decide +kernel
      have hl : raw36590step0Labels = raw36590Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36590 raw36590Labels permutation346 hz
    mixedMoment B raw36590step0 raw36590step0Labels = mixedMoment B raw36590step1 raw36590step1Labels := by
      have ha : raw36590step1 = (fun i j => raw36590step0 (permutation58 i) (permutation2 j)) := by apply Matrix.ext; unfold raw36590step1 raw36590step0; decide +kernel
      have hl : raw36590step1Labels = raw36590step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36590step0 raw36590step0Labels permutation58 permutation2
    _ = mixedMoment B node5411 node5411Labels := by rfl

theorem canonical36591 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36591 raw36591Labels = mixedMoment B node5410 node5410Labels := by
  calc
    mixedMoment B raw36591 raw36591Labels = mixedMoment B raw36591step0 raw36591step0Labels := by
      have hz : ∀ j, raw36591 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36591step0 = (fun i j => raw36591 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36591step0 raw36591; decide +kernel
      have hl : raw36591step0Labels = raw36591Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36591 raw36591Labels permutation346 hz
    mixedMoment B raw36591step0 raw36591step0Labels = mixedMoment B raw36591step1 raw36591step1Labels := by
      have ha : raw36591step1 = (fun i j => raw36591step0 (permutation61 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36591step1 raw36591step0; decide +kernel
      have hl : raw36591step1Labels = raw36591step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36591step0 raw36591step0Labels permutation61 permutation7
    mixedMoment B raw36591step1 raw36591step1Labels = mixedMoment B raw36591step2 raw36591step2Labels := by
      have ha : raw36591step2 = -raw36591step1 := by apply Matrix.ext; change ∀ i j, raw36591step2 i j = -(raw36591step1 i j); unfold raw36591step2 raw36591step1; decide +kernel
      have hl : raw36591step2Labels = raw36591step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36591step2 raw36591step2Labels = mixedMoment B raw36591step3 raw36591step3Labels := by
      have ha : raw36591step3 = raw36591step2 := by apply Matrix.ext; unfold raw36591step3 raw36591step2; decide +kernel
      have hl : raw36591step2Labels = labelEmbedding10 ∘ raw36591step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36591step2 raw36591step2Labels raw36591step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5410 node5410Labels := by rfl

theorem canonical36592 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36592 raw36592Labels = mixedMoment B node5198 node5198Labels := by
  calc
    mixedMoment B raw36592 raw36592Labels = mixedMoment B raw36592step0 raw36592step0Labels := by
      have hz : ∀ j, raw36592 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36592step0 = (fun i j => raw36592 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36592step0 raw36592; decide +kernel
      have hl : raw36592step0Labels = raw36592Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36592 raw36592Labels permutation346 hz
    mixedMoment B raw36592step0 raw36592step0Labels = mixedMoment B raw36592step1 raw36592step1Labels := by
      have ha : raw36592step1 = (fun i j => raw36592step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36592step1 raw36592step0; decide +kernel
      have hl : raw36592step1Labels = raw36592step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36592step0 raw36592step0Labels permutation32 permutation3
    mixedMoment B raw36592step1 raw36592step1Labels = mixedMoment B raw36592step2 raw36592step2Labels := by
      have ha : raw36592step2 = raw36592step1 := by apply Matrix.ext; unfold raw36592step2 raw36592step1; decide +kernel
      have hl : raw36592step1Labels = labelEmbedding6 ∘ raw36592step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36592step1 raw36592step1Labels raw36592step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5198 node5198Labels := by rfl

theorem canonical36593 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36593 raw36593Labels = mixedMoment B node5421 node5421Labels := by
  calc
    mixedMoment B raw36593 raw36593Labels = mixedMoment B raw36593step0 raw36593step0Labels := by
      have ha : raw36593step0 = (fun i j => raw36593 (permutation686 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36593step0 raw36593; decide +kernel
      have hl : raw36593step0Labels = raw36593Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36593 raw36593Labels permutation686 permutation3
    mixedMoment B raw36593step0 raw36593step0Labels = mixedMoment B raw36593step1 raw36593step1Labels := by
      have ha : raw36593step1 = -raw36593step0 := by apply Matrix.ext; change ∀ i j, raw36593step1 i j = -(raw36593step0 i j); unfold raw36593step1 raw36593step0; decide +kernel
      have hl : raw36593step1Labels = raw36593step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36593step1 raw36593step1Labels = mixedMoment B raw36593step2 raw36593step2Labels := by
      have ha : raw36593step2 = raw36593step1 := by apply Matrix.ext; unfold raw36593step2 raw36593step1; decide +kernel
      have hl : raw36593step1Labels = labelEmbedding6 ∘ raw36593step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36593step1 raw36593step1Labels raw36593step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5421 node5421Labels := by rfl

theorem canonical36594 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36594 raw36594Labels = mixedMoment B node5436 node5436Labels := by
  calc
    mixedMoment B raw36594 raw36594Labels = mixedMoment B raw36594step0 raw36594step0Labels := by
      have hz : ∀ j, raw36594 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36594step0 = (fun i j => raw36594 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36594step0 raw36594; decide +kernel
      have hl : raw36594step0Labels = raw36594Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36594 raw36594Labels permutation346 hz
    mixedMoment B raw36594step0 raw36594step0Labels = mixedMoment B raw36594step1 raw36594step1Labels := by
      have ha : raw36594step1 = (fun i j => raw36594step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36594step1 raw36594step0; decide +kernel
      have hl : raw36594step1Labels = raw36594step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36594step0 raw36594step0Labels permutation151 permutation3
    mixedMoment B raw36594step1 raw36594step1Labels = mixedMoment B raw36594step2 raw36594step2Labels := by
      have ha : raw36594step2 = -raw36594step1 := by apply Matrix.ext; change ∀ i j, raw36594step2 i j = -(raw36594step1 i j); unfold raw36594step2 raw36594step1; decide +kernel
      have hl : raw36594step2Labels = raw36594step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36594step2 raw36594step2Labels = mixedMoment B raw36594step3 raw36594step3Labels := by
      have ha : raw36594step3 = raw36594step2 := by apply Matrix.ext; unfold raw36594step3 raw36594step2; decide +kernel
      have hl : raw36594step2Labels = labelEmbedding6 ∘ raw36594step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36594step2 raw36594step2Labels raw36594step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5436 node5436Labels := by rfl

theorem canonical36595 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36595 raw36595Labels = mixedMoment B node5446 node5446Labels := by
  calc
    mixedMoment B raw36595 raw36595Labels = mixedMoment B raw36595step0 raw36595step0Labels := by
      have hz : ∀ j, raw36595 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36595step0 = (fun i j => raw36595 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36595step0 raw36595; decide +kernel
      have hl : raw36595step0Labels = raw36595Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36595 raw36595Labels permutation346 hz
    mixedMoment B raw36595step0 raw36595step0Labels = mixedMoment B raw36595step1 raw36595step1Labels := by
      have ha : raw36595step1 = (fun i j => raw36595step0 (permutation145 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36595step1 raw36595step0; decide +kernel
      have hl : raw36595step1Labels = raw36595step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36595step0 raw36595step0Labels permutation145 permutation3
    mixedMoment B raw36595step1 raw36595step1Labels = mixedMoment B raw36595step2 raw36595step2Labels := by
      have ha : raw36595step2 = -raw36595step1 := by apply Matrix.ext; change ∀ i j, raw36595step2 i j = -(raw36595step1 i j); unfold raw36595step2 raw36595step1; decide +kernel
      have hl : raw36595step2Labels = raw36595step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36595step2 raw36595step2Labels = mixedMoment B raw36595step3 raw36595step3Labels := by
      have ha : raw36595step3 = raw36595step2 := by apply Matrix.ext; unfold raw36595step3 raw36595step2; decide +kernel
      have hl : raw36595step2Labels = labelEmbedding6 ∘ raw36595step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36595step2 raw36595step2Labels raw36595step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5446 node5446Labels := by rfl

theorem canonical36596 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36596 raw36596Labels = mixedMoment B node5473 node5473Labels := by
  calc
    mixedMoment B raw36596 raw36596Labels = mixedMoment B raw36596step0 raw36596step0Labels := by
      have hz : ∀ j, raw36596 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36596step0 = (fun i j => raw36596 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36596step0 raw36596; decide +kernel
      have hl : raw36596step0Labels = raw36596Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36596 raw36596Labels permutation346 hz
    mixedMoment B raw36596step0 raw36596step0Labels = mixedMoment B raw36596step1 raw36596step1Labels := by
      have ha : raw36596step1 = (fun i j => raw36596step0 (permutation61 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36596step1 raw36596step0; decide +kernel
      have hl : raw36596step1Labels = raw36596step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36596step0 raw36596step0Labels permutation61 permutation7
    mixedMoment B raw36596step1 raw36596step1Labels = mixedMoment B raw36596step2 raw36596step2Labels := by
      have ha : raw36596step2 = -raw36596step1 := by apply Matrix.ext; change ∀ i j, raw36596step2 i j = -(raw36596step1 i j); unfold raw36596step2 raw36596step1; decide +kernel
      have hl : raw36596step2Labels = raw36596step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36596step2 raw36596step2Labels = mixedMoment B raw36596step3 raw36596step3Labels := by
      have ha : raw36596step3 = raw36596step2 := by apply Matrix.ext; unfold raw36596step3 raw36596step2; decide +kernel
      have hl : raw36596step2Labels = labelEmbedding10 ∘ raw36596step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36596step2 raw36596step2Labels raw36596step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5473 node5473Labels := by rfl

theorem canonical36597 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36597 raw36597Labels = mixedMoment B node4963 node4963Labels := by
  calc
    mixedMoment B raw36597 raw36597Labels = mixedMoment B raw36597step0 raw36597step0Labels := by
      have ha : raw36597step0 = (fun i j => raw36597 (permutation160 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36597step0 raw36597; decide +kernel
      have hl : raw36597step0Labels = raw36597Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36597 raw36597Labels permutation160 permutation3
    mixedMoment B raw36597step0 raw36597step0Labels = mixedMoment B raw36597step1 raw36597step1Labels := by
      have ha : raw36597step1 = raw36597step0 := by apply Matrix.ext; unfold raw36597step1 raw36597step0; decide +kernel
      have hl : raw36597step0Labels = labelEmbedding6 ∘ raw36597step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36597step0 raw36597step0Labels raw36597step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4963 node4963Labels := by rfl

theorem canonical36598 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36598 raw36598Labels = mixedMoment B node4942 node4942Labels := by
  calc
    mixedMoment B raw36598 raw36598Labels = mixedMoment B raw36598step0 raw36598step0Labels := by
      have ha : raw36598step0 = (fun i j => raw36598 (permutation267 i) (permutation2 j)) := by apply Matrix.ext; unfold raw36598step0 raw36598; decide +kernel
      have hl : raw36598step0Labels = raw36598Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36598 raw36598Labels permutation267 permutation2
    _ = mixedMoment B node4942 node4942Labels := by rfl

theorem canonical36599 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36599 raw36599Labels = mixedMoment B node5360 node5360Labels := by
  calc
    mixedMoment B raw36599 raw36599Labels = mixedMoment B raw36599step0 raw36599step0Labels := by
      have ha : raw36599step0 = (fun i j => raw36599 (permutation271 i) (permutation2 j)) := by apply Matrix.ext; unfold raw36599step0 raw36599; decide +kernel
      have hl : raw36599step0Labels = raw36599Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36599 raw36599Labels permutation271 permutation2
    _ = mixedMoment B node5360 node5360Labels := by rfl

theorem canonical36600 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36600 raw36600Labels = mixedMoment B node5353 node5353Labels := by
  calc
    mixedMoment B raw36600 raw36600Labels = mixedMoment B raw36600step0 raw36600step0Labels := by
      have ha : raw36600step0 = (fun i j => raw36600 (permutation277 i) (permutation2 j)) := by apply Matrix.ext; unfold raw36600step0 raw36600; decide +kernel
      have hl : raw36600step0Labels = raw36600Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36600 raw36600Labels permutation277 permutation2
    _ = mixedMoment B node5353 node5353Labels := by rfl

theorem canonical36601 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36601 raw36601Labels = mixedMoment B node5365 node5365Labels := by
  calc
    mixedMoment B raw36601 raw36601Labels = mixedMoment B raw36601step0 raw36601step0Labels := by
      have ha : raw36601step0 = (fun i j => raw36601 (permutation270 i) (permutation2 j)) := by apply Matrix.ext; unfold raw36601step0 raw36601; decide +kernel
      have hl : raw36601step0Labels = raw36601Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36601 raw36601Labels permutation270 permutation2
    _ = mixedMoment B node5365 node5365Labels := by rfl

theorem canonical36602 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36602 raw36602Labels = mixedMoment B node4973 node4973Labels := by
  calc
    mixedMoment B raw36602 raw36602Labels = mixedMoment B raw36602step0 raw36602step0Labels := by
      have hz : ∀ j, raw36602 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36602step0 = (fun i j => raw36602 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36602step0 raw36602; decide +kernel
      have hl : raw36602step0Labels = raw36602Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36602 raw36602Labels permutation346 hz
    mixedMoment B raw36602step0 raw36602step0Labels = mixedMoment B raw36602step1 raw36602step1Labels := by
      have ha : raw36602step1 = (fun i j => raw36602step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36602step1 raw36602step0; decide +kernel
      have hl : raw36602step1Labels = raw36602step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36602step0 raw36602step0Labels permutation34 permutation3
    mixedMoment B raw36602step1 raw36602step1Labels = mixedMoment B raw36602step2 raw36602step2Labels := by
      have ha : raw36602step2 = raw36602step1 := by apply Matrix.ext; unfold raw36602step2 raw36602step1; decide +kernel
      have hl : raw36602step1Labels = labelEmbedding6 ∘ raw36602step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36602step1 raw36602step1Labels raw36602step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4973 node4973Labels := by rfl

theorem canonical36603 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36603 raw36603Labels = mixedMoment B node4949 node4949Labels := by
  calc
    mixedMoment B raw36603 raw36603Labels = mixedMoment B raw36603step0 raw36603step0Labels := by
      have hz : ∀ j, raw36603 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36603step0 = (fun i j => raw36603 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36603step0 raw36603; decide +kernel
      have hl : raw36603step0Labels = raw36603Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36603 raw36603Labels permutation346 hz
    mixedMoment B raw36603step0 raw36603step0Labels = mixedMoment B raw36603step1 raw36603step1Labels := by
      have ha : raw36603step1 = (fun i j => raw36603step0 (permutation59 i) (permutation2 j)) := by apply Matrix.ext; unfold raw36603step1 raw36603step0; decide +kernel
      have hl : raw36603step1Labels = raw36603step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36603step0 raw36603step0Labels permutation59 permutation2
    _ = mixedMoment B node4949 node4949Labels := by rfl

theorem canonical36604 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36604 raw36604Labels = mixedMoment B node5336 node5336Labels := by
  calc
    mixedMoment B raw36604 raw36604Labels = mixedMoment B raw36604step0 raw36604step0Labels := by
      have ha : raw36604step0 = (fun i j => raw36604 (permutation268 i) (permutation2 j)) := by apply Matrix.ext; unfold raw36604step0 raw36604; decide +kernel
      have hl : raw36604step0Labels = raw36604Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36604 raw36604Labels permutation268 permutation2
    _ = mixedMoment B node5336 node5336Labels := by rfl

theorem canonical36605 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36605 raw36605Labels = mixedMoment B node5355 node5355Labels := by
  calc
    mixedMoment B raw36605 raw36605Labels = mixedMoment B raw36605step0 raw36605step0Labels := by
      have hz : ∀ j, raw36605 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36605step0 = (fun i j => raw36605 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36605step0 raw36605; decide +kernel
      have hl : raw36605step0Labels = raw36605Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36605 raw36605Labels permutation346 hz
    mixedMoment B raw36605step0 raw36605step0Labels = mixedMoment B raw36605step1 raw36605step1Labels := by
      have ha : raw36605step1 = (fun i j => raw36605step0 (permutation59 i) (permutation2 j)) := by apply Matrix.ext; unfold raw36605step1 raw36605step0; decide +kernel
      have hl : raw36605step1Labels = raw36605step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36605step0 raw36605step0Labels permutation59 permutation2
    _ = mixedMoment B node5355 node5355Labels := by rfl

theorem canonical36606 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36606 raw36606Labels = mixedMoment B node5367 node5367Labels := by
  calc
    mixedMoment B raw36606 raw36606Labels = mixedMoment B raw36606step0 raw36606step0Labels := by
      have hz : ∀ j, raw36606 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36606step0 = (fun i j => raw36606 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36606step0 raw36606; decide +kernel
      have hl : raw36606step0Labels = raw36606Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36606 raw36606Labels permutation346 hz
    mixedMoment B raw36606step0 raw36606step0Labels = mixedMoment B raw36606step1 raw36606step1Labels := by
      have ha : raw36606step1 = (fun i j => raw36606step0 (permutation61 i) (permutation2 j)) := by apply Matrix.ext; unfold raw36606step1 raw36606step0; decide +kernel
      have hl : raw36606step1Labels = raw36606step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36606step0 raw36606step0Labels permutation61 permutation2
    _ = mixedMoment B node5367 node5367Labels := by rfl

theorem canonical36607 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36607 raw36607Labels = mixedMoment B node4966 node4966Labels := by
  calc
    mixedMoment B raw36607 raw36607Labels = mixedMoment B raw36607step0 raw36607step0Labels := by
      have hz : ∀ j, raw36607 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36607step0 = (fun i j => raw36607 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36607step0 raw36607; decide +kernel
      have hl : raw36607step0Labels = raw36607Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36607 raw36607Labels permutation346 hz
    mixedMoment B raw36607step0 raw36607step0Labels = mixedMoment B raw36607step1 raw36607step1Labels := by
      have ha : raw36607step1 = (fun i j => raw36607step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36607step1 raw36607step0; decide +kernel
      have hl : raw36607step1Labels = raw36607step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36607step0 raw36607step0Labels permutation32 permutation3
    mixedMoment B raw36607step1 raw36607step1Labels = mixedMoment B raw36607step2 raw36607step2Labels := by
      have ha : raw36607step2 = raw36607step1 := by apply Matrix.ext; unfold raw36607step2 raw36607step1; decide +kernel
      have hl : raw36607step1Labels = labelEmbedding6 ∘ raw36607step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36607step1 raw36607step1Labels raw36607step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4966 node4966Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical286
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical36608 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36608 raw36608Labels = mixedMoment B node4951 node4951Labels := by
  calc
    mixedMoment B raw36608 raw36608Labels = mixedMoment B raw36608step0 raw36608step0Labels := by
      have hz : ∀ j, raw36608 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36608step0 = (fun i j => raw36608 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36608step0 raw36608; decide +kernel
      have hl : raw36608step0Labels = raw36608Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36608 raw36608Labels permutation346 hz
    mixedMoment B raw36608step0 raw36608step0Labels = mixedMoment B raw36608step1 raw36608step1Labels := by
      have ha : raw36608step1 = (fun i j => raw36608step0 (permutation57 i) (permutation2 j)) := by apply Matrix.ext; unfold raw36608step1 raw36608step0; decide +kernel
      have hl : raw36608step1Labels = raw36608step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36608step0 raw36608step0Labels permutation57 permutation2
    _ = mixedMoment B node4951 node4951Labels := by rfl

theorem canonical36609 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36609 raw36609Labels = mixedMoment B node5338 node5338Labels := by
  calc
    mixedMoment B raw36609 raw36609Labels = mixedMoment B raw36609step0 raw36609step0Labels := by
      have ha : raw36609step0 = (fun i j => raw36609 (permutation266 i) (permutation2 j)) := by apply Matrix.ext; unfold raw36609step0 raw36609; decide +kernel
      have hl : raw36609step0Labels = raw36609Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36609 raw36609Labels permutation266 permutation2
    _ = mixedMoment B node5338 node5338Labels := by rfl

theorem canonical36610 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36610 raw36610Labels = mixedMoment B node5361 node5361Labels := by
  calc
    mixedMoment B raw36610 raw36610Labels = mixedMoment B raw36610step0 raw36610step0Labels := by
      have hz : ∀ j, raw36610 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36610step0 = (fun i j => raw36610 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36610step0 raw36610; decide +kernel
      have hl : raw36610step0Labels = raw36610Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36610 raw36610Labels permutation346 hz
    mixedMoment B raw36610step0 raw36610step0Labels = mixedMoment B raw36610step1 raw36610step1Labels := by
      have ha : raw36610step1 = (fun i j => raw36610step0 (permutation57 i) (permutation2 j)) := by apply Matrix.ext; unfold raw36610step1 raw36610step0; decide +kernel
      have hl : raw36610step1Labels = raw36610step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36610step0 raw36610step0Labels permutation57 permutation2
    _ = mixedMoment B node5361 node5361Labels := by rfl

theorem canonical36611 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36611 raw36611Labels = mixedMoment B node5368 node5368Labels := by
  calc
    mixedMoment B raw36611 raw36611Labels = mixedMoment B raw36611step0 raw36611step0Labels := by
      have hz : ∀ j, raw36611 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36611step0 = (fun i j => raw36611 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36611step0 raw36611; decide +kernel
      have hl : raw36611step0Labels = raw36611Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36611 raw36611Labels permutation346 hz
    mixedMoment B raw36611step0 raw36611step0Labels = mixedMoment B raw36611step1 raw36611step1Labels := by
      have ha : raw36611step1 = (fun i j => raw36611step0 (permutation60 i) (permutation2 j)) := by apply Matrix.ext; unfold raw36611step1 raw36611step0; decide +kernel
      have hl : raw36611step1Labels = raw36611step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36611step0 raw36611step0Labels permutation60 permutation2
    _ = mixedMoment B node5368 node5368Labels := by rfl

theorem canonical36612 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36612 raw36612Labels = mixedMoment B node4776 node4776Labels := by
  calc
    mixedMoment B raw36612 raw36612Labels = mixedMoment B raw36612step0 raw36612step0Labels := by
      have hz : ∀ j, raw36612 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36612step0 = (fun i j => raw36612 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36612step0 raw36612; decide +kernel
      have hl : raw36612step0Labels = raw36612Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36612 raw36612Labels permutation346 hz
    mixedMoment B raw36612step0 raw36612step0Labels = mixedMoment B raw36612step1 raw36612step1Labels := by
      have ha : raw36612step1 = (fun i j => raw36612step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36612step1 raw36612step0; decide +kernel
      have hl : raw36612step1Labels = raw36612step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36612step0 raw36612step0Labels permutation151 permutation3
    mixedMoment B raw36612step1 raw36612step1Labels = mixedMoment B raw36612step2 raw36612step2Labels := by
      have ha : raw36612step2 = -raw36612step1 := by apply Matrix.ext; change ∀ i j, raw36612step2 i j = -(raw36612step1 i j); unfold raw36612step2 raw36612step1; decide +kernel
      have hl : raw36612step2Labels = raw36612step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36612step2 raw36612step2Labels = mixedMoment B raw36612step3 raw36612step3Labels := by
      have ha : raw36612step3 = raw36612step2 := by apply Matrix.ext; unfold raw36612step3 raw36612step2; decide +kernel
      have hl : raw36612step2Labels = labelEmbedding6 ∘ raw36612step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36612step2 raw36612step2Labels raw36612step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4776 node4776Labels := by rfl

theorem canonical36613 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36613 raw36613Labels = mixedMoment B node4777 node4777Labels := by
  calc
    mixedMoment B raw36613 raw36613Labels = mixedMoment B raw36613step0 raw36613step0Labels := by
      have hz : ∀ j, raw36613 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36613step0 = (fun i j => raw36613 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36613step0 raw36613; decide +kernel
      have hl : raw36613step0Labels = raw36613Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36613 raw36613Labels permutation346 hz
    mixedMoment B raw36613step0 raw36613step0Labels = mixedMoment B raw36613step1 raw36613step1Labels := by
      have ha : raw36613step1 = (fun i j => raw36613step0 (permutation150 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36613step1 raw36613step0; decide +kernel
      have hl : raw36613step1Labels = raw36613step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36613step0 raw36613step0Labels permutation150 permutation3
    mixedMoment B raw36613step1 raw36613step1Labels = mixedMoment B raw36613step2 raw36613step2Labels := by
      have ha : raw36613step2 = -raw36613step1 := by apply Matrix.ext; change ∀ i j, raw36613step2 i j = -(raw36613step1 i j); unfold raw36613step2 raw36613step1; decide +kernel
      have hl : raw36613step2Labels = raw36613step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36613step2 raw36613step2Labels = mixedMoment B raw36613step3 raw36613step3Labels := by
      have ha : raw36613step3 = raw36613step2 := by apply Matrix.ext; unfold raw36613step3 raw36613step2; decide +kernel
      have hl : raw36613step2Labels = labelEmbedding6 ∘ raw36613step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36613step2 raw36613step2Labels raw36613step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4777 node4777Labels := by rfl

theorem canonical36614 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36614 raw36614Labels = mixedMoment B node4775 node4775Labels := by
  calc
    mixedMoment B raw36614 raw36614Labels = mixedMoment B raw36614step0 raw36614step0Labels := by
      have ha : raw36614step0 = (fun i j => raw36614 (permutation688 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36614step0 raw36614; decide +kernel
      have hl : raw36614step0Labels = raw36614Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36614 raw36614Labels permutation688 permutation3
    mixedMoment B raw36614step0 raw36614step0Labels = mixedMoment B raw36614step1 raw36614step1Labels := by
      have ha : raw36614step1 = -raw36614step0 := by apply Matrix.ext; change ∀ i j, raw36614step1 i j = -(raw36614step0 i j); unfold raw36614step1 raw36614step0; decide +kernel
      have hl : raw36614step1Labels = raw36614step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36614step1 raw36614step1Labels = mixedMoment B raw36614step2 raw36614step2Labels := by
      have ha : raw36614step2 = raw36614step1 := by apply Matrix.ext; unfold raw36614step2 raw36614step1; decide +kernel
      have hl : raw36614step1Labels = labelEmbedding6 ∘ raw36614step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36614step1 raw36614step1Labels raw36614step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4775 node4775Labels := by rfl

theorem canonical36615 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36615 raw36615Labels = mixedMoment B node4821 node4821Labels := by
  calc
    mixedMoment B raw36615 raw36615Labels = mixedMoment B raw36615step0 raw36615step0Labels := by
      have hz : ∀ j, raw36615 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36615step0 = (fun i j => raw36615 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36615step0 raw36615; decide +kernel
      have hl : raw36615step0Labels = raw36615Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36615 raw36615Labels permutation346 hz
    mixedMoment B raw36615step0 raw36615step0Labels = mixedMoment B raw36615step1 raw36615step1Labels := by
      have ha : raw36615step1 = (fun i j => raw36615step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36615step1 raw36615step0; decide +kernel
      have hl : raw36615step1Labels = raw36615step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36615step0 raw36615step0Labels permutation151 permutation3
    mixedMoment B raw36615step1 raw36615step1Labels = mixedMoment B raw36615step2 raw36615step2Labels := by
      have ha : raw36615step2 = -raw36615step1 := by apply Matrix.ext; change ∀ i j, raw36615step2 i j = -(raw36615step1 i j); unfold raw36615step2 raw36615step1; decide +kernel
      have hl : raw36615step2Labels = raw36615step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36615step2 raw36615step2Labels = mixedMoment B raw36615step3 raw36615step3Labels := by
      have ha : raw36615step3 = raw36615step2 := by apply Matrix.ext; unfold raw36615step3 raw36615step2; decide +kernel
      have hl : raw36615step2Labels = labelEmbedding6 ∘ raw36615step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36615step2 raw36615step2Labels raw36615step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4821 node4821Labels := by rfl

theorem canonical36616 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36616 raw36616Labels = mixedMoment B node4856 node4856Labels := by
  calc
    mixedMoment B raw36616 raw36616Labels = mixedMoment B raw36616step0 raw36616step0Labels := by
      have hz : ∀ j, raw36616 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36616step0 = (fun i j => raw36616 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36616step0 raw36616; decide +kernel
      have hl : raw36616step0Labels = raw36616Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36616 raw36616Labels permutation346 hz
    mixedMoment B raw36616step0 raw36616step0Labels = mixedMoment B raw36616step1 raw36616step1Labels := by
      have ha : raw36616step1 = (fun i j => raw36616step0 (permutation145 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36616step1 raw36616step0; decide +kernel
      have hl : raw36616step1Labels = raw36616step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36616step0 raw36616step0Labels permutation145 permutation3
    mixedMoment B raw36616step1 raw36616step1Labels = mixedMoment B raw36616step2 raw36616step2Labels := by
      have ha : raw36616step2 = -raw36616step1 := by apply Matrix.ext; change ∀ i j, raw36616step2 i j = -(raw36616step1 i j); unfold raw36616step2 raw36616step1; decide +kernel
      have hl : raw36616step2Labels = raw36616step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36616step2 raw36616step2Labels = mixedMoment B raw36616step3 raw36616step3Labels := by
      have ha : raw36616step3 = raw36616step2 := by apply Matrix.ext; unfold raw36616step3 raw36616step2; decide +kernel
      have hl : raw36616step2Labels = labelEmbedding6 ∘ raw36616step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36616step2 raw36616step2Labels raw36616step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4856 node4856Labels := by rfl

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

theorem singleton5105 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5105 node5105Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2515 node2515Labels + mixedMoment B node3479 node3479Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2130 singletonSmall5105
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5105) = raw2130Labels := by decide +kernel
  rw [hl, canonical2130 B hB] at h
  have hc0 : mixedMoment B raw2130 (Fin.cases (0 : Fin 2) singletonSmall5105) =
      mixedMoment B node2515 node2515Labels := by
    have ha : raw2130 = raw2131 := by apply Matrix.ext; unfold raw2130 raw2131; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5105 = raw2131Labels := by decide +kernel
    rw [ha, hj, canonical2131 B hB]
  have hc1 : mixedMoment B raw2130 (Fin.cases (1 : Fin 2) singletonSmall5105) =
      mixedMoment B node3479 node3479Labels := by
    have ha : raw2130 = raw2132 := by apply Matrix.ext; unfold raw2130 raw2132; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5105 = raw2132Labels := by decide +kernel
    rw [ha, hj, canonical2132 B hB]
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

theorem singleton5355 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5355 node5355Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3693 node3693Labels + mixedMoment B node3770 node3770Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2400 singletonSmall5355
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5355) = raw2400Labels := by decide +kernel
  rw [hl, canonical2400 B hB] at h
  have hc0 : mixedMoment B raw2400 (Fin.cases (0 : Fin 2) singletonSmall5355) =
      mixedMoment B node3693 node3693Labels := by
    have ha : raw2400 = raw2401 := by apply Matrix.ext; unfold raw2400 raw2401; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5355 = raw2401Labels := by decide +kernel
    rw [ha, hj, canonical2401 B hB]
  have hc1 : mixedMoment B raw2400 (Fin.cases (1 : Fin 2) singletonSmall5355) =
      mixedMoment B node3770 node3770Labels := by
    have ha : raw2400 = raw2402 := by apply Matrix.ext; unfold raw2400 raw2402; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5355 = raw2402Labels := by decide +kernel
    rw [ha, hj, canonical2402 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton5365 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5365 node5365Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3703 node3703Labels + mixedMoment B node3758 node3758Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2412 singletonSmall5365
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5365) = raw2412Labels := by decide +kernel
  rw [hl, canonical2412 B hB] at h
  have hc0 : mixedMoment B raw2412 (Fin.cases (0 : Fin 2) singletonSmall5365) =
      mixedMoment B node3703 node3703Labels := by
    have ha : raw2412 = raw2413 := by apply Matrix.ext; unfold raw2412 raw2413; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5365 = raw2413Labels := by decide +kernel
    rw [ha, hj, canonical2413 B hB]
  have hc1 : mixedMoment B raw2412 (Fin.cases (1 : Fin 2) singletonSmall5365) =
      mixedMoment B node3758 node3758Labels := by
    have ha : raw2412 = raw2414 := by apply Matrix.ext; unfold raw2412 raw2414; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5365 = raw2414Labels := by decide +kernel
    rw [ha, hj, canonical2414 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton5368 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5368 node5368Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3705 node3705Labels + mixedMoment B node3767 node3767Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2415 singletonSmall5368
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5368) = raw2415Labels := by decide +kernel
  rw [hl, canonical2415 B hB] at h
  have hc0 : mixedMoment B raw2415 (Fin.cases (0 : Fin 2) singletonSmall5368) =
      mixedMoment B node3705 node3705Labels := by
    have ha : raw2415 = raw2416 := by apply Matrix.ext; unfold raw2415 raw2416; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5368 = raw2416Labels := by decide +kernel
    rw [ha, hj, canonical2416 B hB]
  have hc1 : mixedMoment B raw2415 (Fin.cases (1 : Fin 2) singletonSmall5368) =
      mixedMoment B node3767 node3767Labels := by
    have ha : raw2415 = raw2417 := by apply Matrix.ext; unfold raw2415 raw2417; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5368 = raw2417Labels := by decide +kernel
    rw [ha, hj, canonical2417 B hB]
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

theorem singleton5412 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5412 node5412Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3814 node3814Labels + mixedMoment B node3814 node3814Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2493 singletonSmall5412
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5412) = raw2493Labels := by decide +kernel
  rw [hl, canonical2493 B hB] at h
  have hc0 : mixedMoment B raw2493 (Fin.cases (0 : Fin 2) singletonSmall5412) =
      mixedMoment B node3814 node3814Labels := by
    have ha : raw2493 = raw2494 := by apply Matrix.ext; unfold raw2493 raw2494; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5412 = raw2494Labels := by decide +kernel
    rw [ha, hj, canonical2494 B hB]
  have hc1 : mixedMoment B raw2493 (Fin.cases (1 : Fin 2) singletonSmall5412) =
      mixedMoment B node3814 node3814Labels := by
    have ha : raw2493 = raw2495 := by apply Matrix.ext; unfold raw2493 raw2495; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5412 = raw2495Labels := by decide +kernel
    rw [ha, hj, canonical2495 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons85
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singleton5473 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5473 node5473Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3958 node3958Labels + mixedMoment B node3961 node3961Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2589 singletonSmall5473
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5473) = raw2589Labels := by decide +kernel
  rw [hl, canonical2589 B hB] at h
  have hc0 : mixedMoment B raw2589 (Fin.cases (0 : Fin 2) singletonSmall5473) =
      mixedMoment B node3958 node3958Labels := by
    have ha : raw2589 = raw2590 := by apply Matrix.ext; unfold raw2589 raw2590; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5473 = raw2590Labels := by decide +kernel
    rw [ha, hj, canonical2590 B hB]
  have hc1 : mixedMoment B raw2589 (Fin.cases (1 : Fin 2) singletonSmall5473) =
      mixedMoment B node3961 node3961Labels := by
    have ha : raw2589 = raw2591 := by apply Matrix.ext; unfold raw2589 raw2591; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5473 = raw2591Labels := by decide +kernel
    rw [ha, hj, canonical2591 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_SoundPriority
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound3814 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3814 node3814Labels = Sparse.eval nodeValue3814 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3814) = mixedMoment B node3814 node3814Labels := rfl
  simpa [nodeValue3814, Sparse.eval] using hc.symm

theorem sound5412 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5412 node5412Labels = Sparse.eval nodeValue5412 (mixedVector B) := by
  have h := singleton5412 B _hB
  rw [sound3814 B _hB _hF] at h
  norm_num [nodeValue5412, nodeValue3814, Sparse.eval] at h ⊢
  linarith only [h]

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound39
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound2515 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2515 node2515Labels = Sparse.eval nodeValue2515 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2515) = mixedMoment B node2515 node2515Labels := rfl
  simpa [nodeValue2515, Sparse.eval] using hc.symm

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

theorem sound3479 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3479 node3479Labels = Sparse.eval nodeValue3479 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3479) = mixedMoment B node3479 node3479Labels := rfl
  simpa [nodeValue3479, Sparse.eval] using hc.symm

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

theorem sound3693 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3693 node3693Labels = Sparse.eval nodeValue3693 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3693) = mixedMoment B node3693 node3693Labels := rfl
  simpa [nodeValue3693, Sparse.eval] using hc.symm

theorem sound3703 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3703 node3703Labels = Sparse.eval nodeValue3703 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3703) = mixedMoment B node3703 node3703Labels := rfl
  simpa [nodeValue3703, Sparse.eval] using hc.symm

theorem sound3705 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3705 node3705Labels = Sparse.eval nodeValue3705 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3705) = mixedMoment B node3705 node3705Labels := rfl
  simpa [nodeValue3705, Sparse.eval] using hc.symm

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

theorem sound3754 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3754 node3754Labels = Sparse.eval nodeValue3754 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3754) = mixedMoment B node3754 node3754Labels := rfl
  simpa [nodeValue3754, Sparse.eval] using hc.symm

theorem sound3758 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3758 node3758Labels = Sparse.eval nodeValue3758 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3758) = mixedMoment B node3758 node3758Labels := rfl
  simpa [nodeValue3758, Sparse.eval] using hc.symm

theorem sound3767 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3767 node3767Labels = Sparse.eval nodeValue3767 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3767) = mixedMoment B node3767 node3767Labels := rfl
  simpa [nodeValue3767, Sparse.eval] using hc.symm

theorem sound3770 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3770 node3770Labels = Sparse.eval nodeValue3770 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3770) = mixedMoment B node3770 node3770Labels := rfl
  simpa [nodeValue3770, Sparse.eval] using hc.symm

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

theorem sound3782 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3782 node3782Labels = Sparse.eval nodeValue3782 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3782) = mixedMoment B node3782 node3782Labels := rfl
  simpa [nodeValue3782, Sparse.eval] using hc.symm

theorem sound3796 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3796 node3796Labels = Sparse.eval nodeValue3796 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3796) = mixedMoment B node3796 node3796Labels := rfl
  simpa [nodeValue3796, Sparse.eval] using hc.symm

theorem sound3809 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3809 node3809Labels = Sparse.eval nodeValue3809 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3809) = mixedMoment B node3809 node3809Labels := rfl
  simpa [nodeValue3809, Sparse.eval] using hc.symm

theorem sound3813 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3813 node3813Labels = Sparse.eval nodeValue3813 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3813) = mixedMoment B node3813 node3813Labels := rfl
  simpa [nodeValue3813, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound61
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound3958 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3958 node3958Labels = Sparse.eval nodeValue3958 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3958) = mixedMoment B node3958 node3958Labels := rfl
  simpa [nodeValue3958, Sparse.eval] using hc.symm

theorem sound3961 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3961 node3961Labels = Sparse.eval nodeValue3961 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3961) = mixedMoment B node3961 node3961Labels := rfl
  simpa [nodeValue3961, Sparse.eval] using hc.symm

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

theorem sound4775 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4775 node4775Labels = Sparse.eval nodeValue4775 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4775) = mixedMoment B node4775 node4775Labels := rfl
  simpa [nodeValue4775, Sparse.eval] using hc.symm

theorem sound4776 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4776 node4776Labels = Sparse.eval nodeValue4776 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4776) = mixedMoment B node4776 node4776Labels := rfl
  simpa [nodeValue4776, Sparse.eval] using hc.symm

theorem sound4777 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4777 node4777Labels = Sparse.eval nodeValue4777 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4777) = mixedMoment B node4777 node4777Labels := rfl
  simpa [nodeValue4777, Sparse.eval] using hc.symm

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

theorem sound4821 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4821 node4821Labels = Sparse.eval nodeValue4821 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4821) = mixedMoment B node4821 node4821Labels := rfl
  simpa [nodeValue4821, Sparse.eval] using hc.symm

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

theorem sound4942 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4942 node4942Labels = Sparse.eval nodeValue4942 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4942) = mixedMoment B node4942 node4942Labels := rfl
  simpa [nodeValue4942, Sparse.eval] using hc.symm

theorem sound4949 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4949 node4949Labels = Sparse.eval nodeValue4949 (mixedVector B) := by
  have h := singleton4949 B _hB
  rw [sound2341 B _hB _hF, sound3417 B _hB _hF] at h
  norm_num [nodeValue4949, nodeValue2341, nodeValue3417, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4951 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4951 node4951Labels = Sparse.eval nodeValue4951 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4951) = mixedMoment B node4951 node4951Labels := rfl
  simpa [nodeValue4951, Sparse.eval] using hc.symm

theorem sound4963 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4963 node4963Labels = Sparse.eval nodeValue4963 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4963) = mixedMoment B node4963 node4963Labels := rfl
  simpa [nodeValue4963, Sparse.eval] using hc.symm

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

theorem sound5105 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5105 node5105Labels = Sparse.eval nodeValue5105 (mixedVector B) := by
  have h := singleton5105 B _hB
  rw [sound2515 B _hB _hF, sound3479 B _hB _hF] at h
  norm_num [nodeValue5105, nodeValue2515, nodeValue3479, Sparse.eval] at h ⊢
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

theorem sound5198 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5198 node5198Labels = Sparse.eval nodeValue5198 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5198) = mixedMoment B node5198 node5198Labels := rfl
  simpa [nodeValue5198, Sparse.eval] using hc.symm

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

theorem sound5338 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5338 node5338Labels = Sparse.eval nodeValue5338 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5338) = mixedMoment B node5338 node5338Labels := rfl
  simpa [nodeValue5338, Sparse.eval] using hc.symm

theorem sound5353 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5353 node5353Labels = Sparse.eval nodeValue5353 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5353) = mixedMoment B node5353 node5353Labels := rfl
  simpa [nodeValue5353, Sparse.eval] using hc.symm

theorem sound5355 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5355 node5355Labels = Sparse.eval nodeValue5355 (mixedVector B) := by
  have h := singleton5355 B _hB
  rw [sound3693 B _hB _hF, sound3770 B _hB _hF] at h
  norm_num [nodeValue5355, nodeValue3693, nodeValue3770, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5360 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5360 node5360Labels = Sparse.eval nodeValue5360 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5360) = mixedMoment B node5360 node5360Labels := rfl
  simpa [nodeValue5360, Sparse.eval] using hc.symm

theorem sound5361 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5361 node5361Labels = Sparse.eval nodeValue5361 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5361) = mixedMoment B node5361 node5361Labels := rfl
  simpa [nodeValue5361, Sparse.eval] using hc.symm

theorem sound5365 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5365 node5365Labels = Sparse.eval nodeValue5365 (mixedVector B) := by
  have h := singleton5365 B _hB
  rw [sound3703 B _hB _hF, sound3758 B _hB _hF] at h
  norm_num [nodeValue5365, nodeValue3703, nodeValue3758, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5367 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5367 node5367Labels = Sparse.eval nodeValue5367 (mixedVector B) := by
  simpa only [nodeValue5367, Sparse.eval_nil] using zero5367 B _hB _hF

theorem sound5368 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5368 node5368Labels = Sparse.eval nodeValue5368 (mixedVector B) := by
  have h := singleton5368 B _hB
  rw [sound3705 B _hB _hF, sound3767 B _hB _hF] at h
  norm_num [nodeValue5368, nodeValue3705, nodeValue3767, Sparse.eval] at h ⊢
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

theorem sound5397 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5397 node5397Labels = Sparse.eval nodeValue5397 (mixedVector B) := by
  have h := singleton5397 B _hB
  rw [sound3782 B _hB _hF, sound3796 B _hB _hF] at h
  norm_num [nodeValue5397, nodeValue3782, nodeValue3796, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5410 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5410 node5410Labels = Sparse.eval nodeValue5410 (mixedVector B) := by
  simpa only [nodeValue5410, Sparse.eval_nil] using zero5410 B _hB _hF

theorem sound5411 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5411 node5411Labels = Sparse.eval nodeValue5411 (mixedVector B) := by
  have h := singleton5411 B _hB
  rw [sound3809 B _hB _hF, sound3813 B _hB _hF] at h
  norm_num [nodeValue5411, nodeValue3809, nodeValue3813, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5421 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5421 node5421Labels = Sparse.eval nodeValue5421 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5421) = mixedMoment B node5421 node5421Labels := rfl
  simpa [nodeValue5421, Sparse.eval] using hc.symm

theorem sound5436 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5436 node5436Labels = Sparse.eval nodeValue5436 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5436) = mixedMoment B node5436 node5436Labels := rfl
  simpa [nodeValue5436, Sparse.eval] using hc.symm

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

theorem sound5473 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5473 node5473Labels = Sparse.eval nodeValue5473 (mixedVector B) := by
  have h := singleton5473 B _hB
  rw [sound3958 B _hB _hF, sound3961 B _hB _hF] at h
  norm_num [nodeValue5473, nodeValue3958, nodeValue3961, Sparse.eval] at h ⊢
  linarith only [h]

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources81
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sourceEq2621 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2621 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2621 + difference 0 1) (sourceB2621 + difference 1 0) sourceC2621) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5105) := by
    have ha : (tripleCharges (sourceA2621 + difference 0 1) (sourceB2621 + difference 1 0) sourceC2621) = raw36587 := by
      apply Matrix.ext; unfold tripleCharges sourceA2621 sourceB2621 sourceC2621 difference raw36587; decide +kernel
    rw [ha]
    exact (canonical36587 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2621 + difference 0 2) (sourceB2621 + difference 2 0) sourceC2621) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5397) := by
    have ha : (tripleCharges (sourceA2621 + difference 0 2) (sourceB2621 + difference 2 0) sourceC2621) = raw36588 := by
      apply Matrix.ext; unfold tripleCharges sourceA2621 sourceB2621 sourceC2621 difference raw36588; decide +kernel
    rw [ha]
    exact (canonical36588 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2621 + difference 0 3) (sourceB2621 + difference 3 0) sourceC2621) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5412) := by
    have ha : (tripleCharges (sourceA2621 + difference 0 3) (sourceB2621 + difference 3 0) sourceC2621) = raw36589 := by
      apply Matrix.ext; unfold tripleCharges sourceA2621 sourceB2621 sourceC2621 difference raw36589; decide +kernel
    rw [ha]
    exact (canonical36589 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2621 + difference 0 4) (sourceB2621 + difference 4 0) sourceC2621) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5411) := by
    have ha : (tripleCharges (sourceA2621 + difference 0 4) (sourceB2621 + difference 4 0) sourceC2621) = raw36590 := by
      apply Matrix.ext; unfold tripleCharges sourceA2621 sourceB2621 sourceC2621 difference raw36590; decide +kernel
    rw [ha]
    exact (canonical36590 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2621 + difference 0 5) (sourceB2621 + difference 5 0) sourceC2621) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5410) := by
    have ha : (tripleCharges (sourceA2621 + difference 0 5) (sourceB2621 + difference 5 0) sourceC2621) = raw36591 := by
      apply Matrix.ext; unfold tripleCharges sourceA2621 sourceB2621 sourceC2621 difference raw36591; decide +kernel
    rw [ha]
    exact (canonical36591 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2621 + difference 1 0) (sourceB2621 + difference 0 1) sourceC2621) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5198) := by
    have ha : (tripleCharges (sourceA2621 + difference 1 0) (sourceB2621 + difference 0 1) sourceC2621) = raw36592 := by
      apply Matrix.ext; unfold tripleCharges sourceA2621 sourceB2621 sourceC2621 difference raw36592; decide +kernel
    rw [ha]
    exact (canonical36592 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2621 + difference 1 2) (sourceB2621 + difference 2 1) sourceC2621) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5421) := by
    have ha : (tripleCharges (sourceA2621 + difference 1 2) (sourceB2621 + difference 2 1) sourceC2621) = raw36593 := by
      apply Matrix.ext; unfold tripleCharges sourceA2621 sourceB2621 sourceC2621 difference raw36593; decide +kernel
    rw [ha]
    exact (canonical36593 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2621 + difference 1 3) (sourceB2621 + difference 3 1) sourceC2621) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5436) := by
    have ha : (tripleCharges (sourceA2621 + difference 1 3) (sourceB2621 + difference 3 1) sourceC2621) = raw36594 := by
      apply Matrix.ext; unfold tripleCharges sourceA2621 sourceB2621 sourceC2621 difference raw36594; decide +kernel
    rw [ha]
    exact (canonical36594 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2621 + difference 1 4) (sourceB2621 + difference 4 1) sourceC2621) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5446) := by
    have ha : (tripleCharges (sourceA2621 + difference 1 4) (sourceB2621 + difference 4 1) sourceC2621) = raw36595 := by
      apply Matrix.ext; unfold tripleCharges sourceA2621 sourceB2621 sourceC2621 difference raw36595; decide +kernel
    rw [ha]
    exact (canonical36595 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2621 + difference 1 5) (sourceB2621 + difference 5 1) sourceC2621) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5473) := by
    have ha : (tripleCharges (sourceA2621 + difference 1 5) (sourceB2621 + difference 5 1) sourceC2621) = raw36596 := by
      apply Matrix.ext; unfold tripleCharges sourceA2621 sourceB2621 sourceC2621 difference raw36596; decide +kernel
    rw [ha]
    exact (canonical36596 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2621 + difference 2 0) (sourceB2621 + difference 0 2) sourceC2621) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4963) := by
    have ha : (tripleCharges (sourceA2621 + difference 2 0) (sourceB2621 + difference 0 2) sourceC2621) = raw36597 := by
      apply Matrix.ext; unfold tripleCharges sourceA2621 sourceB2621 sourceC2621 difference raw36597; decide +kernel
    rw [ha]
    exact (canonical36597 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2621 + difference 2 1) (sourceB2621 + difference 1 2) sourceC2621) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4942) := by
    have ha : (tripleCharges (sourceA2621 + difference 2 1) (sourceB2621 + difference 1 2) sourceC2621) = raw36598 := by
      apply Matrix.ext; unfold tripleCharges sourceA2621 sourceB2621 sourceC2621 difference raw36598; decide +kernel
    rw [ha]
    exact (canonical36598 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2621 + difference 2 3) (sourceB2621 + difference 3 2) sourceC2621) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5360) := by
    have ha : (tripleCharges (sourceA2621 + difference 2 3) (sourceB2621 + difference 3 2) sourceC2621) = raw36599 := by
      apply Matrix.ext; unfold tripleCharges sourceA2621 sourceB2621 sourceC2621 difference raw36599; decide +kernel
    rw [ha]
    exact (canonical36599 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2621 + difference 2 4) (sourceB2621 + difference 4 2) sourceC2621) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5353) := by
    have ha : (tripleCharges (sourceA2621 + difference 2 4) (sourceB2621 + difference 4 2) sourceC2621) = raw36600 := by
      apply Matrix.ext; unfold tripleCharges sourceA2621 sourceB2621 sourceC2621 difference raw36600; decide +kernel
    rw [ha]
    exact (canonical36600 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2621 + difference 2 5) (sourceB2621 + difference 5 2) sourceC2621) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5365) := by
    have ha : (tripleCharges (sourceA2621 + difference 2 5) (sourceB2621 + difference 5 2) sourceC2621) = raw36601 := by
      apply Matrix.ext; unfold tripleCharges sourceA2621 sourceB2621 sourceC2621 difference raw36601; decide +kernel
    rw [ha]
    exact (canonical36601 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2621 + difference 3 0) (sourceB2621 + difference 0 3) sourceC2621) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4973) := by
    have ha : (tripleCharges (sourceA2621 + difference 3 0) (sourceB2621 + difference 0 3) sourceC2621) = raw36602 := by
      apply Matrix.ext; unfold tripleCharges sourceA2621 sourceB2621 sourceC2621 difference raw36602; decide +kernel
    rw [ha]
    exact (canonical36602 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2621 + difference 3 1) (sourceB2621 + difference 1 3) sourceC2621) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4949) := by
    have ha : (tripleCharges (sourceA2621 + difference 3 1) (sourceB2621 + difference 1 3) sourceC2621) = raw36603 := by
      apply Matrix.ext; unfold tripleCharges sourceA2621 sourceB2621 sourceC2621 difference raw36603; decide +kernel
    rw [ha]
    exact (canonical36603 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2621 + difference 3 2) (sourceB2621 + difference 2 3) sourceC2621) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5336) := by
    have ha : (tripleCharges (sourceA2621 + difference 3 2) (sourceB2621 + difference 2 3) sourceC2621) = raw36604 := by
      apply Matrix.ext; unfold tripleCharges sourceA2621 sourceB2621 sourceC2621 difference raw36604; decide +kernel
    rw [ha]
    exact (canonical36604 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2621 + difference 3 4) (sourceB2621 + difference 4 3) sourceC2621) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5355) := by
    have ha : (tripleCharges (sourceA2621 + difference 3 4) (sourceB2621 + difference 4 3) sourceC2621) = raw36605 := by
      apply Matrix.ext; unfold tripleCharges sourceA2621 sourceB2621 sourceC2621 difference raw36605; decide +kernel
    rw [ha]
    exact (canonical36605 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2621 + difference 3 5) (sourceB2621 + difference 5 3) sourceC2621) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5367) := by
    have ha : (tripleCharges (sourceA2621 + difference 3 5) (sourceB2621 + difference 5 3) sourceC2621) = raw36606 := by
      apply Matrix.ext; unfold tripleCharges sourceA2621 sourceB2621 sourceC2621 difference raw36606; decide +kernel
    rw [ha]
    exact (canonical36606 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2621 + difference 4 0) (sourceB2621 + difference 0 4) sourceC2621) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4966) := by
    have ha : (tripleCharges (sourceA2621 + difference 4 0) (sourceB2621 + difference 0 4) sourceC2621) = raw36607 := by
      apply Matrix.ext; unfold tripleCharges sourceA2621 sourceB2621 sourceC2621 difference raw36607; decide +kernel
    rw [ha]
    exact (canonical36607 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2621 + difference 4 1) (sourceB2621 + difference 1 4) sourceC2621) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4951) := by
    have ha : (tripleCharges (sourceA2621 + difference 4 1) (sourceB2621 + difference 1 4) sourceC2621) = raw36608 := by
      apply Matrix.ext; unfold tripleCharges sourceA2621 sourceB2621 sourceC2621 difference raw36608; decide +kernel
    rw [ha]
    exact (canonical36608 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2621 + difference 4 2) (sourceB2621 + difference 2 4) sourceC2621) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5338) := by
    have ha : (tripleCharges (sourceA2621 + difference 4 2) (sourceB2621 + difference 2 4) sourceC2621) = raw36609 := by
      apply Matrix.ext; unfold tripleCharges sourceA2621 sourceB2621 sourceC2621 difference raw36609; decide +kernel
    rw [ha]
    exact (canonical36609 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2621 + difference 4 3) (sourceB2621 + difference 3 4) sourceC2621) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5361) := by
    have ha : (tripleCharges (sourceA2621 + difference 4 3) (sourceB2621 + difference 3 4) sourceC2621) = raw36610 := by
      apply Matrix.ext; unfold tripleCharges sourceA2621 sourceB2621 sourceC2621 difference raw36610; decide +kernel
    rw [ha]
    exact (canonical36610 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2621 + difference 4 5) (sourceB2621 + difference 5 4) sourceC2621) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5368) := by
    have ha : (tripleCharges (sourceA2621 + difference 4 5) (sourceB2621 + difference 5 4) sourceC2621) = raw36611 := by
      apply Matrix.ext; unfold tripleCharges sourceA2621 sourceB2621 sourceC2621 difference raw36611; decide +kernel
    rw [ha]
    exact (canonical36611 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2621 + difference 5 0) (sourceB2621 + difference 0 5) sourceC2621) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4776) := by
    have ha : (tripleCharges (sourceA2621 + difference 5 0) (sourceB2621 + difference 0 5) sourceC2621) = raw36612 := by
      apply Matrix.ext; unfold tripleCharges sourceA2621 sourceB2621 sourceC2621 difference raw36612; decide +kernel
    rw [ha]
    exact (canonical36612 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2621 + difference 5 1) (sourceB2621 + difference 1 5) sourceC2621) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4777) := by
    have ha : (tripleCharges (sourceA2621 + difference 5 1) (sourceB2621 + difference 1 5) sourceC2621) = raw36613 := by
      apply Matrix.ext; unfold tripleCharges sourceA2621 sourceB2621 sourceC2621 difference raw36613; decide +kernel
    rw [ha]
    exact (canonical36613 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2621 + difference 5 2) (sourceB2621 + difference 2 5) sourceC2621) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4775) := by
    have ha : (tripleCharges (sourceA2621 + difference 5 2) (sourceB2621 + difference 2 5) sourceC2621) = raw36614 := by
      apply Matrix.ext; unfold tripleCharges sourceA2621 sourceB2621 sourceC2621 difference raw36614; decide +kernel
    rw [ha]
    exact (canonical36614 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2621 + difference 5 3) (sourceB2621 + difference 3 5) sourceC2621) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4821) := by
    have ha : (tripleCharges (sourceA2621 + difference 5 3) (sourceB2621 + difference 3 5) sourceC2621) = raw36615 := by
      apply Matrix.ext; unfold tripleCharges sourceA2621 sourceB2621 sourceC2621 difference raw36615; decide +kernel
    rw [ha]
    exact (canonical36615 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2621 + difference 5 4) (sourceB2621 + difference 4 5) sourceC2621) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4856) := by
    have ha : (tripleCharges (sourceA2621 + difference 5 4) (sourceB2621 + difference 4 5) sourceC2621) = raw36616 := by
      apply Matrix.ext; unfold tripleCharges sourceA2621 sourceB2621 sourceC2621 difference raw36616; decide +kernel
    rw [ha]
    exact (canonical36616 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2621 sourceB2621 sourceC2621
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2621, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic130
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reindexCheck2088 : Integer.Sparse.reindex keyMap MixedData.row2088 = numericRow2088 := by decide +kernel

theorem numericCheck2088 (x : Master → ℝ) : Integer.Sparse.eval numericRow2088 x =
    (4 : ℝ) * reducedSource2088 x := by
  norm_num [numericRow2088, reducedSource2088, Integer.Sparse.eval, Sparse.eval, nodeValue4775, nodeValue4776, nodeValue4777, nodeValue4821, nodeValue4856, nodeValue4942, nodeValue4949, nodeValue4951, nodeValue4963, nodeValue4966, nodeValue4973, nodeValue5105, nodeValue5198, nodeValue5336, nodeValue5338, nodeValue5353, nodeValue5355, nodeValue5360, nodeValue5361, nodeValue5365, nodeValue5367, nodeValue5368, nodeValue5397, nodeValue5410, nodeValue5411, nodeValue5412, nodeValue5421, nodeValue5436, nodeValue5446, nodeValue5473]
  ring

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Rows130
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero2088 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource2088 (mixedVector B) = 0 := by
  have h4775 : mixedVector B (Sum.inr 4775) = Sparse.eval nodeValue4775 (mixedVector B) := by
    change mixedMoment B node4775 node4775Labels = _
    exact sound4775 B hB hF
  have h4776 : mixedVector B (Sum.inr 4776) = Sparse.eval nodeValue4776 (mixedVector B) := by
    change mixedMoment B node4776 node4776Labels = _
    exact sound4776 B hB hF
  have h4777 : mixedVector B (Sum.inr 4777) = Sparse.eval nodeValue4777 (mixedVector B) := by
    change mixedMoment B node4777 node4777Labels = _
    exact sound4777 B hB hF
  have h4821 : mixedVector B (Sum.inr 4821) = Sparse.eval nodeValue4821 (mixedVector B) := by
    change mixedMoment B node4821 node4821Labels = _
    exact sound4821 B hB hF
  have h4856 : mixedVector B (Sum.inr 4856) = Sparse.eval nodeValue4856 (mixedVector B) := by
    change mixedMoment B node4856 node4856Labels = _
    exact sound4856 B hB hF
  have h4942 : mixedVector B (Sum.inr 4942) = Sparse.eval nodeValue4942 (mixedVector B) := by
    change mixedMoment B node4942 node4942Labels = _
    exact sound4942 B hB hF
  have h4949 : mixedVector B (Sum.inr 4949) = Sparse.eval nodeValue4949 (mixedVector B) := by
    change mixedMoment B node4949 node4949Labels = _
    exact sound4949 B hB hF
  have h4951 : mixedVector B (Sum.inr 4951) = Sparse.eval nodeValue4951 (mixedVector B) := by
    change mixedMoment B node4951 node4951Labels = _
    exact sound4951 B hB hF
  have h4963 : mixedVector B (Sum.inr 4963) = Sparse.eval nodeValue4963 (mixedVector B) := by
    change mixedMoment B node4963 node4963Labels = _
    exact sound4963 B hB hF
  have h4966 : mixedVector B (Sum.inr 4966) = Sparse.eval nodeValue4966 (mixedVector B) := by
    change mixedMoment B node4966 node4966Labels = _
    exact sound4966 B hB hF
  have h4973 : mixedVector B (Sum.inr 4973) = Sparse.eval nodeValue4973 (mixedVector B) := by
    change mixedMoment B node4973 node4973Labels = _
    exact sound4973 B hB hF
  have h5105 : mixedVector B (Sum.inr 5105) = Sparse.eval nodeValue5105 (mixedVector B) := by
    change mixedMoment B node5105 node5105Labels = _
    exact sound5105 B hB hF
  have h5198 : mixedVector B (Sum.inr 5198) = Sparse.eval nodeValue5198 (mixedVector B) := by
    change mixedMoment B node5198 node5198Labels = _
    exact sound5198 B hB hF
  have h5336 : mixedVector B (Sum.inr 5336) = Sparse.eval nodeValue5336 (mixedVector B) := by
    change mixedMoment B node5336 node5336Labels = _
    exact sound5336 B hB hF
  have h5338 : mixedVector B (Sum.inr 5338) = Sparse.eval nodeValue5338 (mixedVector B) := by
    change mixedMoment B node5338 node5338Labels = _
    exact sound5338 B hB hF
  have h5353 : mixedVector B (Sum.inr 5353) = Sparse.eval nodeValue5353 (mixedVector B) := by
    change mixedMoment B node5353 node5353Labels = _
    exact sound5353 B hB hF
  have h5355 : mixedVector B (Sum.inr 5355) = Sparse.eval nodeValue5355 (mixedVector B) := by
    change mixedMoment B node5355 node5355Labels = _
    exact sound5355 B hB hF
  have h5360 : mixedVector B (Sum.inr 5360) = Sparse.eval nodeValue5360 (mixedVector B) := by
    change mixedMoment B node5360 node5360Labels = _
    exact sound5360 B hB hF
  have h5361 : mixedVector B (Sum.inr 5361) = Sparse.eval nodeValue5361 (mixedVector B) := by
    change mixedMoment B node5361 node5361Labels = _
    exact sound5361 B hB hF
  have h5365 : mixedVector B (Sum.inr 5365) = Sparse.eval nodeValue5365 (mixedVector B) := by
    change mixedMoment B node5365 node5365Labels = _
    exact sound5365 B hB hF
  have h5367 : mixedVector B (Sum.inr 5367) = Sparse.eval nodeValue5367 (mixedVector B) := by
    change mixedMoment B node5367 node5367Labels = _
    exact sound5367 B hB hF
  have h5368 : mixedVector B (Sum.inr 5368) = Sparse.eval nodeValue5368 (mixedVector B) := by
    change mixedMoment B node5368 node5368Labels = _
    exact sound5368 B hB hF
  have h5397 : mixedVector B (Sum.inr 5397) = Sparse.eval nodeValue5397 (mixedVector B) := by
    change mixedMoment B node5397 node5397Labels = _
    exact sound5397 B hB hF
  have h5410 : mixedVector B (Sum.inr 5410) = Sparse.eval nodeValue5410 (mixedVector B) := by
    change mixedMoment B node5410 node5410Labels = _
    exact sound5410 B hB hF
  have h5411 : mixedVector B (Sum.inr 5411) = Sparse.eval nodeValue5411 (mixedVector B) := by
    change mixedMoment B node5411 node5411Labels = _
    exact sound5411 B hB hF
  have h5412 : mixedVector B (Sum.inr 5412) = Sparse.eval nodeValue5412 (mixedVector B) := by
    change mixedMoment B node5412 node5412Labels = _
    exact sound5412 B hB hF
  have h5421 : mixedVector B (Sum.inr 5421) = Sparse.eval nodeValue5421 (mixedVector B) := by
    change mixedMoment B node5421 node5421Labels = _
    exact sound5421 B hB hF
  have h5436 : mixedVector B (Sum.inr 5436) = Sparse.eval nodeValue5436 (mixedVector B) := by
    change mixedMoment B node5436 node5436Labels = _
    exact sound5436 B hB hF
  have h5446 : mixedVector B (Sum.inr 5446) = Sparse.eval nodeValue5446 (mixedVector B) := by
    change mixedMoment B node5446 node5446Labels = _
    exact sound5446 B hB hF
  have h5473 : mixedVector B (Sum.inr 5473) = Sparse.eval nodeValue5473 (mixedVector B) := by
    change mixedMoment B node5473 node5473Labels = _
    exact sound5473 B hB hF
  simpa only [sourceForm2621, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4775, h4776, h4777, h4821, h4856, h4942, h4949, h4951, h4963, h4966, h4973, h5105, h5198, h5336, h5338, h5353, h5355, h5360, h5361, h5365, h5367, h5368, h5397, h5410, h5411, h5412, h5421, h5436, h5446, h5473, reducedSource2088] using sourceEq2621 B hB

theorem rowSound2088_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row2088 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck2088, numericCheck2088, reducedZero2088 B hB hF, mul_zero]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedSourceBridge.rowSound2088_e_oai := @OAI.MUB6.Certificate.MixedSourceBridge.rowSound2088_e_oai
