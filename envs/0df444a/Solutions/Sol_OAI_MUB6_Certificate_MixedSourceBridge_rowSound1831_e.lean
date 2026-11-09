-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedSourceBridge.rowSound1831_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-08T21:51:00.408192+00:00
-- url     : https://prove2.me/submissions/91eb107c-10ce-4802-be47-0517c8d3f6b3

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E070
import Definitions.Def_OAIQ106E086
import Definitions.Def_OAIQ106E090
import Definitions.Def_OAIQ106E091
import Definitions.Def_OAIQ106E092
import Definitions.Def_OAIQ106E097
import Definitions.Def_OAIQ106E190
import Definitions.Def_OAIQ106E191
import Definitions.Def_OAIQ106E105
import Definitions.Def_OAIQ106E115
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

theorem canonical1392 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1392 raw1392Labels = mixedMoment B node4557 node4557Labels := by
  calc
    mixedMoment B raw1392 raw1392Labels = mixedMoment B raw1392step0 raw1392step0Labels := by
      have ha : raw1392step0 = (fun i j => raw1392 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1392step0 raw1392; decide +kernel
      have hl : raw1392step0Labels = raw1392Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1392 raw1392Labels permutation8 permutation4
    mixedMoment B raw1392step0 raw1392step0Labels = mixedMoment B raw1392step1 raw1392step1Labels := by
      have ha : raw1392step1 = raw1392step0 := by apply Matrix.ext; unfold raw1392step1 raw1392step0; decide +kernel
      have hl : raw1392step0Labels = labelEmbedding7 ∘ raw1392step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1392step0 raw1392step0Labels raw1392step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4557 node4557Labels := by rfl

theorem canonical1393 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1393 raw1393Labels = mixedMoment B node1143 node1143Labels := by
  calc
    mixedMoment B raw1393 raw1393Labels = mixedMoment B raw1393step0 raw1393step0Labels := by
      have ha : raw1393step0 = (fun i j => raw1393 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1393step0 raw1393; decide +kernel
      have hl : raw1393step0Labels = raw1393Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1393 raw1393Labels permutation8 permutation4
    _ = mixedMoment B node1143 node1143Labels := by rfl

theorem canonical1394 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1394 raw1394Labels = mixedMoment B node2167 node2167Labels := by
  calc
    mixedMoment B raw1394 raw1394Labels = mixedMoment B raw1394step0 raw1394step0Labels := by
      have ha : raw1394step0 = (fun i j => raw1394 (permutation31 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1394step0 raw1394; decide +kernel
      have hl : raw1394step0Labels = raw1394Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1394 raw1394Labels permutation31 permutation6
    mixedMoment B raw1394step0 raw1394step0Labels = mixedMoment B raw1394step1 raw1394step1Labels := by
      have ha : raw1394step1 = raw1394step0 := by apply Matrix.ext; unfold raw1394step1 raw1394step0; decide +kernel
      have hl : raw1394step0Labels = labelEmbedding1 ∘ raw1394step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1394step0 raw1394step0Labels raw1394step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2167 node2167Labels := by rfl

end MUB6.Certificate.MixedSemantics

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

theorem canonical1563 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1563 raw1563Labels = mixedMoment B node4681 node4681Labels := by
  calc
    mixedMoment B raw1563 raw1563Labels = mixedMoment B raw1563step0 raw1563step0Labels := by
      have ha : raw1563step0 = (fun i j => raw1563 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1563step0 raw1563; decide +kernel
      have hl : raw1563step0Labels = raw1563Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1563 raw1563Labels permutation32 permutation4
    mixedMoment B raw1563step0 raw1563step0Labels = mixedMoment B raw1563step1 raw1563step1Labels := by
      have ha : raw1563step1 = raw1563step0 := by apply Matrix.ext; unfold raw1563step1 raw1563step0; decide +kernel
      have hl : raw1563step0Labels = labelEmbedding7 ∘ raw1563step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1563step0 raw1563step0Labels raw1563step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4681 node4681Labels := by rfl

theorem canonical1564 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1564 raw1564Labels = mixedMoment B node1807 node1807Labels := by
  calc
    mixedMoment B raw1564 raw1564Labels = mixedMoment B raw1564step0 raw1564step0Labels := by
      have ha : raw1564step0 = (fun i j => raw1564 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1564step0 raw1564; decide +kernel
      have hl : raw1564step0Labels = raw1564Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1564 raw1564Labels permutation32 permutation4
    _ = mixedMoment B node1807 node1807Labels := by rfl

theorem canonical1565 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1565 raw1565Labels = mixedMoment B node2151 node2151Labels := by
  calc
    mixedMoment B raw1565 raw1565Labels = mixedMoment B raw1565step0 raw1565step0Labels := by
      have ha : raw1565step0 = (fun i j => raw1565 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1565step0 raw1565; decide +kernel
      have hl : raw1565step0Labels = raw1565Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1565 raw1565Labels permutation32 permutation6
    mixedMoment B raw1565step0 raw1565step0Labels = mixedMoment B raw1565step1 raw1565step1Labels := by
      have ha : raw1565step1 = -raw1565step0 := by apply Matrix.ext; change ∀ i j, raw1565step1 i j = -(raw1565step0 i j); unfold raw1565step1 raw1565step0; decide +kernel
      have hl : raw1565step1Labels = raw1565step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1565step1 raw1565step1Labels = mixedMoment B raw1565step2 raw1565step2Labels := by
      have ha : raw1565step2 = raw1565step1 := by apply Matrix.ext; unfold raw1565step2 raw1565step1; decide +kernel
      have hl : raw1565step1Labels = labelEmbedding1 ∘ raw1565step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1565step1 raw1565step1Labels raw1565step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2151 node2151Labels := by rfl

theorem canonical1584 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1584 raw1584Labels = mixedMoment B node4692 node4692Labels := by
  calc
    mixedMoment B raw1584 raw1584Labels = mixedMoment B raw1584step0 raw1584step0Labels := by
      have ha : raw1584step0 = (fun i j => raw1584 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1584step0 raw1584; decide +kernel
      have hl : raw1584step0Labels = raw1584Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1584 raw1584Labels permutation8 permutation4
    mixedMoment B raw1584step0 raw1584step0Labels = mixedMoment B raw1584step1 raw1584step1Labels := by
      have ha : raw1584step1 = raw1584step0 := by apply Matrix.ext; unfold raw1584step1 raw1584step0; decide +kernel
      have hl : raw1584step0Labels = labelEmbedding7 ∘ raw1584step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1584step0 raw1584step0Labels raw1584step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4692 node4692Labels := by rfl

theorem canonical1585 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1585 raw1585Labels = mixedMoment B node1818 node1818Labels := by
  calc
    mixedMoment B raw1585 raw1585Labels = mixedMoment B raw1585step0 raw1585step0Labels := by
      have ha : raw1585step0 = (fun i j => raw1585 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1585step0 raw1585; decide +kernel
      have hl : raw1585step0Labels = raw1585Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1585 raw1585Labels permutation8 permutation4
    _ = mixedMoment B node1818 node1818Labels := by rfl

theorem canonical1586 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1586 raw1586Labels = mixedMoment B node2168 node2168Labels := by
  calc
    mixedMoment B raw1586 raw1586Labels = mixedMoment B raw1586step0 raw1586step0Labels := by
      have ha : raw1586step0 = (fun i j => raw1586 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1586step0 raw1586; decide +kernel
      have hl : raw1586step0Labels = raw1586Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1586 raw1586Labels permutation8 permutation6
    mixedMoment B raw1586step0 raw1586step0Labels = mixedMoment B raw1586step1 raw1586step1Labels := by
      have ha : raw1586step1 = -raw1586step0 := by apply Matrix.ext; change ∀ i j, raw1586step1 i j = -(raw1586step0 i j); unfold raw1586step1 raw1586step0; decide +kernel
      have hl : raw1586step1Labels = raw1586step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1586step1 raw1586step1Labels = mixedMoment B raw1586step2 raw1586step2Labels := by
      have ha : raw1586step2 = raw1586step1 := by apply Matrix.ext; unfold raw1586step2 raw1586step1; decide +kernel
      have hl : raw1586step1Labels = labelEmbedding1 ∘ raw1586step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1586step1 raw1586step1Labels raw1586step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2168 node2168Labels := by rfl

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

theorem canonical2124 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2124 raw2124Labels = mixedMoment B node5099 node5099Labels := by
  calc
    mixedMoment B raw2124 raw2124Labels = mixedMoment B raw2124step0 raw2124step0Labels := by
      have ha : raw2124step0 = (fun i j => raw2124 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2124step0 raw2124; decide +kernel
      have hl : raw2124step0Labels = raw2124Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2124 raw2124Labels permutation32 permutation4
    mixedMoment B raw2124step0 raw2124step0Labels = mixedMoment B raw2124step1 raw2124step1Labels := by
      have ha : raw2124step1 = raw2124step0 := by apply Matrix.ext; unfold raw2124step1 raw2124step0; decide +kernel
      have hl : raw2124step0Labels = labelEmbedding7 ∘ raw2124step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2124step0 raw2124step0Labels raw2124step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5099 node5099Labels := by rfl

theorem canonical2125 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2125 raw2125Labels = mixedMoment B node2509 node2509Labels := by
  calc
    mixedMoment B raw2125 raw2125Labels = mixedMoment B raw2125step0 raw2125step0Labels := by
      have ha : raw2125step0 = (fun i j => raw2125 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2125step0 raw2125; decide +kernel
      have hl : raw2125step0Labels = raw2125Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2125 raw2125Labels permutation32 permutation4
    _ = mixedMoment B node2509 node2509Labels := by rfl

theorem canonical2126 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2126 raw2126Labels = mixedMoment B node2704 node2704Labels := by
  calc
    mixedMoment B raw2126 raw2126Labels = mixedMoment B raw2126step0 raw2126step0Labels := by
      have ha : raw2126step0 = (fun i j => raw2126 (permutation145 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2126step0 raw2126; decide +kernel
      have hl : raw2126step0Labels = raw2126Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2126 raw2126Labels permutation145 permutation6
    mixedMoment B raw2126step0 raw2126step0Labels = mixedMoment B raw2126step1 raw2126step1Labels := by
      have ha : raw2126step1 = raw2126step0 := by apply Matrix.ext; unfold raw2126step1 raw2126step0; decide +kernel
      have hl : raw2126step0Labels = labelEmbedding1 ∘ raw2126step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2126step0 raw2126step0Labels raw2126step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2704 node2704Labels := by rfl

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

theorem canonical2250 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2250 raw2250Labels = mixedMoment B node5228 node5228Labels := by
  calc
    mixedMoment B raw2250 raw2250Labels = mixedMoment B raw2250step0 raw2250step0Labels := by
      have ha : raw2250step0 = (fun i j => raw2250 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2250step0 raw2250; decide +kernel
      have hl : raw2250step0Labels = raw2250Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2250 raw2250Labels permutation32 permutation4
    mixedMoment B raw2250step0 raw2250step0Labels = mixedMoment B raw2250step1 raw2250step1Labels := by
      have ha : raw2250step1 = raw2250step0 := by apply Matrix.ext; unfold raw2250step1 raw2250step0; decide +kernel
      have hl : raw2250step0Labels = labelEmbedding7 ∘ raw2250step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2250step0 raw2250step0Labels raw2250step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5228 node5228Labels := by rfl

theorem canonical2251 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2251 raw2251Labels = mixedMoment B node2672 node2672Labels := by
  calc
    mixedMoment B raw2251 raw2251Labels = mixedMoment B raw2251step0 raw2251step0Labels := by
      have ha : raw2251step0 = (fun i j => raw2251 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2251step0 raw2251; decide +kernel
      have hl : raw2251step0Labels = raw2251Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2251 raw2251Labels permutation32 permutation4
    _ = mixedMoment B node2672 node2672Labels := by rfl

theorem canonical2252 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2252 raw2252Labels = mixedMoment B node3391 node3391Labels := by
  calc
    mixedMoment B raw2252 raw2252Labels = mixedMoment B raw2252step0 raw2252step0Labels := by
      have ha : raw2252step0 = (fun i j => raw2252 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2252step0 raw2252; decide +kernel
      have hl : raw2252step0Labels = raw2252Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2252 raw2252Labels permutation32 permutation6
    mixedMoment B raw2252step0 raw2252step0Labels = mixedMoment B raw2252step1 raw2252step1Labels := by
      have ha : raw2252step1 = -raw2252step0 := by apply Matrix.ext; change ∀ i j, raw2252step1 i j = -(raw2252step0 i j); unfold raw2252step1 raw2252step0; decide +kernel
      have hl : raw2252step1Labels = raw2252step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2252step1 raw2252step1Labels = mixedMoment B raw2252step2 raw2252step2Labels := by
      have ha : raw2252step2 = raw2252step1 := by apply Matrix.ext; unfold raw2252step2 raw2252step1; decide +kernel
      have hl : raw2252step1Labels = labelEmbedding1 ∘ raw2252step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2252step1 raw2252step1Labels raw2252step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3391 node3391Labels := by rfl

theorem canonical2256 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2256 raw2256Labels = mixedMoment B node5238 node5238Labels := by
  calc
    mixedMoment B raw2256 raw2256Labels = mixedMoment B raw2256step0 raw2256step0Labels := by
      have ha : raw2256step0 = (fun i j => raw2256 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2256step0 raw2256; decide +kernel
      have hl : raw2256step0Labels = raw2256Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2256 raw2256Labels permutation8 permutation4
    mixedMoment B raw2256step0 raw2256step0Labels = mixedMoment B raw2256step1 raw2256step1Labels := by
      have ha : raw2256step1 = raw2256step0 := by apply Matrix.ext; unfold raw2256step1 raw2256step0; decide +kernel
      have hl : raw2256step0Labels = labelEmbedding7 ∘ raw2256step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2256step0 raw2256step0Labels raw2256step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5238 node5238Labels := by rfl

theorem canonical2257 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2257 raw2257Labels = mixedMoment B node2686 node2686Labels := by
  calc
    mixedMoment B raw2257 raw2257Labels = mixedMoment B raw2257step0 raw2257step0Labels := by
      have ha : raw2257step0 = (fun i j => raw2257 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2257step0 raw2257; decide +kernel
      have hl : raw2257step0Labels = raw2257Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2257 raw2257Labels permutation8 permutation4
    _ = mixedMoment B node2686 node2686Labels := by rfl

theorem canonical2258 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2258 raw2258Labels = mixedMoment B node3397 node3397Labels := by
  calc
    mixedMoment B raw2258 raw2258Labels = mixedMoment B raw2258step0 raw2258step0Labels := by
      have ha : raw2258step0 = (fun i j => raw2258 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2258step0 raw2258; decide +kernel
      have hl : raw2258step0Labels = raw2258Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2258 raw2258Labels permutation8 permutation6
    mixedMoment B raw2258step0 raw2258step0Labels = mixedMoment B raw2258step1 raw2258step1Labels := by
      have ha : raw2258step1 = -raw2258step0 := by apply Matrix.ext; change ∀ i j, raw2258step1 i j = -(raw2258step0 i j); unfold raw2258step1 raw2258step0; decide +kernel
      have hl : raw2258step1Labels = raw2258step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2258step1 raw2258step1Labels = mixedMoment B raw2258step2 raw2258step2Labels := by
      have ha : raw2258step2 = raw2258step1 := by apply Matrix.ext; unfold raw2258step2 raw2258step1; decide +kernel
      have hl : raw2258step1Labels = labelEmbedding1 ∘ raw2258step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2258step1 raw2258step1Labels raw2258step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3397 node3397Labels := by rfl

theorem canonical2283 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2283 raw2283Labels = mixedMoment B node5272 node5272Labels := by
  calc
    mixedMoment B raw2283 raw2283Labels = mixedMoment B raw2283step0 raw2283step0Labels := by
      have ha : raw2283step0 = (fun i j => raw2283 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2283step0 raw2283; decide +kernel
      have hl : raw2283step0Labels = raw2283Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2283 raw2283Labels permutation8 permutation4
    mixedMoment B raw2283step0 raw2283step0Labels = mixedMoment B raw2283step1 raw2283step1Labels := by
      have ha : raw2283step1 = raw2283step0 := by apply Matrix.ext; unfold raw2283step1 raw2283step0; decide +kernel
      have hl : raw2283step0Labels = labelEmbedding7 ∘ raw2283step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2283step0 raw2283step0Labels raw2283step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5272 node5272Labels := by rfl

theorem canonical2284 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2284 raw2284Labels = mixedMoment B node2740 node2740Labels := by
  calc
    mixedMoment B raw2284 raw2284Labels = mixedMoment B raw2284step0 raw2284step0Labels := by
      have ha : raw2284step0 = (fun i j => raw2284 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2284step0 raw2284; decide +kernel
      have hl : raw2284step0Labels = raw2284Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2284 raw2284Labels permutation8 permutation4
    _ = mixedMoment B node2740 node2740Labels := by rfl

theorem canonical2285 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2285 raw2285Labels = mixedMoment B node2740 node2740Labels := by
  calc
    mixedMoment B raw2285 raw2285Labels = mixedMoment B raw2285step0 raw2285step0Labels := by
      have ha : raw2285step0 = (fun i j => raw2285 (permutation31 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2285step0 raw2285; decide +kernel
      have hl : raw2285step0Labels = raw2285Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2285 raw2285Labels permutation31 permutation6
    mixedMoment B raw2285step0 raw2285step0Labels = mixedMoment B raw2285step1 raw2285step1Labels := by
      have ha : raw2285step1 = raw2285step0 := by apply Matrix.ext; unfold raw2285step1 raw2285step0; decide +kernel
      have hl : raw2285step0Labels = labelEmbedding1 ∘ raw2285step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2285step0 raw2285step0Labels raw2285step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2740 node2740Labels := by rfl

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

theorem canonical2313 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2313 raw2313Labels = mixedMoment B node5302 node5302Labels := by
  calc
    mixedMoment B raw2313 raw2313Labels = mixedMoment B raw2313step0 raw2313step0Labels := by
      have ha : raw2313step0 = (fun i j => raw2313 (permutation8 i) (permutation5 j)) := by apply Matrix.ext; unfold raw2313step0 raw2313; decide +kernel
      have hl : raw2313step0Labels = raw2313Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2313 raw2313Labels permutation8 permutation5
    mixedMoment B raw2313step0 raw2313step0Labels = mixedMoment B raw2313step1 raw2313step1Labels := by
      have ha : raw2313step1 = raw2313step0 := by apply Matrix.ext; unfold raw2313step1 raw2313step0; decide +kernel
      have hl : raw2313step0Labels = labelEmbedding8 ∘ raw2313step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2313step0 raw2313step0Labels raw2313step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5302 node5302Labels := by rfl

theorem canonical2314 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2314 raw2314Labels = mixedMoment B node3054 node3054Labels := by
  calc
    mixedMoment B raw2314 raw2314Labels = mixedMoment B raw2314step0 raw2314step0Labels := by
      have ha : raw2314step0 = (fun i j => raw2314 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2314step0 raw2314; decide +kernel
      have hl : raw2314step0Labels = raw2314Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2314 raw2314Labels permutation8 permutation4
    _ = mixedMoment B node3054 node3054Labels := by rfl

theorem canonical2315 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2315 raw2315Labels = mixedMoment B node3626 node3626Labels := by
  calc
    mixedMoment B raw2315 raw2315Labels = mixedMoment B raw2315step0 raw2315step0Labels := by
      have ha : raw2315step0 = (fun i j => raw2315 (permutation11 i) (permutation3 j)) := by apply Matrix.ext; unfold raw2315step0 raw2315; decide +kernel
      have hl : raw2315step0Labels = raw2315Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2315 raw2315Labels permutation11 permutation3
    mixedMoment B raw2315step0 raw2315step0Labels = mixedMoment B raw2315step1 raw2315step1Labels := by
      have ha : raw2315step1 = -raw2315step0 := by apply Matrix.ext; change ∀ i j, raw2315step1 i j = -(raw2315step0 i j); unfold raw2315step1 raw2315step0; decide +kernel
      have hl : raw2315step1Labels = raw2315step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2315step1 raw2315step1Labels = mixedMoment B raw2315step2 raw2315step2Labels := by
      have ha : raw2315step2 = raw2315step1 := by apply Matrix.ext; unfold raw2315step2 raw2315step1; decide +kernel
      have hl : raw2315step1Labels = labelEmbedding1 ∘ raw2315step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2315step1 raw2315step1Labels raw2315step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3626 node3626Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical239
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical30601 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30601 raw30601Labels = mixedMoment B node5238 node5238Labels := by
  calc
    mixedMoment B raw30601 raw30601Labels = mixedMoment B raw30601step0 raw30601step0Labels := by
      have hz : ∀ j, raw30601 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30601step0 = (fun i j => raw30601 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30601step0 raw30601; decide +kernel
      have hl : raw30601step0Labels = raw30601Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30601 raw30601Labels permutation434 hz
    mixedMoment B raw30601step0 raw30601step0Labels = mixedMoment B raw30601step1 raw30601step1Labels := by
      have hz : ∀ j, raw30601step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw30601step1 = (fun i j => raw30601step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw30601step1 raw30601step0; decide +kernel
      have hl : raw30601step1Labels = raw30601step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30601step0 raw30601step0Labels permutation80 hz
    mixedMoment B raw30601step1 raw30601step1Labels = mixedMoment B raw30601step2 raw30601step2Labels := by
      have ha : raw30601step2 = (fun i j => raw30601step1 (permutation25 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30601step2 raw30601step1; decide +kernel
      have hl : raw30601step2Labels = raw30601step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30601step1 raw30601step1Labels permutation25 permutation7
    mixedMoment B raw30601step2 raw30601step2Labels = mixedMoment B raw30601step3 raw30601step3Labels := by
      have ha : raw30601step3 = raw30601step2 := by apply Matrix.ext; unfold raw30601step3 raw30601step2; decide +kernel
      have hl : raw30601step2Labels = labelEmbedding10 ∘ raw30601step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30601step2 raw30601step2Labels raw30601step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5238 node5238Labels := by rfl

theorem canonical30602 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30602 raw30602Labels = mixedMoment B node5228 node5228Labels := by
  calc
    mixedMoment B raw30602 raw30602Labels = mixedMoment B raw30602step0 raw30602step0Labels := by
      have hz : ∀ j, raw30602 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30602step0 = (fun i j => raw30602 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30602step0 raw30602; decide +kernel
      have hl : raw30602step0Labels = raw30602Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30602 raw30602Labels permutation434 hz
    mixedMoment B raw30602step0 raw30602step0Labels = mixedMoment B raw30602step1 raw30602step1Labels := by
      have ha : raw30602step1 = (fun i j => raw30602step0 (permutation127 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30602step1 raw30602step0; decide +kernel
      have hl : raw30602step1Labels = raw30602step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30602step0 raw30602step0Labels permutation127 permutation7
    mixedMoment B raw30602step1 raw30602step1Labels = mixedMoment B raw30602step2 raw30602step2Labels := by
      have ha : raw30602step2 = raw30602step1 := by apply Matrix.ext; unfold raw30602step2 raw30602step1; decide +kernel
      have hl : raw30602step1Labels = labelEmbedding10 ∘ raw30602step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30602step1 raw30602step1Labels raw30602step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5228 node5228Labels := by rfl

theorem canonical30603 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30603 raw30603Labels = mixedMoment B node5228 node5228Labels := by
  calc
    mixedMoment B raw30603 raw30603Labels = mixedMoment B raw30603step0 raw30603step0Labels := by
      have hz : ∀ j, raw30603 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30603step0 = (fun i j => raw30603 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30603step0 raw30603; decide +kernel
      have hl : raw30603step0Labels = raw30603Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30603 raw30603Labels permutation346 hz
    mixedMoment B raw30603step0 raw30603step0Labels = mixedMoment B raw30603step1 raw30603step1Labels := by
      have ha : raw30603step1 = (fun i j => raw30603step0 (permutation127 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30603step1 raw30603step0; decide +kernel
      have hl : raw30603step1Labels = raw30603step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30603step0 raw30603step0Labels permutation127 permutation7
    mixedMoment B raw30603step1 raw30603step1Labels = mixedMoment B raw30603step2 raw30603step2Labels := by
      have ha : raw30603step2 = raw30603step1 := by apply Matrix.ext; unfold raw30603step2 raw30603step1; decide +kernel
      have hl : raw30603step1Labels = labelEmbedding10 ∘ raw30603step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30603step1 raw30603step1Labels raw30603step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5228 node5228Labels := by rfl

theorem canonical30604 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30604 raw30604Labels = mixedMoment B node5274 node5274Labels := by
  calc
    mixedMoment B raw30604 raw30604Labels = mixedMoment B raw30604step0 raw30604step0Labels := by
      have hz : ∀ j, raw30604 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30604step0 = (fun i j => raw30604 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30604step0 raw30604; decide +kernel
      have hl : raw30604step0Labels = raw30604Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30604 raw30604Labels permutation434 hz
    mixedMoment B raw30604step0 raw30604step0Labels = mixedMoment B raw30604step1 raw30604step1Labels := by
      have hz : ∀ j, raw30604step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw30604step1 = (fun i j => raw30604step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw30604step1 raw30604step0; decide +kernel
      have hl : raw30604step1Labels = raw30604step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30604step0 raw30604step0Labels permutation80 hz
    mixedMoment B raw30604step1 raw30604step1Labels = mixedMoment B raw30604step2 raw30604step2Labels := by
      have ha : raw30604step2 = (fun i j => raw30604step1 (permutation25 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30604step2 raw30604step1; decide +kernel
      have hl : raw30604step2Labels = raw30604step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30604step1 raw30604step1Labels permutation25 permutation7
    mixedMoment B raw30604step2 raw30604step2Labels = mixedMoment B raw30604step3 raw30604step3Labels := by
      have ha : raw30604step3 = raw30604step2 := by apply Matrix.ext; unfold raw30604step3 raw30604step2; decide +kernel
      have hl : raw30604step2Labels = labelEmbedding10 ∘ raw30604step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30604step2 raw30604step2Labels raw30604step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5274 node5274Labels := by rfl

theorem canonical30605 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30605 raw30605Labels = mixedMoment B node5276 node5276Labels := by
  calc
    mixedMoment B raw30605 raw30605Labels = mixedMoment B raw30605step0 raw30605step0Labels := by
      have hz : ∀ j, raw30605 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30605step0 = (fun i j => raw30605 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30605step0 raw30605; decide +kernel
      have hl : raw30605step0Labels = raw30605Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30605 raw30605Labels permutation434 hz
    mixedMoment B raw30605step0 raw30605step0Labels = mixedMoment B raw30605step1 raw30605step1Labels := by
      have hz : ∀ j, raw30605step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw30605step1 = (fun i j => raw30605step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw30605step1 raw30605step0; decide +kernel
      have hl : raw30605step1Labels = raw30605step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30605step0 raw30605step0Labels permutation80 hz
    _ = mixedMoment B node5276 node5276Labels := by rfl

theorem canonical30606 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30606 raw30606Labels = mixedMoment B node4548 node4548Labels := by
  calc
    mixedMoment B raw30606 raw30606Labels = mixedMoment B raw30606step0 raw30606step0Labels := by
      have hz : ∀ j, raw30606 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30606step0 = (fun i j => raw30606 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30606step0 raw30606; decide +kernel
      have hl : raw30606step0Labels = raw30606Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30606 raw30606Labels permutation434 hz
    mixedMoment B raw30606step0 raw30606step0Labels = mixedMoment B raw30606step1 raw30606step1Labels := by
      have ha : raw30606step1 = (fun i j => raw30606step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30606step1 raw30606step0; decide +kernel
      have hl : raw30606step1Labels = raw30606step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30606step0 raw30606step0Labels permutation33 permutation2
    _ = mixedMoment B node4548 node4548Labels := by rfl

theorem canonical30607 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30607 raw30607Labels = mixedMoment B node4945 node4945Labels := by
  calc
    mixedMoment B raw30607 raw30607Labels = mixedMoment B raw30607step0 raw30607step0Labels := by
      have hz : ∀ j, raw30607 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30607step0 = (fun i j => raw30607 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30607step0 raw30607; decide +kernel
      have hl : raw30607step0Labels = raw30607Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30607 raw30607Labels permutation434 hz
    mixedMoment B raw30607step0 raw30607step0Labels = mixedMoment B raw30607step1 raw30607step1Labels := by
      have ha : raw30607step1 = (fun i j => raw30607step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30607step1 raw30607step0; decide +kernel
      have hl : raw30607step1Labels = raw30607step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30607step0 raw30607step0Labels permutation33 permutation2
    _ = mixedMoment B node4945 node4945Labels := by rfl

theorem canonical30608 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30608 raw30608Labels = mixedMoment B node5035 node5035Labels := by
  calc
    mixedMoment B raw30608 raw30608Labels = mixedMoment B raw30608step0 raw30608step0Labels := by
      have ha : raw30608step0 = (fun i j => raw30608 (permutation159 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30608step0 raw30608; decide +kernel
      have hl : raw30608step0Labels = raw30608Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30608 raw30608Labels permutation159 permutation2
    _ = mixedMoment B node5035 node5035Labels := by rfl

theorem canonical30609 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30609 raw30609Labels = mixedMoment B node5099 node5099Labels := by
  calc
    mixedMoment B raw30609 raw30609Labels = mixedMoment B raw30609step0 raw30609step0Labels := by
      have hz : ∀ j, raw30609 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30609step0 = (fun i j => raw30609 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30609step0 raw30609; decide +kernel
      have hl : raw30609step0Labels = raw30609Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30609 raw30609Labels permutation434 hz
    mixedMoment B raw30609step0 raw30609step0Labels = mixedMoment B raw30609step1 raw30609step1Labels := by
      have ha : raw30609step1 = (fun i j => raw30609step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30609step1 raw30609step0; decide +kernel
      have hl : raw30609step1Labels = raw30609step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30609step0 raw30609step0Labels permutation33 permutation2
    _ = mixedMoment B node5099 node5099Labels := by rfl

theorem canonical30610 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30610 raw30610Labels = mixedMoment B node4548 node4548Labels := by
  calc
    mixedMoment B raw30610 raw30610Labels = mixedMoment B raw30610step0 raw30610step0Labels := by
      have hz : ∀ j, raw30610 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30610step0 = (fun i j => raw30610 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30610step0 raw30610; decide +kernel
      have hl : raw30610step0Labels = raw30610Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30610 raw30610Labels permutation346 hz
    mixedMoment B raw30610step0 raw30610step0Labels = mixedMoment B raw30610step1 raw30610step1Labels := by
      have ha : raw30610step1 = (fun i j => raw30610step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30610step1 raw30610step0; decide +kernel
      have hl : raw30610step1Labels = raw30610step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30610step0 raw30610step0Labels permutation33 permutation2
    _ = mixedMoment B node4548 node4548Labels := by rfl

theorem canonical30611 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30611 raw30611Labels = mixedMoment B node4945 node4945Labels := by
  calc
    mixedMoment B raw30611 raw30611Labels = mixedMoment B raw30611step0 raw30611step0Labels := by
      have hz : ∀ j, raw30611 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30611step0 = (fun i j => raw30611 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30611step0 raw30611; decide +kernel
      have hl : raw30611step0Labels = raw30611Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30611 raw30611Labels permutation346 hz
    mixedMoment B raw30611step0 raw30611step0Labels = mixedMoment B raw30611step1 raw30611step1Labels := by
      have ha : raw30611step1 = (fun i j => raw30611step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30611step1 raw30611step0; decide +kernel
      have hl : raw30611step1Labels = raw30611step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30611step0 raw30611step0Labels permutation33 permutation2
    _ = mixedMoment B node4945 node4945Labels := by rfl

theorem canonical30612 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30612 raw30612Labels = mixedMoment B node5035 node5035Labels := by
  calc
    mixedMoment B raw30612 raw30612Labels = mixedMoment B raw30612step0 raw30612step0Labels := by
      have ha : raw30612step0 = (fun i j => raw30612 (permutation153 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30612step0 raw30612; decide +kernel
      have hl : raw30612step0Labels = raw30612Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30612 raw30612Labels permutation153 permutation2
    _ = mixedMoment B node5035 node5035Labels := by rfl

theorem canonical30613 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30613 raw30613Labels = mixedMoment B node5099 node5099Labels := by
  calc
    mixedMoment B raw30613 raw30613Labels = mixedMoment B raw30613step0 raw30613step0Labels := by
      have hz : ∀ j, raw30613 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30613step0 = (fun i j => raw30613 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30613step0 raw30613; decide +kernel
      have hl : raw30613step0Labels = raw30613Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30613 raw30613Labels permutation346 hz
    mixedMoment B raw30613step0 raw30613step0Labels = mixedMoment B raw30613step1 raw30613step1Labels := by
      have ha : raw30613step1 = (fun i j => raw30613step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30613step1 raw30613step0; decide +kernel
      have hl : raw30613step1Labels = raw30613step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30613step0 raw30613step0Labels permutation33 permutation2
    _ = mixedMoment B node5099 node5099Labels := by rfl

theorem canonical30614 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30614 raw30614Labels = mixedMoment B node4557 node4557Labels := by
  calc
    mixedMoment B raw30614 raw30614Labels = mixedMoment B raw30614step0 raw30614step0Labels := by
      have hz : ∀ j, raw30614 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30614step0 = (fun i j => raw30614 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30614step0 raw30614; decide +kernel
      have hl : raw30614step0Labels = raw30614Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30614 raw30614Labels permutation434 hz
    mixedMoment B raw30614step0 raw30614step0Labels = mixedMoment B raw30614step1 raw30614step1Labels := by
      have hz : ∀ j, raw30614step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw30614step1 = (fun i j => raw30614step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw30614step1 raw30614step0; decide +kernel
      have hl : raw30614step1Labels = raw30614step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30614step0 raw30614step0Labels permutation80 hz
    mixedMoment B raw30614step1 raw30614step1Labels = mixedMoment B raw30614step2 raw30614step2Labels := by
      have ha : raw30614step2 = (fun i j => raw30614step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30614step2 raw30614step1; decide +kernel
      have hl : raw30614step2Labels = raw30614step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30614step1 raw30614step1Labels permutation9 permutation2
    _ = mixedMoment B node4557 node4557Labels := by rfl

theorem canonical30615 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30615 raw30615Labels = mixedMoment B node4692 node4692Labels := by
  calc
    mixedMoment B raw30615 raw30615Labels = mixedMoment B raw30615step0 raw30615step0Labels := by
      have hz : ∀ j, raw30615 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30615step0 = (fun i j => raw30615 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30615step0 raw30615; decide +kernel
      have hl : raw30615step0Labels = raw30615Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30615 raw30615Labels permutation434 hz
    mixedMoment B raw30615step0 raw30615step0Labels = mixedMoment B raw30615step1 raw30615step1Labels := by
      have hz : ∀ j, raw30615step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw30615step1 = (fun i j => raw30615step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw30615step1 raw30615step0; decide +kernel
      have hl : raw30615step1Labels = raw30615step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30615step0 raw30615step0Labels permutation80 hz
    mixedMoment B raw30615step1 raw30615step1Labels = mixedMoment B raw30615step2 raw30615step2Labels := by
      have ha : raw30615step2 = (fun i j => raw30615step1 (permutation25 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30615step2 raw30615step1; decide +kernel
      have hl : raw30615step2Labels = raw30615step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30615step1 raw30615step1Labels permutation25 permutation2
    mixedMoment B raw30615step2 raw30615step2Labels = mixedMoment B raw30615step3 raw30615step3Labels := by
      have ha : raw30615step3 = -raw30615step2 := by apply Matrix.ext; change ∀ i j, raw30615step3 i j = -(raw30615step2 i j); unfold raw30615step3 raw30615step2; decide +kernel
      have hl : raw30615step3Labels = raw30615step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4692 node4692Labels := by rfl

theorem canonical30616 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30616 raw30616Labels = mixedMoment B node4681 node4681Labels := by
  calc
    mixedMoment B raw30616 raw30616Labels = mixedMoment B raw30616step0 raw30616step0Labels := by
      have hz : ∀ j, raw30616 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30616step0 = (fun i j => raw30616 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30616step0 raw30616; decide +kernel
      have hl : raw30616step0Labels = raw30616Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30616 raw30616Labels permutation434 hz
    mixedMoment B raw30616step0 raw30616step0Labels = mixedMoment B raw30616step1 raw30616step1Labels := by
      have ha : raw30616step1 = (fun i j => raw30616step0 (permutation127 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30616step1 raw30616step0; decide +kernel
      have hl : raw30616step1Labels = raw30616step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30616step0 raw30616step0Labels permutation127 permutation2
    mixedMoment B raw30616step1 raw30616step1Labels = mixedMoment B raw30616step2 raw30616step2Labels := by
      have ha : raw30616step2 = -raw30616step1 := by apply Matrix.ext; change ∀ i j, raw30616step2 i j = -(raw30616step1 i j); unfold raw30616step2 raw30616step1; decide +kernel
      have hl : raw30616step2Labels = raw30616step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4681 node4681Labels := by rfl

theorem canonical30617 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30617 raw30617Labels = mixedMoment B node4681 node4681Labels := by
  calc
    mixedMoment B raw30617 raw30617Labels = mixedMoment B raw30617step0 raw30617step0Labels := by
      have hz : ∀ j, raw30617 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30617step0 = (fun i j => raw30617 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30617step0 raw30617; decide +kernel
      have hl : raw30617step0Labels = raw30617Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30617 raw30617Labels permutation346 hz
    mixedMoment B raw30617step0 raw30617step0Labels = mixedMoment B raw30617step1 raw30617step1Labels := by
      have ha : raw30617step1 = (fun i j => raw30617step0 (permutation127 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30617step1 raw30617step0; decide +kernel
      have hl : raw30617step1Labels = raw30617step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30617step0 raw30617step0Labels permutation127 permutation2
    mixedMoment B raw30617step1 raw30617step1Labels = mixedMoment B raw30617step2 raw30617step2Labels := by
      have ha : raw30617step2 = -raw30617step1 := by apply Matrix.ext; change ∀ i j, raw30617step2 i j = -(raw30617step1 i j); unfold raw30617step2 raw30617step1; decide +kernel
      have hl : raw30617step2Labels = raw30617step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4681 node4681Labels := by rfl

theorem canonical30618 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30618 raw30618Labels = mixedMoment B node4841 node4841Labels := by
  calc
    mixedMoment B raw30618 raw30618Labels = mixedMoment B raw30618step0 raw30618step0Labels := by
      have hz : ∀ j, raw30618 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30618step0 = (fun i j => raw30618 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30618step0 raw30618; decide +kernel
      have hl : raw30618step0Labels = raw30618Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30618 raw30618Labels permutation434 hz
    mixedMoment B raw30618step0 raw30618step0Labels = mixedMoment B raw30618step1 raw30618step1Labels := by
      have hz : ∀ j, raw30618step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw30618step1 = (fun i j => raw30618step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw30618step1 raw30618step0; decide +kernel
      have hl : raw30618step1Labels = raw30618step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30618step0 raw30618step0Labels permutation80 hz
    mixedMoment B raw30618step1 raw30618step1Labels = mixedMoment B raw30618step2 raw30618step2Labels := by
      have ha : raw30618step2 = (fun i j => raw30618step1 (permutation25 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30618step2 raw30618step1; decide +kernel
      have hl : raw30618step2Labels = raw30618step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30618step1 raw30618step1Labels permutation25 permutation2
    mixedMoment B raw30618step2 raw30618step2Labels = mixedMoment B raw30618step3 raw30618step3Labels := by
      have ha : raw30618step3 = -raw30618step2 := by apply Matrix.ext; change ∀ i j, raw30618step3 i j = -(raw30618step2 i j); unfold raw30618step3 raw30618step2; decide +kernel
      have hl : raw30618step3Labels = raw30618step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4841 node4841Labels := by rfl

theorem canonical30619 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30619 raw30619Labels = mixedMoment B node4560 node4560Labels := by
  calc
    mixedMoment B raw30619 raw30619Labels = mixedMoment B raw30619step0 raw30619step0Labels := by
      have hz : ∀ j, raw30619 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30619step0 = (fun i j => raw30619 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30619step0 raw30619; decide +kernel
      have hl : raw30619step0Labels = raw30619Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30619 raw30619Labels permutation434 hz
    mixedMoment B raw30619step0 raw30619step0Labels = mixedMoment B raw30619step1 raw30619step1Labels := by
      have hz : ∀ j, raw30619step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw30619step1 = (fun i j => raw30619step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw30619step1 raw30619step0; decide +kernel
      have hl : raw30619step1Labels = raw30619step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30619step0 raw30619step0Labels permutation80 hz
    _ = mixedMoment B node4560 node4560Labels := by rfl

theorem canonical30620 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30620 raw30620Labels = mixedMoment B node4705 node4705Labels := by
  calc
    mixedMoment B raw30620 raw30620Labels = mixedMoment B raw30620step0 raw30620step0Labels := by
      have hz : ∀ j, raw30620 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30620step0 = (fun i j => raw30620 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30620step0 raw30620; decide +kernel
      have hl : raw30620step0Labels = raw30620Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30620 raw30620Labels permutation434 hz
    mixedMoment B raw30620step0 raw30620step0Labels = mixedMoment B raw30620step1 raw30620step1Labels := by
      have hz : ∀ j, raw30620step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw30620step1 = (fun i j => raw30620step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw30620step1 raw30620step0; decide +kernel
      have hl : raw30620step1Labels = raw30620step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30620step0 raw30620step0Labels permutation80 hz
    mixedMoment B raw30620step1 raw30620step1Labels = mixedMoment B raw30620step2 raw30620step2Labels := by
      have ha : raw30620step2 = (fun i j => raw30620step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw30620step2 raw30620step1; decide +kernel
      have hl : raw30620step2Labels = raw30620step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30620step1 raw30620step1Labels permutation31 permutation3
    mixedMoment B raw30620step2 raw30620step2Labels = mixedMoment B raw30620step3 raw30620step3Labels := by
      have ha : raw30620step3 = -raw30620step2 := by apply Matrix.ext; change ∀ i j, raw30620step3 i j = -(raw30620step2 i j); unfold raw30620step3 raw30620step2; decide +kernel
      have hl : raw30620step3Labels = raw30620step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30620step3 raw30620step3Labels = mixedMoment B raw30620step4 raw30620step4Labels := by
      have ha : raw30620step4 = raw30620step3 := by apply Matrix.ext; unfold raw30620step4 raw30620step3; decide +kernel
      have hl : raw30620step3Labels = labelEmbedding6 ∘ raw30620step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30620step3 raw30620step3Labels raw30620step4Labels labelEmbedding6 hl
    _ = mixedMoment B node4705 node4705Labels := by rfl

theorem canonical30621 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30621 raw30621Labels = mixedMoment B node4699 node4699Labels := by
  calc
    mixedMoment B raw30621 raw30621Labels = mixedMoment B raw30621step0 raw30621step0Labels := by
      have hz : ∀ j, raw30621 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30621step0 = (fun i j => raw30621 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30621step0 raw30621; decide +kernel
      have hl : raw30621step0Labels = raw30621Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30621 raw30621Labels permutation434 hz
    mixedMoment B raw30621step0 raw30621step0Labels = mixedMoment B raw30621step1 raw30621step1Labels := by
      have ha : raw30621step1 = (fun i j => raw30621step0 (permutation149 i) (permutation3 j)) := by apply Matrix.ext; unfold raw30621step1 raw30621step0; decide +kernel
      have hl : raw30621step1Labels = raw30621step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30621step0 raw30621step0Labels permutation149 permutation3
    mixedMoment B raw30621step1 raw30621step1Labels = mixedMoment B raw30621step2 raw30621step2Labels := by
      have ha : raw30621step2 = -raw30621step1 := by apply Matrix.ext; change ∀ i j, raw30621step2 i j = -(raw30621step1 i j); unfold raw30621step2 raw30621step1; decide +kernel
      have hl : raw30621step2Labels = raw30621step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30621step2 raw30621step2Labels = mixedMoment B raw30621step3 raw30621step3Labels := by
      have ha : raw30621step3 = raw30621step2 := by apply Matrix.ext; unfold raw30621step3 raw30621step2; decide +kernel
      have hl : raw30621step2Labels = labelEmbedding6 ∘ raw30621step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30621step2 raw30621step2Labels raw30621step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4699 node4699Labels := by rfl

theorem canonical30622 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30622 raw30622Labels = mixedMoment B node4699 node4699Labels := by
  calc
    mixedMoment B raw30622 raw30622Labels = mixedMoment B raw30622step0 raw30622step0Labels := by
      have hz : ∀ j, raw30622 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30622step0 = (fun i j => raw30622 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30622step0 raw30622; decide +kernel
      have hl : raw30622step0Labels = raw30622Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30622 raw30622Labels permutation346 hz
    mixedMoment B raw30622step0 raw30622step0Labels = mixedMoment B raw30622step1 raw30622step1Labels := by
      have ha : raw30622step1 = (fun i j => raw30622step0 (permutation149 i) (permutation3 j)) := by apply Matrix.ext; unfold raw30622step1 raw30622step0; decide +kernel
      have hl : raw30622step1Labels = raw30622step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30622step0 raw30622step0Labels permutation149 permutation3
    mixedMoment B raw30622step1 raw30622step1Labels = mixedMoment B raw30622step2 raw30622step2Labels := by
      have ha : raw30622step2 = -raw30622step1 := by apply Matrix.ext; change ∀ i j, raw30622step2 i j = -(raw30622step1 i j); unfold raw30622step2 raw30622step1; decide +kernel
      have hl : raw30622step2Labels = raw30622step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30622step2 raw30622step2Labels = mixedMoment B raw30622step3 raw30622step3Labels := by
      have ha : raw30622step3 = raw30622step2 := by apply Matrix.ext; unfold raw30622step3 raw30622step2; decide +kernel
      have hl : raw30622step2Labels = labelEmbedding6 ∘ raw30622step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30622step2 raw30622step2Labels raw30622step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4699 node4699Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical45
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical5771 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5771 raw5771Labels = mixedMoment B node5302 node5302Labels := by
  calc
    mixedMoment B raw5771 raw5771Labels = mixedMoment B raw5771step0 raw5771step0Labels := by
      have hz : ∀ j, raw5771 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5771step0 = (fun i j => raw5771 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5771step0 raw5771; decide +kernel
      have hl : raw5771step0Labels = raw5771Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5771 raw5771Labels permutation434 hz
    mixedMoment B raw5771step0 raw5771step0Labels = mixedMoment B raw5771step1 raw5771step1Labels := by
      have hz : ∀ j, raw5771step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5771step1 = (fun i j => raw5771step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5771step1 raw5771step0; decide +kernel
      have hl : raw5771step1Labels = raw5771step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5771step0 raw5771step0Labels permutation80 hz
    mixedMoment B raw5771step1 raw5771step1Labels = mixedMoment B raw5771step2 raw5771step2Labels := by
      have ha : raw5771step2 = (fun i j => raw5771step1 (permutation25 i) (permutation6 j)) := by apply Matrix.ext; unfold raw5771step2 raw5771step1; decide +kernel
      have hl : raw5771step2Labels = raw5771step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5771step1 raw5771step1Labels permutation25 permutation6
    mixedMoment B raw5771step2 raw5771step2Labels = mixedMoment B raw5771step3 raw5771step3Labels := by
      have ha : raw5771step3 = raw5771step2 := by apply Matrix.ext; unfold raw5771step3 raw5771step2; decide +kernel
      have hl : raw5771step2Labels = labelEmbedding9 ∘ raw5771step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5771step2 raw5771step2Labels raw5771step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5302 node5302Labels := by rfl

theorem canonical5782 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5782 raw5782Labels = mixedMoment B node5103 node5103Labels := by
  calc
    mixedMoment B raw5782 raw5782Labels = mixedMoment B raw5782step0 raw5782step0Labels := by
      have hz : ∀ j, raw5782 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5782step0 = (fun i j => raw5782 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5782step0 raw5782; decide +kernel
      have hl : raw5782step0Labels = raw5782Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5782 raw5782Labels permutation434 hz
    _ = mixedMoment B node5103 node5103Labels := by rfl

theorem canonical5787 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5787 raw5787Labels = mixedMoment B node5103 node5103Labels := by
  calc
    mixedMoment B raw5787 raw5787Labels = mixedMoment B raw5787step0 raw5787step0Labels := by
      have hz : ∀ j, raw5787 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw5787step0 = (fun i j => raw5787 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw5787step0 raw5787; decide +kernel
      have hl : raw5787step0Labels = raw5787Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5787 raw5787Labels permutation346 hz
    _ = mixedMoment B node5103 node5103Labels := by rfl

theorem canonical5791 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5791 raw5791Labels = mixedMoment B node4611 node4611Labels := by
  calc
    mixedMoment B raw5791 raw5791Labels = mixedMoment B raw5791step0 raw5791step0Labels := by
      have hz : ∀ j, raw5791 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5791step0 = (fun i j => raw5791 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5791step0 raw5791; decide +kernel
      have hl : raw5791step0Labels = raw5791Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5791 raw5791Labels permutation434 hz
    mixedMoment B raw5791step0 raw5791step0Labels = mixedMoment B raw5791step1 raw5791step1Labels := by
      have hz : ∀ j, raw5791step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5791step1 = (fun i j => raw5791step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5791step1 raw5791step0; decide +kernel
      have hl : raw5791step1Labels = raw5791step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5791step0 raw5791step0Labels permutation80 hz
    mixedMoment B raw5791step1 raw5791step1Labels = mixedMoment B raw5791step2 raw5791step2Labels := by
      have ha : raw5791step2 = (fun i j => raw5791step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5791step2 raw5791step1; decide +kernel
      have hl : raw5791step2Labels = raw5791step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5791step1 raw5791step1Labels permutation9 permutation2
    _ = mixedMoment B node4611 node4611Labels := by rfl

theorem canonical5793 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5793 raw5793Labels = mixedMoment B node5140 node5140Labels := by
  calc
    mixedMoment B raw5793 raw5793Labels = mixedMoment B raw5793step0 raw5793step0Labels := by
      have hz : ∀ j, raw5793 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5793step0 = (fun i j => raw5793 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5793step0 raw5793; decide +kernel
      have hl : raw5793step0Labels = raw5793Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5793 raw5793Labels permutation434 hz
    mixedMoment B raw5793step0 raw5793step0Labels = mixedMoment B raw5793step1 raw5793step1Labels := by
      have ha : raw5793step1 = (fun i j => raw5793step0 (permutation39 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5793step1 raw5793step0; decide +kernel
      have hl : raw5793step1Labels = raw5793step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5793step0 raw5793step0Labels permutation39 permutation2
    _ = mixedMoment B node5140 node5140Labels := by rfl

theorem canonical5794 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5794 raw5794Labels = mixedMoment B node5140 node5140Labels := by
  calc
    mixedMoment B raw5794 raw5794Labels = mixedMoment B raw5794step0 raw5794step0Labels := by
      have hz : ∀ j, raw5794 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw5794step0 = (fun i j => raw5794 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw5794step0 raw5794; decide +kernel
      have hl : raw5794step0Labels = raw5794Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5794 raw5794Labels permutation346 hz
    mixedMoment B raw5794step0 raw5794step0Labels = mixedMoment B raw5794step1 raw5794step1Labels := by
      have ha : raw5794step1 = (fun i j => raw5794step0 (permutation39 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5794step1 raw5794step0; decide +kernel
      have hl : raw5794step1Labels = raw5794step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5794step0 raw5794step0Labels permutation39 permutation2
    _ = mixedMoment B node5140 node5140Labels := by rfl

theorem canonical5795 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5795 raw5795Labels = mixedMoment B node5272 node5272Labels := by
  calc
    mixedMoment B raw5795 raw5795Labels = mixedMoment B raw5795step0 raw5795step0Labels := by
      have hz : ∀ j, raw5795 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5795step0 = (fun i j => raw5795 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5795step0 raw5795; decide +kernel
      have hl : raw5795step0Labels = raw5795Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5795 raw5795Labels permutation434 hz
    mixedMoment B raw5795step0 raw5795step0Labels = mixedMoment B raw5795step1 raw5795step1Labels := by
      have hz : ∀ j, raw5795step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5795step1 = (fun i j => raw5795step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5795step1 raw5795step0; decide +kernel
      have hl : raw5795step1Labels = raw5795step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5795step0 raw5795step0Labels permutation80 hz
    mixedMoment B raw5795step1 raw5795step1Labels = mixedMoment B raw5795step2 raw5795step2Labels := by
      have ha : raw5795step2 = (fun i j => raw5795step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5795step2 raw5795step1; decide +kernel
      have hl : raw5795step2Labels = raw5795step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5795step1 raw5795step1Labels permutation9 permutation2
    _ = mixedMoment B node5272 node5272Labels := by rfl

theorem canonical5797 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5797 raw5797Labels = mixedMoment B node4881 node4881Labels := by
  calc
    mixedMoment B raw5797 raw5797Labels = mixedMoment B raw5797step0 raw5797step0Labels := by
      have hz : ∀ j, raw5797 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5797step0 = (fun i j => raw5797 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5797step0 raw5797; decide +kernel
      have hl : raw5797step0Labels = raw5797Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5797 raw5797Labels permutation434 hz
    mixedMoment B raw5797step0 raw5797step0Labels = mixedMoment B raw5797step1 raw5797step1Labels := by
      have hz : ∀ j, raw5797step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5797step1 = (fun i j => raw5797step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5797step1 raw5797step0; decide +kernel
      have hl : raw5797step1Labels = raw5797step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5797step0 raw5797step0Labels permutation80 hz
    mixedMoment B raw5797step1 raw5797step1Labels = mixedMoment B raw5797step2 raw5797step2Labels := by
      have ha : raw5797step2 = (fun i j => raw5797step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw5797step2 raw5797step1; decide +kernel
      have hl : raw5797step2Labels = raw5797step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5797step1 raw5797step1Labels permutation31 permutation3
    mixedMoment B raw5797step2 raw5797step2Labels = mixedMoment B raw5797step3 raw5797step3Labels := by
      have ha : raw5797step3 = -raw5797step2 := by apply Matrix.ext; change ∀ i j, raw5797step3 i j = -(raw5797step2 i j); unfold raw5797step3 raw5797step2; decide +kernel
      have hl : raw5797step3Labels = raw5797step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw5797step3 raw5797step3Labels = mixedMoment B raw5797step4 raw5797step4Labels := by
      have ha : raw5797step4 = raw5797step3 := by apply Matrix.ext; unfold raw5797step4 raw5797step3; decide +kernel
      have hl : raw5797step3Labels = labelEmbedding6 ∘ raw5797step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5797step3 raw5797step3Labels raw5797step4Labels labelEmbedding6 hl
    _ = mixedMoment B node4881 node4881Labels := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons71
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singleton4557 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4557 node4557Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1143 node1143Labels + mixedMoment B node2167 node2167Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1392 singletonSmall4557
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4557) = raw1392Labels := by decide +kernel
  rw [hl, canonical1392 B hB] at h
  have hc0 : mixedMoment B raw1392 (Fin.cases (0 : Fin 2) singletonSmall4557) =
      mixedMoment B node1143 node1143Labels := by
    have ha : raw1392 = raw1393 := by apply Matrix.ext; unfold raw1392 raw1393; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4557 = raw1393Labels := by decide +kernel
    rw [ha, hj, canonical1393 B hB]
  have hc1 : mixedMoment B raw1392 (Fin.cases (1 : Fin 2) singletonSmall4557) =
      mixedMoment B node2167 node2167Labels := by
    have ha : raw1392 = raw1394 := by apply Matrix.ext; unfold raw1392 raw1394; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4557 = raw1394Labels := by decide +kernel
    rw [ha, hj, canonical1394 B hB]
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

theorem singleton4681 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4681 node4681Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1807 node1807Labels + mixedMoment B node2151 node2151Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1563 singletonSmall4681
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4681) = raw1563Labels := by decide +kernel
  rw [hl, canonical1563 B hB] at h
  have hc0 : mixedMoment B raw1563 (Fin.cases (0 : Fin 2) singletonSmall4681) =
      mixedMoment B node1807 node1807Labels := by
    have ha : raw1563 = raw1564 := by apply Matrix.ext; unfold raw1563 raw1564; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4681 = raw1564Labels := by decide +kernel
    rw [ha, hj, canonical1564 B hB]
  have hc1 : mixedMoment B raw1563 (Fin.cases (1 : Fin 2) singletonSmall4681) =
      mixedMoment B node2151 node2151Labels := by
    have ha : raw1563 = raw1565 := by apply Matrix.ext; unfold raw1563 raw1565; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4681 = raw1565Labels := by decide +kernel
    rw [ha, hj, canonical1565 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4692 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4692 node4692Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1818 node1818Labels + mixedMoment B node2168 node2168Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1584 singletonSmall4692
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4692) = raw1584Labels := by decide +kernel
  rw [hl, canonical1584 B hB] at h
  have hc0 : mixedMoment B raw1584 (Fin.cases (0 : Fin 2) singletonSmall4692) =
      mixedMoment B node1818 node1818Labels := by
    have ha : raw1584 = raw1585 := by apply Matrix.ext; unfold raw1584 raw1585; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4692 = raw1585Labels := by decide +kernel
    rw [ha, hj, canonical1585 B hB]
  have hc1 : mixedMoment B raw1584 (Fin.cases (1 : Fin 2) singletonSmall4692) =
      mixedMoment B node2168 node2168Labels := by
    have ha : raw1584 = raw1586 := by apply Matrix.ext; unfold raw1584 raw1586; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4692 = raw1586Labels := by decide +kernel
    rw [ha, hj, canonical1586 B hB]
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

theorem singleton5099 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5099 node5099Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2509 node2509Labels + mixedMoment B node2704 node2704Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2124 singletonSmall5099
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5099) = raw2124Labels := by decide +kernel
  rw [hl, canonical2124 B hB] at h
  have hc0 : mixedMoment B raw2124 (Fin.cases (0 : Fin 2) singletonSmall5099) =
      mixedMoment B node2509 node2509Labels := by
    have ha : raw2124 = raw2125 := by apply Matrix.ext; unfold raw2124 raw2125; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5099 = raw2125Labels := by decide +kernel
    rw [ha, hj, canonical2125 B hB]
  have hc1 : mixedMoment B raw2124 (Fin.cases (1 : Fin 2) singletonSmall5099) =
      mixedMoment B node2704 node2704Labels := by
    have ha : raw2124 = raw2126 := by apply Matrix.ext; unfold raw2124 raw2126; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5099 = raw2126Labels := by decide +kernel
    rw [ha, hj, canonical2126 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons81
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singleton5228 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5228 node5228Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2672 node2672Labels + mixedMoment B node3391 node3391Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2250 singletonSmall5228
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5228) = raw2250Labels := by decide +kernel
  rw [hl, canonical2250 B hB] at h
  have hc0 : mixedMoment B raw2250 (Fin.cases (0 : Fin 2) singletonSmall5228) =
      mixedMoment B node2672 node2672Labels := by
    have ha : raw2250 = raw2251 := by apply Matrix.ext; unfold raw2250 raw2251; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5228 = raw2251Labels := by decide +kernel
    rw [ha, hj, canonical2251 B hB]
  have hc1 : mixedMoment B raw2250 (Fin.cases (1 : Fin 2) singletonSmall5228) =
      mixedMoment B node3391 node3391Labels := by
    have ha : raw2250 = raw2252 := by apply Matrix.ext; unfold raw2250 raw2252; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5228 = raw2252Labels := by decide +kernel
    rw [ha, hj, canonical2252 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton5238 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5238 node5238Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2686 node2686Labels + mixedMoment B node3397 node3397Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2256 singletonSmall5238
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5238) = raw2256Labels := by decide +kernel
  rw [hl, canonical2256 B hB] at h
  have hc0 : mixedMoment B raw2256 (Fin.cases (0 : Fin 2) singletonSmall5238) =
      mixedMoment B node2686 node2686Labels := by
    have ha : raw2256 = raw2257 := by apply Matrix.ext; unfold raw2256 raw2257; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5238 = raw2257Labels := by decide +kernel
    rw [ha, hj, canonical2257 B hB]
  have hc1 : mixedMoment B raw2256 (Fin.cases (1 : Fin 2) singletonSmall5238) =
      mixedMoment B node3397 node3397Labels := by
    have ha : raw2256 = raw2258 := by apply Matrix.ext; unfold raw2256 raw2258; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5238 = raw2258Labels := by decide +kernel
    rw [ha, hj, canonical2258 B hB]
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

theorem singleton5272 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5272 node5272Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2740 node2740Labels + mixedMoment B node2740 node2740Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2283 singletonSmall5272
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5272) = raw2283Labels := by decide +kernel
  rw [hl, canonical2283 B hB] at h
  have hc0 : mixedMoment B raw2283 (Fin.cases (0 : Fin 2) singletonSmall5272) =
      mixedMoment B node2740 node2740Labels := by
    have ha : raw2283 = raw2284 := by apply Matrix.ext; unfold raw2283 raw2284; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5272 = raw2284Labels := by decide +kernel
    rw [ha, hj, canonical2284 B hB]
  have hc1 : mixedMoment B raw2283 (Fin.cases (1 : Fin 2) singletonSmall5272) =
      mixedMoment B node2740 node2740Labels := by
    have ha : raw2283 = raw2285 := by apply Matrix.ext; unfold raw2283 raw2285; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5272 = raw2285Labels := by decide +kernel
    rw [ha, hj, canonical2285 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton5302 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5302 node5302Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3054 node3054Labels + mixedMoment B node3626 node3626Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2313 singletonSmall5302
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5302) = raw2313Labels := by decide +kernel
  rw [hl, canonical2313 B hB] at h
  have hc0 : mixedMoment B raw2313 (Fin.cases (0 : Fin 2) singletonSmall5302) =
      mixedMoment B node3054 node3054Labels := by
    have ha : raw2313 = raw2314 := by apply Matrix.ext; unfold raw2313 raw2314; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5302 = raw2314Labels := by decide +kernel
    rw [ha, hj, canonical2314 B hB]
  have hc1 : mixedMoment B raw2313 (Fin.cases (1 : Fin 2) singletonSmall5302) =
      mixedMoment B node3626 node3626Labels := by
    have ha : raw2313 = raw2315 := by apply Matrix.ext; unfold raw2313 raw2315; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5302 = raw2315Labels := by decide +kernel
    rw [ha, hj, canonical2315 B hB]
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

theorem sound3054 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3054 node3054Labels = Sparse.eval nodeValue3054 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3054) = mixedMoment B node3054 node3054Labels := rfl
  simpa [nodeValue3054, Sparse.eval] using hc.symm

theorem sound3626 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3626 node3626Labels = Sparse.eval nodeValue3626 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3626) = mixedMoment B node3626 node3626Labels := rfl
  simpa [nodeValue3626, Sparse.eval] using hc.symm

theorem sound5302 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5302 node5302Labels = Sparse.eval nodeValue5302 (mixedVector B) := by
  have h := singleton5302 B _hB
  rw [sound3054 B _hB _hF, sound3626 B _hB _hF] at h
  norm_num [nodeValue5302, nodeValue3054, nodeValue3626, Sparse.eval] at h ⊢
  linarith only [h]

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

theorem sound1143 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1143 node1143Labels = Sparse.eval nodeValue1143 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1143) = mixedMoment B node1143 node1143Labels := rfl
  simpa [nodeValue1143, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound28
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound1807 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1807 node1807Labels = Sparse.eval nodeValue1807 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1807) = mixedMoment B node1807 node1807Labels := rfl
  simpa [nodeValue1807, Sparse.eval] using hc.symm

theorem sound1818 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1818 node1818Labels = Sparse.eval nodeValue1818 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1818) = mixedMoment B node1818 node1818Labels := rfl
  simpa [nodeValue1818, Sparse.eval] using hc.symm

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

theorem sound2151 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2151 node2151Labels = Sparse.eval nodeValue2151 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2151) = mixedMoment B node2151 node2151Labels := rfl
  simpa [nodeValue2151, Sparse.eval] using hc.symm

theorem sound2167 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2167 node2167Labels = Sparse.eval nodeValue2167 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2167) = mixedMoment B node2167 node2167Labels := rfl
  simpa [nodeValue2167, Sparse.eval] using hc.symm

theorem sound2168 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2168 node2168Labels = Sparse.eval nodeValue2168 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2168) = mixedMoment B node2168 node2168Labels := rfl
  simpa [nodeValue2168, Sparse.eval] using hc.symm

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

theorem sound2509 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2509 node2509Labels = Sparse.eval nodeValue2509 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2509) = mixedMoment B node2509 node2509Labels := rfl
  simpa [nodeValue2509, Sparse.eval] using hc.symm

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

theorem sound2672 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2672 node2672Labels = Sparse.eval nodeValue2672 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2672) = mixedMoment B node2672 node2672Labels := rfl
  simpa [nodeValue2672, Sparse.eval] using hc.symm

theorem sound2686 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2686 node2686Labels = Sparse.eval nodeValue2686 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2686) = mixedMoment B node2686 node2686Labels := rfl
  simpa [nodeValue2686, Sparse.eval] using hc.symm

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

theorem sound2704 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2704 node2704Labels = Sparse.eval nodeValue2704 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2704) = mixedMoment B node2704 node2704Labels := rfl
  simpa [nodeValue2704, Sparse.eval] using hc.symm

theorem sound2740 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2740 node2740Labels = Sparse.eval nodeValue2740 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2740) = mixedMoment B node2740 node2740Labels := rfl
  simpa [nodeValue2740, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound52
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound3391 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3391 node3391Labels = Sparse.eval nodeValue3391 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3391) = mixedMoment B node3391 node3391Labels := rfl
  simpa [nodeValue3391, Sparse.eval] using hc.symm

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

theorem sound3397 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3397 node3397Labels = Sparse.eval nodeValue3397 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3397) = mixedMoment B node3397 node3397Labels := rfl
  simpa [nodeValue3397, Sparse.eval] using hc.symm

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

theorem sound4548 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4548 node4548Labels = Sparse.eval nodeValue4548 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4548) = mixedMoment B node4548 node4548Labels := rfl
  simpa [nodeValue4548, Sparse.eval] using hc.symm

theorem sound4557 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4557 node4557Labels = Sparse.eval nodeValue4557 (mixedVector B) := by
  have h := singleton4557 B _hB
  rw [sound1143 B _hB _hF, sound2167 B _hB _hF] at h
  norm_num [nodeValue4557, nodeValue1143, nodeValue2167, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4560 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4560 node4560Labels = Sparse.eval nodeValue4560 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4560) = mixedMoment B node4560 node4560Labels := rfl
  simpa [nodeValue4560, Sparse.eval] using hc.symm

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

theorem sound4611 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4611 node4611Labels = Sparse.eval nodeValue4611 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4611) = mixedMoment B node4611 node4611Labels := rfl
  simpa [nodeValue4611, Sparse.eval] using hc.symm

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

theorem sound4681 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4681 node4681Labels = Sparse.eval nodeValue4681 (mixedVector B) := by
  have h := singleton4681 B _hB
  rw [sound1807 B _hB _hF, sound2151 B _hB _hF] at h
  norm_num [nodeValue4681, nodeValue1807, nodeValue2151, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4692 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4692 node4692Labels = Sparse.eval nodeValue4692 (mixedVector B) := by
  have h := singleton4692 B _hB
  rw [sound1818 B _hB _hF, sound2168 B _hB _hF] at h
  norm_num [nodeValue4692, nodeValue1818, nodeValue2168, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4699 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4699 node4699Labels = Sparse.eval nodeValue4699 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4699) = mixedMoment B node4699 node4699Labels := rfl
  simpa [nodeValue4699, Sparse.eval] using hc.symm

theorem sound4705 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4705 node4705Labels = Sparse.eval nodeValue4705 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4705) = mixedMoment B node4705 node4705Labels := rfl
  simpa [nodeValue4705, Sparse.eval] using hc.symm

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

theorem sound4841 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4841 node4841Labels = Sparse.eval nodeValue4841 (mixedVector B) := by
  simpa only [nodeValue4841, Sparse.eval_nil] using zero4841 B _hB _hF

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

theorem sound4881 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4881 node4881Labels = Sparse.eval nodeValue4881 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4881) = mixedMoment B node4881 node4881Labels := rfl
  simpa [nodeValue4881, Sparse.eval] using hc.symm

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

theorem sound4945 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4945 node4945Labels = Sparse.eval nodeValue4945 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4945) = mixedMoment B node4945 node4945Labels := rfl
  simpa [nodeValue4945, Sparse.eval] using hc.symm

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

theorem sound5035 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5035 node5035Labels = Sparse.eval nodeValue5035 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5035) = mixedMoment B node5035 node5035Labels := rfl
  simpa [nodeValue5035, Sparse.eval] using hc.symm

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

theorem sound5099 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5099 node5099Labels = Sparse.eval nodeValue5099 (mixedVector B) := by
  have h := singleton5099 B _hB
  rw [sound2509 B _hB _hF, sound2704 B _hB _hF] at h
  norm_num [nodeValue5099, nodeValue2509, nodeValue2704, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5103 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5103 node5103Labels = Sparse.eval nodeValue5103 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5103) = mixedMoment B node5103 node5103Labels := rfl
  simpa [nodeValue5103, Sparse.eval] using hc.symm

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

theorem sound5140 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5140 node5140Labels = Sparse.eval nodeValue5140 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5140) = mixedMoment B node5140 node5140Labels := rfl
  simpa [nodeValue5140, Sparse.eval] using hc.symm

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

theorem sound5228 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5228 node5228Labels = Sparse.eval nodeValue5228 (mixedVector B) := by
  have h := singleton5228 B _hB
  rw [sound2672 B _hB _hF, sound3391 B _hB _hF] at h
  norm_num [nodeValue5228, nodeValue2672, nodeValue3391, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5238 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5238 node5238Labels = Sparse.eval nodeValue5238 (mixedVector B) := by
  have h := singleton5238 B _hB
  rw [sound2686 B _hB _hF, sound3397 B _hB _hF] at h
  norm_num [nodeValue5238, nodeValue2686, nodeValue3397, Sparse.eval] at h ⊢
  linarith only [h]

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

theorem zero5274 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5274 node5274Labels = 0 := by
  exact mixedMoment_order_one B hB node5274 node5274Labels 1
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

theorem sound5272 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5272 node5272Labels = Sparse.eval nodeValue5272 (mixedVector B) := by
  have h := singleton5272 B _hB
  rw [sound2740 B _hB _hF] at h
  norm_num [nodeValue5272, nodeValue2740, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5274 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5274 node5274Labels = Sparse.eval nodeValue5274 (mixedVector B) := by
  simpa only [nodeValue5274, Sparse.eval_nil] using zero5274 B _hB _hF

theorem sound5276 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5276 node5276Labels = Sparse.eval nodeValue5276 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5276) = mixedMoment B node5276 node5276Labels := rfl
  simpa [nodeValue5276, Sparse.eval] using hc.symm

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources69
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sourceEq2229 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2229 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2229 + difference 0 1) (sourceB2229 + difference 1 0) sourceC2229) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5238) := by
    have ha : (tripleCharges (sourceA2229 + difference 0 1) (sourceB2229 + difference 1 0) sourceC2229) = raw30601 := by
      apply Matrix.ext; unfold tripleCharges sourceA2229 sourceB2229 sourceC2229 difference raw30601; decide +kernel
    rw [ha]
    exact (canonical30601 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2229 + difference 0 2) (sourceB2229 + difference 2 0) sourceC2229) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5228) := by
    have ha : (tripleCharges (sourceA2229 + difference 0 2) (sourceB2229 + difference 2 0) sourceC2229) = raw30602 := by
      apply Matrix.ext; unfold tripleCharges sourceA2229 sourceB2229 sourceC2229 difference raw30602; decide +kernel
    rw [ha]
    exact (canonical30602 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2229 + difference 0 3) (sourceB2229 + difference 3 0) sourceC2229) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5228) := by
    have ha : (tripleCharges (sourceA2229 + difference 0 3) (sourceB2229 + difference 3 0) sourceC2229) = raw30603 := by
      apply Matrix.ext; unfold tripleCharges sourceA2229 sourceB2229 sourceC2229 difference raw30603; decide +kernel
    rw [ha]
    exact (canonical30603 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2229 + difference 0 4) (sourceB2229 + difference 4 0) sourceC2229) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5302) := by
    have ha : (tripleCharges (sourceA2229 + difference 0 4) (sourceB2229 + difference 4 0) sourceC2229) = raw5771 := by
      apply Matrix.ext; unfold tripleCharges sourceA2229 sourceB2229 sourceC2229 difference raw5771; decide +kernel
    rw [ha]
    exact (canonical5771 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2229 + difference 0 5) (sourceB2229 + difference 5 0) sourceC2229) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5274) := by
    have ha : (tripleCharges (sourceA2229 + difference 0 5) (sourceB2229 + difference 5 0) sourceC2229) = raw30604 := by
      apply Matrix.ext; unfold tripleCharges sourceA2229 sourceB2229 sourceC2229 difference raw30604; decide +kernel
    rw [ha]
    exact (canonical30604 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2229 + difference 1 0) (sourceB2229 + difference 0 1) sourceC2229) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4611) := by
    have ha : (tripleCharges (sourceA2229 + difference 1 0) (sourceB2229 + difference 0 1) sourceC2229) = raw5791 := by
      apply Matrix.ext; unfold tripleCharges sourceA2229 sourceB2229 sourceC2229 difference raw5791; decide +kernel
    rw [ha]
    exact (canonical5791 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2229 + difference 1 2) (sourceB2229 + difference 2 1) sourceC2229) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5140) := by
    have ha : (tripleCharges (sourceA2229 + difference 1 2) (sourceB2229 + difference 2 1) sourceC2229) = raw5793 := by
      apply Matrix.ext; unfold tripleCharges sourceA2229 sourceB2229 sourceC2229 difference raw5793; decide +kernel
    rw [ha]
    exact (canonical5793 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2229 + difference 1 3) (sourceB2229 + difference 3 1) sourceC2229) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5140) := by
    have ha : (tripleCharges (sourceA2229 + difference 1 3) (sourceB2229 + difference 3 1) sourceC2229) = raw5794 := by
      apply Matrix.ext; unfold tripleCharges sourceA2229 sourceB2229 sourceC2229 difference raw5794; decide +kernel
    rw [ha]
    exact (canonical5794 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2229 + difference 1 4) (sourceB2229 + difference 4 1) sourceC2229) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5276) := by
    have ha : (tripleCharges (sourceA2229 + difference 1 4) (sourceB2229 + difference 4 1) sourceC2229) = raw30605 := by
      apply Matrix.ext; unfold tripleCharges sourceA2229 sourceB2229 sourceC2229 difference raw30605; decide +kernel
    rw [ha]
    exact (canonical30605 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2229 + difference 1 5) (sourceB2229 + difference 5 1) sourceC2229) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5272) := by
    have ha : (tripleCharges (sourceA2229 + difference 1 5) (sourceB2229 + difference 5 1) sourceC2229) = raw5795 := by
      apply Matrix.ext; unfold tripleCharges sourceA2229 sourceB2229 sourceC2229 difference raw5795; decide +kernel
    rw [ha]
    exact (canonical5795 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2229 + difference 2 0) (sourceB2229 + difference 0 2) sourceC2229) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4548) := by
    have ha : (tripleCharges (sourceA2229 + difference 2 0) (sourceB2229 + difference 0 2) sourceC2229) = raw30606 := by
      apply Matrix.ext; unfold tripleCharges sourceA2229 sourceB2229 sourceC2229 difference raw30606; decide +kernel
    rw [ha]
    exact (canonical30606 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2229 + difference 2 1) (sourceB2229 + difference 1 2) sourceC2229) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4945) := by
    have ha : (tripleCharges (sourceA2229 + difference 2 1) (sourceB2229 + difference 1 2) sourceC2229) = raw30607 := by
      apply Matrix.ext; unfold tripleCharges sourceA2229 sourceB2229 sourceC2229 difference raw30607; decide +kernel
    rw [ha]
    exact (canonical30607 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2229 + difference 2 3) (sourceB2229 + difference 3 2) sourceC2229) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5035) := by
    have ha : (tripleCharges (sourceA2229 + difference 2 3) (sourceB2229 + difference 3 2) sourceC2229) = raw30608 := by
      apply Matrix.ext; unfold tripleCharges sourceA2229 sourceB2229 sourceC2229 difference raw30608; decide +kernel
    rw [ha]
    exact (canonical30608 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2229 + difference 2 4) (sourceB2229 + difference 4 2) sourceC2229) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5103) := by
    have ha : (tripleCharges (sourceA2229 + difference 2 4) (sourceB2229 + difference 4 2) sourceC2229) = raw5782 := by
      apply Matrix.ext; unfold tripleCharges sourceA2229 sourceB2229 sourceC2229 difference raw5782; decide +kernel
    rw [ha]
    exact (canonical5782 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2229 + difference 2 5) (sourceB2229 + difference 5 2) sourceC2229) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5099) := by
    have ha : (tripleCharges (sourceA2229 + difference 2 5) (sourceB2229 + difference 5 2) sourceC2229) = raw30609 := by
      apply Matrix.ext; unfold tripleCharges sourceA2229 sourceB2229 sourceC2229 difference raw30609; decide +kernel
    rw [ha]
    exact (canonical30609 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2229 + difference 3 0) (sourceB2229 + difference 0 3) sourceC2229) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4548) := by
    have ha : (tripleCharges (sourceA2229 + difference 3 0) (sourceB2229 + difference 0 3) sourceC2229) = raw30610 := by
      apply Matrix.ext; unfold tripleCharges sourceA2229 sourceB2229 sourceC2229 difference raw30610; decide +kernel
    rw [ha]
    exact (canonical30610 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2229 + difference 3 1) (sourceB2229 + difference 1 3) sourceC2229) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4945) := by
    have ha : (tripleCharges (sourceA2229 + difference 3 1) (sourceB2229 + difference 1 3) sourceC2229) = raw30611 := by
      apply Matrix.ext; unfold tripleCharges sourceA2229 sourceB2229 sourceC2229 difference raw30611; decide +kernel
    rw [ha]
    exact (canonical30611 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2229 + difference 3 2) (sourceB2229 + difference 2 3) sourceC2229) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5035) := by
    have ha : (tripleCharges (sourceA2229 + difference 3 2) (sourceB2229 + difference 2 3) sourceC2229) = raw30612 := by
      apply Matrix.ext; unfold tripleCharges sourceA2229 sourceB2229 sourceC2229 difference raw30612; decide +kernel
    rw [ha]
    exact (canonical30612 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2229 + difference 3 4) (sourceB2229 + difference 4 3) sourceC2229) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5103) := by
    have ha : (tripleCharges (sourceA2229 + difference 3 4) (sourceB2229 + difference 4 3) sourceC2229) = raw5787 := by
      apply Matrix.ext; unfold tripleCharges sourceA2229 sourceB2229 sourceC2229 difference raw5787; decide +kernel
    rw [ha]
    exact (canonical5787 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2229 + difference 3 5) (sourceB2229 + difference 5 3) sourceC2229) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5099) := by
    have ha : (tripleCharges (sourceA2229 + difference 3 5) (sourceB2229 + difference 5 3) sourceC2229) = raw30613 := by
      apply Matrix.ext; unfold tripleCharges sourceA2229 sourceB2229 sourceC2229 difference raw30613; decide +kernel
    rw [ha]
    exact (canonical30613 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2229 + difference 4 0) (sourceB2229 + difference 0 4) sourceC2229) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4557) := by
    have ha : (tripleCharges (sourceA2229 + difference 4 0) (sourceB2229 + difference 0 4) sourceC2229) = raw30614 := by
      apply Matrix.ext; unfold tripleCharges sourceA2229 sourceB2229 sourceC2229 difference raw30614; decide +kernel
    rw [ha]
    exact (canonical30614 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2229 + difference 4 1) (sourceB2229 + difference 1 4) sourceC2229) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4692) := by
    have ha : (tripleCharges (sourceA2229 + difference 4 1) (sourceB2229 + difference 1 4) sourceC2229) = raw30615 := by
      apply Matrix.ext; unfold tripleCharges sourceA2229 sourceB2229 sourceC2229 difference raw30615; decide +kernel
    rw [ha]
    exact (canonical30615 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2229 + difference 4 2) (sourceB2229 + difference 2 4) sourceC2229) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4681) := by
    have ha : (tripleCharges (sourceA2229 + difference 4 2) (sourceB2229 + difference 2 4) sourceC2229) = raw30616 := by
      apply Matrix.ext; unfold tripleCharges sourceA2229 sourceB2229 sourceC2229 difference raw30616; decide +kernel
    rw [ha]
    exact (canonical30616 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2229 + difference 4 3) (sourceB2229 + difference 3 4) sourceC2229) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4681) := by
    have ha : (tripleCharges (sourceA2229 + difference 4 3) (sourceB2229 + difference 3 4) sourceC2229) = raw30617 := by
      apply Matrix.ext; unfold tripleCharges sourceA2229 sourceB2229 sourceC2229 difference raw30617; decide +kernel
    rw [ha]
    exact (canonical30617 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2229 + difference 4 5) (sourceB2229 + difference 5 4) sourceC2229) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4841) := by
    have ha : (tripleCharges (sourceA2229 + difference 4 5) (sourceB2229 + difference 5 4) sourceC2229) = raw30618 := by
      apply Matrix.ext; unfold tripleCharges sourceA2229 sourceB2229 sourceC2229 difference raw30618; decide +kernel
    rw [ha]
    exact (canonical30618 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2229 + difference 5 0) (sourceB2229 + difference 0 5) sourceC2229) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4560) := by
    have ha : (tripleCharges (sourceA2229 + difference 5 0) (sourceB2229 + difference 0 5) sourceC2229) = raw30619 := by
      apply Matrix.ext; unfold tripleCharges sourceA2229 sourceB2229 sourceC2229 difference raw30619; decide +kernel
    rw [ha]
    exact (canonical30619 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2229 + difference 5 1) (sourceB2229 + difference 1 5) sourceC2229) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4705) := by
    have ha : (tripleCharges (sourceA2229 + difference 5 1) (sourceB2229 + difference 1 5) sourceC2229) = raw30620 := by
      apply Matrix.ext; unfold tripleCharges sourceA2229 sourceB2229 sourceC2229 difference raw30620; decide +kernel
    rw [ha]
    exact (canonical30620 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2229 + difference 5 2) (sourceB2229 + difference 2 5) sourceC2229) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4699) := by
    have ha : (tripleCharges (sourceA2229 + difference 5 2) (sourceB2229 + difference 2 5) sourceC2229) = raw30621 := by
      apply Matrix.ext; unfold tripleCharges sourceA2229 sourceB2229 sourceC2229 difference raw30621; decide +kernel
    rw [ha]
    exact (canonical30621 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2229 + difference 5 3) (sourceB2229 + difference 3 5) sourceC2229) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4699) := by
    have ha : (tripleCharges (sourceA2229 + difference 5 3) (sourceB2229 + difference 3 5) sourceC2229) = raw30622 := by
      apply Matrix.ext; unfold tripleCharges sourceA2229 sourceB2229 sourceC2229 difference raw30622; decide +kernel
    rw [ha]
    exact (canonical30622 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2229 + difference 5 4) (sourceB2229 + difference 4 5) sourceC2229) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4881) := by
    have ha : (tripleCharges (sourceA2229 + difference 5 4) (sourceB2229 + difference 4 5) sourceC2229) = raw5797 := by
      apply Matrix.ext; unfold tripleCharges sourceA2229 sourceB2229 sourceC2229 difference raw5797; decide +kernel
    rw [ha]
    exact (canonical5797 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2229 sourceB2229 sourceC2229
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2229, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic114
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reindexCheck1831 : Integer.Sparse.reindex keyMap MixedData.row1831 = numericRow1831 := by decide +kernel

theorem numericCheck1831 (x : Master → ℝ) : Integer.Sparse.eval numericRow1831 x =
    (4 : ℝ) * reducedSource1831 x := by
  norm_num [numericRow1831, reducedSource1831, Integer.Sparse.eval, Sparse.eval, nodeValue4548, nodeValue4557, nodeValue4560, nodeValue4611, nodeValue4681, nodeValue4692, nodeValue4699, nodeValue4705, nodeValue4841, nodeValue4881, nodeValue4945, nodeValue5035, nodeValue5099, nodeValue5103, nodeValue5140, nodeValue5228, nodeValue5238, nodeValue5272, nodeValue5274, nodeValue5276, nodeValue5302]
  ring

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Rows114
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero1831 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1831 (mixedVector B) = 0 := by
  have h4548 : mixedVector B (Sum.inr 4548) = Sparse.eval nodeValue4548 (mixedVector B) := by
    change mixedMoment B node4548 node4548Labels = _
    exact sound4548 B hB hF
  have h4557 : mixedVector B (Sum.inr 4557) = Sparse.eval nodeValue4557 (mixedVector B) := by
    change mixedMoment B node4557 node4557Labels = _
    exact sound4557 B hB hF
  have h4560 : mixedVector B (Sum.inr 4560) = Sparse.eval nodeValue4560 (mixedVector B) := by
    change mixedMoment B node4560 node4560Labels = _
    exact sound4560 B hB hF
  have h4611 : mixedVector B (Sum.inr 4611) = Sparse.eval nodeValue4611 (mixedVector B) := by
    change mixedMoment B node4611 node4611Labels = _
    exact sound4611 B hB hF
  have h4681 : mixedVector B (Sum.inr 4681) = Sparse.eval nodeValue4681 (mixedVector B) := by
    change mixedMoment B node4681 node4681Labels = _
    exact sound4681 B hB hF
  have h4692 : mixedVector B (Sum.inr 4692) = Sparse.eval nodeValue4692 (mixedVector B) := by
    change mixedMoment B node4692 node4692Labels = _
    exact sound4692 B hB hF
  have h4699 : mixedVector B (Sum.inr 4699) = Sparse.eval nodeValue4699 (mixedVector B) := by
    change mixedMoment B node4699 node4699Labels = _
    exact sound4699 B hB hF
  have h4705 : mixedVector B (Sum.inr 4705) = Sparse.eval nodeValue4705 (mixedVector B) := by
    change mixedMoment B node4705 node4705Labels = _
    exact sound4705 B hB hF
  have h4841 : mixedVector B (Sum.inr 4841) = Sparse.eval nodeValue4841 (mixedVector B) := by
    change mixedMoment B node4841 node4841Labels = _
    exact sound4841 B hB hF
  have h4881 : mixedVector B (Sum.inr 4881) = Sparse.eval nodeValue4881 (mixedVector B) := by
    change mixedMoment B node4881 node4881Labels = _
    exact sound4881 B hB hF
  have h4945 : mixedVector B (Sum.inr 4945) = Sparse.eval nodeValue4945 (mixedVector B) := by
    change mixedMoment B node4945 node4945Labels = _
    exact sound4945 B hB hF
  have h5035 : mixedVector B (Sum.inr 5035) = Sparse.eval nodeValue5035 (mixedVector B) := by
    change mixedMoment B node5035 node5035Labels = _
    exact sound5035 B hB hF
  have h5099 : mixedVector B (Sum.inr 5099) = Sparse.eval nodeValue5099 (mixedVector B) := by
    change mixedMoment B node5099 node5099Labels = _
    exact sound5099 B hB hF
  have h5103 : mixedVector B (Sum.inr 5103) = Sparse.eval nodeValue5103 (mixedVector B) := by
    change mixedMoment B node5103 node5103Labels = _
    exact sound5103 B hB hF
  have h5140 : mixedVector B (Sum.inr 5140) = Sparse.eval nodeValue5140 (mixedVector B) := by
    change mixedMoment B node5140 node5140Labels = _
    exact sound5140 B hB hF
  have h5228 : mixedVector B (Sum.inr 5228) = Sparse.eval nodeValue5228 (mixedVector B) := by
    change mixedMoment B node5228 node5228Labels = _
    exact sound5228 B hB hF
  have h5238 : mixedVector B (Sum.inr 5238) = Sparse.eval nodeValue5238 (mixedVector B) := by
    change mixedMoment B node5238 node5238Labels = _
    exact sound5238 B hB hF
  have h5272 : mixedVector B (Sum.inr 5272) = Sparse.eval nodeValue5272 (mixedVector B) := by
    change mixedMoment B node5272 node5272Labels = _
    exact sound5272 B hB hF
  have h5274 : mixedVector B (Sum.inr 5274) = Sparse.eval nodeValue5274 (mixedVector B) := by
    change mixedMoment B node5274 node5274Labels = _
    exact sound5274 B hB hF
  have h5276 : mixedVector B (Sum.inr 5276) = Sparse.eval nodeValue5276 (mixedVector B) := by
    change mixedMoment B node5276 node5276Labels = _
    exact sound5276 B hB hF
  have h5302 : mixedVector B (Sum.inr 5302) = Sparse.eval nodeValue5302 (mixedVector B) := by
    change mixedMoment B node5302 node5302Labels = _
    exact sound5302 B hB hF
  simpa only [sourceForm2229, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4548, h4557, h4560, h4611, h4681, h4692, h4699, h4705, h4841, h4881, h4945, h5035, h5099, h5103, h5140, h5228, h5238, h5272, h5274, h5276, h5302, reducedSource1831] using sourceEq2229 B hB

theorem rowSound1831_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1831 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1831, numericCheck1831, reducedZero1831 B hB hF, mul_zero]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedSourceBridge.rowSound1831_e_oai := @OAI.MUB6.Certificate.MixedSourceBridge.rowSound1831_e_oai
