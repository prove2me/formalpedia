-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedSourceBridge.rowSound1828_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-08T21:50:58.945392+00:00
-- url     : https://prove2.me/submissions/7c626556-c1a2-4aec-8ddb-38ec3dc90d7b

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E070
import Definitions.Def_OAIQ106E086
import Definitions.Def_OAIQ106E090
import Definitions.Def_OAIQ106E095
import Definitions.Def_OAIQ106E187
import Definitions.Def_OAIQ106E097
import Definitions.Def_OAIQ106E190
import Definitions.Def_OAIQ106E192
import Definitions.Def_OAIQ106E193
import Definitions.Def_OAIQ106E100
import Definitions.Def_OAIQ106E194
import Definitions.Def_OAIQ106E105
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

theorem canonical1386 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1386 raw1386Labels = mixedMoment B node4554 node4554Labels := by
  calc
    mixedMoment B raw1386 raw1386Labels = mixedMoment B raw1386step0 raw1386step0Labels := by
      have ha : raw1386step0 = (fun i j => raw1386 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1386step0 raw1386; decide +kernel
      have hl : raw1386step0Labels = raw1386Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1386 raw1386Labels permutation32 permutation4
    mixedMoment B raw1386step0 raw1386step0Labels = mixedMoment B raw1386step1 raw1386step1Labels := by
      have ha : raw1386step1 = raw1386step0 := by apply Matrix.ext; unfold raw1386step1 raw1386step0; decide +kernel
      have hl : raw1386step0Labels = labelEmbedding7 ∘ raw1386step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1386step0 raw1386step0Labels raw1386step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4554 node4554Labels := by rfl

theorem canonical1387 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1387 raw1387Labels = mixedMoment B node1139 node1139Labels := by
  calc
    mixedMoment B raw1387 raw1387Labels = mixedMoment B raw1387step0 raw1387step0Labels := by
      have ha : raw1387step0 = (fun i j => raw1387 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1387step0 raw1387; decide +kernel
      have hl : raw1387step0Labels = raw1387Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1387 raw1387Labels permutation32 permutation4
    _ = mixedMoment B node1139 node1139Labels := by rfl

theorem canonical1388 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1388 raw1388Labels = mixedMoment B node3274 node3274Labels := by
  calc
    mixedMoment B raw1388 raw1388Labels = mixedMoment B raw1388step0 raw1388step0Labels := by
      have ha : raw1388step0 = (fun i j => raw1388 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1388step0 raw1388; decide +kernel
      have hl : raw1388step0Labels = raw1388Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1388 raw1388Labels permutation32 permutation6
    mixedMoment B raw1388step0 raw1388step0Labels = mixedMoment B raw1388step1 raw1388step1Labels := by
      have ha : raw1388step1 = -raw1388step0 := by apply Matrix.ext; change ∀ i j, raw1388step1 i j = -(raw1388step0 i j); unfold raw1388step1 raw1388step0; decide +kernel
      have hl : raw1388step1Labels = raw1388step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1388step1 raw1388step1Labels = mixedMoment B raw1388step2 raw1388step2Labels := by
      have ha : raw1388step2 = raw1388step1 := by apply Matrix.ext; unfold raw1388step2 raw1388step1; decide +kernel
      have hl : raw1388step1Labels = labelEmbedding1 ∘ raw1388step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1388step1 raw1388step1Labels raw1388step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3274 node3274Labels := by rfl

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

theorem canonical1923 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1923 raw1923Labels = mixedMoment B node4950 node4950Labels := by
  calc
    mixedMoment B raw1923 raw1923Labels = mixedMoment B raw1923step0 raw1923step0Labels := by
      have ha : raw1923step0 = (fun i j => raw1923 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1923step0 raw1923; decide +kernel
      have hl : raw1923step0Labels = raw1923Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1923 raw1923Labels permutation32 permutation4
    mixedMoment B raw1923step0 raw1923step0Labels = mixedMoment B raw1923step1 raw1923step1Labels := by
      have ha : raw1923step1 = raw1923step0 := by apply Matrix.ext; unfold raw1923step1 raw1923step0; decide +kernel
      have hl : raw1923step0Labels = labelEmbedding7 ∘ raw1923step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1923step0 raw1923step0Labels raw1923step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4950 node4950Labels := by rfl

theorem canonical1924 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1924 raw1924Labels = mixedMoment B node2342 node2342Labels := by
  calc
    mixedMoment B raw1924 raw1924Labels = mixedMoment B raw1924step0 raw1924step0Labels := by
      have ha : raw1924step0 = (fun i j => raw1924 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1924step0 raw1924; decide +kernel
      have hl : raw1924step0Labels = raw1924Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1924 raw1924Labels permutation32 permutation4
    _ = mixedMoment B node2342 node2342Labels := by rfl

theorem canonical1925 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1925 raw1925Labels = mixedMoment B node3421 node3421Labels := by
  calc
    mixedMoment B raw1925 raw1925Labels = mixedMoment B raw1925step0 raw1925step0Labels := by
      have ha : raw1925step0 = (fun i j => raw1925 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1925step0 raw1925; decide +kernel
      have hl : raw1925step0Labels = raw1925Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1925 raw1925Labels permutation32 permutation6
    mixedMoment B raw1925step0 raw1925step0Labels = mixedMoment B raw1925step1 raw1925step1Labels := by
      have ha : raw1925step1 = -raw1925step0 := by apply Matrix.ext; change ∀ i j, raw1925step1 i j = -(raw1925step0 i j); unfold raw1925step1 raw1925step0; decide +kernel
      have hl : raw1925step1Labels = raw1925step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1925step1 raw1925step1Labels = mixedMoment B raw1925step2 raw1925step2Labels := by
      have ha : raw1925step2 = raw1925step1 := by apply Matrix.ext; unfold raw1925step2 raw1925step1; decide +kernel
      have hl : raw1925step1Labels = labelEmbedding1 ∘ raw1925step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1925step1 raw1925step1Labels raw1925step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3421 node3421Labels := by rfl

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

theorem canonical2064 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2064 raw2064Labels = mixedMoment B node5039 node5039Labels := by
  calc
    mixedMoment B raw2064 raw2064Labels = mixedMoment B raw2064step0 raw2064step0Labels := by
      have ha : raw2064step0 = (fun i j => raw2064 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2064step0 raw2064; decide +kernel
      have hl : raw2064step0Labels = raw2064Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2064 raw2064Labels permutation152 permutation4
    mixedMoment B raw2064step0 raw2064step0Labels = mixedMoment B raw2064step1 raw2064step1Labels := by
      have ha : raw2064step1 = raw2064step0 := by apply Matrix.ext; unfold raw2064step1 raw2064step0; decide +kernel
      have hl : raw2064step0Labels = labelEmbedding7 ∘ raw2064step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2064step0 raw2064step0Labels raw2064step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5039 node5039Labels := by rfl

theorem canonical2065 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2065 raw2065Labels = mixedMoment B node2432 node2432Labels := by
  calc
    mixedMoment B raw2065 raw2065Labels = mixedMoment B raw2065step0 raw2065step0Labels := by
      have ha : raw2065step0 = (fun i j => raw2065 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2065step0 raw2065; decide +kernel
      have hl : raw2065step0Labels = raw2065Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2065 raw2065Labels permutation152 permutation4
    _ = mixedMoment B node2432 node2432Labels := by rfl

theorem canonical2066 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2066 raw2066Labels = mixedMoment B node3456 node3456Labels := by
  calc
    mixedMoment B raw2066 raw2066Labels = mixedMoment B raw2066step0 raw2066step0Labels := by
      have ha : raw2066step0 = (fun i j => raw2066 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2066step0 raw2066; decide +kernel
      have hl : raw2066step0Labels = raw2066Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2066 raw2066Labels permutation152 permutation6
    mixedMoment B raw2066step0 raw2066step0Labels = mixedMoment B raw2066step1 raw2066step1Labels := by
      have ha : raw2066step1 = -raw2066step0 := by apply Matrix.ext; change ∀ i j, raw2066step1 i j = -(raw2066step0 i j); unfold raw2066step1 raw2066step0; decide +kernel
      have hl : raw2066step1Labels = raw2066step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2066step1 raw2066step1Labels = mixedMoment B raw2066step2 raw2066step2Labels := by
      have ha : raw2066step2 = raw2066step1 := by apply Matrix.ext; unfold raw2066step2 raw2066step1; decide +kernel
      have hl : raw2066step1Labels = labelEmbedding1 ∘ raw2066step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2066step1 raw2066step1Labels raw2066step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3456 node3456Labels := by rfl

theorem canonical2094 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2094 raw2094Labels = mixedMoment B node5073 node5073Labels := by
  calc
    mixedMoment B raw2094 raw2094Labels = mixedMoment B raw2094step0 raw2094step0Labels := by
      have ha : raw2094step0 = (fun i j => raw2094 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2094step0 raw2094; decide +kernel
      have hl : raw2094step0Labels = raw2094Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2094 raw2094Labels permutation152 permutation4
    mixedMoment B raw2094step0 raw2094step0Labels = mixedMoment B raw2094step1 raw2094step1Labels := by
      have ha : raw2094step1 = raw2094step0 := by apply Matrix.ext; unfold raw2094step1 raw2094step0; decide +kernel
      have hl : raw2094step0Labels = labelEmbedding7 ∘ raw2094step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2094step0 raw2094step0Labels raw2094step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5073 node5073Labels := by rfl

theorem canonical2095 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2095 raw2095Labels = mixedMoment B node2480 node2480Labels := by
  calc
    mixedMoment B raw2095 raw2095Labels = mixedMoment B raw2095step0 raw2095step0Labels := by
      have ha : raw2095step0 = (fun i j => raw2095 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2095step0 raw2095; decide +kernel
      have hl : raw2095step0Labels = raw2095Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2095 raw2095Labels permutation152 permutation4
    _ = mixedMoment B node2480 node2480Labels := by rfl

theorem canonical2096 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2096 raw2096Labels = mixedMoment B node3467 node3467Labels := by
  calc
    mixedMoment B raw2096 raw2096Labels = mixedMoment B raw2096step0 raw2096step0Labels := by
      have ha : raw2096step0 = (fun i j => raw2096 (permutation158 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2096step0 raw2096; decide +kernel
      have hl : raw2096step0Labels = raw2096Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2096 raw2096Labels permutation158 permutation6
    mixedMoment B raw2096step0 raw2096step0Labels = mixedMoment B raw2096step1 raw2096step1Labels := by
      have ha : raw2096step1 = -raw2096step0 := by apply Matrix.ext; change ∀ i j, raw2096step1 i j = -(raw2096step0 i j); unfold raw2096step1 raw2096step0; decide +kernel
      have hl : raw2096step1Labels = raw2096step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2096step1 raw2096step1Labels = mixedMoment B raw2096step2 raw2096step2Labels := by
      have ha : raw2096step2 = raw2096step1 := by apply Matrix.ext; unfold raw2096step2 raw2096step1; decide +kernel
      have hl : raw2096step1Labels = labelEmbedding1 ∘ raw2096step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2096step1 raw2096step1Labels raw2096step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3467 node3467Labels := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical17
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical2274 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2274 raw2274Labels = mixedMoment B node5259 node5259Labels := by
  calc
    mixedMoment B raw2274 raw2274Labels = mixedMoment B raw2274step0 raw2274step0Labels := by
      have ha : raw2274step0 = (fun i j => raw2274 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2274step0 raw2274; decide +kernel
      have hl : raw2274step0Labels = raw2274Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2274 raw2274Labels permutation32 permutation4
    mixedMoment B raw2274step0 raw2274step0Labels = mixedMoment B raw2274step1 raw2274step1Labels := by
      have ha : raw2274step1 = raw2274step0 := by apply Matrix.ext; unfold raw2274step1 raw2274step0; decide +kernel
      have hl : raw2274step0Labels = labelEmbedding7 ∘ raw2274step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2274step0 raw2274step0Labels raw2274step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5259 node5259Labels := by rfl

theorem canonical2275 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2275 raw2275Labels = mixedMoment B node2723 node2723Labels := by
  calc
    mixedMoment B raw2275 raw2275Labels = mixedMoment B raw2275step0 raw2275step0Labels := by
      have ha : raw2275step0 = (fun i j => raw2275 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2275step0 raw2275; decide +kernel
      have hl : raw2275step0Labels = raw2275Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2275 raw2275Labels permutation32 permutation4
    _ = mixedMoment B node2723 node2723Labels := by rfl

theorem canonical2276 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2276 raw2276Labels = mixedMoment B node3544 node3544Labels := by
  calc
    mixedMoment B raw2276 raw2276Labels = mixedMoment B raw2276step0 raw2276step0Labels := by
      have ha : raw2276step0 = (fun i j => raw2276 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2276step0 raw2276; decide +kernel
      have hl : raw2276step0Labels = raw2276Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2276 raw2276Labels permutation32 permutation6
    mixedMoment B raw2276step0 raw2276step0Labels = mixedMoment B raw2276step1 raw2276step1Labels := by
      have ha : raw2276step1 = -raw2276step0 := by apply Matrix.ext; change ∀ i j, raw2276step1 i j = -(raw2276step0 i j); unfold raw2276step1 raw2276step0; decide +kernel
      have hl : raw2276step1Labels = raw2276step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2276step1 raw2276step1Labels = mixedMoment B raw2276step2 raw2276step2Labels := by
      have ha : raw2276step2 = raw2276step1 := by apply Matrix.ext; unfold raw2276step2 raw2276step1; decide +kernel
      have hl : raw2276step1Labels = labelEmbedding1 ∘ raw2276step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2276step1 raw2276step1Labels raw2276step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3544 node3544Labels := by rfl

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

theorem canonical2403 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2403 raw2403Labels = mixedMoment B node5356 node5356Labels := by
  calc
    mixedMoment B raw2403 raw2403Labels = mixedMoment B raw2403step0 raw2403step0Labels := by
      have ha : raw2403step0 = (fun i j => raw2403 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2403step0 raw2403; decide +kernel
      have hl : raw2403step0Labels = raw2403Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2403 raw2403Labels permutation32 permutation4
    mixedMoment B raw2403step0 raw2403step0Labels = mixedMoment B raw2403step1 raw2403step1Labels := by
      have ha : raw2403step1 = raw2403step0 := by apply Matrix.ext; unfold raw2403step1 raw2403step0; decide +kernel
      have hl : raw2403step0Labels = labelEmbedding7 ∘ raw2403step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2403step0 raw2403step0Labels raw2403step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5356 node5356Labels := by rfl

theorem canonical2404 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2404 raw2404Labels = mixedMoment B node3694 node3694Labels := by
  calc
    mixedMoment B raw2404 raw2404Labels = mixedMoment B raw2404step0 raw2404step0Labels := by
      have ha : raw2404step0 = (fun i j => raw2404 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2404step0 raw2404; decide +kernel
      have hl : raw2404step0Labels = raw2404Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2404 raw2404Labels permutation32 permutation4
    _ = mixedMoment B node3694 node3694Labels := by rfl

theorem canonical2405 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2405 raw2405Labels = mixedMoment B node3773 node3773Labels := by
  calc
    mixedMoment B raw2405 raw2405Labels = mixedMoment B raw2405step0 raw2405step0Labels := by
      have ha : raw2405step0 = (fun i j => raw2405 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2405step0 raw2405; decide +kernel
      have hl : raw2405step0Labels = raw2405Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2405 raw2405Labels permutation32 permutation6
    mixedMoment B raw2405step0 raw2405step0Labels = mixedMoment B raw2405step1 raw2405step1Labels := by
      have ha : raw2405step1 = -raw2405step0 := by apply Matrix.ext; change ∀ i j, raw2405step1 i j = -(raw2405step0 i j); unfold raw2405step1 raw2405step0; decide +kernel
      have hl : raw2405step1Labels = raw2405step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2405step1 raw2405step1Labels = mixedMoment B raw2405step2 raw2405step2Labels := by
      have ha : raw2405step2 = raw2405step1 := by apply Matrix.ext; unfold raw2405step2 raw2405step1; decide +kernel
      have hl : raw2405step1Labels = labelEmbedding1 ∘ raw2405step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2405step1 raw2405step1Labels raw2405step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3773 node3773Labels := by rfl

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

theorem canonical2460 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2460 raw2460Labels = mixedMoment B node5393 node5393Labels := by
  calc
    mixedMoment B raw2460 raw2460Labels = mixedMoment B raw2460step0 raw2460step0Labels := by
      have ha : raw2460step0 = (fun i j => raw2460 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2460step0 raw2460; decide +kernel
      have hl : raw2460step0Labels = raw2460Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2460 raw2460Labels permutation152 permutation4
    mixedMoment B raw2460step0 raw2460step0Labels = mixedMoment B raw2460step1 raw2460step1Labels := by
      have ha : raw2460step1 = raw2460step0 := by apply Matrix.ext; unfold raw2460step1 raw2460step0; decide +kernel
      have hl : raw2460step0Labels = labelEmbedding7 ∘ raw2460step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2460step0 raw2460step0Labels raw2460step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5393 node5393Labels := by rfl

theorem canonical2461 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2461 raw2461Labels = mixedMoment B node3779 node3779Labels := by
  calc
    mixedMoment B raw2461 raw2461Labels = mixedMoment B raw2461step0 raw2461step0Labels := by
      have ha : raw2461step0 = (fun i j => raw2461 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2461step0 raw2461; decide +kernel
      have hl : raw2461step0Labels = raw2461Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2461 raw2461Labels permutation152 permutation4
    _ = mixedMoment B node3779 node3779Labels := by rfl

theorem canonical2462 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2462 raw2462Labels = mixedMoment B node3797 node3797Labels := by
  calc
    mixedMoment B raw2462 raw2462Labels = mixedMoment B raw2462step0 raw2462step0Labels := by
      have ha : raw2462step0 = (fun i j => raw2462 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2462step0 raw2462; decide +kernel
      have hl : raw2462step0Labels = raw2462Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2462 raw2462Labels permutation152 permutation6
    mixedMoment B raw2462step0 raw2462step0Labels = mixedMoment B raw2462step1 raw2462step1Labels := by
      have ha : raw2462step1 = -raw2462step0 := by apply Matrix.ext; change ∀ i j, raw2462step1 i j = -(raw2462step0 i j); unfold raw2462step1 raw2462step0; decide +kernel
      have hl : raw2462step1Labels = raw2462step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2462step1 raw2462step1Labels = mixedMoment B raw2462step2 raw2462step2Labels := by
      have ha : raw2462step2 = raw2462step1 := by apply Matrix.ext; unfold raw2462step2 raw2462step1; decide +kernel
      have hl : raw2462step1Labels = labelEmbedding1 ∘ raw2462step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2462step1 raw2462step1Labels raw2462step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3797 node3797Labels := by rfl

theorem canonical2481 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2481 raw2481Labels = mixedMoment B node5404 node5404Labels := by
  calc
    mixedMoment B raw2481 raw2481Labels = mixedMoment B raw2481step0 raw2481step0Labels := by
      have ha : raw2481step0 = (fun i j => raw2481 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2481step0 raw2481; decide +kernel
      have hl : raw2481step0Labels = raw2481Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2481 raw2481Labels permutation32 permutation4
    mixedMoment B raw2481step0 raw2481step0Labels = mixedMoment B raw2481step1 raw2481step1Labels := by
      have ha : raw2481step1 = raw2481step0 := by apply Matrix.ext; unfold raw2481step1 raw2481step0; decide +kernel
      have hl : raw2481step0Labels = labelEmbedding7 ∘ raw2481step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2481step0 raw2481step0Labels raw2481step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5404 node5404Labels := by rfl

theorem canonical2482 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2482 raw2482Labels = mixedMoment B node3790 node3790Labels := by
  calc
    mixedMoment B raw2482 raw2482Labels = mixedMoment B raw2482step0 raw2482step0Labels := by
      have ha : raw2482step0 = (fun i j => raw2482 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2482step0 raw2482; decide +kernel
      have hl : raw2482step0Labels = raw2482Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2482 raw2482Labels permutation32 permutation4
    _ = mixedMoment B node3790 node3790Labels := by rfl

theorem canonical2483 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2483 raw2483Labels = mixedMoment B node3815 node3815Labels := by
  calc
    mixedMoment B raw2483 raw2483Labels = mixedMoment B raw2483step0 raw2483step0Labels := by
      have ha : raw2483step0 = (fun i j => raw2483 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2483step0 raw2483; decide +kernel
      have hl : raw2483step0Labels = raw2483Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2483 raw2483Labels permutation32 permutation6
    mixedMoment B raw2483step0 raw2483step0Labels = mixedMoment B raw2483step1 raw2483step1Labels := by
      have ha : raw2483step1 = -raw2483step0 := by apply Matrix.ext; change ∀ i j, raw2483step1 i j = -(raw2483step0 i j); unfold raw2483step1 raw2483step0; decide +kernel
      have hl : raw2483step1Labels = raw2483step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2483step1 raw2483step1Labels = mixedMoment B raw2483step2 raw2483step2Labels := by
      have ha : raw2483step2 = raw2483step1 := by apply Matrix.ext; unfold raw2483step2 raw2483step1; decide +kernel
      have hl : raw2483step1Labels = labelEmbedding1 ∘ raw2483step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2483step1 raw2483step1Labels raw2483step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3815 node3815Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical237
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical30412 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30412 raw30412Labels = mixedMoment B node5356 node5356Labels := by
  calc
    mixedMoment B raw30412 raw30412Labels = mixedMoment B raw30412step0 raw30412step0Labels := by
      have hz : ∀ j, raw30412 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30412step0 = (fun i j => raw30412 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30412step0 raw30412; decide +kernel
      have hl : raw30412step0Labels = raw30412Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30412 raw30412Labels permutation434 hz
    _ = mixedMoment B node5356 node5356Labels := by rfl

theorem canonical30413 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30413 raw30413Labels = mixedMoment B node5404 node5404Labels := by
  calc
    mixedMoment B raw30413 raw30413Labels = mixedMoment B raw30413step0 raw30413step0Labels := by
      have hz : ∀ j, raw30413 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30413step0 = (fun i j => raw30413 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30413step0 raw30413; decide +kernel
      have hl : raw30413step0Labels = raw30413Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30413 raw30413Labels permutation434 hz
    _ = mixedMoment B node5404 node5404Labels := by rfl

theorem canonical30414 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30414 raw30414Labels = mixedMoment B node5393 node5393Labels := by
  calc
    mixedMoment B raw30414 raw30414Labels = mixedMoment B raw30414step0 raw30414step0Labels := by
      have ha : raw30414step0 = (fun i j => raw30414 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30414step0 raw30414; decide +kernel
      have hl : raw30414step0Labels = raw30414Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30414 raw30414Labels permutation158 permutation2
    _ = mixedMoment B node5393 node5393Labels := by rfl

theorem canonical30415 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30415 raw30415Labels = mixedMoment B node5410 node5410Labels := by
  calc
    mixedMoment B raw30415 raw30415Labels = mixedMoment B raw30415step0 raw30415step0Labels := by
      have hz : ∀ j, raw30415 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30415step0 = (fun i j => raw30415 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30415step0 raw30415; decide +kernel
      have hl : raw30415step0Labels = raw30415Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30415 raw30415Labels permutation434 hz
    _ = mixedMoment B node5410 node5410Labels := by rfl

theorem canonical30416 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30416 raw30416Labels = mixedMoment B node5410 node5410Labels := by
  calc
    mixedMoment B raw30416 raw30416Labels = mixedMoment B raw30416step0 raw30416step0Labels := by
      have hz : ∀ j, raw30416 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30416step0 = (fun i j => raw30416 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30416step0 raw30416; decide +kernel
      have hl : raw30416step0Labels = raw30416Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30416 raw30416Labels permutation434 hz
    mixedMoment B raw30416step0 raw30416step0Labels = mixedMoment B raw30416step1 raw30416step1Labels := by
      have ha : raw30416step1 = (fun i j => raw30416step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30416step1 raw30416step0; decide +kernel
      have hl : raw30416step1Labels = raw30416step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30416step0 raw30416step0Labels permutation33 permutation2
    _ = mixedMoment B node5410 node5410Labels := by rfl

theorem canonical30417 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30417 raw30417Labels = mixedMoment B node4593 node4593Labels := by
  calc
    mixedMoment B raw30417 raw30417Labels = mixedMoment B raw30417step0 raw30417step0Labels := by
      have hz : ∀ j, raw30417 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30417step0 = (fun i j => raw30417 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30417step0 raw30417; decide +kernel
      have hl : raw30417step0Labels = raw30417Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30417 raw30417Labels permutation434 hz
    _ = mixedMoment B node4593 node4593Labels := by rfl

theorem canonical30418 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30418 raw30418Labels = mixedMoment B node5189 node5189Labels := by
  calc
    mixedMoment B raw30418 raw30418Labels = mixedMoment B raw30418step0 raw30418step0Labels := by
      have hz : ∀ j, raw30418 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30418step0 = (fun i j => raw30418 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30418step0 raw30418; decide +kernel
      have hl : raw30418step0Labels = raw30418Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30418 raw30418Labels permutation434 hz
    mixedMoment B raw30418step0 raw30418step0Labels = mixedMoment B raw30418step1 raw30418step1Labels := by
      have ha : raw30418step1 = (fun i j => raw30418step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30418step1 raw30418step0; decide +kernel
      have hl : raw30418step1Labels = raw30418step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30418step0 raw30418step0Labels permutation38 permutation2
    _ = mixedMoment B node5189 node5189Labels := by rfl

theorem canonical30419 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30419 raw30419Labels = mixedMoment B node5130 node5130Labels := by
  calc
    mixedMoment B raw30419 raw30419Labels = mixedMoment B raw30419step0 raw30419step0Labels := by
      have ha : raw30419step0 = (fun i j => raw30419 (permutation200 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30419step0 raw30419; decide +kernel
      have hl : raw30419step0Labels = raw30419Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30419 raw30419Labels permutation200 permutation2
    _ = mixedMoment B node5130 node5130Labels := by rfl

theorem canonical30420 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30420 raw30420Labels = mixedMoment B node5259 node5259Labels := by
  calc
    mixedMoment B raw30420 raw30420Labels = mixedMoment B raw30420step0 raw30420step0Labels := by
      have hz : ∀ j, raw30420 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30420step0 = (fun i j => raw30420 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30420step0 raw30420; decide +kernel
      have hl : raw30420step0Labels = raw30420Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30420 raw30420Labels permutation434 hz
    _ = mixedMoment B node5259 node5259Labels := by rfl

theorem canonical30421 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30421 raw30421Labels = mixedMoment B node5259 node5259Labels := by
  calc
    mixedMoment B raw30421 raw30421Labels = mixedMoment B raw30421step0 raw30421step0Labels := by
      have hz : ∀ j, raw30421 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30421step0 = (fun i j => raw30421 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30421step0 raw30421; decide +kernel
      have hl : raw30421step0Labels = raw30421Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30421 raw30421Labels permutation434 hz
    mixedMoment B raw30421step0 raw30421step0Labels = mixedMoment B raw30421step1 raw30421step1Labels := by
      have ha : raw30421step1 = (fun i j => raw30421step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30421step1 raw30421step0; decide +kernel
      have hl : raw30421step1Labels = raw30421step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30421step0 raw30421step0Labels permutation33 permutation2
    _ = mixedMoment B node5259 node5259Labels := by rfl

theorem canonical30422 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30422 raw30422Labels = mixedMoment B node4554 node4554Labels := by
  calc
    mixedMoment B raw30422 raw30422Labels = mixedMoment B raw30422step0 raw30422step0Labels := by
      have hz : ∀ j, raw30422 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30422step0 = (fun i j => raw30422 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30422step0 raw30422; decide +kernel
      have hl : raw30422step0Labels = raw30422Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30422 raw30422Labels permutation434 hz
    _ = mixedMoment B node4554 node4554Labels := by rfl

theorem canonical30423 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30423 raw30423Labels = mixedMoment B node4950 node4950Labels := by
  calc
    mixedMoment B raw30423 raw30423Labels = mixedMoment B raw30423step0 raw30423step0Labels := by
      have hz : ∀ j, raw30423 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30423step0 = (fun i j => raw30423 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30423step0 raw30423; decide +kernel
      have hl : raw30423step0Labels = raw30423Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30423 raw30423Labels permutation434 hz
    _ = mixedMoment B node4950 node4950Labels := by rfl

theorem canonical30424 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30424 raw30424Labels = mixedMoment B node5039 node5039Labels := by
  calc
    mixedMoment B raw30424 raw30424Labels = mixedMoment B raw30424step0 raw30424step0Labels := by
      have ha : raw30424step0 = (fun i j => raw30424 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30424step0 raw30424; decide +kernel
      have hl : raw30424step0Labels = raw30424Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30424 raw30424Labels permutation158 permutation2
    _ = mixedMoment B node5039 node5039Labels := by rfl

theorem canonical30425 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30425 raw30425Labels = mixedMoment B node5104 node5104Labels := by
  calc
    mixedMoment B raw30425 raw30425Labels = mixedMoment B raw30425step0 raw30425step0Labels := by
      have hz : ∀ j, raw30425 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30425step0 = (fun i j => raw30425 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30425step0 raw30425; decide +kernel
      have hl : raw30425step0Labels = raw30425Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30425 raw30425Labels permutation434 hz
    _ = mixedMoment B node5104 node5104Labels := by rfl

theorem canonical30426 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30426 raw30426Labels = mixedMoment B node5104 node5104Labels := by
  calc
    mixedMoment B raw30426 raw30426Labels = mixedMoment B raw30426step0 raw30426step0Labels := by
      have hz : ∀ j, raw30426 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30426step0 = (fun i j => raw30426 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30426step0 raw30426; decide +kernel
      have hl : raw30426step0Labels = raw30426Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30426 raw30426Labels permutation434 hz
    mixedMoment B raw30426step0 raw30426step0Labels = mixedMoment B raw30426step1 raw30426step1Labels := by
      have ha : raw30426step1 = (fun i j => raw30426step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30426step1 raw30426step0; decide +kernel
      have hl : raw30426step1Labels = raw30426step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30426step0 raw30426step0Labels permutation33 permutation2
    _ = mixedMoment B node5104 node5104Labels := by rfl

theorem canonical30427 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30427 raw30427Labels = mixedMoment B node4530 node4530Labels := by
  calc
    _ = mixedMoment B node4530 node4530Labels := by rfl

theorem canonical30428 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30428 raw30428Labels = mixedMoment B node4932 node4932Labels := by
  calc
    _ = mixedMoment B node4932 node4932Labels := by rfl

theorem canonical30429 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30429 raw30429Labels = mixedMoment B node5043 node5043Labels := by
  calc
    _ = mixedMoment B node5043 node5043Labels := by rfl

theorem canonical30430 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30430 raw30430Labels = mixedMoment B node5073 node5073Labels := by
  calc
    _ = mixedMoment B node5073 node5073Labels := by rfl

theorem canonical30431 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30431 raw30431Labels = mixedMoment B node5073 node5073Labels := by
  calc
    mixedMoment B raw30431 raw30431Labels = mixedMoment B raw30431step0 raw30431step0Labels := by
      have ha : raw30431step0 = (fun i j => raw30431 (permutation153 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30431step0 raw30431; decide +kernel
      have hl : raw30431step0Labels = raw30431Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30431 raw30431Labels permutation153 permutation2
    _ = mixedMoment B node5073 node5073Labels := by rfl

theorem canonical30432 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30432 raw30432Labels = mixedMoment B node4535 node4535Labels := by
  calc
    mixedMoment B raw30432 raw30432Labels = mixedMoment B raw30432step0 raw30432step0Labels := by
      have hz : ∀ j, raw30432 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30432step0 = (fun i j => raw30432 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30432step0 raw30432; decide +kernel
      have hl : raw30432step0Labels = raw30432Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30432 raw30432Labels permutation434 hz
    mixedMoment B raw30432step0 raw30432step0Labels = mixedMoment B raw30432step1 raw30432step1Labels := by
      have ha : raw30432step1 = (fun i j => raw30432step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30432step1 raw30432step0; decide +kernel
      have hl : raw30432step1Labels = raw30432step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30432step0 raw30432step0Labels permutation33 permutation2
    _ = mixedMoment B node4535 node4535Labels := by rfl

theorem canonical30433 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30433 raw30433Labels = mixedMoment B node4935 node4935Labels := by
  calc
    mixedMoment B raw30433 raw30433Labels = mixedMoment B raw30433step0 raw30433step0Labels := by
      have hz : ∀ j, raw30433 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30433step0 = (fun i j => raw30433 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30433step0 raw30433; decide +kernel
      have hl : raw30433step0Labels = raw30433Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30433 raw30433Labels permutation434 hz
    mixedMoment B raw30433step0 raw30433step0Labels = mixedMoment B raw30433step1 raw30433step1Labels := by
      have ha : raw30433step1 = (fun i j => raw30433step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30433step1 raw30433step0; decide +kernel
      have hl : raw30433step1Labels = raw30433step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30433step0 raw30433step0Labels permutation33 permutation2
    _ = mixedMoment B node4935 node4935Labels := by rfl

theorem canonical30434 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30434 raw30434Labels = mixedMoment B node4944 node4944Labels := by
  calc
    mixedMoment B raw30434 raw30434Labels = mixedMoment B raw30434step0 raw30434step0Labels := by
      have hz : ∀ j, raw30434 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30434step0 = (fun i j => raw30434 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30434step0 raw30434; decide +kernel
      have hl : raw30434step0Labels = raw30434Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30434 raw30434Labels permutation434 hz
    mixedMoment B raw30434step0 raw30434step0Labels = mixedMoment B raw30434step1 raw30434step1Labels := by
      have ha : raw30434step1 = (fun i j => raw30434step0 (permutation125 i) (permutation3 j)) := by apply Matrix.ext; unfold raw30434step1 raw30434step0; decide +kernel
      have hl : raw30434step1Labels = raw30434step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30434step0 raw30434step0Labels permutation125 permutation3
    mixedMoment B raw30434step1 raw30434step1Labels = mixedMoment B raw30434step2 raw30434step2Labels := by
      have ha : raw30434step2 = -raw30434step1 := by apply Matrix.ext; change ∀ i j, raw30434step2 i j = -(raw30434step1 i j); unfold raw30434step2 raw30434step1; decide +kernel
      have hl : raw30434step2Labels = raw30434step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30434step2 raw30434step2Labels = mixedMoment B raw30434step3 raw30434step3Labels := by
      have ha : raw30434step3 = raw30434step2 := by apply Matrix.ext; unfold raw30434step3 raw30434step2; decide +kernel
      have hl : raw30434step2Labels = labelEmbedding6 ∘ raw30434step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30434step2 raw30434step2Labels raw30434step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4944 node4944Labels := by rfl

theorem canonical30435 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30435 raw30435Labels = mixedMoment B node4930 node4930Labels := by
  calc
    mixedMoment B raw30435 raw30435Labels = mixedMoment B raw30435step0 raw30435step0Labels := by
      have ha : raw30435step0 = (fun i j => raw30435 (permutation582 i) (permutation3 j)) := by apply Matrix.ext; unfold raw30435step0 raw30435; decide +kernel
      have hl : raw30435step0Labels = raw30435Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30435 raw30435Labels permutation582 permutation3
    mixedMoment B raw30435step0 raw30435step0Labels = mixedMoment B raw30435step1 raw30435step1Labels := by
      have ha : raw30435step1 = -raw30435step0 := by apply Matrix.ext; change ∀ i j, raw30435step1 i j = -(raw30435step0 i j); unfold raw30435step1 raw30435step0; decide +kernel
      have hl : raw30435step1Labels = raw30435step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30435step1 raw30435step1Labels = mixedMoment B raw30435step2 raw30435step2Labels := by
      have ha : raw30435step2 = raw30435step1 := by apply Matrix.ext; unfold raw30435step2 raw30435step1; decide +kernel
      have hl : raw30435step1Labels = labelEmbedding6 ∘ raw30435step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30435step1 raw30435step1Labels raw30435step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4930 node4930Labels := by rfl

theorem canonical30436 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30436 raw30436Labels = mixedMoment B node5078 node5078Labels := by
  calc
    mixedMoment B raw30436 raw30436Labels = mixedMoment B raw30436step0 raw30436step0Labels := by
      have hz : ∀ j, raw30436 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30436step0 = (fun i j => raw30436 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30436step0 raw30436; decide +kernel
      have hl : raw30436step0Labels = raw30436Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30436 raw30436Labels permutation434 hz
    mixedMoment B raw30436step0 raw30436step0Labels = mixedMoment B raw30436step1 raw30436step1Labels := by
      have ha : raw30436step1 = (fun i j => raw30436step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30436step1 raw30436step0; decide +kernel
      have hl : raw30436step1Labels = raw30436step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30436step0 raw30436step0Labels permutation33 permutation2
    _ = mixedMoment B node5078 node5078Labels := by rfl

theorem canonical30437 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30437 raw30437Labels = mixedMoment B node4535 node4535Labels := by
  calc
    mixedMoment B raw30437 raw30437Labels = mixedMoment B raw30437step0 raw30437step0Labels := by
      have hz : ∀ j, raw30437 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30437step0 = (fun i j => raw30437 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30437step0 raw30437; decide +kernel
      have hl : raw30437step0Labels = raw30437Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30437 raw30437Labels permutation434 hz
    _ = mixedMoment B node4535 node4535Labels := by rfl

theorem canonical30438 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30438 raw30438Labels = mixedMoment B node4935 node4935Labels := by
  calc
    mixedMoment B raw30438 raw30438Labels = mixedMoment B raw30438step0 raw30438step0Labels := by
      have hz : ∀ j, raw30438 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30438step0 = (fun i j => raw30438 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30438step0 raw30438; decide +kernel
      have hl : raw30438step0Labels = raw30438Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30438 raw30438Labels permutation434 hz
    _ = mixedMoment B node4935 node4935Labels := by rfl

theorem canonical30439 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30439 raw30439Labels = mixedMoment B node4944 node4944Labels := by
  calc
    mixedMoment B raw30439 raw30439Labels = mixedMoment B raw30439step0 raw30439step0Labels := by
      have hz : ∀ j, raw30439 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30439step0 = (fun i j => raw30439 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30439step0 raw30439; decide +kernel
      have hl : raw30439step0Labels = raw30439Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30439 raw30439Labels permutation434 hz
    mixedMoment B raw30439step0 raw30439step0Labels = mixedMoment B raw30439step1 raw30439step1Labels := by
      have ha : raw30439step1 = (fun i j => raw30439step0 (permutation149 i) (permutation3 j)) := by apply Matrix.ext; unfold raw30439step1 raw30439step0; decide +kernel
      have hl : raw30439step1Labels = raw30439step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30439step0 raw30439step0Labels permutation149 permutation3
    mixedMoment B raw30439step1 raw30439step1Labels = mixedMoment B raw30439step2 raw30439step2Labels := by
      have ha : raw30439step2 = -raw30439step1 := by apply Matrix.ext; change ∀ i j, raw30439step2 i j = -(raw30439step1 i j); unfold raw30439step2 raw30439step1; decide +kernel
      have hl : raw30439step2Labels = raw30439step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30439step2 raw30439step2Labels = mixedMoment B raw30439step3 raw30439step3Labels := by
      have ha : raw30439step3 = raw30439step2 := by apply Matrix.ext; unfold raw30439step3 raw30439step2; decide +kernel
      have hl : raw30439step2Labels = labelEmbedding6 ∘ raw30439step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30439step2 raw30439step2Labels raw30439step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4944 node4944Labels := by rfl

theorem canonical30440 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30440 raw30440Labels = mixedMoment B node4930 node4930Labels := by
  calc
    mixedMoment B raw30440 raw30440Labels = mixedMoment B raw30440step0 raw30440step0Labels := by
      have ha : raw30440step0 = (fun i j => raw30440 (permutation680 i) (permutation3 j)) := by apply Matrix.ext; unfold raw30440step0 raw30440; decide +kernel
      have hl : raw30440step0Labels = raw30440Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30440 raw30440Labels permutation680 permutation3
    mixedMoment B raw30440step0 raw30440step0Labels = mixedMoment B raw30440step1 raw30440step1Labels := by
      have ha : raw30440step1 = -raw30440step0 := by apply Matrix.ext; change ∀ i j, raw30440step1 i j = -(raw30440step0 i j); unfold raw30440step1 raw30440step0; decide +kernel
      have hl : raw30440step1Labels = raw30440step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30440step1 raw30440step1Labels = mixedMoment B raw30440step2 raw30440step2Labels := by
      have ha : raw30440step2 = raw30440step1 := by apply Matrix.ext; unfold raw30440step2 raw30440step1; decide +kernel
      have hl : raw30440step1Labels = labelEmbedding6 ∘ raw30440step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30440step1 raw30440step1Labels raw30440step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4930 node4930Labels := by rfl

theorem canonical30441 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30441 raw30441Labels = mixedMoment B node5078 node5078Labels := by
  calc
    mixedMoment B raw30441 raw30441Labels = mixedMoment B raw30441step0 raw30441step0Labels := by
      have hz : ∀ j, raw30441 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30441step0 = (fun i j => raw30441 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30441step0 raw30441; decide +kernel
      have hl : raw30441step0Labels = raw30441Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30441 raw30441Labels permutation434 hz
    _ = mixedMoment B node5078 node5078Labels := by rfl

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

theorem singleton4554 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4554 node4554Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1139 node1139Labels + mixedMoment B node3274 node3274Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1386 singletonSmall4554
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4554) = raw1386Labels := by decide +kernel
  rw [hl, canonical1386 B hB] at h
  have hc0 : mixedMoment B raw1386 (Fin.cases (0 : Fin 2) singletonSmall4554) =
      mixedMoment B node1139 node1139Labels := by
    have ha : raw1386 = raw1387 := by apply Matrix.ext; unfold raw1386 raw1387; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4554 = raw1387Labels := by decide +kernel
    rw [ha, hj, canonical1387 B hB]
  have hc1 : mixedMoment B raw1386 (Fin.cases (1 : Fin 2) singletonSmall4554) =
      mixedMoment B node3274 node3274Labels := by
    have ha : raw1386 = raw1388 := by apply Matrix.ext; unfold raw1386 raw1388; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4554 = raw1388Labels := by decide +kernel
    rw [ha, hj, canonical1388 B hB]
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

theorem singleton4950 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4950 node4950Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2342 node2342Labels + mixedMoment B node3421 node3421Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1923 singletonSmall4950
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4950) = raw1923Labels := by decide +kernel
  rw [hl, canonical1923 B hB] at h
  have hc0 : mixedMoment B raw1923 (Fin.cases (0 : Fin 2) singletonSmall4950) =
      mixedMoment B node2342 node2342Labels := by
    have ha : raw1923 = raw1924 := by apply Matrix.ext; unfold raw1923 raw1924; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4950 = raw1924Labels := by decide +kernel
    rw [ha, hj, canonical1924 B hB]
  have hc1 : mixedMoment B raw1923 (Fin.cases (1 : Fin 2) singletonSmall4950) =
      mixedMoment B node3421 node3421Labels := by
    have ha : raw1923 = raw1925 := by apply Matrix.ext; unfold raw1923 raw1925; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4950 = raw1925Labels := by decide +kernel
    rw [ha, hj, canonical1925 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons78
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singleton5039 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5039 node5039Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2432 node2432Labels + mixedMoment B node3456 node3456Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2064 singletonSmall5039
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5039) = raw2064Labels := by decide +kernel
  rw [hl, canonical2064 B hB] at h
  have hc0 : mixedMoment B raw2064 (Fin.cases (0 : Fin 2) singletonSmall5039) =
      mixedMoment B node2432 node2432Labels := by
    have ha : raw2064 = raw2065 := by apply Matrix.ext; unfold raw2064 raw2065; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5039 = raw2065Labels := by decide +kernel
    rw [ha, hj, canonical2065 B hB]
  have hc1 : mixedMoment B raw2064 (Fin.cases (1 : Fin 2) singletonSmall5039) =
      mixedMoment B node3456 node3456Labels := by
    have ha : raw2064 = raw2066 := by apply Matrix.ext; unfold raw2064 raw2066; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5039 = raw2066Labels := by decide +kernel
    rw [ha, hj, canonical2066 B hB]
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

theorem singleton5073 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5073 node5073Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2480 node2480Labels + mixedMoment B node3467 node3467Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2094 singletonSmall5073
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5073) = raw2094Labels := by decide +kernel
  rw [hl, canonical2094 B hB] at h
  have hc0 : mixedMoment B raw2094 (Fin.cases (0 : Fin 2) singletonSmall5073) =
      mixedMoment B node2480 node2480Labels := by
    have ha : raw2094 = raw2095 := by apply Matrix.ext; unfold raw2094 raw2095; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5073 = raw2095Labels := by decide +kernel
    rw [ha, hj, canonical2095 B hB]
  have hc1 : mixedMoment B raw2094 (Fin.cases (1 : Fin 2) singletonSmall5073) =
      mixedMoment B node3467 node3467Labels := by
    have ha : raw2094 = raw2096 := by apply Matrix.ext; unfold raw2094 raw2096; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5073 = raw2096Labels := by decide +kernel
    rw [ha, hj, canonical2096 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons82
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singleton5259 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5259 node5259Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2723 node2723Labels + mixedMoment B node3544 node3544Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2274 singletonSmall5259
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5259) = raw2274Labels := by decide +kernel
  rw [hl, canonical2274 B hB] at h
  have hc0 : mixedMoment B raw2274 (Fin.cases (0 : Fin 2) singletonSmall5259) =
      mixedMoment B node2723 node2723Labels := by
    have ha : raw2274 = raw2275 := by apply Matrix.ext; unfold raw2274 raw2275; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5259 = raw2275Labels := by decide +kernel
    rw [ha, hj, canonical2275 B hB]
  have hc1 : mixedMoment B raw2274 (Fin.cases (1 : Fin 2) singletonSmall5259) =
      mixedMoment B node3544 node3544Labels := by
    have ha : raw2274 = raw2276 := by apply Matrix.ext; unfold raw2274 raw2276; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5259 = raw2276Labels := by decide +kernel
    rw [ha, hj, canonical2276 B hB]
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

theorem singleton5356 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5356 node5356Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3694 node3694Labels + mixedMoment B node3773 node3773Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2403 singletonSmall5356
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5356) = raw2403Labels := by decide +kernel
  rw [hl, canonical2403 B hB] at h
  have hc0 : mixedMoment B raw2403 (Fin.cases (0 : Fin 2) singletonSmall5356) =
      mixedMoment B node3694 node3694Labels := by
    have ha : raw2403 = raw2404 := by apply Matrix.ext; unfold raw2403 raw2404; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5356 = raw2404Labels := by decide +kernel
    rw [ha, hj, canonical2404 B hB]
  have hc1 : mixedMoment B raw2403 (Fin.cases (1 : Fin 2) singletonSmall5356) =
      mixedMoment B node3773 node3773Labels := by
    have ha : raw2403 = raw2405 := by apply Matrix.ext; unfold raw2403 raw2405; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5356 = raw2405Labels := by decide +kernel
    rw [ha, hj, canonical2405 B hB]
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

theorem singleton5393 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5393 node5393Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3779 node3779Labels + mixedMoment B node3797 node3797Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2460 singletonSmall5393
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5393) = raw2460Labels := by decide +kernel
  rw [hl, canonical2460 B hB] at h
  have hc0 : mixedMoment B raw2460 (Fin.cases (0 : Fin 2) singletonSmall5393) =
      mixedMoment B node3779 node3779Labels := by
    have ha : raw2460 = raw2461 := by apply Matrix.ext; unfold raw2460 raw2461; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5393 = raw2461Labels := by decide +kernel
    rw [ha, hj, canonical2461 B hB]
  have hc1 : mixedMoment B raw2460 (Fin.cases (1 : Fin 2) singletonSmall5393) =
      mixedMoment B node3797 node3797Labels := by
    have ha : raw2460 = raw2462 := by apply Matrix.ext; unfold raw2460 raw2462; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5393 = raw2462Labels := by decide +kernel
    rw [ha, hj, canonical2462 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton5404 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5404 node5404Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3790 node3790Labels + mixedMoment B node3815 node3815Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2481 singletonSmall5404
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5404) = raw2481Labels := by decide +kernel
  rw [hl, canonical2481 B hB] at h
  have hc0 : mixedMoment B raw2481 (Fin.cases (0 : Fin 2) singletonSmall5404) =
      mixedMoment B node3790 node3790Labels := by
    have ha : raw2481 = raw2482 := by apply Matrix.ext; unfold raw2481 raw2482; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5404 = raw2482Labels := by decide +kernel
    rw [ha, hj, canonical2482 B hB]
  have hc1 : mixedMoment B raw2481 (Fin.cases (1 : Fin 2) singletonSmall5404) =
      mixedMoment B node3815 node3815Labels := by
    have ha : raw2481 = raw2483 := by apply Matrix.ext; unfold raw2481 raw2483; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5404 = raw2483Labels := by decide +kernel
    rw [ha, hj, canonical2483 B hB]
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

theorem sound1139 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1139 node1139Labels = Sparse.eval nodeValue1139 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1139) = mixedMoment B node1139 node1139Labels := rfl
  simpa [nodeValue1139, Sparse.eval] using hc.symm

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

theorem sound2342 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2342 node2342Labels = Sparse.eval nodeValue2342 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2342) = mixedMoment B node2342 node2342Labels := rfl
  simpa [nodeValue2342, Sparse.eval] using hc.symm

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

theorem sound2432 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2432 node2432Labels = Sparse.eval nodeValue2432 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2432) = mixedMoment B node2432 node2432Labels := rfl
  simpa [nodeValue2432, Sparse.eval] using hc.symm

theorem sound2480 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2480 node2480Labels = Sparse.eval nodeValue2480 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2480) = mixedMoment B node2480 node2480Labels := rfl
  simpa [nodeValue2480, Sparse.eval] using hc.symm

theorem sound2485 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2485 node2485Labels = Sparse.eval nodeValue2485 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2485) = mixedMoment B node2485 node2485Labels := rfl
  simpa [nodeValue2485, Sparse.eval] using hc.symm

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

theorem sound2723 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2723 node2723Labels = Sparse.eval nodeValue2723 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2723) = mixedMoment B node2723 node2723Labels := rfl
  simpa [nodeValue2723, Sparse.eval] using hc.symm

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

theorem sound3274 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3274 node3274Labels = Sparse.eval nodeValue3274 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3274) = mixedMoment B node3274 node3274Labels := rfl
  simpa [nodeValue3274, Sparse.eval] using hc.symm

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

theorem sound3421 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3421 node3421Labels = Sparse.eval nodeValue3421 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3421) = mixedMoment B node3421 node3421Labels := rfl
  simpa [nodeValue3421, Sparse.eval] using hc.symm

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

theorem sound3456 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3456 node3456Labels = Sparse.eval nodeValue3456 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3456) = mixedMoment B node3456 node3456Labels := rfl
  simpa [nodeValue3456, Sparse.eval] using hc.symm

theorem sound3467 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3467 node3467Labels = Sparse.eval nodeValue3467 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3467) = mixedMoment B node3467 node3467Labels := rfl
  simpa [nodeValue3467, Sparse.eval] using hc.symm

theorem sound3481 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3481 node3481Labels = Sparse.eval nodeValue3481 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3481) = mixedMoment B node3481 node3481Labels := rfl
  simpa [nodeValue3481, Sparse.eval] using hc.symm

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

theorem sound3544 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3544 node3544Labels = Sparse.eval nodeValue3544 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3544) = mixedMoment B node3544 node3544Labels := rfl
  simpa [nodeValue3544, Sparse.eval] using hc.symm

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

theorem sound3694 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3694 node3694Labels = Sparse.eval nodeValue3694 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3694) = mixedMoment B node3694 node3694Labels := rfl
  simpa [nodeValue3694, Sparse.eval] using hc.symm

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

theorem sound3773 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3773 node3773Labels = Sparse.eval nodeValue3773 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3773) = mixedMoment B node3773 node3773Labels := rfl
  simpa [nodeValue3773, Sparse.eval] using hc.symm

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

theorem sound3779 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3779 node3779Labels = Sparse.eval nodeValue3779 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3779) = mixedMoment B node3779 node3779Labels := rfl
  simpa [nodeValue3779, Sparse.eval] using hc.symm

theorem sound3790 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3790 node3790Labels = Sparse.eval nodeValue3790 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3790) = mixedMoment B node3790 node3790Labels := rfl
  simpa [nodeValue3790, Sparse.eval] using hc.symm

theorem sound3797 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3797 node3797Labels = Sparse.eval nodeValue3797 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3797) = mixedMoment B node3797 node3797Labels := rfl
  simpa [nodeValue3797, Sparse.eval] using hc.symm

theorem sound3815 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3815 node3815Labels = Sparse.eval nodeValue3815 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3815) = mixedMoment B node3815 node3815Labels := rfl
  simpa [nodeValue3815, Sparse.eval] using hc.symm

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

theorem sound4530 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4530 node4530Labels = Sparse.eval nodeValue4530 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4530) = mixedMoment B node4530 node4530Labels := rfl
  simpa [nodeValue4530, Sparse.eval] using hc.symm

theorem sound4535 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4535 node4535Labels = Sparse.eval nodeValue4535 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4535) = mixedMoment B node4535 node4535Labels := rfl
  simpa [nodeValue4535, Sparse.eval] using hc.symm

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

theorem sound4554 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4554 node4554Labels = Sparse.eval nodeValue4554 (mixedVector B) := by
  have h := singleton4554 B _hB
  rw [sound1139 B _hB _hF, sound3274 B _hB _hF] at h
  norm_num [nodeValue4554, nodeValue1139, nodeValue3274, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4593 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4593 node4593Labels = Sparse.eval nodeValue4593 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4593) = mixedMoment B node4593 node4593Labels := rfl
  simpa [nodeValue4593, Sparse.eval] using hc.symm

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

theorem zero4932 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node4932 node4932Labels = 0 := by
  exact mixedMoment_alpha B hF node4932 node4932Labels 1 permutation152
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

theorem sound4930 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4930 node4930Labels = Sparse.eval nodeValue4930 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4930) = mixedMoment B node4930 node4930Labels := rfl
  simpa [nodeValue4930, Sparse.eval] using hc.symm

theorem sound4932 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4932 node4932Labels = Sparse.eval nodeValue4932 (mixedVector B) := by
  simpa only [nodeValue4932, Sparse.eval_nil] using zero4932 B _hB _hF

theorem sound4935 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4935 node4935Labels = Sparse.eval nodeValue4935 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4935) = mixedMoment B node4935 node4935Labels := rfl
  simpa [nodeValue4935, Sparse.eval] using hc.symm

theorem sound4944 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4944 node4944Labels = Sparse.eval nodeValue4944 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4944) = mixedMoment B node4944 node4944Labels := rfl
  simpa [nodeValue4944, Sparse.eval] using hc.symm

theorem sound4950 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4950 node4950Labels = Sparse.eval nodeValue4950 (mixedVector B) := by
  have h := singleton4950 B _hB
  rw [sound2342 B _hB _hF, sound3421 B _hB _hF] at h
  norm_num [nodeValue4950, nodeValue2342, nodeValue3421, Sparse.eval] at h ⊢
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

theorem sound5039 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5039 node5039Labels = Sparse.eval nodeValue5039 (mixedVector B) := by
  have h := singleton5039 B _hB
  rw [sound2432 B _hB _hF, sound3456 B _hB _hF] at h
  norm_num [nodeValue5039, nodeValue2432, nodeValue3456, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5043 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5043 node5043Labels = Sparse.eval nodeValue5043 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5043) = mixedMoment B node5043 node5043Labels := rfl
  simpa [nodeValue5043, Sparse.eval] using hc.symm

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

theorem zero5104 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5104 node5104Labels = 0 := by
  exact mixedMoment_order_one B hB node5104 node5104Labels 1
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

theorem sound5073 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5073 node5073Labels = Sparse.eval nodeValue5073 (mixedVector B) := by
  have h := singleton5073 B _hB
  rw [sound2480 B _hB _hF, sound3467 B _hB _hF] at h
  norm_num [nodeValue5073, nodeValue2480, nodeValue3467, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5078 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5078 node5078Labels = Sparse.eval nodeValue5078 (mixedVector B) := by
  have h := singleton5078 B _hB
  rw [sound2485 B _hB _hF, sound3481 B _hB _hF] at h
  norm_num [nodeValue5078, nodeValue2485, nodeValue3481, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5104 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5104 node5104Labels = Sparse.eval nodeValue5104 (mixedVector B) := by
  simpa only [nodeValue5104, Sparse.eval_nil] using zero5104 B _hB _hF

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

theorem zero5130 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node5130 node5130Labels = 0 := by
  exact mixedMoment_alpha B hF node5130 node5130Labels 1 permutation158
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

theorem sound5130 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5130 node5130Labels = Sparse.eval nodeValue5130 (mixedVector B) := by
  simpa only [nodeValue5130, Sparse.eval_nil] using zero5130 B _hB _hF

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

theorem sound5189 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5189 node5189Labels = Sparse.eval nodeValue5189 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5189) = mixedMoment B node5189 node5189Labels := rfl
  simpa [nodeValue5189, Sparse.eval] using hc.symm

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

theorem sound5259 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5259 node5259Labels = Sparse.eval nodeValue5259 (mixedVector B) := by
  have h := singleton5259 B _hB
  rw [sound2723 B _hB _hF, sound3544 B _hB _hF] at h
  norm_num [nodeValue5259, nodeValue2723, nodeValue3544, Sparse.eval] at h ⊢
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

theorem sound5356 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5356 node5356Labels = Sparse.eval nodeValue5356 (mixedVector B) := by
  have h := singleton5356 B _hB
  rw [sound3694 B _hB _hF, sound3773 B _hB _hF] at h
  norm_num [nodeValue5356, nodeValue3694, nodeValue3773, Sparse.eval] at h ⊢
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

theorem sound5393 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5393 node5393Labels = Sparse.eval nodeValue5393 (mixedVector B) := by
  have h := singleton5393 B _hB
  rw [sound3779 B _hB _hF, sound3797 B _hB _hF] at h
  norm_num [nodeValue5393, nodeValue3779, nodeValue3797, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5404 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5404 node5404Labels = Sparse.eval nodeValue5404 (mixedVector B) := by
  have h := singleton5404 B _hB
  rw [sound3790 B _hB _hF, sound3815 B _hB _hF] at h
  norm_num [nodeValue5404, nodeValue3790, nodeValue3815, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5410 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5410 node5410Labels = Sparse.eval nodeValue5410 (mixedVector B) := by
  simpa only [nodeValue5410, Sparse.eval_nil] using zero5410 B _hB _hF

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

theorem sourceEq2217 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2217 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2217 + difference 0 1) (sourceB2217 + difference 1 0) sourceC2217) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5356) := by
    have ha : (tripleCharges (sourceA2217 + difference 0 1) (sourceB2217 + difference 1 0) sourceC2217) = raw30412 := by
      apply Matrix.ext; unfold tripleCharges sourceA2217 sourceB2217 sourceC2217 difference raw30412; decide +kernel
    rw [ha]
    exact (canonical30412 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2217 + difference 0 2) (sourceB2217 + difference 2 0) sourceC2217) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5404) := by
    have ha : (tripleCharges (sourceA2217 + difference 0 2) (sourceB2217 + difference 2 0) sourceC2217) = raw30413 := by
      apply Matrix.ext; unfold tripleCharges sourceA2217 sourceB2217 sourceC2217 difference raw30413; decide +kernel
    rw [ha]
    exact (canonical30413 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2217 + difference 0 3) (sourceB2217 + difference 3 0) sourceC2217) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5393) := by
    have ha : (tripleCharges (sourceA2217 + difference 0 3) (sourceB2217 + difference 3 0) sourceC2217) = raw30414 := by
      apply Matrix.ext; unfold tripleCharges sourceA2217 sourceB2217 sourceC2217 difference raw30414; decide +kernel
    rw [ha]
    exact (canonical30414 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2217 + difference 0 4) (sourceB2217 + difference 4 0) sourceC2217) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5410) := by
    have ha : (tripleCharges (sourceA2217 + difference 0 4) (sourceB2217 + difference 4 0) sourceC2217) = raw30415 := by
      apply Matrix.ext; unfold tripleCharges sourceA2217 sourceB2217 sourceC2217 difference raw30415; decide +kernel
    rw [ha]
    exact (canonical30415 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2217 + difference 0 5) (sourceB2217 + difference 5 0) sourceC2217) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5410) := by
    have ha : (tripleCharges (sourceA2217 + difference 0 5) (sourceB2217 + difference 5 0) sourceC2217) = raw30416 := by
      apply Matrix.ext; unfold tripleCharges sourceA2217 sourceB2217 sourceC2217 difference raw30416; decide +kernel
    rw [ha]
    exact (canonical30416 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2217 + difference 1 0) (sourceB2217 + difference 0 1) sourceC2217) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4593) := by
    have ha : (tripleCharges (sourceA2217 + difference 1 0) (sourceB2217 + difference 0 1) sourceC2217) = raw30417 := by
      apply Matrix.ext; unfold tripleCharges sourceA2217 sourceB2217 sourceC2217 difference raw30417; decide +kernel
    rw [ha]
    exact (canonical30417 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2217 + difference 1 2) (sourceB2217 + difference 2 1) sourceC2217) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5189) := by
    have ha : (tripleCharges (sourceA2217 + difference 1 2) (sourceB2217 + difference 2 1) sourceC2217) = raw30418 := by
      apply Matrix.ext; unfold tripleCharges sourceA2217 sourceB2217 sourceC2217 difference raw30418; decide +kernel
    rw [ha]
    exact (canonical30418 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2217 + difference 1 3) (sourceB2217 + difference 3 1) sourceC2217) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5130) := by
    have ha : (tripleCharges (sourceA2217 + difference 1 3) (sourceB2217 + difference 3 1) sourceC2217) = raw30419 := by
      apply Matrix.ext; unfold tripleCharges sourceA2217 sourceB2217 sourceC2217 difference raw30419; decide +kernel
    rw [ha]
    exact (canonical30419 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2217 + difference 1 4) (sourceB2217 + difference 4 1) sourceC2217) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5259) := by
    have ha : (tripleCharges (sourceA2217 + difference 1 4) (sourceB2217 + difference 4 1) sourceC2217) = raw30420 := by
      apply Matrix.ext; unfold tripleCharges sourceA2217 sourceB2217 sourceC2217 difference raw30420; decide +kernel
    rw [ha]
    exact (canonical30420 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2217 + difference 1 5) (sourceB2217 + difference 5 1) sourceC2217) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5259) := by
    have ha : (tripleCharges (sourceA2217 + difference 1 5) (sourceB2217 + difference 5 1) sourceC2217) = raw30421 := by
      apply Matrix.ext; unfold tripleCharges sourceA2217 sourceB2217 sourceC2217 difference raw30421; decide +kernel
    rw [ha]
    exact (canonical30421 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2217 + difference 2 0) (sourceB2217 + difference 0 2) sourceC2217) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4554) := by
    have ha : (tripleCharges (sourceA2217 + difference 2 0) (sourceB2217 + difference 0 2) sourceC2217) = raw30422 := by
      apply Matrix.ext; unfold tripleCharges sourceA2217 sourceB2217 sourceC2217 difference raw30422; decide +kernel
    rw [ha]
    exact (canonical30422 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2217 + difference 2 1) (sourceB2217 + difference 1 2) sourceC2217) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4950) := by
    have ha : (tripleCharges (sourceA2217 + difference 2 1) (sourceB2217 + difference 1 2) sourceC2217) = raw30423 := by
      apply Matrix.ext; unfold tripleCharges sourceA2217 sourceB2217 sourceC2217 difference raw30423; decide +kernel
    rw [ha]
    exact (canonical30423 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2217 + difference 2 3) (sourceB2217 + difference 3 2) sourceC2217) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5039) := by
    have ha : (tripleCharges (sourceA2217 + difference 2 3) (sourceB2217 + difference 3 2) sourceC2217) = raw30424 := by
      apply Matrix.ext; unfold tripleCharges sourceA2217 sourceB2217 sourceC2217 difference raw30424; decide +kernel
    rw [ha]
    exact (canonical30424 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2217 + difference 2 4) (sourceB2217 + difference 4 2) sourceC2217) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5104) := by
    have ha : (tripleCharges (sourceA2217 + difference 2 4) (sourceB2217 + difference 4 2) sourceC2217) = raw30425 := by
      apply Matrix.ext; unfold tripleCharges sourceA2217 sourceB2217 sourceC2217 difference raw30425; decide +kernel
    rw [ha]
    exact (canonical30425 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2217 + difference 2 5) (sourceB2217 + difference 5 2) sourceC2217) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5104) := by
    have ha : (tripleCharges (sourceA2217 + difference 2 5) (sourceB2217 + difference 5 2) sourceC2217) = raw30426 := by
      apply Matrix.ext; unfold tripleCharges sourceA2217 sourceB2217 sourceC2217 difference raw30426; decide +kernel
    rw [ha]
    exact (canonical30426 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2217 + difference 3 0) (sourceB2217 + difference 0 3) sourceC2217) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4530) := by
    have ha : (tripleCharges (sourceA2217 + difference 3 0) (sourceB2217 + difference 0 3) sourceC2217) = raw30427 := by
      apply Matrix.ext; unfold tripleCharges sourceA2217 sourceB2217 sourceC2217 difference raw30427; decide +kernel
    rw [ha]
    exact (canonical30427 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2217 + difference 3 1) (sourceB2217 + difference 1 3) sourceC2217) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4932) := by
    have ha : (tripleCharges (sourceA2217 + difference 3 1) (sourceB2217 + difference 1 3) sourceC2217) = raw30428 := by
      apply Matrix.ext; unfold tripleCharges sourceA2217 sourceB2217 sourceC2217 difference raw30428; decide +kernel
    rw [ha]
    exact (canonical30428 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2217 + difference 3 2) (sourceB2217 + difference 2 3) sourceC2217) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5043) := by
    have ha : (tripleCharges (sourceA2217 + difference 3 2) (sourceB2217 + difference 2 3) sourceC2217) = raw30429 := by
      apply Matrix.ext; unfold tripleCharges sourceA2217 sourceB2217 sourceC2217 difference raw30429; decide +kernel
    rw [ha]
    exact (canonical30429 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2217 + difference 3 4) (sourceB2217 + difference 4 3) sourceC2217) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5073) := by
    have ha : (tripleCharges (sourceA2217 + difference 3 4) (sourceB2217 + difference 4 3) sourceC2217) = raw30430 := by
      apply Matrix.ext; unfold tripleCharges sourceA2217 sourceB2217 sourceC2217 difference raw30430; decide +kernel
    rw [ha]
    exact (canonical30430 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2217 + difference 3 5) (sourceB2217 + difference 5 3) sourceC2217) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5073) := by
    have ha : (tripleCharges (sourceA2217 + difference 3 5) (sourceB2217 + difference 5 3) sourceC2217) = raw30431 := by
      apply Matrix.ext; unfold tripleCharges sourceA2217 sourceB2217 sourceC2217 difference raw30431; decide +kernel
    rw [ha]
    exact (canonical30431 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2217 + difference 4 0) (sourceB2217 + difference 0 4) sourceC2217) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4535) := by
    have ha : (tripleCharges (sourceA2217 + difference 4 0) (sourceB2217 + difference 0 4) sourceC2217) = raw30432 := by
      apply Matrix.ext; unfold tripleCharges sourceA2217 sourceB2217 sourceC2217 difference raw30432; decide +kernel
    rw [ha]
    exact (canonical30432 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2217 + difference 4 1) (sourceB2217 + difference 1 4) sourceC2217) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4935) := by
    have ha : (tripleCharges (sourceA2217 + difference 4 1) (sourceB2217 + difference 1 4) sourceC2217) = raw30433 := by
      apply Matrix.ext; unfold tripleCharges sourceA2217 sourceB2217 sourceC2217 difference raw30433; decide +kernel
    rw [ha]
    exact (canonical30433 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2217 + difference 4 2) (sourceB2217 + difference 2 4) sourceC2217) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4944) := by
    have ha : (tripleCharges (sourceA2217 + difference 4 2) (sourceB2217 + difference 2 4) sourceC2217) = raw30434 := by
      apply Matrix.ext; unfold tripleCharges sourceA2217 sourceB2217 sourceC2217 difference raw30434; decide +kernel
    rw [ha]
    exact (canonical30434 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2217 + difference 4 3) (sourceB2217 + difference 3 4) sourceC2217) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4930) := by
    have ha : (tripleCharges (sourceA2217 + difference 4 3) (sourceB2217 + difference 3 4) sourceC2217) = raw30435 := by
      apply Matrix.ext; unfold tripleCharges sourceA2217 sourceB2217 sourceC2217 difference raw30435; decide +kernel
    rw [ha]
    exact (canonical30435 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2217 + difference 4 5) (sourceB2217 + difference 5 4) sourceC2217) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5078) := by
    have ha : (tripleCharges (sourceA2217 + difference 4 5) (sourceB2217 + difference 5 4) sourceC2217) = raw30436 := by
      apply Matrix.ext; unfold tripleCharges sourceA2217 sourceB2217 sourceC2217 difference raw30436; decide +kernel
    rw [ha]
    exact (canonical30436 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2217 + difference 5 0) (sourceB2217 + difference 0 5) sourceC2217) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4535) := by
    have ha : (tripleCharges (sourceA2217 + difference 5 0) (sourceB2217 + difference 0 5) sourceC2217) = raw30437 := by
      apply Matrix.ext; unfold tripleCharges sourceA2217 sourceB2217 sourceC2217 difference raw30437; decide +kernel
    rw [ha]
    exact (canonical30437 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2217 + difference 5 1) (sourceB2217 + difference 1 5) sourceC2217) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4935) := by
    have ha : (tripleCharges (sourceA2217 + difference 5 1) (sourceB2217 + difference 1 5) sourceC2217) = raw30438 := by
      apply Matrix.ext; unfold tripleCharges sourceA2217 sourceB2217 sourceC2217 difference raw30438; decide +kernel
    rw [ha]
    exact (canonical30438 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2217 + difference 5 2) (sourceB2217 + difference 2 5) sourceC2217) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4944) := by
    have ha : (tripleCharges (sourceA2217 + difference 5 2) (sourceB2217 + difference 2 5) sourceC2217) = raw30439 := by
      apply Matrix.ext; unfold tripleCharges sourceA2217 sourceB2217 sourceC2217 difference raw30439; decide +kernel
    rw [ha]
    exact (canonical30439 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2217 + difference 5 3) (sourceB2217 + difference 3 5) sourceC2217) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4930) := by
    have ha : (tripleCharges (sourceA2217 + difference 5 3) (sourceB2217 + difference 3 5) sourceC2217) = raw30440 := by
      apply Matrix.ext; unfold tripleCharges sourceA2217 sourceB2217 sourceC2217 difference raw30440; decide +kernel
    rw [ha]
    exact (canonical30440 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2217 + difference 5 4) (sourceB2217 + difference 4 5) sourceC2217) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5078) := by
    have ha : (tripleCharges (sourceA2217 + difference 5 4) (sourceB2217 + difference 4 5) sourceC2217) = raw30441 := by
      apply Matrix.ext; unfold tripleCharges sourceA2217 sourceB2217 sourceC2217 difference raw30441; decide +kernel
    rw [ha]
    exact (canonical30441 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2217 sourceB2217 sourceC2217
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2217, Integer.Sparse.eval]
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

theorem reindexCheck1828 : Integer.Sparse.reindex keyMap MixedData.row1828 = numericRow1828 := by decide +kernel

theorem numericCheck1828 (x : Master → ℝ) : Integer.Sparse.eval numericRow1828 x =
    (4 : ℝ) * reducedSource1828 x := by
  norm_num [numericRow1828, reducedSource1828, Integer.Sparse.eval, Sparse.eval, nodeValue4530, nodeValue4535, nodeValue4554, nodeValue4593, nodeValue4930, nodeValue4932, nodeValue4935, nodeValue4944, nodeValue4950, nodeValue5039, nodeValue5043, nodeValue5073, nodeValue5078, nodeValue5104, nodeValue5130, nodeValue5189, nodeValue5259, nodeValue5356, nodeValue5393, nodeValue5404, nodeValue5410]
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

theorem reducedZero1828 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1828 (mixedVector B) = 0 := by
  have h4530 : mixedVector B (Sum.inr 4530) = Sparse.eval nodeValue4530 (mixedVector B) := by
    change mixedMoment B node4530 node4530Labels = _
    exact sound4530 B hB hF
  have h4535 : mixedVector B (Sum.inr 4535) = Sparse.eval nodeValue4535 (mixedVector B) := by
    change mixedMoment B node4535 node4535Labels = _
    exact sound4535 B hB hF
  have h4554 : mixedVector B (Sum.inr 4554) = Sparse.eval nodeValue4554 (mixedVector B) := by
    change mixedMoment B node4554 node4554Labels = _
    exact sound4554 B hB hF
  have h4593 : mixedVector B (Sum.inr 4593) = Sparse.eval nodeValue4593 (mixedVector B) := by
    change mixedMoment B node4593 node4593Labels = _
    exact sound4593 B hB hF
  have h4930 : mixedVector B (Sum.inr 4930) = Sparse.eval nodeValue4930 (mixedVector B) := by
    change mixedMoment B node4930 node4930Labels = _
    exact sound4930 B hB hF
  have h4932 : mixedVector B (Sum.inr 4932) = Sparse.eval nodeValue4932 (mixedVector B) := by
    change mixedMoment B node4932 node4932Labels = _
    exact sound4932 B hB hF
  have h4935 : mixedVector B (Sum.inr 4935) = Sparse.eval nodeValue4935 (mixedVector B) := by
    change mixedMoment B node4935 node4935Labels = _
    exact sound4935 B hB hF
  have h4944 : mixedVector B (Sum.inr 4944) = Sparse.eval nodeValue4944 (mixedVector B) := by
    change mixedMoment B node4944 node4944Labels = _
    exact sound4944 B hB hF
  have h4950 : mixedVector B (Sum.inr 4950) = Sparse.eval nodeValue4950 (mixedVector B) := by
    change mixedMoment B node4950 node4950Labels = _
    exact sound4950 B hB hF
  have h5039 : mixedVector B (Sum.inr 5039) = Sparse.eval nodeValue5039 (mixedVector B) := by
    change mixedMoment B node5039 node5039Labels = _
    exact sound5039 B hB hF
  have h5043 : mixedVector B (Sum.inr 5043) = Sparse.eval nodeValue5043 (mixedVector B) := by
    change mixedMoment B node5043 node5043Labels = _
    exact sound5043 B hB hF
  have h5073 : mixedVector B (Sum.inr 5073) = Sparse.eval nodeValue5073 (mixedVector B) := by
    change mixedMoment B node5073 node5073Labels = _
    exact sound5073 B hB hF
  have h5078 : mixedVector B (Sum.inr 5078) = Sparse.eval nodeValue5078 (mixedVector B) := by
    change mixedMoment B node5078 node5078Labels = _
    exact sound5078 B hB hF
  have h5104 : mixedVector B (Sum.inr 5104) = Sparse.eval nodeValue5104 (mixedVector B) := by
    change mixedMoment B node5104 node5104Labels = _
    exact sound5104 B hB hF
  have h5130 : mixedVector B (Sum.inr 5130) = Sparse.eval nodeValue5130 (mixedVector B) := by
    change mixedMoment B node5130 node5130Labels = _
    exact sound5130 B hB hF
  have h5189 : mixedVector B (Sum.inr 5189) = Sparse.eval nodeValue5189 (mixedVector B) := by
    change mixedMoment B node5189 node5189Labels = _
    exact sound5189 B hB hF
  have h5259 : mixedVector B (Sum.inr 5259) = Sparse.eval nodeValue5259 (mixedVector B) := by
    change mixedMoment B node5259 node5259Labels = _
    exact sound5259 B hB hF
  have h5356 : mixedVector B (Sum.inr 5356) = Sparse.eval nodeValue5356 (mixedVector B) := by
    change mixedMoment B node5356 node5356Labels = _
    exact sound5356 B hB hF
  have h5393 : mixedVector B (Sum.inr 5393) = Sparse.eval nodeValue5393 (mixedVector B) := by
    change mixedMoment B node5393 node5393Labels = _
    exact sound5393 B hB hF
  have h5404 : mixedVector B (Sum.inr 5404) = Sparse.eval nodeValue5404 (mixedVector B) := by
    change mixedMoment B node5404 node5404Labels = _
    exact sound5404 B hB hF
  have h5410 : mixedVector B (Sum.inr 5410) = Sparse.eval nodeValue5410 (mixedVector B) := by
    change mixedMoment B node5410 node5410Labels = _
    exact sound5410 B hB hF
  simpa only [sourceForm2217, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4530, h4535, h4554, h4593, h4930, h4932, h4935, h4944, h4950, h5039, h5043, h5073, h5078, h5104, h5130, h5189, h5259, h5356, h5393, h5404, h5410, reducedSource1828] using sourceEq2217 B hB

theorem rowSound1828_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1828 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1828, numericCheck1828, reducedZero1828 B hB hF, mul_zero]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedSourceBridge.rowSound1828_e_oai := @OAI.MUB6.Certificate.MixedSourceBridge.rowSound1828_e_oai
