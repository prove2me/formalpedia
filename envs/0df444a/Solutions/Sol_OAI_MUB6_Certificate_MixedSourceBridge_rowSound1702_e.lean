-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedSourceBridge.rowSound1702_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-08T21:35:29.92412+00:00
-- url     : https://prove2.me/submissions/a1a60b71-d6b4-4363-ab23-48a4b44a52e7

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E070
import Definitions.Def_OAIQ106E086
import Definitions.Def_OAIQ106E089
import Definitions.Def_OAIQ106E090
import Definitions.Def_OAIQ106E093
import Definitions.Def_OAIQ106E094
import Definitions.Def_OAIQ106E095
import Definitions.Def_OAIQ106E187
import Definitions.Def_OAIQ106E191
import Definitions.Def_OAIQ106E099
import Definitions.Def_OAIQ106E103
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical11
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical1446 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1446 raw1446Labels = mixedMoment B node4621 node4621Labels := by
  calc
    mixedMoment B raw1446 raw1446Labels = mixedMoment B raw1446step0 raw1446step0Labels := by
      have ha : raw1446step0 = (fun i j => raw1446 (permutation2 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1446step0 raw1446; decide +kernel
      have hl : raw1446step0Labels = raw1446Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1446 raw1446Labels permutation2 permutation4
    mixedMoment B raw1446step0 raw1446step0Labels = mixedMoment B raw1446step1 raw1446step1Labels := by
      have ha : raw1446step1 = raw1446step0 := by apply Matrix.ext; unfold raw1446step1 raw1446step0; decide +kernel
      have hl : raw1446step0Labels = labelEmbedding7 ∘ raw1446step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1446step0 raw1446step0Labels raw1446step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4621 node4621Labels := by rfl

theorem canonical1447 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1447 raw1447Labels = mixedMoment B node1297 node1297Labels := by
  calc
    mixedMoment B raw1447 raw1447Labels = mixedMoment B raw1447step0 raw1447step0Labels := by
      have ha : raw1447step0 = (fun i j => raw1447 (permutation2 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1447step0 raw1447; decide +kernel
      have hl : raw1447step0Labels = raw1447Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1447 raw1447Labels permutation2 permutation4
    _ = mixedMoment B node1297 node1297Labels := by rfl

theorem canonical1448 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1448 raw1448Labels = mixedMoment B node2289 node2289Labels := by
  calc
    mixedMoment B raw1448 raw1448Labels = mixedMoment B raw1448step0 raw1448step0Labels := by
      have ha : raw1448step0 = (fun i j => raw1448 (permutation7 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1448step0 raw1448; decide +kernel
      have hl : raw1448step0Labels = raw1448Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1448 raw1448Labels permutation7 permutation6
    mixedMoment B raw1448step0 raw1448step0Labels = mixedMoment B raw1448step1 raw1448step1Labels := by
      have ha : raw1448step1 = raw1448step0 := by apply Matrix.ext; unfold raw1448step1 raw1448step0; decide +kernel
      have hl : raw1448step0Labels = labelEmbedding1 ∘ raw1448step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1448step0 raw1448step0Labels raw1448step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2289 node2289Labels := by rfl

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

theorem canonical1791 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1791 raw1791Labels = mixedMoment B node4865 node4865Labels := by
  calc
    mixedMoment B raw1791 raw1791Labels = mixedMoment B raw1791step0 raw1791step0Labels := by
      have ha : raw1791step0 = (fun i j => raw1791 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1791step0 raw1791; decide +kernel
      have hl : raw1791step0Labels = raw1791Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1791 raw1791Labels permutation32 permutation4
    mixedMoment B raw1791step0 raw1791step0Labels = mixedMoment B raw1791step1 raw1791step1Labels := by
      have ha : raw1791step1 = raw1791step0 := by apply Matrix.ext; unfold raw1791step1 raw1791step0; decide +kernel
      have hl : raw1791step0Labels = labelEmbedding7 ∘ raw1791step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1791step0 raw1791step0Labels raw1791step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4865 node4865Labels := by rfl

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

theorem canonical1792 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1792 raw1792Labels = mixedMoment B node2106 node2106Labels := by
  calc
    mixedMoment B raw1792 raw1792Labels = mixedMoment B raw1792step0 raw1792step0Labels := by
      have ha : raw1792step0 = (fun i j => raw1792 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1792step0 raw1792; decide +kernel
      have hl : raw1792step0Labels = raw1792Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1792 raw1792Labels permutation32 permutation4
    _ = mixedMoment B node2106 node2106Labels := by rfl

theorem canonical1793 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1793 raw1793Labels = mixedMoment B node2242 node2242Labels := by
  calc
    mixedMoment B raw1793 raw1793Labels = mixedMoment B raw1793step0 raw1793step0Labels := by
      have ha : raw1793step0 = (fun i j => raw1793 (permutation40 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1793step0 raw1793; decide +kernel
      have hl : raw1793step0Labels = raw1793Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1793 raw1793Labels permutation40 permutation6
    mixedMoment B raw1793step0 raw1793step0Labels = mixedMoment B raw1793step1 raw1793step1Labels := by
      have ha : raw1793step1 = -raw1793step0 := by apply Matrix.ext; change ∀ i j, raw1793step1 i j = -(raw1793step0 i j); unfold raw1793step1 raw1793step0; decide +kernel
      have hl : raw1793step1Labels = raw1793step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1793step1 raw1793step1Labels = mixedMoment B raw1793step2 raw1793step2Labels := by
      have ha : raw1793step2 = raw1793step1 := by apply Matrix.ext; unfold raw1793step2 raw1793step1; decide +kernel
      have hl : raw1793step1Labels = labelEmbedding1 ∘ raw1793step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1793step1 raw1793step1Labels raw1793step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2242 node2242Labels := by rfl

theorem canonical1797 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1797 raw1797Labels = mixedMoment B node4868 node4868Labels := by
  calc
    mixedMoment B raw1797 raw1797Labels = mixedMoment B raw1797step0 raw1797step0Labels := by
      have ha : raw1797step0 = (fun i j => raw1797 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1797step0 raw1797; decide +kernel
      have hl : raw1797step0Labels = raw1797Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1797 raw1797Labels permutation8 permutation4
    mixedMoment B raw1797step0 raw1797step0Labels = mixedMoment B raw1797step1 raw1797step1Labels := by
      have ha : raw1797step1 = raw1797step0 := by apply Matrix.ext; unfold raw1797step1 raw1797step0; decide +kernel
      have hl : raw1797step0Labels = labelEmbedding7 ∘ raw1797step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1797step0 raw1797step0Labels raw1797step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4868 node4868Labels := by rfl

theorem canonical1798 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1798 raw1798Labels = mixedMoment B node2109 node2109Labels := by
  calc
    mixedMoment B raw1798 raw1798Labels = mixedMoment B raw1798step0 raw1798step0Labels := by
      have ha : raw1798step0 = (fun i j => raw1798 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1798step0 raw1798; decide +kernel
      have hl : raw1798step0Labels = raw1798Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1798 raw1798Labels permutation8 permutation4
    _ = mixedMoment B node2109 node2109Labels := by rfl

theorem canonical1799 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1799 raw1799Labels = mixedMoment B node2261 node2261Labels := by
  calc
    mixedMoment B raw1799 raw1799Labels = mixedMoment B raw1799step0 raw1799step0Labels := by
      have ha : raw1799step0 = (fun i j => raw1799 (permutation10 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1799step0 raw1799; decide +kernel
      have hl : raw1799step0Labels = raw1799Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1799 raw1799Labels permutation10 permutation6
    mixedMoment B raw1799step0 raw1799step0Labels = mixedMoment B raw1799step1 raw1799step1Labels := by
      have ha : raw1799step1 = -raw1799step0 := by apply Matrix.ext; change ∀ i j, raw1799step1 i j = -(raw1799step0 i j); unfold raw1799step1 raw1799step0; decide +kernel
      have hl : raw1799step1Labels = raw1799step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1799step1 raw1799step1Labels = mixedMoment B raw1799step2 raw1799step2Labels := by
      have ha : raw1799step2 = raw1799step1 := by apply Matrix.ext; unfold raw1799step2 raw1799step1; decide +kernel
      have hl : raw1799step1Labels = labelEmbedding1 ∘ raw1799step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1799step1 raw1799step1Labels raw1799step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2261 node2261Labels := by rfl

theorem canonical1806 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1806 raw1806Labels = mixedMoment B node4874 node4874Labels := by
  calc
    mixedMoment B raw1806 raw1806Labels = mixedMoment B raw1806step0 raw1806step0Labels := by
      have ha : raw1806step0 = (fun i j => raw1806 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1806step0 raw1806; decide +kernel
      have hl : raw1806step0Labels = raw1806Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1806 raw1806Labels permutation8 permutation4
    mixedMoment B raw1806step0 raw1806step0Labels = mixedMoment B raw1806step1 raw1806step1Labels := by
      have ha : raw1806step1 = raw1806step0 := by apply Matrix.ext; unfold raw1806step1 raw1806step0; decide +kernel
      have hl : raw1806step0Labels = labelEmbedding7 ∘ raw1806step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1806step0 raw1806step0Labels raw1806step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4874 node4874Labels := by rfl

theorem canonical1807 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1807 raw1807Labels = mixedMoment B node2115 node2115Labels := by
  calc
    mixedMoment B raw1807 raw1807Labels = mixedMoment B raw1807step0 raw1807step0Labels := by
      have ha : raw1807step0 = (fun i j => raw1807 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1807step0 raw1807; decide +kernel
      have hl : raw1807step0Labels = raw1807Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1807 raw1807Labels permutation8 permutation4
    _ = mixedMoment B node2115 node2115Labels := by rfl

theorem canonical1808 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1808 raw1808Labels = mixedMoment B node2276 node2276Labels := by
  calc
    mixedMoment B raw1808 raw1808Labels = mixedMoment B raw1808step0 raw1808step0Labels := by
      have ha : raw1808step0 = (fun i j => raw1808 (permutation10 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1808step0 raw1808; decide +kernel
      have hl : raw1808step0Labels = raw1808Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1808 raw1808Labels permutation10 permutation6
    mixedMoment B raw1808step0 raw1808step0Labels = mixedMoment B raw1808step1 raw1808step1Labels := by
      have ha : raw1808step1 = -raw1808step0 := by apply Matrix.ext; change ∀ i j, raw1808step1 i j = -(raw1808step0 i j); unfold raw1808step1 raw1808step0; decide +kernel
      have hl : raw1808step1Labels = raw1808step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1808step1 raw1808step1Labels = mixedMoment B raw1808step2 raw1808step2Labels := by
      have ha : raw1808step2 = raw1808step1 := by apply Matrix.ext; unfold raw1808step2 raw1808step1; decide +kernel
      have hl : raw1808step1Labels = labelEmbedding1 ∘ raw1808step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1808step1 raw1808step1Labels raw1808step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2276 node2276Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical153
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical19632 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19632 raw19632Labels = mixedMoment B node4370 node4370Labels := by
  calc
    mixedMoment B raw19632 raw19632Labels = mixedMoment B raw19632step0 raw19632step0Labels := by
      have hz : ∀ j, raw19632 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19632step0 = (fun i j => raw19632 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19632step0 raw19632; decide +kernel
      have hl : raw19632step0Labels = raw19632Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19632 raw19632Labels permutation434 hz
    mixedMoment B raw19632step0 raw19632step0Labels = mixedMoment B raw19632step1 raw19632step1Labels := by
      have hz : ∀ j, raw19632step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19632step1 = (fun i j => raw19632step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19632step1 raw19632step0; decide +kernel
      have hl : raw19632step1Labels = raw19632step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19632step0 raw19632step0Labels permutation80 hz
    mixedMoment B raw19632step1 raw19632step1Labels = mixedMoment B raw19632step2 raw19632step2Labels := by
      have ha : raw19632step2 = (fun i j => raw19632step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19632step2 raw19632step1; decide +kernel
      have hl : raw19632step2Labels = raw19632step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19632step1 raw19632step1Labels permutation31 permutation2
    mixedMoment B raw19632step2 raw19632step2Labels = mixedMoment B raw19632step3 raw19632step3Labels := by
      have ha : raw19632step3 = -raw19632step2 := by apply Matrix.ext; change ∀ i j, raw19632step3 i j = -(raw19632step2 i j); unfold raw19632step3 raw19632step2; decide +kernel
      have hl : raw19632step3Labels = raw19632step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4370 node4370Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical160
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical20487 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20487 raw20487Labels = mixedMoment B node4552 node4552Labels := by
  calc
    mixedMoment B raw20487 raw20487Labels = mixedMoment B raw20487step0 raw20487step0Labels := by
      have hz : ∀ j, raw20487 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20487step0 = (fun i j => raw20487 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20487step0 raw20487; decide +kernel
      have hl : raw20487step0Labels = raw20487Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20487 raw20487Labels permutation434 hz
    mixedMoment B raw20487step0 raw20487step0Labels = mixedMoment B raw20487step1 raw20487step1Labels := by
      have ha : raw20487step1 = (fun i j => raw20487step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20487step1 raw20487step0; decide +kernel
      have hl : raw20487step1Labels = raw20487step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20487step0 raw20487step0Labels permutation32 permutation3
    mixedMoment B raw20487step1 raw20487step1Labels = mixedMoment B raw20487step2 raw20487step2Labels := by
      have ha : raw20487step2 = raw20487step1 := by apply Matrix.ext; unfold raw20487step2 raw20487step1; decide +kernel
      have hl : raw20487step1Labels = labelEmbedding6 ∘ raw20487step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20487step1 raw20487step1Labels raw20487step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4552 node4552Labels := by rfl

theorem canonical20490 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20490 raw20490Labels = mixedMoment B node4552 node4552Labels := by
  calc
    mixedMoment B raw20490 raw20490Labels = mixedMoment B raw20490step0 raw20490step0Labels := by
      have hz : ∀ j, raw20490 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20490step0 = (fun i j => raw20490 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20490step0 raw20490; decide +kernel
      have hl : raw20490step0Labels = raw20490Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20490 raw20490Labels permutation346 hz
    mixedMoment B raw20490step0 raw20490step0Labels = mixedMoment B raw20490step1 raw20490step1Labels := by
      have ha : raw20490step1 = (fun i j => raw20490step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20490step1 raw20490step0; decide +kernel
      have hl : raw20490step1Labels = raw20490step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20490step0 raw20490step0Labels permutation32 permutation3
    mixedMoment B raw20490step1 raw20490step1Labels = mixedMoment B raw20490step2 raw20490step2Labels := by
      have ha : raw20490step2 = raw20490step1 := by apply Matrix.ext; unfold raw20490step2 raw20490step1; decide +kernel
      have hl : raw20490step1Labels = labelEmbedding6 ∘ raw20490step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20490step1 raw20490step1Labels raw20490step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4552 node4552Labels := by rfl

theorem canonical20493 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20493 raw20493Labels = mixedMoment B node4560 node4560Labels := by
  calc
    mixedMoment B raw20493 raw20493Labels = mixedMoment B raw20493step0 raw20493step0Labels := by
      have hz : ∀ j, raw20493 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20493step0 = (fun i j => raw20493 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20493step0 raw20493; decide +kernel
      have hl : raw20493step0Labels = raw20493Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20493 raw20493Labels permutation434 hz
    mixedMoment B raw20493step0 raw20493step0Labels = mixedMoment B raw20493step1 raw20493step1Labels := by
      have hz : ∀ j, raw20493step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20493step1 = (fun i j => raw20493step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20493step1 raw20493step0; decide +kernel
      have hl : raw20493step1Labels = raw20493step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20493step0 raw20493step0Labels permutation80 hz
    mixedMoment B raw20493step1 raw20493step1Labels = mixedMoment B raw20493step2 raw20493step2Labels := by
      have ha : raw20493step2 = (fun i j => raw20493step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20493step2 raw20493step1; decide +kernel
      have hl : raw20493step2Labels = raw20493step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20493step1 raw20493step1Labels permutation8 permutation3
    mixedMoment B raw20493step2 raw20493step2Labels = mixedMoment B raw20493step3 raw20493step3Labels := by
      have ha : raw20493step3 = raw20493step2 := by apply Matrix.ext; unfold raw20493step3 raw20493step2; decide +kernel
      have hl : raw20493step2Labels = labelEmbedding6 ∘ raw20493step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20493step2 raw20493step2Labels raw20493step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4560 node4560Labels := by rfl

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

theorem canonical2295 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2295 raw2295Labels = mixedMoment B node5291 node5291Labels := by
  calc
    mixedMoment B raw2295 raw2295Labels = mixedMoment B raw2295step0 raw2295step0Labels := by
      have ha : raw2295step0 = (fun i j => raw2295 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2295step0 raw2295; decide +kernel
      have hl : raw2295step0Labels = raw2295Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2295 raw2295Labels permutation8 permutation4
    mixedMoment B raw2295step0 raw2295step0Labels = mixedMoment B raw2295step1 raw2295step1Labels := by
      have ha : raw2295step1 = raw2295step0 := by apply Matrix.ext; unfold raw2295step1 raw2295step0; decide +kernel
      have hl : raw2295step0Labels = labelEmbedding7 ∘ raw2295step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2295step0 raw2295step0Labels raw2295step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5291 node5291Labels := by rfl

theorem canonical2296 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2296 raw2296Labels = mixedMoment B node2765 node2765Labels := by
  calc
    mixedMoment B raw2296 raw2296Labels = mixedMoment B raw2296step0 raw2296step0Labels := by
      have ha : raw2296step0 = (fun i j => raw2296 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2296step0 raw2296; decide +kernel
      have hl : raw2296step0Labels = raw2296Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2296 raw2296Labels permutation8 permutation4
    _ = mixedMoment B node2765 node2765Labels := by rfl

theorem canonical2297 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2297 raw2297Labels = mixedMoment B node3582 node3582Labels := by
  calc
    mixedMoment B raw2297 raw2297Labels = mixedMoment B raw2297step0 raw2297step0Labels := by
      have ha : raw2297step0 = (fun i j => raw2297 (permutation10 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2297step0 raw2297; decide +kernel
      have hl : raw2297step0Labels = raw2297Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2297 raw2297Labels permutation10 permutation6
    mixedMoment B raw2297step0 raw2297step0Labels = mixedMoment B raw2297step1 raw2297step1Labels := by
      have ha : raw2297step1 = -raw2297step0 := by apply Matrix.ext; change ∀ i j, raw2297step1 i j = -(raw2297step0 i j); unfold raw2297step1 raw2297step0; decide +kernel
      have hl : raw2297step1Labels = raw2297step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2297step1 raw2297step1Labels = mixedMoment B raw2297step2 raw2297step2Labels := by
      have ha : raw2297step2 = raw2297step1 := by apply Matrix.ext; unfold raw2297step2 raw2297step1; decide +kernel
      have hl : raw2297step1Labels = labelEmbedding1 ∘ raw2297step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2297step1 raw2297step1Labels raw2297step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3582 node3582Labels := by rfl

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

theorem canonical2319 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2319 raw2319Labels = mixedMoment B node5305 node5305Labels := by
  calc
    mixedMoment B raw2319 raw2319Labels = mixedMoment B raw2319step0 raw2319step0Labels := by
      have ha : raw2319step0 = (fun i j => raw2319 (permutation2 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2319step0 raw2319; decide +kernel
      have hl : raw2319step0Labels = raw2319Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2319 raw2319Labels permutation2 permutation4
    mixedMoment B raw2319step0 raw2319step0Labels = mixedMoment B raw2319step1 raw2319step1Labels := by
      have ha : raw2319step1 = raw2319step0 := by apply Matrix.ext; unfold raw2319step1 raw2319step0; decide +kernel
      have hl : raw2319step0Labels = labelEmbedding7 ∘ raw2319step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2319step0 raw2319step0Labels raw2319step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5305 node5305Labels := by rfl

theorem canonical2320 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2320 raw2320Labels = mixedMoment B node2783 node2783Labels := by
  calc
    mixedMoment B raw2320 raw2320Labels = mixedMoment B raw2320step0 raw2320step0Labels := by
      have ha : raw2320step0 = (fun i j => raw2320 (permutation2 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2320step0 raw2320; decide +kernel
      have hl : raw2320step0Labels = raw2320Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2320 raw2320Labels permutation2 permutation4
    _ = mixedMoment B node2783 node2783Labels := by rfl

theorem canonical2321 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2321 raw2321Labels = mixedMoment B node2783 node2783Labels := by
  calc
    mixedMoment B raw2321 raw2321Labels = mixedMoment B raw2321step0 raw2321step0Labels := by
      have ha : raw2321step0 = (fun i j => raw2321 (permutation7 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2321step0 raw2321; decide +kernel
      have hl : raw2321step0Labels = raw2321Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2321 raw2321Labels permutation7 permutation6
    mixedMoment B raw2321step0 raw2321step0Labels = mixedMoment B raw2321step1 raw2321step1Labels := by
      have ha : raw2321step1 = raw2321step0 := by apply Matrix.ext; unfold raw2321step1 raw2321step0; decide +kernel
      have hl : raw2321step0Labels = labelEmbedding1 ∘ raw2321step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2321step0 raw2321step0Labels raw2321step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2783 node2783Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical223
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical28562 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28562 raw28562Labels = mixedMoment B node4874 node4874Labels := by
  calc
    mixedMoment B raw28562 raw28562Labels = mixedMoment B raw28562step0 raw28562step0Labels := by
      have hz : ∀ j, raw28562 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28562step0 = (fun i j => raw28562 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28562step0 raw28562; decide +kernel
      have hl : raw28562step0Labels = raw28562Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28562 raw28562Labels permutation434 hz
    mixedMoment B raw28562step0 raw28562step0Labels = mixedMoment B raw28562step1 raw28562step1Labels := by
      have hz : ∀ j, raw28562step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw28562step1 = (fun i j => raw28562step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw28562step1 raw28562step0; decide +kernel
      have hl : raw28562step1Labels = raw28562step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28562step0 raw28562step0Labels permutation80 hz
    mixedMoment B raw28562step1 raw28562step1Labels = mixedMoment B raw28562step2 raw28562step2Labels := by
      have ha : raw28562step2 = (fun i j => raw28562step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28562step2 raw28562step1; decide +kernel
      have hl : raw28562step2Labels = raw28562step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28562step1 raw28562step1Labels permutation31 permutation2
    mixedMoment B raw28562step2 raw28562step2Labels = mixedMoment B raw28562step3 raw28562step3Labels := by
      have ha : raw28562step3 = -raw28562step2 := by apply Matrix.ext; change ∀ i j, raw28562step3 i j = -(raw28562step2 i j); unfold raw28562step3 raw28562step2; decide +kernel
      have hl : raw28562step3Labels = raw28562step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4874 node4874Labels := by rfl

theorem canonical28563 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28563 raw28563Labels = mixedMoment B node4865 node4865Labels := by
  calc
    mixedMoment B raw28563 raw28563Labels = mixedMoment B raw28563step0 raw28563step0Labels := by
      have hz : ∀ j, raw28563 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28563step0 = (fun i j => raw28563 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28563step0 raw28563; decide +kernel
      have hl : raw28563step0Labels = raw28563Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28563 raw28563Labels permutation434 hz
    mixedMoment B raw28563step0 raw28563step0Labels = mixedMoment B raw28563step1 raw28563step1Labels := by
      have ha : raw28563step1 = (fun i j => raw28563step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28563step1 raw28563step0; decide +kernel
      have hl : raw28563step1Labels = raw28563step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28563step0 raw28563step0Labels permutation149 permutation2
    mixedMoment B raw28563step1 raw28563step1Labels = mixedMoment B raw28563step2 raw28563step2Labels := by
      have ha : raw28563step2 = -raw28563step1 := by apply Matrix.ext; change ∀ i j, raw28563step2 i j = -(raw28563step1 i j); unfold raw28563step2 raw28563step1; decide +kernel
      have hl : raw28563step2Labels = raw28563step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4865 node4865Labels := by rfl

theorem canonical28564 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28564 raw28564Labels = mixedMoment B node4865 node4865Labels := by
  calc
    mixedMoment B raw28564 raw28564Labels = mixedMoment B raw28564step0 raw28564step0Labels := by
      have hz : ∀ j, raw28564 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28564step0 = (fun i j => raw28564 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28564step0 raw28564; decide +kernel
      have hl : raw28564step0Labels = raw28564Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28564 raw28564Labels permutation346 hz
    mixedMoment B raw28564step0 raw28564step0Labels = mixedMoment B raw28564step1 raw28564step1Labels := by
      have ha : raw28564step1 = (fun i j => raw28564step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28564step1 raw28564step0; decide +kernel
      have hl : raw28564step1Labels = raw28564step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28564step0 raw28564step0Labels permutation149 permutation2
    mixedMoment B raw28564step1 raw28564step1Labels = mixedMoment B raw28564step2 raw28564step2Labels := by
      have ha : raw28564step2 = -raw28564step1 := by apply Matrix.ext; change ∀ i j, raw28564step2 i j = -(raw28564step1 i j); unfold raw28564step2 raw28564step1; decide +kernel
      have hl : raw28564step2Labels = raw28564step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4865 node4865Labels := by rfl

theorem canonical28565 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28565 raw28565Labels = mixedMoment B node4776 node4776Labels := by
  calc
    mixedMoment B raw28565 raw28565Labels = mixedMoment B raw28565step0 raw28565step0Labels := by
      have hz : ∀ j, raw28565 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28565step0 = (fun i j => raw28565 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28565step0 raw28565; decide +kernel
      have hl : raw28565step0Labels = raw28565Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28565 raw28565Labels permutation434 hz
    mixedMoment B raw28565step0 raw28565step0Labels = mixedMoment B raw28565step1 raw28565step1Labels := by
      have ha : raw28565step1 = (fun i j => raw28565step0 (permutation145 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28565step1 raw28565step0; decide +kernel
      have hl : raw28565step1Labels = raw28565step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28565step0 raw28565step0Labels permutation145 permutation2
    mixedMoment B raw28565step1 raw28565step1Labels = mixedMoment B raw28565step2 raw28565step2Labels := by
      have ha : raw28565step2 = -raw28565step1 := by apply Matrix.ext; change ∀ i j, raw28565step2 i j = -(raw28565step1 i j); unfold raw28565step2 raw28565step1; decide +kernel
      have hl : raw28565step2Labels = raw28565step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4776 node4776Labels := by rfl

theorem canonical28566 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28566 raw28566Labels = mixedMoment B node4771 node4771Labels := by
  calc
    mixedMoment B raw28566 raw28566Labels = mixedMoment B raw28566step0 raw28566step0Labels := by
      have ha : raw28566step0 = (fun i j => raw28566 (permutation644 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28566step0 raw28566; decide +kernel
      have hl : raw28566step0Labels = raw28566Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28566 raw28566Labels permutation644 permutation2
    mixedMoment B raw28566step0 raw28566step0Labels = mixedMoment B raw28566step1 raw28566step1Labels := by
      have ha : raw28566step1 = -raw28566step0 := by apply Matrix.ext; change ∀ i j, raw28566step1 i j = -(raw28566step0 i j); unfold raw28566step1 raw28566step0; decide +kernel
      have hl : raw28566step1Labels = raw28566step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4771 node4771Labels := by rfl

theorem canonical28567 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28567 raw28567Labels = mixedMoment B node4776 node4776Labels := by
  calc
    mixedMoment B raw28567 raw28567Labels = mixedMoment B raw28567step0 raw28567step0Labels := by
      have hz : ∀ j, raw28567 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28567step0 = (fun i j => raw28567 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28567step0 raw28567; decide +kernel
      have hl : raw28567step0Labels = raw28567Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28567 raw28567Labels permutation346 hz
    mixedMoment B raw28567step0 raw28567step0Labels = mixedMoment B raw28567step1 raw28567step1Labels := by
      have ha : raw28567step1 = (fun i j => raw28567step0 (permutation145 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28567step1 raw28567step0; decide +kernel
      have hl : raw28567step1Labels = raw28567step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28567step0 raw28567step0Labels permutation145 permutation2
    mixedMoment B raw28567step1 raw28567step1Labels = mixedMoment B raw28567step2 raw28567step2Labels := by
      have ha : raw28567step2 = -raw28567step1 := by apply Matrix.ext; change ∀ i j, raw28567step2 i j = -(raw28567step1 i j); unfold raw28567step2 raw28567step1; decide +kernel
      have hl : raw28567step2Labels = raw28567step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4776 node4776Labels := by rfl

theorem canonical28568 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28568 raw28568Labels = mixedMoment B node4771 node4771Labels := by
  calc
    mixedMoment B raw28568 raw28568Labels = mixedMoment B raw28568step0 raw28568step0Labels := by
      have ha : raw28568step0 = (fun i j => raw28568 (permutation662 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28568step0 raw28568; decide +kernel
      have hl : raw28568step0Labels = raw28568Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28568 raw28568Labels permutation662 permutation2
    mixedMoment B raw28568step0 raw28568step0Labels = mixedMoment B raw28568step1 raw28568step1Labels := by
      have ha : raw28568step1 = -raw28568step0 := by apply Matrix.ext; change ∀ i j, raw28568step1 i j = -(raw28568step0 i j); unfold raw28568step1 raw28568step0; decide +kernel
      have hl : raw28568step1Labels = raw28568step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4771 node4771Labels := by rfl

theorem canonical28569 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28569 raw28569Labels = mixedMoment B node4704 node4704Labels := by
  calc
    mixedMoment B raw28569 raw28569Labels = mixedMoment B raw28569step0 raw28569step0Labels := by
      have hz : ∀ j, raw28569 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28569step0 = (fun i j => raw28569 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28569step0 raw28569; decide +kernel
      have hl : raw28569step0Labels = raw28569Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28569 raw28569Labels permutation434 hz
    mixedMoment B raw28569step0 raw28569step0Labels = mixedMoment B raw28569step1 raw28569step1Labels := by
      have hz : ∀ j, raw28569step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw28569step1 = (fun i j => raw28569step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw28569step1 raw28569step0; decide +kernel
      have hl : raw28569step1Labels = raw28569step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28569step0 raw28569step0Labels permutation80 hz
    mixedMoment B raw28569step1 raw28569step1Labels = mixedMoment B raw28569step2 raw28569step2Labels := by
      have ha : raw28569step2 = (fun i j => raw28569step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28569step2 raw28569step1; decide +kernel
      have hl : raw28569step2Labels = raw28569step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28569step1 raw28569step1Labels permutation31 permutation2
    mixedMoment B raw28569step2 raw28569step2Labels = mixedMoment B raw28569step3 raw28569step3Labels := by
      have ha : raw28569step3 = -raw28569step2 := by apply Matrix.ext; change ∀ i j, raw28569step3 i j = -(raw28569step2 i j); unfold raw28569step3 raw28569step2; decide +kernel
      have hl : raw28569step3Labels = raw28569step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4704 node4704Labels := by rfl

theorem canonical28570 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28570 raw28570Labels = mixedMoment B node4697 node4697Labels := by
  calc
    mixedMoment B raw28570 raw28570Labels = mixedMoment B raw28570step0 raw28570step0Labels := by
      have hz : ∀ j, raw28570 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28570step0 = (fun i j => raw28570 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28570step0 raw28570; decide +kernel
      have hl : raw28570step0Labels = raw28570Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28570 raw28570Labels permutation434 hz
    mixedMoment B raw28570step0 raw28570step0Labels = mixedMoment B raw28570step1 raw28570step1Labels := by
      have ha : raw28570step1 = (fun i j => raw28570step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28570step1 raw28570step0; decide +kernel
      have hl : raw28570step1Labels = raw28570step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28570step0 raw28570step0Labels permutation149 permutation2
    mixedMoment B raw28570step1 raw28570step1Labels = mixedMoment B raw28570step2 raw28570step2Labels := by
      have ha : raw28570step2 = -raw28570step1 := by apply Matrix.ext; change ∀ i j, raw28570step2 i j = -(raw28570step1 i j); unfold raw28570step2 raw28570step1; decide +kernel
      have hl : raw28570step2Labels = raw28570step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4697 node4697Labels := by rfl

theorem canonical28571 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28571 raw28571Labels = mixedMoment B node4697 node4697Labels := by
  calc
    mixedMoment B raw28571 raw28571Labels = mixedMoment B raw28571step0 raw28571step0Labels := by
      have hz : ∀ j, raw28571 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28571step0 = (fun i j => raw28571 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28571step0 raw28571; decide +kernel
      have hl : raw28571step0Labels = raw28571Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28571 raw28571Labels permutation346 hz
    mixedMoment B raw28571step0 raw28571step0Labels = mixedMoment B raw28571step1 raw28571step1Labels := by
      have ha : raw28571step1 = (fun i j => raw28571step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28571step1 raw28571step0; decide +kernel
      have hl : raw28571step1Labels = raw28571step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28571step0 raw28571step0Labels permutation149 permutation2
    mixedMoment B raw28571step1 raw28571step1Labels = mixedMoment B raw28571step2 raw28571step2Labels := by
      have ha : raw28571step2 = -raw28571step1 := by apply Matrix.ext; change ∀ i j, raw28571step2 i j = -(raw28571step1 i j); unfold raw28571step2 raw28571step1; decide +kernel
      have hl : raw28571step2Labels = raw28571step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4697 node4697Labels := by rfl

theorem canonical28572 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28572 raw28572Labels = mixedMoment B node4373 node4373Labels := by
  calc
    mixedMoment B raw28572 raw28572Labels = mixedMoment B raw28572step0 raw28572step0Labels := by
      have hz : ∀ j, raw28572 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28572step0 = (fun i j => raw28572 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28572step0 raw28572; decide +kernel
      have hl : raw28572step0Labels = raw28572Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28572 raw28572Labels permutation434 hz
    mixedMoment B raw28572step0 raw28572step0Labels = mixedMoment B raw28572step1 raw28572step1Labels := by
      have hz : ∀ j, raw28572step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw28572step1 = (fun i j => raw28572step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw28572step1 raw28572step0; decide +kernel
      have hl : raw28572step1Labels = raw28572step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28572step0 raw28572step0Labels permutation80 hz
    mixedMoment B raw28572step1 raw28572step1Labels = mixedMoment B raw28572step2 raw28572step2Labels := by
      have ha : raw28572step2 = (fun i j => raw28572step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28572step2 raw28572step1; decide +kernel
      have hl : raw28572step2Labels = raw28572step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28572step1 raw28572step1Labels permutation31 permutation2
    mixedMoment B raw28572step2 raw28572step2Labels = mixedMoment B raw28572step3 raw28572step3Labels := by
      have ha : raw28572step3 = -raw28572step2 := by apply Matrix.ext; change ∀ i j, raw28572step3 i j = -(raw28572step2 i j); unfold raw28572step3 raw28572step2; decide +kernel
      have hl : raw28572step3Labels = raw28572step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4373 node4373Labels := by rfl

theorem canonical28573 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28573 raw28573Labels = mixedMoment B node4365 node4365Labels := by
  calc
    mixedMoment B raw28573 raw28573Labels = mixedMoment B raw28573step0 raw28573step0Labels := by
      have hz : ∀ j, raw28573 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28573step0 = (fun i j => raw28573 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28573step0 raw28573; decide +kernel
      have hl : raw28573step0Labels = raw28573Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28573 raw28573Labels permutation434 hz
    mixedMoment B raw28573step0 raw28573step0Labels = mixedMoment B raw28573step1 raw28573step1Labels := by
      have ha : raw28573step1 = (fun i j => raw28573step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28573step1 raw28573step0; decide +kernel
      have hl : raw28573step1Labels = raw28573step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28573step0 raw28573step0Labels permutation149 permutation2
    mixedMoment B raw28573step1 raw28573step1Labels = mixedMoment B raw28573step2 raw28573step2Labels := by
      have ha : raw28573step2 = -raw28573step1 := by apply Matrix.ext; change ∀ i j, raw28573step2 i j = -(raw28573step1 i j); unfold raw28573step2 raw28573step1; decide +kernel
      have hl : raw28573step2Labels = raw28573step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4365 node4365Labels := by rfl

theorem canonical28574 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28574 raw28574Labels = mixedMoment B node4365 node4365Labels := by
  calc
    mixedMoment B raw28574 raw28574Labels = mixedMoment B raw28574step0 raw28574step0Labels := by
      have hz : ∀ j, raw28574 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28574step0 = (fun i j => raw28574 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28574step0 raw28574; decide +kernel
      have hl : raw28574step0Labels = raw28574Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28574 raw28574Labels permutation346 hz
    mixedMoment B raw28574step0 raw28574step0Labels = mixedMoment B raw28574step1 raw28574step1Labels := by
      have ha : raw28574step1 = (fun i j => raw28574step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28574step1 raw28574step0; decide +kernel
      have hl : raw28574step1Labels = raw28574step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28574step0 raw28574step0Labels permutation149 permutation2
    mixedMoment B raw28574step1 raw28574step1Labels = mixedMoment B raw28574step2 raw28574step2Labels := by
      have ha : raw28574step2 = -raw28574step1 := by apply Matrix.ext; change ∀ i j, raw28574step2 i j = -(raw28574step1 i j); unfold raw28574step2 raw28574step1; decide +kernel
      have hl : raw28574step2Labels = raw28574step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4365 node4365Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical39
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical5101 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5101 raw5101Labels = mixedMoment B node4894 node4894Labels := by
  calc
    mixedMoment B raw5101 raw5101Labels = mixedMoment B raw5101step0 raw5101step0Labels := by
      have hz : ∀ j, raw5101 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5101step0 = (fun i j => raw5101 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5101step0 raw5101; decide +kernel
      have hl : raw5101step0Labels = raw5101Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5101 raw5101Labels permutation434 hz
    mixedMoment B raw5101step0 raw5101step0Labels = mixedMoment B raw5101step1 raw5101step1Labels := by
      have hz : ∀ j, raw5101step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5101step1 = (fun i j => raw5101step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5101step1 raw5101step0; decide +kernel
      have hl : raw5101step1Labels = raw5101step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5101step0 raw5101step0Labels permutation80 hz
    mixedMoment B raw5101step1 raw5101step1Labels = mixedMoment B raw5101step2 raw5101step2Labels := by
      have ha : raw5101step2 = (fun i j => raw5101step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5101step2 raw5101step1; decide +kernel
      have hl : raw5101step2Labels = raw5101step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5101step1 raw5101step1Labels permutation31 permutation2
    mixedMoment B raw5101step2 raw5101step2Labels = mixedMoment B raw5101step3 raw5101step3Labels := by
      have ha : raw5101step3 = -raw5101step2 := by apply Matrix.ext; change ∀ i j, raw5101step3 i j = -(raw5101step2 i j); unfold raw5101step3 raw5101step2; decide +kernel
      have hl : raw5101step3Labels = raw5101step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4894 node4894Labels := by rfl

theorem canonical5112 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5112 raw5112Labels = mixedMoment B node4804 node4804Labels := by
  calc
    mixedMoment B raw5112 raw5112Labels = mixedMoment B raw5112step0 raw5112step0Labels := by
      have hz : ∀ j, raw5112 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5112step0 = (fun i j => raw5112 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5112step0 raw5112; decide +kernel
      have hl : raw5112step0Labels = raw5112Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5112 raw5112Labels permutation434 hz
    mixedMoment B raw5112step0 raw5112step0Labels = mixedMoment B raw5112step1 raw5112step1Labels := by
      have ha : raw5112step1 = (fun i j => raw5112step0 (permutation145 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5112step1 raw5112step0; decide +kernel
      have hl : raw5112step1Labels = raw5112step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5112step0 raw5112step0Labels permutation145 permutation2
    mixedMoment B raw5112step1 raw5112step1Labels = mixedMoment B raw5112step2 raw5112step2Labels := by
      have ha : raw5112step2 = -raw5112step1 := by apply Matrix.ext; change ∀ i j, raw5112step2 i j = -(raw5112step1 i j); unfold raw5112step2 raw5112step1; decide +kernel
      have hl : raw5112step2Labels = raw5112step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4804 node4804Labels := by rfl

theorem canonical5117 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5117 raw5117Labels = mixedMoment B node4804 node4804Labels := by
  calc
    mixedMoment B raw5117 raw5117Labels = mixedMoment B raw5117step0 raw5117step0Labels := by
      have hz : ∀ j, raw5117 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw5117step0 = (fun i j => raw5117 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw5117step0 raw5117; decide +kernel
      have hl : raw5117step0Labels = raw5117Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5117 raw5117Labels permutation346 hz
    mixedMoment B raw5117step0 raw5117step0Labels = mixedMoment B raw5117step1 raw5117step1Labels := by
      have ha : raw5117step1 = (fun i j => raw5117step0 (permutation145 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5117step1 raw5117step0; decide +kernel
      have hl : raw5117step1Labels = raw5117step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5117step0 raw5117step0Labels permutation145 permutation2
    mixedMoment B raw5117step1 raw5117step1Labels = mixedMoment B raw5117step2 raw5117step2Labels := by
      have ha : raw5117step2 = -raw5117step1 := by apply Matrix.ext; change ∀ i j, raw5117step2 i j = -(raw5117step1 i j); unfold raw5117step2 raw5117step1; decide +kernel
      have hl : raw5117step2Labels = raw5117step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4804 node4804Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical40
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical5121 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5121 raw5121Labels = mixedMoment B node4621 node4621Labels := by
  calc
    mixedMoment B raw5121 raw5121Labels = mixedMoment B raw5121step0 raw5121step0Labels := by
      have hz : ∀ j, raw5121 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5121step0 = (fun i j => raw5121 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5121step0 raw5121; decide +kernel
      have hl : raw5121step0Labels = raw5121Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5121 raw5121Labels permutation434 hz
    mixedMoment B raw5121step0 raw5121step0Labels = mixedMoment B raw5121step1 raw5121step1Labels := by
      have hz : ∀ j, raw5121step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5121step1 = (fun i j => raw5121step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5121step1 raw5121step0; decide +kernel
      have hl : raw5121step1Labels = raw5121step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5121step0 raw5121step0Labels permutation80 hz
    mixedMoment B raw5121step1 raw5121step1Labels = mixedMoment B raw5121step2 raw5121step2Labels := by
      have hz : ∀ j, raw5121step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw5121step2 = (fun i j => raw5121step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw5121step2 raw5121step1; decide +kernel
      have hl : raw5121step2Labels = raw5121step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5121step1 raw5121step1Labels permutation14 hz
    _ = mixedMoment B node4621 node4621Labels := by rfl

theorem canonical5123 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5123 raw5123Labels = mixedMoment B node4868 node4868Labels := by
  calc
    mixedMoment B raw5123 raw5123Labels = mixedMoment B raw5123step0 raw5123step0Labels := by
      have hz : ∀ j, raw5123 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5123step0 = (fun i j => raw5123 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5123step0 raw5123; decide +kernel
      have hl : raw5123step0Labels = raw5123Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5123 raw5123Labels permutation434 hz
    mixedMoment B raw5123step0 raw5123step0Labels = mixedMoment B raw5123step1 raw5123step1Labels := by
      have hz : ∀ j, raw5123step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw5123step1 = (fun i j => raw5123step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw5123step1 raw5123step0; decide +kernel
      have hl : raw5123step1Labels = raw5123step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5123step0 raw5123step0Labels permutation56 hz
    mixedMoment B raw5123step1 raw5123step1Labels = mixedMoment B raw5123step2 raw5123step2Labels := by
      have ha : raw5123step2 = (fun i j => raw5123step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5123step2 raw5123step1; decide +kernel
      have hl : raw5123step2Labels = raw5123step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5123step1 raw5123step1Labels permutation31 permutation2
    mixedMoment B raw5123step2 raw5123step2Labels = mixedMoment B raw5123step3 raw5123step3Labels := by
      have ha : raw5123step3 = -raw5123step2 := by apply Matrix.ext; change ∀ i j, raw5123step3 i j = -(raw5123step2 i j); unfold raw5123step3 raw5123step2; decide +kernel
      have hl : raw5123step3Labels = raw5123step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4868 node4868Labels := by rfl

theorem canonical5124 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5124 raw5124Labels = mixedMoment B node4868 node4868Labels := by
  calc
    mixedMoment B raw5124 raw5124Labels = mixedMoment B raw5124step0 raw5124step0Labels := by
      have hz : ∀ j, raw5124 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw5124step0 = (fun i j => raw5124 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw5124step0 raw5124; decide +kernel
      have hl : raw5124step0Labels = raw5124Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5124 raw5124Labels permutation346 hz
    mixedMoment B raw5124step0 raw5124step0Labels = mixedMoment B raw5124step1 raw5124step1Labels := by
      have hz : ∀ j, raw5124step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw5124step1 = (fun i j => raw5124step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw5124step1 raw5124step0; decide +kernel
      have hl : raw5124step1Labels = raw5124step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5124step0 raw5124step0Labels permutation56 hz
    mixedMoment B raw5124step1 raw5124step1Labels = mixedMoment B raw5124step2 raw5124step2Labels := by
      have ha : raw5124step2 = (fun i j => raw5124step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5124step2 raw5124step1; decide +kernel
      have hl : raw5124step2Labels = raw5124step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5124step1 raw5124step1Labels permutation31 permutation2
    mixedMoment B raw5124step2 raw5124step2Labels = mixedMoment B raw5124step3 raw5124step3Labels := by
      have ha : raw5124step3 = -raw5124step2 := by apply Matrix.ext; change ∀ i j, raw5124step3 i j = -(raw5124step2 i j); unfold raw5124step3 raw5124step2; decide +kernel
      have hl : raw5124step3Labels = raw5124step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4868 node4868Labels := by rfl

theorem canonical5125 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5125 raw5125Labels = mixedMoment B node5305 node5305Labels := by
  calc
    mixedMoment B raw5125 raw5125Labels = mixedMoment B raw5125step0 raw5125step0Labels := by
      have hz : ∀ j, raw5125 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5125step0 = (fun i j => raw5125 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5125step0 raw5125; decide +kernel
      have hl : raw5125step0Labels = raw5125Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5125 raw5125Labels permutation434 hz
    mixedMoment B raw5125step0 raw5125step0Labels = mixedMoment B raw5125step1 raw5125step1Labels := by
      have hz : ∀ j, raw5125step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5125step1 = (fun i j => raw5125step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5125step1 raw5125step0; decide +kernel
      have hl : raw5125step1Labels = raw5125step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5125step0 raw5125step0Labels permutation80 hz
    mixedMoment B raw5125step1 raw5125step1Labels = mixedMoment B raw5125step2 raw5125step2Labels := by
      have hz : ∀ j, raw5125step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw5125step2 = (fun i j => raw5125step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw5125step2 raw5125step1; decide +kernel
      have hl : raw5125step2Labels = raw5125step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5125step1 raw5125step1Labels permutation14 hz
    _ = mixedMoment B node5305 node5305Labels := by rfl

theorem canonical5127 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5127 raw5127Labels = mixedMoment B node4460 node4460Labels := by
  calc
    mixedMoment B raw5127 raw5127Labels = mixedMoment B raw5127step0 raw5127step0Labels := by
      have hz : ∀ j, raw5127 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5127step0 = (fun i j => raw5127 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5127step0 raw5127; decide +kernel
      have hl : raw5127step0Labels = raw5127Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5127 raw5127Labels permutation434 hz
    mixedMoment B raw5127step0 raw5127step0Labels = mixedMoment B raw5127step1 raw5127step1Labels := by
      have hz : ∀ j, raw5127step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5127step1 = (fun i j => raw5127step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5127step1 raw5127step0; decide +kernel
      have hl : raw5127step1Labels = raw5127step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5127step0 raw5127step0Labels permutation80 hz
    mixedMoment B raw5127step1 raw5127step1Labels = mixedMoment B raw5127step2 raw5127step2Labels := by
      have ha : raw5127step2 = (fun i j => raw5127step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5127step2 raw5127step1; decide +kernel
      have hl : raw5127step2Labels = raw5127step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5127step1 raw5127step1Labels permutation31 permutation2
    mixedMoment B raw5127step2 raw5127step2Labels = mixedMoment B raw5127step3 raw5127step3Labels := by
      have ha : raw5127step3 = -raw5127step2 := by apply Matrix.ext; change ∀ i j, raw5127step3 i j = -(raw5127step2 i j); unfold raw5127step3 raw5127step2; decide +kernel
      have hl : raw5127step3Labels = raw5127step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4460 node4460Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical79
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical10238 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10238 raw10238Labels = mixedMoment B node5291 node5291Labels := by
  calc
    mixedMoment B raw10238 raw10238Labels = mixedMoment B raw10238step0 raw10238step0Labels := by
      have hz : ∀ j, raw10238 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10238step0 = (fun i j => raw10238 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10238step0 raw10238; decide +kernel
      have hl : raw10238step0Labels = raw10238Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10238 raw10238Labels permutation434 hz
    mixedMoment B raw10238step0 raw10238step0Labels = mixedMoment B raw10238step1 raw10238step1Labels := by
      have hz : ∀ j, raw10238step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw10238step1 = (fun i j => raw10238step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw10238step1 raw10238step0; decide +kernel
      have hl : raw10238step1Labels = raw10238step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10238step0 raw10238step0Labels permutation80 hz
    mixedMoment B raw10238step1 raw10238step1Labels = mixedMoment B raw10238step2 raw10238step2Labels := by
      have ha : raw10238step2 = (fun i j => raw10238step1 (permutation29 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10238step2 raw10238step1; decide +kernel
      have hl : raw10238step2Labels = raw10238step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10238step1 raw10238step1Labels permutation29 permutation7
    mixedMoment B raw10238step2 raw10238step2Labels = mixedMoment B raw10238step3 raw10238step3Labels := by
      have ha : raw10238step3 = raw10238step2 := by apply Matrix.ext; unfold raw10238step3 raw10238step2; decide +kernel
      have hl : raw10238step2Labels = labelEmbedding10 ∘ raw10238step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10238step2 raw10238step2Labels raw10238step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5291 node5291Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical80
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical10247 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10247 raw10247Labels = mixedMoment B node5161 node5161Labels := by
  calc
    mixedMoment B raw10247 raw10247Labels = mixedMoment B raw10247step0 raw10247step0Labels := by
      have hz : ∀ j, raw10247 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10247step0 = (fun i j => raw10247 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10247step0 raw10247; decide +kernel
      have hl : raw10247step0Labels = raw10247Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10247 raw10247Labels permutation434 hz
    mixedMoment B raw10247step0 raw10247step0Labels = mixedMoment B raw10247step1 raw10247step1Labels := by
      have ha : raw10247step1 = (fun i j => raw10247step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw10247step1 raw10247step0; decide +kernel
      have hl : raw10247step1Labels = raw10247step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10247step0 raw10247step0Labels permutation34 permutation2
    _ = mixedMoment B node5161 node5161Labels := by rfl

theorem canonical10251 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10251 raw10251Labels = mixedMoment B node5161 node5161Labels := by
  calc
    mixedMoment B raw10251 raw10251Labels = mixedMoment B raw10251step0 raw10251step0Labels := by
      have hz : ∀ j, raw10251 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10251step0 = (fun i j => raw10251 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10251step0 raw10251; decide +kernel
      have hl : raw10251step0Labels = raw10251Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10251 raw10251Labels permutation346 hz
    mixedMoment B raw10251step0 raw10251step0Labels = mixedMoment B raw10251step1 raw10251step1Labels := by
      have ha : raw10251step1 = (fun i j => raw10251step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw10251step1 raw10251step0; decide +kernel
      have hl : raw10251step1Labels = raw10251step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10251step0 raw10251step0Labels permutation34 permutation2
    _ = mixedMoment B node5161 node5161Labels := by rfl

theorem canonical10255 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10255 raw10255Labels = mixedMoment B node5175 node5175Labels := by
  calc
    mixedMoment B raw10255 raw10255Labels = mixedMoment B raw10255step0 raw10255step0Labels := by
      have hz : ∀ j, raw10255 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10255step0 = (fun i j => raw10255 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10255step0 raw10255; decide +kernel
      have hl : raw10255step0Labels = raw10255Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10255 raw10255Labels permutation434 hz
    mixedMoment B raw10255step0 raw10255step0Labels = mixedMoment B raw10255step1 raw10255step1Labels := by
      have hz : ∀ j, raw10255step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw10255step1 = (fun i j => raw10255step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw10255step1 raw10255step0; decide +kernel
      have hl : raw10255step1Labels = raw10255step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10255step0 raw10255step0Labels permutation80 hz
    _ = mixedMoment B node5175 node5175Labels := by rfl

theorem canonical10259 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10259 raw10259Labels = mixedMoment B node4897 node4897Labels := by
  calc
    mixedMoment B raw10259 raw10259Labels = mixedMoment B raw10259step0 raw10259step0Labels := by
      have hz : ∀ j, raw10259 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10259step0 = (fun i j => raw10259 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10259step0 raw10259; decide +kernel
      have hl : raw10259step0Labels = raw10259Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10259 raw10259Labels permutation434 hz
    mixedMoment B raw10259step0 raw10259step0Labels = mixedMoment B raw10259step1 raw10259step1Labels := by
      have hz : ∀ j, raw10259step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw10259step1 = (fun i j => raw10259step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw10259step1 raw10259step0; decide +kernel
      have hl : raw10259step1Labels = raw10259step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10259step0 raw10259step0Labels permutation80 hz
    mixedMoment B raw10259step1 raw10259step1Labels = mixedMoment B raw10259step2 raw10259step2Labels := by
      have hz : ∀ j, raw10259step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw10259step2 = (fun i j => raw10259step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw10259step2 raw10259step1; decide +kernel
      have hl : raw10259step2Labels = raw10259step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10259step1 raw10259step1Labels permutation14 hz
    mixedMoment B raw10259step2 raw10259step2Labels = mixedMoment B raw10259step3 raw10259step3Labels := by
      have ha : raw10259step3 = (fun i j => raw10259step2 (permutation7 i) (permutation2 j)) := by apply Matrix.ext; unfold raw10259step3 raw10259step2; decide +kernel
      have hl : raw10259step3Labels = raw10259step2Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10259step2 raw10259step2Labels permutation7 permutation2
    mixedMoment B raw10259step3 raw10259step3Labels = mixedMoment B raw10259step4 raw10259step4Labels := by
      have ha : raw10259step4 = -raw10259step3 := by apply Matrix.ext; change ∀ i j, raw10259step4 i j = -(raw10259step3 i j); unfold raw10259step4 raw10259step3; decide +kernel
      have hl : raw10259step4Labels = raw10259step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4897 node4897Labels := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons69
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons72
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singleton4621 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4621 node4621Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1297 node1297Labels + mixedMoment B node2289 node2289Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1446 singletonSmall4621
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4621) = raw1446Labels := by decide +kernel
  rw [hl, canonical1446 B hB] at h
  have hc0 : mixedMoment B raw1446 (Fin.cases (0 : Fin 2) singletonSmall4621) =
      mixedMoment B node1297 node1297Labels := by
    have ha : raw1446 = raw1447 := by apply Matrix.ext; unfold raw1446 raw1447; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4621 = raw1447Labels := by decide +kernel
    rw [ha, hj, canonical1447 B hB]
  have hc1 : mixedMoment B raw1446 (Fin.cases (1 : Fin 2) singletonSmall4621) =
      mixedMoment B node2289 node2289Labels := by
    have ha : raw1446 = raw1448 := by apply Matrix.ext; unfold raw1446 raw1448; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4621 = raw1448Labels := by decide +kernel
    rw [ha, hj, canonical1448 B hB]
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

theorem singleton4865 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4865 node4865Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2106 node2106Labels + mixedMoment B node2242 node2242Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1791 singletonSmall4865
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4865) = raw1791Labels := by decide +kernel
  rw [hl, canonical1791 B hB] at h
  have hc0 : mixedMoment B raw1791 (Fin.cases (0 : Fin 2) singletonSmall4865) =
      mixedMoment B node2106 node2106Labels := by
    have ha : raw1791 = raw1792 := by apply Matrix.ext; unfold raw1791 raw1792; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4865 = raw1792Labels := by decide +kernel
    rw [ha, hj, canonical1792 B hB]
  have hc1 : mixedMoment B raw1791 (Fin.cases (1 : Fin 2) singletonSmall4865) =
      mixedMoment B node2242 node2242Labels := by
    have ha : raw1791 = raw1793 := by apply Matrix.ext; unfold raw1791 raw1793; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4865 = raw1793Labels := by decide +kernel
    rw [ha, hj, canonical1793 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4868 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4868 node4868Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2109 node2109Labels + mixedMoment B node2261 node2261Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1797 singletonSmall4868
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4868) = raw1797Labels := by decide +kernel
  rw [hl, canonical1797 B hB] at h
  have hc0 : mixedMoment B raw1797 (Fin.cases (0 : Fin 2) singletonSmall4868) =
      mixedMoment B node2109 node2109Labels := by
    have ha : raw1797 = raw1798 := by apply Matrix.ext; unfold raw1797 raw1798; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4868 = raw1798Labels := by decide +kernel
    rw [ha, hj, canonical1798 B hB]
  have hc1 : mixedMoment B raw1797 (Fin.cases (1 : Fin 2) singletonSmall4868) =
      mixedMoment B node2261 node2261Labels := by
    have ha : raw1797 = raw1799 := by apply Matrix.ext; unfold raw1797 raw1799; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4868 = raw1799Labels := by decide +kernel
    rw [ha, hj, canonical1799 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4874 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4874 node4874Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2115 node2115Labels + mixedMoment B node2276 node2276Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1806 singletonSmall4874
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4874) = raw1806Labels := by decide +kernel
  rw [hl, canonical1806 B hB] at h
  have hc0 : mixedMoment B raw1806 (Fin.cases (0 : Fin 2) singletonSmall4874) =
      mixedMoment B node2115 node2115Labels := by
    have ha : raw1806 = raw1807 := by apply Matrix.ext; unfold raw1806 raw1807; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4874 = raw1807Labels := by decide +kernel
    rw [ha, hj, canonical1807 B hB]
  have hc1 : mixedMoment B raw1806 (Fin.cases (1 : Fin 2) singletonSmall4874) =
      mixedMoment B node2276 node2276Labels := by
    have ha : raw1806 = raw1808 := by apply Matrix.ext; unfold raw1806 raw1808; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4874 = raw1808Labels := by decide +kernel
    rw [ha, hj, canonical1808 B hB]
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

theorem singleton5291 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5291 node5291Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2765 node2765Labels + mixedMoment B node3582 node3582Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2295 singletonSmall5291
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5291) = raw2295Labels := by decide +kernel
  rw [hl, canonical2295 B hB] at h
  have hc0 : mixedMoment B raw2295 (Fin.cases (0 : Fin 2) singletonSmall5291) =
      mixedMoment B node2765 node2765Labels := by
    have ha : raw2295 = raw2296 := by apply Matrix.ext; unfold raw2295 raw2296; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5291 = raw2296Labels := by decide +kernel
    rw [ha, hj, canonical2296 B hB]
  have hc1 : mixedMoment B raw2295 (Fin.cases (1 : Fin 2) singletonSmall5291) =
      mixedMoment B node3582 node3582Labels := by
    have ha : raw2295 = raw2297 := by apply Matrix.ext; unfold raw2295 raw2297; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5291 = raw2297Labels := by decide +kernel
    rw [ha, hj, canonical2297 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton5305 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5305 node5305Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2783 node2783Labels + mixedMoment B node2783 node2783Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2319 singletonSmall5305
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5305) = raw2319Labels := by decide +kernel
  rw [hl, canonical2319 B hB] at h
  have hc0 : mixedMoment B raw2319 (Fin.cases (0 : Fin 2) singletonSmall5305) =
      mixedMoment B node2783 node2783Labels := by
    have ha : raw2319 = raw2320 := by apply Matrix.ext; unfold raw2319 raw2320; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5305 = raw2320Labels := by decide +kernel
    rw [ha, hj, canonical2320 B hB]
  have hc1 : mixedMoment B raw2319 (Fin.cases (1 : Fin 2) singletonSmall5305) =
      mixedMoment B node2783 node2783Labels := by
    have ha : raw2319 = raw2321 := by apply Matrix.ext; unfold raw2319 raw2321; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5305 = raw2321Labels := by decide +kernel
    rw [ha, hj, canonical2321 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

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

theorem sound1043 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1043 node1043Labels = Sparse.eval nodeValue1043 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1043) = mixedMoment B node1043 node1043Labels := rfl
  simpa [nodeValue1043, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound20
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound1297 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1297 node1297Labels = Sparse.eval nodeValue1297 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1297) = mixedMoment B node1297 node1297Labels := rfl
  simpa [nodeValue1297, Sparse.eval] using hc.symm

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound31
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound2022 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2022 node2022Labels = Sparse.eval nodeValue2022 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2022) = mixedMoment B node2022 node2022Labels := rfl
  simpa [nodeValue2022, Sparse.eval] using hc.symm

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

theorem sound2106 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2106 node2106Labels = Sparse.eval nodeValue2106 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2106) = mixedMoment B node2106 node2106Labels := rfl
  simpa [nodeValue2106, Sparse.eval] using hc.symm

theorem sound2109 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2109 node2109Labels = Sparse.eval nodeValue2109 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2109) = mixedMoment B node2109 node2109Labels := rfl
  simpa [nodeValue2109, Sparse.eval] using hc.symm

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

theorem sound2115 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2115 node2115Labels = Sparse.eval nodeValue2115 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2115) = mixedMoment B node2115 node2115Labels := rfl
  simpa [nodeValue2115, Sparse.eval] using hc.symm

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

theorem sound2242 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2242 node2242Labels = Sparse.eval nodeValue2242 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2242) = mixedMoment B node2242 node2242Labels := rfl
  simpa [nodeValue2242, Sparse.eval] using hc.symm

theorem sound2261 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2261 node2261Labels = Sparse.eval nodeValue2261 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2261) = mixedMoment B node2261 node2261Labels := rfl
  simpa [nodeValue2261, Sparse.eval] using hc.symm

theorem sound2276 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2276 node2276Labels = Sparse.eval nodeValue2276 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2276) = mixedMoment B node2276 node2276Labels := rfl
  simpa [nodeValue2276, Sparse.eval] using hc.symm

theorem sound2289 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2289 node2289Labels = Sparse.eval nodeValue2289 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2289) = mixedMoment B node2289 node2289Labels := rfl
  simpa [nodeValue2289, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound43
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound2765 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2765 node2765Labels = Sparse.eval nodeValue2765 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2765) = mixedMoment B node2765 node2765Labels := rfl
  simpa [nodeValue2765, Sparse.eval] using hc.symm

theorem sound2783 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2783 node2783Labels = Sparse.eval nodeValue2783 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2783) = mixedMoment B node2783 node2783Labels := rfl
  simpa [nodeValue2783, Sparse.eval] using hc.symm

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

theorem sound3582 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3582 node3582Labels = Sparse.eval nodeValue3582 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3582) = mixedMoment B node3582 node3582Labels := rfl
  simpa [nodeValue3582, Sparse.eval] using hc.symm

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

theorem sound4365 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4365 node4365Labels = Sparse.eval nodeValue4365 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4365) = mixedMoment B node4365 node4365Labels := rfl
  simpa [nodeValue4365, Sparse.eval] using hc.symm

theorem sound4370 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4370 node4370Labels = Sparse.eval nodeValue4370 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4370) = mixedMoment B node4370 node4370Labels := rfl
  simpa [nodeValue4370, Sparse.eval] using hc.symm

theorem sound4373 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4373 node4373Labels = Sparse.eval nodeValue4373 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4373) = mixedMoment B node4373 node4373Labels := rfl
  simpa [nodeValue4373, Sparse.eval] using hc.symm

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound71
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound4552 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4552 node4552Labels = Sparse.eval nodeValue4552 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4552) = mixedMoment B node4552 node4552Labels := rfl
  simpa [nodeValue4552, Sparse.eval] using hc.symm

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

theorem sound4621 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4621 node4621Labels = Sparse.eval nodeValue4621 (mixedVector B) := by
  have h := singleton4621 B _hB
  rw [sound1297 B _hB _hF, sound2289 B _hB _hF] at h
  norm_num [nodeValue4621, nodeValue1297, nodeValue2289, Sparse.eval] at h ⊢
  linarith only [h]

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

theorem sound4697 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4697 node4697Labels = Sparse.eval nodeValue4697 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4697) = mixedMoment B node4697 node4697Labels := rfl
  simpa [nodeValue4697, Sparse.eval] using hc.symm

theorem sound4704 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4704 node4704Labels = Sparse.eval nodeValue4704 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4704) = mixedMoment B node4704 node4704Labels := rfl
  simpa [nodeValue4704, Sparse.eval] using hc.symm

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

theorem sound4771 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4771 node4771Labels = Sparse.eval nodeValue4771 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4771) = mixedMoment B node4771 node4771Labels := rfl
  simpa [nodeValue4771, Sparse.eval] using hc.symm

theorem sound4776 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4776 node4776Labels = Sparse.eval nodeValue4776 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4776) = mixedMoment B node4776 node4776Labels := rfl
  simpa [nodeValue4776, Sparse.eval] using hc.symm

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

theorem zero4894 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4894 node4894Labels = 0 := by
  exact mixedMoment_order_one B hB node4894 node4894Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero4897 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4897 node4897Labels = 0 := by
  exact mixedMoment_order_one B hB node4897 node4897Labels 1
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

theorem sound4865 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4865 node4865Labels = Sparse.eval nodeValue4865 (mixedVector B) := by
  have h := singleton4865 B _hB
  rw [sound2106 B _hB _hF, sound2242 B _hB _hF] at h
  norm_num [nodeValue4865, nodeValue2106, nodeValue2242, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4868 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4868 node4868Labels = Sparse.eval nodeValue4868 (mixedVector B) := by
  have h := singleton4868 B _hB
  rw [sound2109 B _hB _hF, sound2261 B _hB _hF] at h
  norm_num [nodeValue4868, nodeValue2109, nodeValue2261, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4874 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4874 node4874Labels = Sparse.eval nodeValue4874 (mixedVector B) := by
  have h := singleton4874 B _hB
  rw [sound2115 B _hB _hF, sound2276 B _hB _hF] at h
  norm_num [nodeValue4874, nodeValue2115, nodeValue2276, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4894 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4894 node4894Labels = Sparse.eval nodeValue4894 (mixedVector B) := by
  simpa only [nodeValue4894, Sparse.eval_nil] using zero4894 B _hB _hF

theorem sound4897 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4897 node4897Labels = Sparse.eval nodeValue4897 (mixedVector B) := by
  simpa only [nodeValue4897, Sparse.eval_nil] using zero4897 B _hB _hF

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

theorem sound5161 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5161 node5161Labels = Sparse.eval nodeValue5161 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5161) = mixedMoment B node5161 node5161Labels := rfl
  simpa [nodeValue5161, Sparse.eval] using hc.symm

theorem sound5175 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5175 node5175Labels = Sparse.eval nodeValue5175 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5175) = mixedMoment B node5175 node5175Labels := rfl
  simpa [nodeValue5175, Sparse.eval] using hc.symm

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

theorem sound5291 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5291 node5291Labels = Sparse.eval nodeValue5291 (mixedVector B) := by
  have h := singleton5291 B _hB
  rw [sound2765 B _hB _hF, sound3582 B _hB _hF] at h
  norm_num [nodeValue5291, nodeValue2765, nodeValue3582, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5305 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5305 node5305Labels = Sparse.eval nodeValue5305 (mixedVector B) := by
  have h := singleton5305 B _hB
  rw [sound2783 B _hB _hF] at h
  norm_num [nodeValue5305, nodeValue2783, Sparse.eval] at h ⊢
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources63
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sourceEq2021 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2021 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2021 + difference 0 1) (sourceB2021 + difference 1 0) sourceC2021) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4874) := by
    have ha : (tripleCharges (sourceA2021 + difference 0 1) (sourceB2021 + difference 1 0) sourceC2021) = raw28562 := by
      apply Matrix.ext; unfold tripleCharges sourceA2021 sourceB2021 sourceC2021 difference raw28562; decide +kernel
    rw [ha]
    exact (canonical28562 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2021 + difference 0 2) (sourceB2021 + difference 2 0) sourceC2021) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4865) := by
    have ha : (tripleCharges (sourceA2021 + difference 0 2) (sourceB2021 + difference 2 0) sourceC2021) = raw28563 := by
      apply Matrix.ext; unfold tripleCharges sourceA2021 sourceB2021 sourceC2021 difference raw28563; decide +kernel
    rw [ha]
    exact (canonical28563 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2021 + difference 0 3) (sourceB2021 + difference 3 0) sourceC2021) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4865) := by
    have ha : (tripleCharges (sourceA2021 + difference 0 3) (sourceB2021 + difference 3 0) sourceC2021) = raw28564 := by
      apply Matrix.ext; unfold tripleCharges sourceA2021 sourceB2021 sourceC2021 difference raw28564; decide +kernel
    rw [ha]
    exact (canonical28564 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2021 + difference 0 4) (sourceB2021 + difference 4 0) sourceC2021) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4894) := by
    have ha : (tripleCharges (sourceA2021 + difference 0 4) (sourceB2021 + difference 4 0) sourceC2021) = raw5101 := by
      apply Matrix.ext; unfold tripleCharges sourceA2021 sourceB2021 sourceC2021 difference raw5101; decide +kernel
    rw [ha]
    exact (canonical5101 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2021 + difference 0 5) (sourceB2021 + difference 5 0) sourceC2021) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5291) := by
    have ha : (tripleCharges (sourceA2021 + difference 0 5) (sourceB2021 + difference 5 0) sourceC2021) = raw10238 := by
      apply Matrix.ext; unfold tripleCharges sourceA2021 sourceB2021 sourceC2021 difference raw10238; decide +kernel
    rw [ha]
    exact (canonical10238 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2021 + difference 1 0) (sourceB2021 + difference 0 1) sourceC2021) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4621) := by
    have ha : (tripleCharges (sourceA2021 + difference 1 0) (sourceB2021 + difference 0 1) sourceC2021) = raw5121 := by
      apply Matrix.ext; unfold tripleCharges sourceA2021 sourceB2021 sourceC2021 difference raw5121; decide +kernel
    rw [ha]
    exact (canonical5121 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2021 + difference 1 2) (sourceB2021 + difference 2 1) sourceC2021) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4868) := by
    have ha : (tripleCharges (sourceA2021 + difference 1 2) (sourceB2021 + difference 2 1) sourceC2021) = raw5123 := by
      apply Matrix.ext; unfold tripleCharges sourceA2021 sourceB2021 sourceC2021 difference raw5123; decide +kernel
    rw [ha]
    exact (canonical5123 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2021 + difference 1 3) (sourceB2021 + difference 3 1) sourceC2021) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4868) := by
    have ha : (tripleCharges (sourceA2021 + difference 1 3) (sourceB2021 + difference 3 1) sourceC2021) = raw5124 := by
      apply Matrix.ext; unfold tripleCharges sourceA2021 sourceB2021 sourceC2021 difference raw5124; decide +kernel
    rw [ha]
    exact (canonical5124 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2021 + difference 1 4) (sourceB2021 + difference 4 1) sourceC2021) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4897) := by
    have ha : (tripleCharges (sourceA2021 + difference 1 4) (sourceB2021 + difference 4 1) sourceC2021) = raw10259 := by
      apply Matrix.ext; unfold tripleCharges sourceA2021 sourceB2021 sourceC2021 difference raw10259; decide +kernel
    rw [ha]
    exact (canonical10259 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2021 + difference 1 5) (sourceB2021 + difference 5 1) sourceC2021) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5305) := by
    have ha : (tripleCharges (sourceA2021 + difference 1 5) (sourceB2021 + difference 5 1) sourceC2021) = raw5125 := by
      apply Matrix.ext; unfold tripleCharges sourceA2021 sourceB2021 sourceC2021 difference raw5125; decide +kernel
    rw [ha]
    exact (canonical5125 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2021 + difference 2 0) (sourceB2021 + difference 0 2) sourceC2021) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4552) := by
    have ha : (tripleCharges (sourceA2021 + difference 2 0) (sourceB2021 + difference 0 2) sourceC2021) = raw20487 := by
      apply Matrix.ext; unfold tripleCharges sourceA2021 sourceB2021 sourceC2021 difference raw20487; decide +kernel
    rw [ha]
    exact (canonical20487 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2021 + difference 2 1) (sourceB2021 + difference 1 2) sourceC2021) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4776) := by
    have ha : (tripleCharges (sourceA2021 + difference 2 1) (sourceB2021 + difference 1 2) sourceC2021) = raw28565 := by
      apply Matrix.ext; unfold tripleCharges sourceA2021 sourceB2021 sourceC2021 difference raw28565; decide +kernel
    rw [ha]
    exact (canonical28565 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2021 + difference 2 3) (sourceB2021 + difference 3 2) sourceC2021) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4771) := by
    have ha : (tripleCharges (sourceA2021 + difference 2 3) (sourceB2021 + difference 3 2) sourceC2021) = raw28566 := by
      apply Matrix.ext; unfold tripleCharges sourceA2021 sourceB2021 sourceC2021 difference raw28566; decide +kernel
    rw [ha]
    exact (canonical28566 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2021 + difference 2 4) (sourceB2021 + difference 4 2) sourceC2021) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4804) := by
    have ha : (tripleCharges (sourceA2021 + difference 2 4) (sourceB2021 + difference 4 2) sourceC2021) = raw5112 := by
      apply Matrix.ext; unfold tripleCharges sourceA2021 sourceB2021 sourceC2021 difference raw5112; decide +kernel
    rw [ha]
    exact (canonical5112 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2021 + difference 2 5) (sourceB2021 + difference 5 2) sourceC2021) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5161) := by
    have ha : (tripleCharges (sourceA2021 + difference 2 5) (sourceB2021 + difference 5 2) sourceC2021) = raw10247 := by
      apply Matrix.ext; unfold tripleCharges sourceA2021 sourceB2021 sourceC2021 difference raw10247; decide +kernel
    rw [ha]
    exact (canonical10247 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2021 + difference 3 0) (sourceB2021 + difference 0 3) sourceC2021) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4552) := by
    have ha : (tripleCharges (sourceA2021 + difference 3 0) (sourceB2021 + difference 0 3) sourceC2021) = raw20490 := by
      apply Matrix.ext; unfold tripleCharges sourceA2021 sourceB2021 sourceC2021 difference raw20490; decide +kernel
    rw [ha]
    exact (canonical20490 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2021 + difference 3 1) (sourceB2021 + difference 1 3) sourceC2021) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4776) := by
    have ha : (tripleCharges (sourceA2021 + difference 3 1) (sourceB2021 + difference 1 3) sourceC2021) = raw28567 := by
      apply Matrix.ext; unfold tripleCharges sourceA2021 sourceB2021 sourceC2021 difference raw28567; decide +kernel
    rw [ha]
    exact (canonical28567 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2021 + difference 3 2) (sourceB2021 + difference 2 3) sourceC2021) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4771) := by
    have ha : (tripleCharges (sourceA2021 + difference 3 2) (sourceB2021 + difference 2 3) sourceC2021) = raw28568 := by
      apply Matrix.ext; unfold tripleCharges sourceA2021 sourceB2021 sourceC2021 difference raw28568; decide +kernel
    rw [ha]
    exact (canonical28568 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2021 + difference 3 4) (sourceB2021 + difference 4 3) sourceC2021) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4804) := by
    have ha : (tripleCharges (sourceA2021 + difference 3 4) (sourceB2021 + difference 4 3) sourceC2021) = raw5117 := by
      apply Matrix.ext; unfold tripleCharges sourceA2021 sourceB2021 sourceC2021 difference raw5117; decide +kernel
    rw [ha]
    exact (canonical5117 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2021 + difference 3 5) (sourceB2021 + difference 5 3) sourceC2021) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5161) := by
    have ha : (tripleCharges (sourceA2021 + difference 3 5) (sourceB2021 + difference 5 3) sourceC2021) = raw10251 := by
      apply Matrix.ext; unfold tripleCharges sourceA2021 sourceB2021 sourceC2021 difference raw10251; decide +kernel
    rw [ha]
    exact (canonical10251 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2021 + difference 4 0) (sourceB2021 + difference 0 4) sourceC2021) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4560) := by
    have ha : (tripleCharges (sourceA2021 + difference 4 0) (sourceB2021 + difference 0 4) sourceC2021) = raw20493 := by
      apply Matrix.ext; unfold tripleCharges sourceA2021 sourceB2021 sourceC2021 difference raw20493; decide +kernel
    rw [ha]
    exact (canonical20493 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2021 + difference 4 1) (sourceB2021 + difference 1 4) sourceC2021) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4704) := by
    have ha : (tripleCharges (sourceA2021 + difference 4 1) (sourceB2021 + difference 1 4) sourceC2021) = raw28569 := by
      apply Matrix.ext; unfold tripleCharges sourceA2021 sourceB2021 sourceC2021 difference raw28569; decide +kernel
    rw [ha]
    exact (canonical28569 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2021 + difference 4 2) (sourceB2021 + difference 2 4) sourceC2021) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4697) := by
    have ha : (tripleCharges (sourceA2021 + difference 4 2) (sourceB2021 + difference 2 4) sourceC2021) = raw28570 := by
      apply Matrix.ext; unfold tripleCharges sourceA2021 sourceB2021 sourceC2021 difference raw28570; decide +kernel
    rw [ha]
    exact (canonical28570 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2021 + difference 4 3) (sourceB2021 + difference 3 4) sourceC2021) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4697) := by
    have ha : (tripleCharges (sourceA2021 + difference 4 3) (sourceB2021 + difference 3 4) sourceC2021) = raw28571 := by
      apply Matrix.ext; unfold tripleCharges sourceA2021 sourceB2021 sourceC2021 difference raw28571; decide +kernel
    rw [ha]
    exact (canonical28571 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2021 + difference 4 5) (sourceB2021 + difference 5 4) sourceC2021) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5175) := by
    have ha : (tripleCharges (sourceA2021 + difference 4 5) (sourceB2021 + difference 5 4) sourceC2021) = raw10255 := by
      apply Matrix.ext; unfold tripleCharges sourceA2021 sourceB2021 sourceC2021 difference raw10255; decide +kernel
    rw [ha]
    exact (canonical10255 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2021 + difference 5 0) (sourceB2021 + difference 0 5) sourceC2021) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4370) := by
    have ha : (tripleCharges (sourceA2021 + difference 5 0) (sourceB2021 + difference 0 5) sourceC2021) = raw19632 := by
      apply Matrix.ext; unfold tripleCharges sourceA2021 sourceB2021 sourceC2021 difference raw19632; decide +kernel
    rw [ha]
    exact (canonical19632 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2021 + difference 5 1) (sourceB2021 + difference 1 5) sourceC2021) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4373) := by
    have ha : (tripleCharges (sourceA2021 + difference 5 1) (sourceB2021 + difference 1 5) sourceC2021) = raw28572 := by
      apply Matrix.ext; unfold tripleCharges sourceA2021 sourceB2021 sourceC2021 difference raw28572; decide +kernel
    rw [ha]
    exact (canonical28572 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2021 + difference 5 2) (sourceB2021 + difference 2 5) sourceC2021) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4365) := by
    have ha : (tripleCharges (sourceA2021 + difference 5 2) (sourceB2021 + difference 2 5) sourceC2021) = raw28573 := by
      apply Matrix.ext; unfold tripleCharges sourceA2021 sourceB2021 sourceC2021 difference raw28573; decide +kernel
    rw [ha]
    exact (canonical28573 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2021 + difference 5 3) (sourceB2021 + difference 3 5) sourceC2021) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4365) := by
    have ha : (tripleCharges (sourceA2021 + difference 5 3) (sourceB2021 + difference 3 5) sourceC2021) = raw28574 := by
      apply Matrix.ext; unfold tripleCharges sourceA2021 sourceB2021 sourceC2021 difference raw28574; decide +kernel
    rw [ha]
    exact (canonical28574 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2021 + difference 5 4) (sourceB2021 + difference 4 5) sourceC2021) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4460) := by
    have ha : (tripleCharges (sourceA2021 + difference 5 4) (sourceB2021 + difference 4 5) sourceC2021) = raw5127 := by
      apply Matrix.ext; unfold tripleCharges sourceA2021 sourceB2021 sourceC2021 difference raw5127; decide +kernel
    rw [ha]
    exact (canonical5127 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2021 sourceB2021 sourceC2021
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2021, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic106
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reindexCheck1702 : Integer.Sparse.reindex keyMap MixedData.row1702 = numericRow1702 := by decide +kernel

theorem numericCheck1702 (x : Master → ℝ) : Integer.Sparse.eval numericRow1702 x =
    (4 : ℝ) * reducedSource1702 x := by
  norm_num [numericRow1702, reducedSource1702, Integer.Sparse.eval, Sparse.eval, nodeValue4365, nodeValue4370, nodeValue4373, nodeValue4460, nodeValue4552, nodeValue4560, nodeValue4621, nodeValue4697, nodeValue4704, nodeValue4771, nodeValue4776, nodeValue4804, nodeValue4865, nodeValue4868, nodeValue4874, nodeValue4894, nodeValue4897, nodeValue5161, nodeValue5175, nodeValue5291, nodeValue5305]
  ring

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Rows106
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero1702 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1702 (mixedVector B) = 0 := by
  have h4365 : mixedVector B (Sum.inr 4365) = Sparse.eval nodeValue4365 (mixedVector B) := by
    change mixedMoment B node4365 node4365Labels = _
    exact sound4365 B hB hF
  have h4370 : mixedVector B (Sum.inr 4370) = Sparse.eval nodeValue4370 (mixedVector B) := by
    change mixedMoment B node4370 node4370Labels = _
    exact sound4370 B hB hF
  have h4373 : mixedVector B (Sum.inr 4373) = Sparse.eval nodeValue4373 (mixedVector B) := by
    change mixedMoment B node4373 node4373Labels = _
    exact sound4373 B hB hF
  have h4460 : mixedVector B (Sum.inr 4460) = Sparse.eval nodeValue4460 (mixedVector B) := by
    change mixedMoment B node4460 node4460Labels = _
    exact sound4460 B hB hF
  have h4552 : mixedVector B (Sum.inr 4552) = Sparse.eval nodeValue4552 (mixedVector B) := by
    change mixedMoment B node4552 node4552Labels = _
    exact sound4552 B hB hF
  have h4560 : mixedVector B (Sum.inr 4560) = Sparse.eval nodeValue4560 (mixedVector B) := by
    change mixedMoment B node4560 node4560Labels = _
    exact sound4560 B hB hF
  have h4621 : mixedVector B (Sum.inr 4621) = Sparse.eval nodeValue4621 (mixedVector B) := by
    change mixedMoment B node4621 node4621Labels = _
    exact sound4621 B hB hF
  have h4697 : mixedVector B (Sum.inr 4697) = Sparse.eval nodeValue4697 (mixedVector B) := by
    change mixedMoment B node4697 node4697Labels = _
    exact sound4697 B hB hF
  have h4704 : mixedVector B (Sum.inr 4704) = Sparse.eval nodeValue4704 (mixedVector B) := by
    change mixedMoment B node4704 node4704Labels = _
    exact sound4704 B hB hF
  have h4771 : mixedVector B (Sum.inr 4771) = Sparse.eval nodeValue4771 (mixedVector B) := by
    change mixedMoment B node4771 node4771Labels = _
    exact sound4771 B hB hF
  have h4776 : mixedVector B (Sum.inr 4776) = Sparse.eval nodeValue4776 (mixedVector B) := by
    change mixedMoment B node4776 node4776Labels = _
    exact sound4776 B hB hF
  have h4804 : mixedVector B (Sum.inr 4804) = Sparse.eval nodeValue4804 (mixedVector B) := by
    change mixedMoment B node4804 node4804Labels = _
    exact sound4804 B hB hF
  have h4865 : mixedVector B (Sum.inr 4865) = Sparse.eval nodeValue4865 (mixedVector B) := by
    change mixedMoment B node4865 node4865Labels = _
    exact sound4865 B hB hF
  have h4868 : mixedVector B (Sum.inr 4868) = Sparse.eval nodeValue4868 (mixedVector B) := by
    change mixedMoment B node4868 node4868Labels = _
    exact sound4868 B hB hF
  have h4874 : mixedVector B (Sum.inr 4874) = Sparse.eval nodeValue4874 (mixedVector B) := by
    change mixedMoment B node4874 node4874Labels = _
    exact sound4874 B hB hF
  have h4894 : mixedVector B (Sum.inr 4894) = Sparse.eval nodeValue4894 (mixedVector B) := by
    change mixedMoment B node4894 node4894Labels = _
    exact sound4894 B hB hF
  have h4897 : mixedVector B (Sum.inr 4897) = Sparse.eval nodeValue4897 (mixedVector B) := by
    change mixedMoment B node4897 node4897Labels = _
    exact sound4897 B hB hF
  have h5161 : mixedVector B (Sum.inr 5161) = Sparse.eval nodeValue5161 (mixedVector B) := by
    change mixedMoment B node5161 node5161Labels = _
    exact sound5161 B hB hF
  have h5175 : mixedVector B (Sum.inr 5175) = Sparse.eval nodeValue5175 (mixedVector B) := by
    change mixedMoment B node5175 node5175Labels = _
    exact sound5175 B hB hF
  have h5291 : mixedVector B (Sum.inr 5291) = Sparse.eval nodeValue5291 (mixedVector B) := by
    change mixedMoment B node5291 node5291Labels = _
    exact sound5291 B hB hF
  have h5305 : mixedVector B (Sum.inr 5305) = Sparse.eval nodeValue5305 (mixedVector B) := by
    change mixedMoment B node5305 node5305Labels = _
    exact sound5305 B hB hF
  simpa only [sourceForm2021, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4365, h4370, h4373, h4460, h4552, h4560, h4621, h4697, h4704, h4771, h4776, h4804, h4865, h4868, h4874, h4894, h4897, h5161, h5175, h5291, h5305, reducedSource1702] using sourceEq2021 B hB

theorem rowSound1702_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1702 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1702, numericCheck1702, reducedZero1702 B hB hF, mul_zero]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedSourceBridge.rowSound1702_e_oai := @OAI.MUB6.Certificate.MixedSourceBridge.rowSound1702_e_oai
