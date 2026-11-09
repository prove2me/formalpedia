-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedSourceBridge.rowSound1539_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-08T21:34:58.689054+00:00
-- url     : https://prove2.me/submissions/81a133e7-8b69-465b-ac7b-3ea2f215f0b2

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E070
import Definitions.Def_OAIQ106E086
import Definitions.Def_OAIQ106E088
import Definitions.Def_OAIQ106E089
import Definitions.Def_OAIQ106E193
import Definitions.Def_OAIQ106E100
import Definitions.Def_OAIQ106E194
import Definitions.Def_OAIQ106E195
import Definitions.Def_OAIQ106E101
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical189
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical24252 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24252 raw24252Labels = mixedMoment B node4458 node4458Labels := by
  calc
    mixedMoment B raw24252 raw24252Labels = mixedMoment B raw24252step0 raw24252step0Labels := by
      have hz : ∀ j, raw24252 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24252step0 = (fun i j => raw24252 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24252step0 raw24252; decide +kernel
      have hl : raw24252step0Labels = raw24252Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24252 raw24252Labels permutation346 hz
    mixedMoment B raw24252step0 raw24252step0Labels = mixedMoment B raw24252step1 raw24252step1Labels := by
      have ha : raw24252step1 = (fun i j => raw24252step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw24252step1 raw24252step0; decide +kernel
      have hl : raw24252step1Labels = raw24252step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24252step0 raw24252step0Labels permutation32 permutation6
    mixedMoment B raw24252step1 raw24252step1Labels = mixedMoment B raw24252step2 raw24252step2Labels := by
      have ha : raw24252step2 = raw24252step1 := by apply Matrix.ext; unfold raw24252step2 raw24252step1; decide +kernel
      have hl : raw24252step1Labels = labelEmbedding9 ∘ raw24252step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24252step1 raw24252step1Labels raw24252step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4458 node4458Labels := by rfl

theorem canonical24260 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24260 raw24260Labels = mixedMoment B node4502 node4502Labels := by
  calc
    mixedMoment B raw24260 raw24260Labels = mixedMoment B raw24260step0 raw24260step0Labels := by
      have hz : ∀ j, raw24260 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24260step0 = (fun i j => raw24260 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24260step0 raw24260; decide +kernel
      have hl : raw24260step0Labels = raw24260Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24260 raw24260Labels permutation346 hz
    mixedMoment B raw24260step0 raw24260step0Labels = mixedMoment B raw24260step1 raw24260step1Labels := by
      have hz : ∀ j, raw24260step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw24260step1 = (fun i j => raw24260step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw24260step1 raw24260step0; decide +kernel
      have hl : raw24260step1Labels = raw24260step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24260step0 raw24260step0Labels permutation56 hz
    mixedMoment B raw24260step1 raw24260step1Labels = mixedMoment B raw24260step2 raw24260step2Labels := by
      have ha : raw24260step2 = (fun i j => raw24260step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw24260step2 raw24260step1; decide +kernel
      have hl : raw24260step2Labels = raw24260step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24260step1 raw24260step1Labels permutation8 permutation6
    mixedMoment B raw24260step2 raw24260step2Labels = mixedMoment B raw24260step3 raw24260step3Labels := by
      have ha : raw24260step3 = raw24260step2 := by apply Matrix.ext; unfold raw24260step3 raw24260step2; decide +kernel
      have hl : raw24260step2Labels = labelEmbedding9 ∘ raw24260step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24260step2 raw24260step2Labels raw24260step3Labels labelEmbedding9 hl
    _ = mixedMoment B node4502 node4502Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical192
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical24605 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24605 raw24605Labels = mixedMoment B node4399 node4399Labels := by
  calc
    mixedMoment B raw24605 raw24605Labels = mixedMoment B raw24605step0 raw24605step0Labels := by
      have ha : raw24605step0 = (fun i j => raw24605 (permutation176 i) (permutation6 j)) := by apply Matrix.ext; unfold raw24605step0 raw24605; decide +kernel
      have hl : raw24605step0Labels = raw24605Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24605 raw24605Labels permutation176 permutation6
    mixedMoment B raw24605step0 raw24605step0Labels = mixedMoment B raw24605step1 raw24605step1Labels := by
      have ha : raw24605step1 = raw24605step0 := by apply Matrix.ext; unfold raw24605step1 raw24605step0; decide +kernel
      have hl : raw24605step0Labels = labelEmbedding9 ∘ raw24605step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24605step0 raw24605step0Labels raw24605step1Labels labelEmbedding9 hl
    _ = mixedMoment B node4399 node4399Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical196
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical25089 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25089 raw25089Labels = mixedMoment B node4275 node4275Labels := by
  calc
    mixedMoment B raw25089 raw25089Labels = mixedMoment B raw25089step0 raw25089step0Labels := by
      have hz : ∀ j, raw25089 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25089step0 = (fun i j => raw25089 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25089step0 raw25089; decide +kernel
      have hl : raw25089step0Labels = raw25089Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25089 raw25089Labels permutation346 hz
    mixedMoment B raw25089step0 raw25089step0Labels = mixedMoment B raw25089step1 raw25089step1Labels := by
      have ha : raw25089step1 = (fun i j => raw25089step0 (permutation53 i) (permutation4 j)) := by apply Matrix.ext; unfold raw25089step1 raw25089step0; decide +kernel
      have hl : raw25089step1Labels = raw25089step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25089step0 raw25089step0Labels permutation53 permutation4
    mixedMoment B raw25089step1 raw25089step1Labels = mixedMoment B raw25089step2 raw25089step2Labels := by
      have ha : raw25089step2 = -raw25089step1 := by apply Matrix.ext; change ∀ i j, raw25089step2 i j = -(raw25089step1 i j); unfold raw25089step2 raw25089step1; decide +kernel
      have hl : raw25089step2Labels = raw25089step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25089step2 raw25089step2Labels = mixedMoment B raw25089step3 raw25089step3Labels := by
      have ha : raw25089step3 = raw25089step2 := by apply Matrix.ext; unfold raw25089step3 raw25089step2; decide +kernel
      have hl : raw25089step2Labels = labelEmbedding7 ∘ raw25089step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25089step2 raw25089step2Labels raw25089step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4275 node4275Labels := by rfl

theorem canonical25094 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25094 raw25094Labels = mixedMoment B node4252 node4252Labels := by
  calc
    mixedMoment B raw25094 raw25094Labels = mixedMoment B raw25094step0 raw25094step0Labels := by
      have ha : raw25094step0 = (fun i j => raw25094 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw25094step0 raw25094; decide +kernel
      have hl : raw25094step0Labels = raw25094Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25094 raw25094Labels permutation152 permutation6
    mixedMoment B raw25094step0 raw25094step0Labels = mixedMoment B raw25094step1 raw25094step1Labels := by
      have ha : raw25094step1 = raw25094step0 := by apply Matrix.ext; unfold raw25094step1 raw25094step0; decide +kernel
      have hl : raw25094step0Labels = labelEmbedding9 ∘ raw25094step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25094step0 raw25094step0Labels raw25094step1Labels labelEmbedding9 hl
    _ = mixedMoment B node4252 node4252Labels := by rfl

theorem canonical25099 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25099 raw25099Labels = mixedMoment B node4268 node4268Labels := by
  calc
    mixedMoment B raw25099 raw25099Labels = mixedMoment B raw25099step0 raw25099step0Labels := by
      have hz : ∀ j, raw25099 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25099step0 = (fun i j => raw25099 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25099step0 raw25099; decide +kernel
      have hl : raw25099step0Labels = raw25099Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25099 raw25099Labels permutation346 hz
    mixedMoment B raw25099step0 raw25099step0Labels = mixedMoment B raw25099step1 raw25099step1Labels := by
      have ha : raw25099step1 = (fun i j => raw25099step0 (permutation34 i) (permutation6 j)) := by apply Matrix.ext; unfold raw25099step1 raw25099step0; decide +kernel
      have hl : raw25099step1Labels = raw25099step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25099step0 raw25099step0Labels permutation34 permutation6
    mixedMoment B raw25099step1 raw25099step1Labels = mixedMoment B raw25099step2 raw25099step2Labels := by
      have ha : raw25099step2 = raw25099step1 := by apply Matrix.ext; unfold raw25099step2 raw25099step1; decide +kernel
      have hl : raw25099step1Labels = labelEmbedding9 ∘ raw25099step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25099step1 raw25099step1Labels raw25099step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4268 node4268Labels := by rfl

theorem canonical25104 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25104 raw25104Labels = mixedMoment B node4268 node4268Labels := by
  calc
    mixedMoment B raw25104 raw25104Labels = mixedMoment B raw25104step0 raw25104step0Labels := by
      have hz : ∀ j, raw25104 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25104step0 = (fun i j => raw25104 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25104step0 raw25104; decide +kernel
      have hl : raw25104step0Labels = raw25104Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25104 raw25104Labels permutation346 hz
    mixedMoment B raw25104step0 raw25104step0Labels = mixedMoment B raw25104step1 raw25104step1Labels := by
      have ha : raw25104step1 = (fun i j => raw25104step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw25104step1 raw25104step0; decide +kernel
      have hl : raw25104step1Labels = raw25104step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25104step0 raw25104step0Labels permutation32 permutation6
    mixedMoment B raw25104step1 raw25104step1Labels = mixedMoment B raw25104step2 raw25104step2Labels := by
      have ha : raw25104step2 = raw25104step1 := by apply Matrix.ext; unfold raw25104step2 raw25104step1; decide +kernel
      have hl : raw25104step1Labels = labelEmbedding9 ∘ raw25104step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25104step1 raw25104step1Labels raw25104step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4268 node4268Labels := by rfl

theorem canonical25108 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25108 raw25108Labels = mixedMoment B node4458 node4458Labels := by
  calc
    mixedMoment B raw25108 raw25108Labels = mixedMoment B raw25108step0 raw25108step0Labels := by
      have hz : ∀ j, raw25108 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25108step0 = (fun i j => raw25108 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25108step0 raw25108; decide +kernel
      have hl : raw25108step0Labels = raw25108Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25108 raw25108Labels permutation346 hz
    mixedMoment B raw25108step0 raw25108step0Labels = mixedMoment B raw25108step1 raw25108step1Labels := by
      have ha : raw25108step1 = (fun i j => raw25108step0 (permutation34 i) (permutation6 j)) := by apply Matrix.ext; unfold raw25108step1 raw25108step0; decide +kernel
      have hl : raw25108step1Labels = raw25108step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25108step0 raw25108step0Labels permutation34 permutation6
    mixedMoment B raw25108step1 raw25108step1Labels = mixedMoment B raw25108step2 raw25108step2Labels := by
      have ha : raw25108step2 = raw25108step1 := by apply Matrix.ext; unfold raw25108step2 raw25108step1; decide +kernel
      have hl : raw25108step1Labels = labelEmbedding9 ∘ raw25108step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25108step1 raw25108step1Labels raw25108step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4458 node4458Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical197
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical25273 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25273 raw25273Labels = mixedMoment B node4268 node4268Labels := by
  calc
    mixedMoment B raw25273 raw25273Labels = mixedMoment B raw25273step0 raw25273step0Labels := by
      have hz : ∀ j, raw25273 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25273step0 = (fun i j => raw25273 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25273step0 raw25273; decide +kernel
      have hl : raw25273step0Labels = raw25273Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25273 raw25273Labels permutation346 hz
    mixedMoment B raw25273step0 raw25273step0Labels = mixedMoment B raw25273step1 raw25273step1Labels := by
      have ha : raw25273step1 = (fun i j => raw25273step0 (permutation47 i) (permutation4 j)) := by apply Matrix.ext; unfold raw25273step1 raw25273step0; decide +kernel
      have hl : raw25273step1Labels = raw25273step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25273step0 raw25273step0Labels permutation47 permutation4
    mixedMoment B raw25273step1 raw25273step1Labels = mixedMoment B raw25273step2 raw25273step2Labels := by
      have ha : raw25273step2 = -raw25273step1 := by apply Matrix.ext; change ∀ i j, raw25273step2 i j = -(raw25273step1 i j); unfold raw25273step2 raw25273step1; decide +kernel
      have hl : raw25273step2Labels = raw25273step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25273step2 raw25273step2Labels = mixedMoment B raw25273step3 raw25273step3Labels := by
      have ha : raw25273step3 = raw25273step2 := by apply Matrix.ext; unfold raw25273step3 raw25273step2; decide +kernel
      have hl : raw25273step2Labels = labelEmbedding7 ∘ raw25273step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25273step2 raw25273step2Labels raw25273step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4268 node4268Labels := by rfl

theorem canonical25277 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25277 raw25277Labels = mixedMoment B node4249 node4249Labels := by
  calc
    mixedMoment B raw25277 raw25277Labels = mixedMoment B raw25277step0 raw25277step0Labels := by
      have ha : raw25277step0 = (fun i j => raw25277 (permutation154 i) (permutation6 j)) := by apply Matrix.ext; unfold raw25277step0 raw25277; decide +kernel
      have hl : raw25277step0Labels = raw25277Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25277 raw25277Labels permutation154 permutation6
    mixedMoment B raw25277step0 raw25277step0Labels = mixedMoment B raw25277step1 raw25277step1Labels := by
      have ha : raw25277step1 = raw25277step0 := by apply Matrix.ext; unfold raw25277step1 raw25277step0; decide +kernel
      have hl : raw25277step0Labels = labelEmbedding9 ∘ raw25277step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25277step0 raw25277step0Labels raw25277step1Labels labelEmbedding9 hl
    _ = mixedMoment B node4249 node4249Labels := by rfl

theorem canonical25281 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25281 raw25281Labels = mixedMoment B node4265 node4265Labels := by
  calc
    mixedMoment B raw25281 raw25281Labels = mixedMoment B raw25281step0 raw25281step0Labels := by
      have hz : ∀ j, raw25281 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25281step0 = (fun i j => raw25281 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25281step0 raw25281; decide +kernel
      have hl : raw25281step0Labels = raw25281Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25281 raw25281Labels permutation346 hz
    mixedMoment B raw25281step0 raw25281step0Labels = mixedMoment B raw25281step1 raw25281step1Labels := by
      have ha : raw25281step1 = (fun i j => raw25281step0 (permutation45 i) (permutation4 j)) := by apply Matrix.ext; unfold raw25281step1 raw25281step0; decide +kernel
      have hl : raw25281step1Labels = raw25281step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25281step0 raw25281step0Labels permutation45 permutation4
    mixedMoment B raw25281step1 raw25281step1Labels = mixedMoment B raw25281step2 raw25281step2Labels := by
      have ha : raw25281step2 = -raw25281step1 := by apply Matrix.ext; change ∀ i j, raw25281step2 i j = -(raw25281step1 i j); unfold raw25281step2 raw25281step1; decide +kernel
      have hl : raw25281step2Labels = raw25281step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25281step2 raw25281step2Labels = mixedMoment B raw25281step3 raw25281step3Labels := by
      have ha : raw25281step3 = raw25281step2 := by apply Matrix.ext; unfold raw25281step3 raw25281step2; decide +kernel
      have hl : raw25281step2Labels = labelEmbedding7 ∘ raw25281step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25281step2 raw25281step2Labels raw25281step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4265 node4265Labels := by rfl

theorem canonical25285 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25285 raw25285Labels = mixedMoment B node4461 node4461Labels := by
  calc
    mixedMoment B raw25285 raw25285Labels = mixedMoment B raw25285step0 raw25285step0Labels := by
      have hz : ∀ j, raw25285 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25285step0 = (fun i j => raw25285 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25285step0 raw25285; decide +kernel
      have hl : raw25285step0Labels = raw25285Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25285 raw25285Labels permutation346 hz
    mixedMoment B raw25285step0 raw25285step0Labels = mixedMoment B raw25285step1 raw25285step1Labels := by
      have ha : raw25285step1 = (fun i j => raw25285step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw25285step1 raw25285step0; decide +kernel
      have hl : raw25285step1Labels = raw25285step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25285step0 raw25285step0Labels permutation32 permutation6
    mixedMoment B raw25285step1 raw25285step1Labels = mixedMoment B raw25285step2 raw25285step2Labels := by
      have ha : raw25285step2 = raw25285step1 := by apply Matrix.ext; unfold raw25285step2 raw25285step1; decide +kernel
      have hl : raw25285step1Labels = labelEmbedding9 ∘ raw25285step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25285step1 raw25285step1Labels raw25285step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4461 node4461Labels := by rfl

theorem canonical25286 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25286 raw25286Labels = mixedMoment B node4264 node4264Labels := by
  calc
    mixedMoment B raw25286 raw25286Labels = mixedMoment B raw25286step0 raw25286step0Labels := by
      have hz : ∀ j, raw25286 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25286step0 = (fun i j => raw25286 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25286step0 raw25286; decide +kernel
      have hl : raw25286step0Labels = raw25286Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25286 raw25286Labels permutation346 hz
    mixedMoment B raw25286step0 raw25286step0Labels = mixedMoment B raw25286step1 raw25286step1Labels := by
      have ha : raw25286step1 = (fun i j => raw25286step0 (permutation44 i) (permutation4 j)) := by apply Matrix.ext; unfold raw25286step1 raw25286step0; decide +kernel
      have hl : raw25286step1Labels = raw25286step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25286step0 raw25286step0Labels permutation44 permutation4
    mixedMoment B raw25286step1 raw25286step1Labels = mixedMoment B raw25286step2 raw25286step2Labels := by
      have ha : raw25286step2 = -raw25286step1 := by apply Matrix.ext; change ∀ i j, raw25286step2 i j = -(raw25286step1 i j); unfold raw25286step2 raw25286step1; decide +kernel
      have hl : raw25286step2Labels = raw25286step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25286step2 raw25286step2Labels = mixedMoment B raw25286step3 raw25286step3Labels := by
      have ha : raw25286step3 = raw25286step2 := by apply Matrix.ext; unfold raw25286step3 raw25286step2; decide +kernel
      have hl : raw25286step2Labels = labelEmbedding7 ∘ raw25286step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25286step2 raw25286step2Labels raw25286step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4264 node4264Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical199
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical25478 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25478 raw25478Labels = mixedMoment B node4264 node4264Labels := by
  calc
    mixedMoment B raw25478 raw25478Labels = mixedMoment B raw25478step0 raw25478step0Labels := by
      have hz : ∀ j, raw25478 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25478step0 = (fun i j => raw25478 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25478step0 raw25478; decide +kernel
      have hl : raw25478step0Labels = raw25478Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25478 raw25478Labels permutation346 hz
    mixedMoment B raw25478step0 raw25478step0Labels = mixedMoment B raw25478step1 raw25478step1Labels := by
      have ha : raw25478step1 = (fun i j => raw25478step0 (permutation38 i) (permutation4 j)) := by apply Matrix.ext; unfold raw25478step1 raw25478step0; decide +kernel
      have hl : raw25478step1Labels = raw25478step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25478step0 raw25478step0Labels permutation38 permutation4
    mixedMoment B raw25478step1 raw25478step1Labels = mixedMoment B raw25478step2 raw25478step2Labels := by
      have ha : raw25478step2 = -raw25478step1 := by apply Matrix.ext; change ∀ i j, raw25478step2 i j = -(raw25478step1 i j); unfold raw25478step2 raw25478step1; decide +kernel
      have hl : raw25478step2Labels = raw25478step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25478step2 raw25478step2Labels = mixedMoment B raw25478step3 raw25478step3Labels := by
      have ha : raw25478step3 = raw25478step2 := by apply Matrix.ext; unfold raw25478step3 raw25478step2; decide +kernel
      have hl : raw25478step2Labels = labelEmbedding7 ∘ raw25478step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25478step2 raw25478step2Labels raw25478step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4264 node4264Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical200
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical25713 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25713 raw25713Labels = mixedMoment B node4283 node4283Labels := by
  calc
    mixedMoment B raw25713 raw25713Labels = mixedMoment B raw25713step0 raw25713step0Labels := by
      have hz : ∀ j, raw25713 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25713step0 = (fun i j => raw25713 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25713step0 raw25713; decide +kernel
      have hl : raw25713step0Labels = raw25713Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25713 raw25713Labels permutation346 hz
    mixedMoment B raw25713step0 raw25713step0Labels = mixedMoment B raw25713step1 raw25713step1Labels := by
      have hz : ∀ j, raw25713step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw25713step1 = (fun i j => raw25713step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw25713step1 raw25713step0; decide +kernel
      have hl : raw25713step1Labels = raw25713step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25713step0 raw25713step0Labels permutation56 hz
    mixedMoment B raw25713step1 raw25713step1Labels = mixedMoment B raw25713step2 raw25713step2Labels := by
      have ha : raw25713step2 = (fun i j => raw25713step1 (permutation11 i) (permutation4 j)) := by apply Matrix.ext; unfold raw25713step2 raw25713step1; decide +kernel
      have hl : raw25713step2Labels = raw25713step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25713step1 raw25713step1Labels permutation11 permutation4
    mixedMoment B raw25713step2 raw25713step2Labels = mixedMoment B raw25713step3 raw25713step3Labels := by
      have ha : raw25713step3 = -raw25713step2 := by apply Matrix.ext; change ∀ i j, raw25713step3 i j = -(raw25713step2 i j); unfold raw25713step3 raw25713step2; decide +kernel
      have hl : raw25713step3Labels = raw25713step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25713step3 raw25713step3Labels = mixedMoment B raw25713step4 raw25713step4Labels := by
      have ha : raw25713step4 = raw25713step3 := by apply Matrix.ext; unfold raw25713step4 raw25713step3; decide +kernel
      have hl : raw25713step3Labels = labelEmbedding7 ∘ raw25713step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25713step3 raw25713step3Labels raw25713step4Labels labelEmbedding7 hl
    _ = mixedMoment B node4283 node4283Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical204
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical26165 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26165 raw26165Labels = mixedMoment B node4209 node4209Labels := by
  calc
    mixedMoment B raw26165 raw26165Labels = mixedMoment B raw26165step0 raw26165step0Labels := by
      have ha : raw26165step0 = (fun i j => raw26165 (permutation176 i) (permutation4 j)) := by apply Matrix.ext; unfold raw26165step0 raw26165; decide +kernel
      have hl : raw26165step0Labels = raw26165Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26165 raw26165Labels permutation176 permutation4
    mixedMoment B raw26165step0 raw26165step0Labels = mixedMoment B raw26165step1 raw26165step1Labels := by
      have ha : raw26165step1 = -raw26165step0 := by apply Matrix.ext; change ∀ i j, raw26165step1 i j = -(raw26165step0 i j); unfold raw26165step1 raw26165step0; decide +kernel
      have hl : raw26165step1Labels = raw26165step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw26165step1 raw26165step1Labels = mixedMoment B raw26165step2 raw26165step2Labels := by
      have ha : raw26165step2 = raw26165step1 := by apply Matrix.ext; unfold raw26165step2 raw26165step1; decide +kernel
      have hl : raw26165step1Labels = labelEmbedding7 ∘ raw26165step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26165step1 raw26165step1Labels raw26165step2Labels labelEmbedding7 hl
    _ = mixedMoment B node4209 node4209Labels := by rfl

theorem canonical26167 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26167 raw26167Labels = mixedMoment B node4069 node4069Labels := by
  calc
    mixedMoment B raw26167 raw26167Labels = mixedMoment B raw26167step0 raw26167step0Labels := by
      have hz : ∀ j, raw26167 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw26167step0 = (fun i j => raw26167 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw26167step0 raw26167; decide +kernel
      have hl : raw26167step0Labels = raw26167Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26167 raw26167Labels permutation346 hz
    mixedMoment B raw26167step0 raw26167step0Labels = mixedMoment B raw26167step1 raw26167step1Labels := by
      have hz : ∀ j, raw26167step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw26167step1 = (fun i j => raw26167step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw26167step1 raw26167step0; decide +kernel
      have hl : raw26167step1Labels = raw26167step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26167step0 raw26167step0Labels permutation56 hz
    mixedMoment B raw26167step1 raw26167step1Labels = mixedMoment B raw26167step2 raw26167step2Labels := by
      have hz : ∀ i, raw26167step1 i (permutation2 0) = 0 := by decide +kernel
      have ha : raw26167step2 = (fun i j => raw26167step1 i (permutation2 j.succ)) := by apply Matrix.ext; unfold raw26167step2 raw26167step1; decide +kernel
      have hl : raw26167step2Labels = (fun j => raw26167step1Labels (permutation2 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw26167step1 raw26167step1Labels permutation2 hz
    mixedMoment B raw26167step2 raw26167step2Labels = mixedMoment B raw26167step3 raw26167step3Labels := by
      have ha : raw26167step3 = -raw26167step2 := by apply Matrix.ext; change ∀ i j, raw26167step3 i j = -(raw26167step2 i j); unfold raw26167step3 raw26167step2; decide +kernel
      have hl : raw26167step3Labels = raw26167step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw26167step3 raw26167step3Labels = mixedMoment B raw26167step4 raw26167step4Labels := by
      have ha : raw26167step4 = raw26167step3 := by apply Matrix.ext; unfold raw26167step4 raw26167step3; decide +kernel
      have hl : raw26167step3Labels = labelEmbedding3 ∘ raw26167step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26167step3 raw26167step3Labels raw26167step4Labels labelEmbedding3 hl
    _ = mixedMoment B node4069 node4069Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical205
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical26281 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26281 raw26281Labels = mixedMoment B node4126 node4126Labels := by
  calc
    mixedMoment B raw26281 raw26281Labels = mixedMoment B raw26281step0 raw26281step0Labels := by
      have hz : ∀ j, raw26281 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw26281step0 = (fun i j => raw26281 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw26281step0 raw26281; decide +kernel
      have hl : raw26281step0Labels = raw26281Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26281 raw26281Labels permutation346 hz
    mixedMoment B raw26281step0 raw26281step0Labels = mixedMoment B raw26281step1 raw26281step1Labels := by
      have ha : raw26281step1 = (fun i j => raw26281step0 (permutation41 i) (permutation4 j)) := by apply Matrix.ext; unfold raw26281step1 raw26281step0; decide +kernel
      have hl : raw26281step1Labels = raw26281step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26281step0 raw26281step0Labels permutation41 permutation4
    mixedMoment B raw26281step1 raw26281step1Labels = mixedMoment B raw26281step2 raw26281step2Labels := by
      have ha : raw26281step2 = -raw26281step1 := by apply Matrix.ext; change ∀ i j, raw26281step2 i j = -(raw26281step1 i j); unfold raw26281step2 raw26281step1; decide +kernel
      have hl : raw26281step2Labels = raw26281step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw26281step2 raw26281step2Labels = mixedMoment B raw26281step3 raw26281step3Labels := by
      have ha : raw26281step3 = raw26281step2 := by apply Matrix.ext; unfold raw26281step3 raw26281step2; decide +kernel
      have hl : raw26281step2Labels = labelEmbedding7 ∘ raw26281step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26281step2 raw26281step2Labels raw26281step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4126 node4126Labels := by rfl

theorem canonical26282 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26282 raw26282Labels = mixedMoment B node4217 node4217Labels := by
  calc
    mixedMoment B raw26282 raw26282Labels = mixedMoment B raw26282step0 raw26282step0Labels := by
      have ha : raw26282step0 = (fun i j => raw26282 (permutation185 i) (permutation4 j)) := by apply Matrix.ext; unfold raw26282step0 raw26282; decide +kernel
      have hl : raw26282step0Labels = raw26282Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26282 raw26282Labels permutation185 permutation4
    mixedMoment B raw26282step0 raw26282step0Labels = mixedMoment B raw26282step1 raw26282step1Labels := by
      have ha : raw26282step1 = -raw26282step0 := by apply Matrix.ext; change ∀ i j, raw26282step1 i j = -(raw26282step0 i j); unfold raw26282step1 raw26282step0; decide +kernel
      have hl : raw26282step1Labels = raw26282step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw26282step1 raw26282step1Labels = mixedMoment B raw26282step2 raw26282step2Labels := by
      have ha : raw26282step2 = raw26282step1 := by apply Matrix.ext; unfold raw26282step2 raw26282step1; decide +kernel
      have hl : raw26282step1Labels = labelEmbedding7 ∘ raw26282step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26282step1 raw26282step1Labels raw26282step2Labels labelEmbedding7 hl
    _ = mixedMoment B node4217 node4217Labels := by rfl

theorem canonical26283 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26283 raw26283Labels = mixedMoment B node4268 node4268Labels := by
  calc
    mixedMoment B raw26283 raw26283Labels = mixedMoment B raw26283step0 raw26283step0Labels := by
      have hz : ∀ j, raw26283 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw26283step0 = (fun i j => raw26283 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw26283step0 raw26283; decide +kernel
      have hl : raw26283step0Labels = raw26283Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26283 raw26283Labels permutation346 hz
    mixedMoment B raw26283step0 raw26283step0Labels = mixedMoment B raw26283step1 raw26283step1Labels := by
      have ha : raw26283step1 = (fun i j => raw26283step0 (permutation41 i) (permutation4 j)) := by apply Matrix.ext; unfold raw26283step1 raw26283step0; decide +kernel
      have hl : raw26283step1Labels = raw26283step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26283step0 raw26283step0Labels permutation41 permutation4
    mixedMoment B raw26283step1 raw26283step1Labels = mixedMoment B raw26283step2 raw26283step2Labels := by
      have ha : raw26283step2 = -raw26283step1 := by apply Matrix.ext; change ∀ i j, raw26283step2 i j = -(raw26283step1 i j); unfold raw26283step2 raw26283step1; decide +kernel
      have hl : raw26283step2Labels = raw26283step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw26283step2 raw26283step2Labels = mixedMoment B raw26283step3 raw26283step3Labels := by
      have ha : raw26283step3 = raw26283step2 := by apply Matrix.ext; unfold raw26283step3 raw26283step2; decide +kernel
      have hl : raw26283step2Labels = labelEmbedding7 ∘ raw26283step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26283step2 raw26283step2Labels raw26283step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4268 node4268Labels := by rfl

theorem canonical26284 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26284 raw26284Labels = mixedMoment B node4113 node4113Labels := by
  calc
    mixedMoment B raw26284 raw26284Labels = mixedMoment B raw26284step0 raw26284step0Labels := by
      have ha : raw26284step0 = (fun i j => raw26284 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw26284step0 raw26284; decide +kernel
      have hl : raw26284step0Labels = raw26284Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26284 raw26284Labels permutation152 permutation4
    mixedMoment B raw26284step0 raw26284step0Labels = mixedMoment B raw26284step1 raw26284step1Labels := by
      have ha : raw26284step1 = -raw26284step0 := by apply Matrix.ext; change ∀ i j, raw26284step1 i j = -(raw26284step0 i j); unfold raw26284step1 raw26284step0; decide +kernel
      have hl : raw26284step1Labels = raw26284step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw26284step1 raw26284step1Labels = mixedMoment B raw26284step2 raw26284step2Labels := by
      have ha : raw26284step2 = raw26284step1 := by apply Matrix.ext; unfold raw26284step2 raw26284step1; decide +kernel
      have hl : raw26284step1Labels = labelEmbedding7 ∘ raw26284step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26284step1 raw26284step1Labels raw26284step2Labels labelEmbedding7 hl
    _ = mixedMoment B node4113 node4113Labels := by rfl

theorem canonical26285 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26285 raw26285Labels = mixedMoment B node4267 node4267Labels := by
  calc
    mixedMoment B raw26285 raw26285Labels = mixedMoment B raw26285step0 raw26285step0Labels := by
      have hz : ∀ j, raw26285 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26285step0 = (fun i j => raw26285 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26285step0 raw26285; decide +kernel
      have hl : raw26285step0Labels = raw26285Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26285 raw26285Labels permutation265 hz
    mixedMoment B raw26285step0 raw26285step0Labels = mixedMoment B raw26285step1 raw26285step1Labels := by
      have ha : raw26285step1 = (fun i j => raw26285step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw26285step1 raw26285step0; decide +kernel
      have hl : raw26285step1Labels = raw26285step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26285step0 raw26285step0Labels permutation32 permutation6
    mixedMoment B raw26285step1 raw26285step1Labels = mixedMoment B raw26285step2 raw26285step2Labels := by
      have ha : raw26285step2 = raw26285step1 := by apply Matrix.ext; unfold raw26285step2 raw26285step1; decide +kernel
      have hl : raw26285step1Labels = labelEmbedding9 ∘ raw26285step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26285step1 raw26285step1Labels raw26285step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4267 node4267Labels := by rfl

theorem canonical26286 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26286 raw26286Labels = mixedMoment B node4249 node4249Labels := by
  calc
    mixedMoment B raw26286 raw26286Labels = mixedMoment B raw26286step0 raw26286step0Labels := by
      have ha : raw26286step0 = (fun i j => raw26286 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw26286step0 raw26286; decide +kernel
      have hl : raw26286step0Labels = raw26286Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26286 raw26286Labels permutation152 permutation6
    mixedMoment B raw26286step0 raw26286step0Labels = mixedMoment B raw26286step1 raw26286step1Labels := by
      have ha : raw26286step1 = raw26286step0 := by apply Matrix.ext; unfold raw26286step1 raw26286step0; decide +kernel
      have hl : raw26286step0Labels = labelEmbedding9 ∘ raw26286step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26286step0 raw26286step0Labels raw26286step1Labels labelEmbedding9 hl
    _ = mixedMoment B node4249 node4249Labels := by rfl

theorem canonical26287 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26287 raw26287Labels = mixedMoment B node4119 node4119Labels := by
  calc
    mixedMoment B raw26287 raw26287Labels = mixedMoment B raw26287step0 raw26287step0Labels := by
      have hz : ∀ j, raw26287 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw26287step0 = (fun i j => raw26287 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw26287step0 raw26287; decide +kernel
      have hl : raw26287step0Labels = raw26287Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26287 raw26287Labels permutation346 hz
    mixedMoment B raw26287step0 raw26287step0Labels = mixedMoment B raw26287step1 raw26287step1Labels := by
      have ha : raw26287step1 = (fun i j => raw26287step0 (permutation35 i) (permutation4 j)) := by apply Matrix.ext; unfold raw26287step1 raw26287step0; decide +kernel
      have hl : raw26287step1Labels = raw26287step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26287step0 raw26287step0Labels permutation35 permutation4
    mixedMoment B raw26287step1 raw26287step1Labels = mixedMoment B raw26287step2 raw26287step2Labels := by
      have ha : raw26287step2 = -raw26287step1 := by apply Matrix.ext; change ∀ i j, raw26287step2 i j = -(raw26287step1 i j); unfold raw26287step2 raw26287step1; decide +kernel
      have hl : raw26287step2Labels = raw26287step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw26287step2 raw26287step2Labels = mixedMoment B raw26287step3 raw26287step3Labels := by
      have ha : raw26287step3 = raw26287step2 := by apply Matrix.ext; unfold raw26287step3 raw26287step2; decide +kernel
      have hl : raw26287step2Labels = labelEmbedding7 ∘ raw26287step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26287step2 raw26287step2Labels raw26287step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4119 node4119Labels := by rfl

theorem canonical26288 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26288 raw26288Labels = mixedMoment B node4210 node4210Labels := by
  calc
    mixedMoment B raw26288 raw26288Labels = mixedMoment B raw26288step0 raw26288step0Labels := by
      have ha : raw26288step0 = (fun i j => raw26288 (permutation179 i) (permutation4 j)) := by apply Matrix.ext; unfold raw26288step0 raw26288; decide +kernel
      have hl : raw26288step0Labels = raw26288Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26288 raw26288Labels permutation179 permutation4
    mixedMoment B raw26288step0 raw26288step0Labels = mixedMoment B raw26288step1 raw26288step1Labels := by
      have ha : raw26288step1 = -raw26288step0 := by apply Matrix.ext; change ∀ i j, raw26288step1 i j = -(raw26288step0 i j); unfold raw26288step1 raw26288step0; decide +kernel
      have hl : raw26288step1Labels = raw26288step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw26288step1 raw26288step1Labels = mixedMoment B raw26288step2 raw26288step2Labels := by
      have ha : raw26288step2 = raw26288step1 := by apply Matrix.ext; unfold raw26288step2 raw26288step1; decide +kernel
      have hl : raw26288step1Labels = labelEmbedding7 ∘ raw26288step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26288step1 raw26288step1Labels raw26288step2Labels labelEmbedding7 hl
    _ = mixedMoment B node4210 node4210Labels := by rfl

theorem canonical26289 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26289 raw26289Labels = mixedMoment B node4119 node4119Labels := by
  calc
    mixedMoment B raw26289 raw26289Labels = mixedMoment B raw26289step0 raw26289step0Labels := by
      have hz : ∀ j, raw26289 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw26289step0 = (fun i j => raw26289 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw26289step0 raw26289; decide +kernel
      have hl : raw26289step0Labels = raw26289Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26289 raw26289Labels permutation346 hz
    mixedMoment B raw26289step0 raw26289step0Labels = mixedMoment B raw26289step1 raw26289step1Labels := by
      have ha : raw26289step1 = (fun i j => raw26289step0 (permutation33 i) (permutation4 j)) := by apply Matrix.ext; unfold raw26289step1 raw26289step0; decide +kernel
      have hl : raw26289step1Labels = raw26289step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26289step0 raw26289step0Labels permutation33 permutation4
    mixedMoment B raw26289step1 raw26289step1Labels = mixedMoment B raw26289step2 raw26289step2Labels := by
      have ha : raw26289step2 = -raw26289step1 := by apply Matrix.ext; change ∀ i j, raw26289step2 i j = -(raw26289step1 i j); unfold raw26289step2 raw26289step1; decide +kernel
      have hl : raw26289step2Labels = raw26289step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw26289step2 raw26289step2Labels = mixedMoment B raw26289step3 raw26289step3Labels := by
      have ha : raw26289step3 = raw26289step2 := by apply Matrix.ext; unfold raw26289step3 raw26289step2; decide +kernel
      have hl : raw26289step2Labels = labelEmbedding7 ∘ raw26289step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26289step2 raw26289step2Labels raw26289step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4119 node4119Labels := by rfl

theorem canonical26290 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26290 raw26290Labels = mixedMoment B node4283 node4283Labels := by
  calc
    mixedMoment B raw26290 raw26290Labels = mixedMoment B raw26290step0 raw26290step0Labels := by
      have hz : ∀ j, raw26290 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw26290step0 = (fun i j => raw26290 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw26290step0 raw26290; decide +kernel
      have hl : raw26290step0Labels = raw26290Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26290 raw26290Labels permutation346 hz
    mixedMoment B raw26290step0 raw26290step0Labels = mixedMoment B raw26290step1 raw26290step1Labels := by
      have hz : ∀ j, raw26290step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw26290step1 = (fun i j => raw26290step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw26290step1 raw26290step0; decide +kernel
      have hl : raw26290step1Labels = raw26290step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26290step0 raw26290step0Labels permutation56 hz
    mixedMoment B raw26290step1 raw26290step1Labels = mixedMoment B raw26290step2 raw26290step2Labels := by
      have ha : raw26290step2 = (fun i j => raw26290step1 (permutation9 i) (permutation4 j)) := by apply Matrix.ext; unfold raw26290step2 raw26290step1; decide +kernel
      have hl : raw26290step2Labels = raw26290step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26290step1 raw26290step1Labels permutation9 permutation4
    mixedMoment B raw26290step2 raw26290step2Labels = mixedMoment B raw26290step3 raw26290step3Labels := by
      have ha : raw26290step3 = -raw26290step2 := by apply Matrix.ext; change ∀ i j, raw26290step3 i j = -(raw26290step2 i j); unfold raw26290step3 raw26290step2; decide +kernel
      have hl : raw26290step3Labels = raw26290step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw26290step3 raw26290step3Labels = mixedMoment B raw26290step4 raw26290step4Labels := by
      have ha : raw26290step4 = raw26290step3 := by apply Matrix.ext; unfold raw26290step4 raw26290step3; decide +kernel
      have hl : raw26290step3Labels = labelEmbedding7 ∘ raw26290step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26290step3 raw26290step3Labels raw26290step4Labels labelEmbedding7 hl
    _ = mixedMoment B node4283 node4283Labels := by rfl

theorem canonical26291 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26291 raw26291Labels = mixedMoment B node4210 node4210Labels := by
  calc
    mixedMoment B raw26291 raw26291Labels = mixedMoment B raw26291step0 raw26291step0Labels := by
      have ha : raw26291step0 = (fun i j => raw26291 (permutation177 i) (permutation4 j)) := by apply Matrix.ext; unfold raw26291step0 raw26291; decide +kernel
      have hl : raw26291step0Labels = raw26291Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26291 raw26291Labels permutation177 permutation4
    mixedMoment B raw26291step0 raw26291step0Labels = mixedMoment B raw26291step1 raw26291step1Labels := by
      have ha : raw26291step1 = -raw26291step0 := by apply Matrix.ext; change ∀ i j, raw26291step1 i j = -(raw26291step0 i j); unfold raw26291step1 raw26291step0; decide +kernel
      have hl : raw26291step1Labels = raw26291step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw26291step1 raw26291step1Labels = mixedMoment B raw26291step2 raw26291step2Labels := by
      have ha : raw26291step2 = raw26291step1 := by apply Matrix.ext; unfold raw26291step2 raw26291step1; decide +kernel
      have hl : raw26291step1Labels = labelEmbedding7 ∘ raw26291step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26291step1 raw26291step1Labels raw26291step2Labels labelEmbedding7 hl
    _ = mixedMoment B node4210 node4210Labels := by rfl

theorem canonical26292 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26292 raw26292Labels = mixedMoment B node4265 node4265Labels := by
  calc
    mixedMoment B raw26292 raw26292Labels = mixedMoment B raw26292step0 raw26292step0Labels := by
      have hz : ∀ j, raw26292 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw26292step0 = (fun i j => raw26292 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw26292step0 raw26292; decide +kernel
      have hl : raw26292step0Labels = raw26292Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26292 raw26292Labels permutation346 hz
    mixedMoment B raw26292step0 raw26292step0Labels = mixedMoment B raw26292step1 raw26292step1Labels := by
      have ha : raw26292step1 = (fun i j => raw26292step0 (permutation39 i) (permutation4 j)) := by apply Matrix.ext; unfold raw26292step1 raw26292step0; decide +kernel
      have hl : raw26292step1Labels = raw26292step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26292step0 raw26292step0Labels permutation39 permutation4
    mixedMoment B raw26292step1 raw26292step1Labels = mixedMoment B raw26292step2 raw26292step2Labels := by
      have ha : raw26292step2 = -raw26292step1 := by apply Matrix.ext; change ∀ i j, raw26292step2 i j = -(raw26292step1 i j); unfold raw26292step2 raw26292step1; decide +kernel
      have hl : raw26292step2Labels = raw26292step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw26292step2 raw26292step2Labels = mixedMoment B raw26292step3 raw26292step3Labels := by
      have ha : raw26292step3 = raw26292step2 := by apply Matrix.ext; unfold raw26292step3 raw26292step2; decide +kernel
      have hl : raw26292step2Labels = labelEmbedding7 ∘ raw26292step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26292step2 raw26292step2Labels raw26292step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4265 node4265Labels := by rfl

theorem canonical26293 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26293 raw26293Labels = mixedMoment B node4118 node4118Labels := by
  calc
    mixedMoment B raw26293 raw26293Labels = mixedMoment B raw26293step0 raw26293step0Labels := by
      have hz : ∀ j, raw26293 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw26293step0 = (fun i j => raw26293 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw26293step0 raw26293; decide +kernel
      have hl : raw26293step0Labels = raw26293Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26293 raw26293Labels permutation346 hz
    mixedMoment B raw26293step0 raw26293step0Labels = mixedMoment B raw26293step1 raw26293step1Labels := by
      have ha : raw26293step1 = (fun i j => raw26293step0 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw26293step1 raw26293step0; decide +kernel
      have hl : raw26293step1Labels = raw26293step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26293step0 raw26293step0Labels permutation32 permutation4
    mixedMoment B raw26293step1 raw26293step1Labels = mixedMoment B raw26293step2 raw26293step2Labels := by
      have ha : raw26293step2 = -raw26293step1 := by apply Matrix.ext; change ∀ i j, raw26293step2 i j = -(raw26293step1 i j); unfold raw26293step2 raw26293step1; decide +kernel
      have hl : raw26293step2Labels = raw26293step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw26293step2 raw26293step2Labels = mixedMoment B raw26293step3 raw26293step3Labels := by
      have ha : raw26293step3 = raw26293step2 := by apply Matrix.ext; unfold raw26293step3 raw26293step2; decide +kernel
      have hl : raw26293step2Labels = labelEmbedding7 ∘ raw26293step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26293step2 raw26293step2Labels raw26293step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4118 node4118Labels := by rfl

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

theorem canonical711 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw711 raw711Labels = mixedMoment B node4113 node4113Labels := by
  calc
    mixedMoment B raw711 raw711Labels = mixedMoment B raw711step0 raw711step0Labels := by
      have ha : raw711step0 = (fun i j => raw711 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw711step0 raw711; decide +kernel
      have hl : raw711step0Labels = raw711Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw711 raw711Labels permutation152 permutation4
    mixedMoment B raw711step0 raw711step0Labels = mixedMoment B raw711step1 raw711step1Labels := by
      have ha : raw711step1 = raw711step0 := by apply Matrix.ext; unfold raw711step1 raw711step0; decide +kernel
      have hl : raw711step0Labels = labelEmbedding7 ∘ raw711step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw711step0 raw711step0Labels raw711step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4113 node4113Labels := by rfl

theorem canonical712 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw712 raw712Labels = mixedMoment B node550 node550Labels := by
  calc
    mixedMoment B raw712 raw712Labels = mixedMoment B raw712step0 raw712step0Labels := by
      have ha : raw712step0 = (fun i j => raw712 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw712step0 raw712; decide +kernel
      have hl : raw712step0Labels = raw712Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw712 raw712Labels permutation152 permutation4
    _ = mixedMoment B node550 node550Labels := by rfl

theorem canonical713 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw713 raw713Labels = mixedMoment B node658 node658Labels := by
  calc
    mixedMoment B raw713 raw713Labels = mixedMoment B raw713step0 raw713step0Labels := by
      have ha : raw713step0 = (fun i j => raw713 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw713step0 raw713; decide +kernel
      have hl : raw713step0Labels = raw713Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw713 raw713Labels permutation152 permutation6
    mixedMoment B raw713step0 raw713step0Labels = mixedMoment B raw713step1 raw713step1Labels := by
      have ha : raw713step1 = -raw713step0 := by apply Matrix.ext; change ∀ i j, raw713step1 i j = -(raw713step0 i j); unfold raw713step1 raw713step0; decide +kernel
      have hl : raw713step1Labels = raw713step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw713step1 raw713step1Labels = mixedMoment B raw713step2 raw713step2Labels := by
      have ha : raw713step2 = raw713step1 := by apply Matrix.ext; unfold raw713step2 raw713step1; decide +kernel
      have hl : raw713step1Labels = labelEmbedding1 ∘ raw713step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw713step1 raw713step1Labels raw713step2Labels labelEmbedding1 hl
    _ = mixedMoment B node658 node658Labels := by rfl

theorem canonical723 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw723 raw723Labels = mixedMoment B node4119 node4119Labels := by
  calc
    mixedMoment B raw723 raw723Labels = mixedMoment B raw723step0 raw723step0Labels := by
      have ha : raw723step0 = (fun i j => raw723 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw723step0 raw723; decide +kernel
      have hl : raw723step0Labels = raw723Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw723 raw723Labels permutation32 permutation4
    mixedMoment B raw723step0 raw723step0Labels = mixedMoment B raw723step1 raw723step1Labels := by
      have ha : raw723step1 = raw723step0 := by apply Matrix.ext; unfold raw723step1 raw723step0; decide +kernel
      have hl : raw723step0Labels = labelEmbedding7 ∘ raw723step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw723step0 raw723step0Labels raw723step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4119 node4119Labels := by rfl

theorem canonical724 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw724 raw724Labels = mixedMoment B node554 node554Labels := by
  calc
    mixedMoment B raw724 raw724Labels = mixedMoment B raw724step0 raw724step0Labels := by
      have ha : raw724step0 = (fun i j => raw724 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw724step0 raw724; decide +kernel
      have hl : raw724step0Labels = raw724Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw724 raw724Labels permutation32 permutation4
    _ = mixedMoment B node554 node554Labels := by rfl

theorem canonical725 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw725 raw725Labels = mixedMoment B node668 node668Labels := by
  calc
    mixedMoment B raw725 raw725Labels = mixedMoment B raw725step0 raw725step0Labels := by
      have ha : raw725step0 = (fun i j => raw725 (permutation33 i) (permutation6 j)) := by apply Matrix.ext; unfold raw725step0 raw725; decide +kernel
      have hl : raw725step0Labels = raw725Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw725 raw725Labels permutation33 permutation6
    mixedMoment B raw725step0 raw725step0Labels = mixedMoment B raw725step1 raw725step1Labels := by
      have ha : raw725step1 = -raw725step0 := by apply Matrix.ext; change ∀ i j, raw725step1 i j = -(raw725step0 i j); unfold raw725step1 raw725step0; decide +kernel
      have hl : raw725step1Labels = raw725step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw725step1 raw725step1Labels = mixedMoment B raw725step2 raw725step2Labels := by
      have ha : raw725step2 = raw725step1 := by apply Matrix.ext; unfold raw725step2 raw725step1; decide +kernel
      have hl : raw725step1Labels = labelEmbedding1 ∘ raw725step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw725step1 raw725step1Labels raw725step2Labels labelEmbedding1 hl
    _ = mixedMoment B node668 node668Labels := by rfl

theorem canonical732 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw732 raw732Labels = mixedMoment B node4126 node4126Labels := by
  calc
    mixedMoment B raw732 raw732Labels = mixedMoment B raw732step0 raw732step0Labels := by
      have ha : raw732step0 = (fun i j => raw732 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw732step0 raw732; decide +kernel
      have hl : raw732step0Labels = raw732Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw732 raw732Labels permutation32 permutation4
    mixedMoment B raw732step0 raw732step0Labels = mixedMoment B raw732step1 raw732step1Labels := by
      have ha : raw732step1 = raw732step0 := by apply Matrix.ext; unfold raw732step1 raw732step0; decide +kernel
      have hl : raw732step0Labels = labelEmbedding7 ∘ raw732step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw732step0 raw732step0Labels raw732step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4126 node4126Labels := by rfl

theorem canonical733 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw733 raw733Labels = mixedMoment B node557 node557Labels := by
  calc
    mixedMoment B raw733 raw733Labels = mixedMoment B raw733step0 raw733step0Labels := by
      have ha : raw733step0 = (fun i j => raw733 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw733step0 raw733; decide +kernel
      have hl : raw733step0Labels = raw733Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw733 raw733Labels permutation32 permutation4
    _ = mixedMoment B node557 node557Labels := by rfl

theorem canonical734 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw734 raw734Labels = mixedMoment B node677 node677Labels := by
  calc
    mixedMoment B raw734 raw734Labels = mixedMoment B raw734step0 raw734step0Labels := by
      have ha : raw734step0 = (fun i j => raw734 (permutation50 i) (permutation6 j)) := by apply Matrix.ext; unfold raw734step0 raw734; decide +kernel
      have hl : raw734step0Labels = raw734Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw734 raw734Labels permutation50 permutation6
    mixedMoment B raw734step0 raw734step0Labels = mixedMoment B raw734step1 raw734step1Labels := by
      have ha : raw734step1 = -raw734step0 := by apply Matrix.ext; change ∀ i j, raw734step1 i j = -(raw734step0 i j); unfold raw734step1 raw734step0; decide +kernel
      have hl : raw734step1Labels = raw734step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw734step1 raw734step1Labels = mixedMoment B raw734step2 raw734step2Labels := by
      have ha : raw734step2 = raw734step1 := by apply Matrix.ext; unfold raw734step2 raw734step1; decide +kernel
      have hl : raw734step1Labels = labelEmbedding1 ∘ raw734step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw734step1 raw734step1Labels raw734step2Labels labelEmbedding1 hl
    _ = mixedMoment B node677 node677Labels := by rfl

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

theorem canonical891 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw891 raw891Labels = mixedMoment B node4210 node4210Labels := by
  calc
    mixedMoment B raw891 raw891Labels = mixedMoment B raw891step0 raw891step0Labels := by
      have ha : raw891step0 = (fun i j => raw891 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw891step0 raw891; decide +kernel
      have hl : raw891step0Labels = raw891Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw891 raw891Labels permutation152 permutation4
    mixedMoment B raw891step0 raw891step0Labels = mixedMoment B raw891step1 raw891step1Labels := by
      have ha : raw891step1 = raw891step0 := by apply Matrix.ext; unfold raw891step1 raw891step0; decide +kernel
      have hl : raw891step0Labels = labelEmbedding7 ∘ raw891step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw891step0 raw891step0Labels raw891step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4210 node4210Labels := by rfl

theorem canonical892 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw892 raw892Labels = mixedMoment B node713 node713Labels := by
  calc
    mixedMoment B raw892 raw892Labels = mixedMoment B raw892step0 raw892step0Labels := by
      have ha : raw892step0 = (fun i j => raw892 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw892step0 raw892; decide +kernel
      have hl : raw892step0Labels = raw892Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw892 raw892Labels permutation152 permutation4
    _ = mixedMoment B node713 node713Labels := by rfl

theorem canonical893 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw893 raw893Labels = mixedMoment B node751 node751Labels := by
  calc
    mixedMoment B raw893 raw893Labels = mixedMoment B raw893step0 raw893step0Labels := by
      have ha : raw893step0 = (fun i j => raw893 (permutation153 i) (permutation6 j)) := by apply Matrix.ext; unfold raw893step0 raw893; decide +kernel
      have hl : raw893step0Labels = raw893Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw893 raw893Labels permutation153 permutation6
    mixedMoment B raw893step0 raw893step0Labels = mixedMoment B raw893step1 raw893step1Labels := by
      have ha : raw893step1 = -raw893step0 := by apply Matrix.ext; change ∀ i j, raw893step1 i j = -(raw893step0 i j); unfold raw893step1 raw893step0; decide +kernel
      have hl : raw893step1Labels = raw893step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw893step1 raw893step1Labels = mixedMoment B raw893step2 raw893step2Labels := by
      have ha : raw893step2 = raw893step1 := by apply Matrix.ext; unfold raw893step2 raw893step1; decide +kernel
      have hl : raw893step1Labels = labelEmbedding1 ∘ raw893step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw893step1 raw893step1Labels raw893step2Labels labelEmbedding1 hl
    _ = mixedMoment B node751 node751Labels := by rfl

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

theorem canonical900 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw900 raw900Labels = mixedMoment B node4217 node4217Labels := by
  calc
    mixedMoment B raw900 raw900Labels = mixedMoment B raw900step0 raw900step0Labels := by
      have ha : raw900step0 = (fun i j => raw900 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw900step0 raw900; decide +kernel
      have hl : raw900step0Labels = raw900Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw900 raw900Labels permutation152 permutation4
    mixedMoment B raw900step0 raw900step0Labels = mixedMoment B raw900step1 raw900step1Labels := by
      have ha : raw900step1 = raw900step0 := by apply Matrix.ext; unfold raw900step1 raw900step0; decide +kernel
      have hl : raw900step0Labels = labelEmbedding7 ∘ raw900step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw900step0 raw900step0Labels raw900step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4217 node4217Labels := by rfl

theorem canonical901 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw901 raw901Labels = mixedMoment B node719 node719Labels := by
  calc
    mixedMoment B raw901 raw901Labels = mixedMoment B raw901step0 raw901step0Labels := by
      have ha : raw901step0 = (fun i j => raw901 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw901step0 raw901; decide +kernel
      have hl : raw901step0Labels = raw901Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw901 raw901Labels permutation152 permutation4
    _ = mixedMoment B node719 node719Labels := by rfl

theorem canonical902 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw902 raw902Labels = mixedMoment B node756 node756Labels := by
  calc
    mixedMoment B raw902 raw902Labels = mixedMoment B raw902step0 raw902step0Labels := by
      have ha : raw902step0 = (fun i j => raw902 (permutation170 i) (permutation6 j)) := by apply Matrix.ext; unfold raw902step0 raw902; decide +kernel
      have hl : raw902step0Labels = raw902Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw902 raw902Labels permutation170 permutation6
    mixedMoment B raw902step0 raw902step0Labels = mixedMoment B raw902step1 raw902step1Labels := by
      have ha : raw902step1 = -raw902step0 := by apply Matrix.ext; change ∀ i j, raw902step1 i j = -(raw902step0 i j); unfold raw902step1 raw902step0; decide +kernel
      have hl : raw902step1Labels = raw902step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw902step1 raw902step1Labels = mixedMoment B raw902step2 raw902step2Labels := by
      have ha : raw902step2 = raw902step1 := by apply Matrix.ext; unfold raw902step2 raw902step1; decide +kernel
      have hl : raw902step1Labels = labelEmbedding1 ∘ raw902step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw902step1 raw902step1Labels raw902step2Labels labelEmbedding1 hl
    _ = mixedMoment B node756 node756Labels := by rfl

theorem canonical969 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw969 raw969Labels = mixedMoment B node4249 node4249Labels := by
  calc
    mixedMoment B raw969 raw969Labels = mixedMoment B raw969step0 raw969step0Labels := by
      have ha : raw969step0 = (fun i j => raw969 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw969step0 raw969; decide +kernel
      have hl : raw969step0Labels = raw969Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw969 raw969Labels permutation152 permutation4
    mixedMoment B raw969step0 raw969step0Labels = mixedMoment B raw969step1 raw969step1Labels := by
      have ha : raw969step1 = raw969step0 := by apply Matrix.ext; unfold raw969step1 raw969step0; decide +kernel
      have hl : raw969step0Labels = labelEmbedding7 ∘ raw969step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw969step0 raw969step0Labels raw969step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4249 node4249Labels := by rfl

theorem canonical970 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw970 raw970Labels = mixedMoment B node783 node783Labels := by
  calc
    mixedMoment B raw970 raw970Labels = mixedMoment B raw970step0 raw970step0Labels := by
      have ha : raw970step0 = (fun i j => raw970 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw970step0 raw970; decide +kernel
      have hl : raw970step0Labels = raw970Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw970 raw970Labels permutation152 permutation4
    _ = mixedMoment B node783 node783Labels := by rfl

theorem canonical971 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw971 raw971Labels = mixedMoment B node803 node803Labels := by
  calc
    mixedMoment B raw971 raw971Labels = mixedMoment B raw971step0 raw971step0Labels := by
      have ha : raw971step0 = (fun i j => raw971 (permutation200 i) (permutation6 j)) := by apply Matrix.ext; unfold raw971step0 raw971; decide +kernel
      have hl : raw971step0Labels = raw971Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw971 raw971Labels permutation200 permutation6
    mixedMoment B raw971step0 raw971step0Labels = mixedMoment B raw971step1 raw971step1Labels := by
      have ha : raw971step1 = -raw971step0 := by apply Matrix.ext; change ∀ i j, raw971step1 i j = -(raw971step0 i j); unfold raw971step1 raw971step0; decide +kernel
      have hl : raw971step1Labels = raw971step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw971step1 raw971step1Labels = mixedMoment B raw971step2 raw971step2Labels := by
      have ha : raw971step2 = raw971step1 := by apply Matrix.ext; unfold raw971step2 raw971step1; decide +kernel
      have hl : raw971step1Labels = labelEmbedding1 ∘ raw971step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw971step1 raw971step1Labels raw971step2Labels labelEmbedding1 hl
    _ = mixedMoment B node803 node803Labels := by rfl

theorem canonical975 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw975 raw975Labels = mixedMoment B node4252 node4252Labels := by
  calc
    mixedMoment B raw975 raw975Labels = mixedMoment B raw975step0 raw975step0Labels := by
      have ha : raw975step0 = (fun i j => raw975 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw975step0 raw975; decide +kernel
      have hl : raw975step0Labels = raw975Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw975 raw975Labels permutation152 permutation4
    mixedMoment B raw975step0 raw975step0Labels = mixedMoment B raw975step1 raw975step1Labels := by
      have ha : raw975step1 = raw975step0 := by apply Matrix.ext; unfold raw975step1 raw975step0; decide +kernel
      have hl : raw975step0Labels = labelEmbedding7 ∘ raw975step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw975step0 raw975step0Labels raw975step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4252 node4252Labels := by rfl

theorem canonical976 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw976 raw976Labels = mixedMoment B node786 node786Labels := by
  calc
    mixedMoment B raw976 raw976Labels = mixedMoment B raw976step0 raw976step0Labels := by
      have ha : raw976step0 = (fun i j => raw976 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw976step0 raw976; decide +kernel
      have hl : raw976step0Labels = raw976Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw976 raw976Labels permutation152 permutation4
    _ = mixedMoment B node786 node786Labels := by rfl

theorem canonical977 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw977 raw977Labels = mixedMoment B node822 node822Labels := by
  calc
    mixedMoment B raw977 raw977Labels = mixedMoment B raw977step0 raw977step0Labels := by
      have ha : raw977step0 = (fun i j => raw977 (permutation246 i) (permutation6 j)) := by apply Matrix.ext; unfold raw977step0 raw977; decide +kernel
      have hl : raw977step0Labels = raw977Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw977 raw977Labels permutation246 permutation6
    mixedMoment B raw977step0 raw977step0Labels = mixedMoment B raw977step1 raw977step1Labels := by
      have ha : raw977step1 = -raw977step0 := by apply Matrix.ext; change ∀ i j, raw977step1 i j = -(raw977step0 i j); unfold raw977step1 raw977step0; decide +kernel
      have hl : raw977step1Labels = raw977step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw977step1 raw977step1Labels = mixedMoment B raw977step2 raw977step2Labels := by
      have ha : raw977step2 = raw977step1 := by apply Matrix.ext; unfold raw977step2 raw977step1; decide +kernel
      have hl : raw977step1Labels = labelEmbedding1 ∘ raw977step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw977step1 raw977step1Labels raw977step2Labels labelEmbedding1 hl
    _ = mixedMoment B node822 node822Labels := by rfl

theorem canonical990 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw990 raw990Labels = mixedMoment B node4265 node4265Labels := by
  calc
    mixedMoment B raw990 raw990Labels = mixedMoment B raw990step0 raw990step0Labels := by
      have ha : raw990step0 = (fun i j => raw990 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw990step0 raw990; decide +kernel
      have hl : raw990step0Labels = raw990Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw990 raw990Labels permutation32 permutation4
    mixedMoment B raw990step0 raw990step0Labels = mixedMoment B raw990step1 raw990step1Labels := by
      have ha : raw990step1 = raw990step0 := by apply Matrix.ext; unfold raw990step1 raw990step0; decide +kernel
      have hl : raw990step0Labels = labelEmbedding7 ∘ raw990step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw990step0 raw990step0Labels raw990step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4265 node4265Labels := by rfl

theorem canonical991 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw991 raw991Labels = mixedMoment B node807 node807Labels := by
  calc
    mixedMoment B raw991 raw991Labels = mixedMoment B raw991step0 raw991step0Labels := by
      have ha : raw991step0 = (fun i j => raw991 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw991step0 raw991; decide +kernel
      have hl : raw991step0Labels = raw991Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw991 raw991Labels permutation32 permutation4
    _ = mixedMoment B node807 node807Labels := by rfl

theorem canonical992 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw992 raw992Labels = mixedMoment B node807 node807Labels := by
  calc
    mixedMoment B raw992 raw992Labels = mixedMoment B raw992step0 raw992step0Labels := by
      have ha : raw992step0 = (fun i j => raw992 (permutation39 i) (permutation6 j)) := by apply Matrix.ext; unfold raw992step0 raw992; decide +kernel
      have hl : raw992step0Labels = raw992Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw992 raw992Labels permutation39 permutation6
    mixedMoment B raw992step0 raw992step0Labels = mixedMoment B raw992step1 raw992step1Labels := by
      have ha : raw992step1 = -raw992step0 := by apply Matrix.ext; change ∀ i j, raw992step1 i j = -(raw992step0 i j); unfold raw992step1 raw992step0; decide +kernel
      have hl : raw992step1Labels = raw992step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw992step1 raw992step1Labels = mixedMoment B raw992step2 raw992step2Labels := by
      have ha : raw992step2 = raw992step1 := by apply Matrix.ext; unfold raw992step2 raw992step1; decide +kernel
      have hl : raw992step1Labels = labelEmbedding1 ∘ raw992step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw992step1 raw992step1Labels raw992step2Labels labelEmbedding1 hl
    _ = mixedMoment B node807 node807Labels := by rfl

theorem canonical993 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw993 raw993Labels = mixedMoment B node4268 node4268Labels := by
  calc
    mixedMoment B raw993 raw993Labels = mixedMoment B raw993step0 raw993step0Labels := by
      have ha : raw993step0 = (fun i j => raw993 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw993step0 raw993; decide +kernel
      have hl : raw993step0Labels = raw993Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw993 raw993Labels permutation32 permutation4
    mixedMoment B raw993step0 raw993step0Labels = mixedMoment B raw993step1 raw993step1Labels := by
      have ha : raw993step1 = raw993step0 := by apply Matrix.ext; unfold raw993step1 raw993step0; decide +kernel
      have hl : raw993step0Labels = labelEmbedding7 ∘ raw993step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw993step0 raw993step0Labels raw993step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4268 node4268Labels := by rfl

theorem canonical994 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw994 raw994Labels = mixedMoment B node811 node811Labels := by
  calc
    mixedMoment B raw994 raw994Labels = mixedMoment B raw994step0 raw994step0Labels := by
      have ha : raw994step0 = (fun i j => raw994 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw994step0 raw994; decide +kernel
      have hl : raw994step0Labels = raw994Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw994 raw994Labels permutation32 permutation4
    _ = mixedMoment B node811 node811Labels := by rfl

theorem canonical995 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw995 raw995Labels = mixedMoment B node824 node824Labels := by
  calc
    mixedMoment B raw995 raw995Labels = mixedMoment B raw995step0 raw995step0Labels := by
      have ha : raw995step0 = (fun i j => raw995 (permutation50 i) (permutation6 j)) := by apply Matrix.ext; unfold raw995step0 raw995; decide +kernel
      have hl : raw995step0Labels = raw995Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw995 raw995Labels permutation50 permutation6
    mixedMoment B raw995step0 raw995step0Labels = mixedMoment B raw995step1 raw995step1Labels := by
      have ha : raw995step1 = -raw995step0 := by apply Matrix.ext; change ∀ i j, raw995step1 i j = -(raw995step0 i j); unfold raw995step1 raw995step0; decide +kernel
      have hl : raw995step1Labels = raw995step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw995step1 raw995step1Labels = mixedMoment B raw995step2 raw995step2Labels := by
      have ha : raw995step2 = raw995step1 := by apply Matrix.ext; unfold raw995step2 raw995step1; decide +kernel
      have hl : raw995step1Labels = labelEmbedding1 ∘ raw995step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw995step1 raw995step1Labels raw995step2Labels labelEmbedding1 hl
    _ = mixedMoment B node824 node824Labels := by rfl

theorem canonical1002 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1002 raw1002Labels = mixedMoment B node4275 node4275Labels := by
  calc
    mixedMoment B raw1002 raw1002Labels = mixedMoment B raw1002step0 raw1002step0Labels := by
      have ha : raw1002step0 = (fun i j => raw1002 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1002step0 raw1002; decide +kernel
      have hl : raw1002step0Labels = raw1002Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1002 raw1002Labels permutation32 permutation4
    mixedMoment B raw1002step0 raw1002step0Labels = mixedMoment B raw1002step1 raw1002step1Labels := by
      have ha : raw1002step1 = raw1002step0 := by apply Matrix.ext; unfold raw1002step1 raw1002step0; decide +kernel
      have hl : raw1002step0Labels = labelEmbedding7 ∘ raw1002step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1002step0 raw1002step0Labels raw1002step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4275 node4275Labels := by rfl

theorem canonical1003 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1003 raw1003Labels = mixedMoment B node827 node827Labels := by
  calc
    mixedMoment B raw1003 raw1003Labels = mixedMoment B raw1003step0 raw1003step0Labels := by
      have ha : raw1003step0 = (fun i j => raw1003 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1003step0 raw1003; decide +kernel
      have hl : raw1003step0Labels = raw1003Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1003 raw1003Labels permutation32 permutation4
    _ = mixedMoment B node827 node827Labels := by rfl

theorem canonical1004 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1004 raw1004Labels = mixedMoment B node827 node827Labels := by
  calc
    mixedMoment B raw1004 raw1004Labels = mixedMoment B raw1004step0 raw1004step0Labels := by
      have ha : raw1004step0 = (fun i j => raw1004 (permutation53 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1004step0 raw1004; decide +kernel
      have hl : raw1004step0Labels = raw1004Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1004 raw1004Labels permutation53 permutation6
    mixedMoment B raw1004step0 raw1004step0Labels = mixedMoment B raw1004step1 raw1004step1Labels := by
      have ha : raw1004step1 = -raw1004step0 := by apply Matrix.ext; change ∀ i j, raw1004step1 i j = -(raw1004step0 i j); unfold raw1004step1 raw1004step0; decide +kernel
      have hl : raw1004step1Labels = raw1004step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1004step1 raw1004step1Labels = mixedMoment B raw1004step2 raw1004step2Labels := by
      have ha : raw1004step2 = raw1004step1 := by apply Matrix.ext; unfold raw1004step2 raw1004step1; decide +kernel
      have hl : raw1004step1Labels = labelEmbedding1 ∘ raw1004step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1004step1 raw1004step1Labels raw1004step2Labels labelEmbedding1 hl
    _ = mixedMoment B node827 node827Labels := by rfl

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

theorem canonical1212 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1212 raw1212Labels = mixedMoment B node4399 node4399Labels := by
  calc
    mixedMoment B raw1212 raw1212Labels = mixedMoment B raw1212step0 raw1212step0Labels := by
      have ha : raw1212step0 = (fun i j => raw1212 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1212step0 raw1212; decide +kernel
      have hl : raw1212step0Labels = raw1212Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1212 raw1212Labels permutation152 permutation4
    mixedMoment B raw1212step0 raw1212step0Labels = mixedMoment B raw1212step1 raw1212step1Labels := by
      have ha : raw1212step1 = raw1212step0 := by apply Matrix.ext; unfold raw1212step1 raw1212step0; decide +kernel
      have hl : raw1212step0Labels = labelEmbedding7 ∘ raw1212step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1212step0 raw1212step0Labels raw1212step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4399 node4399Labels := by rfl

theorem canonical1213 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1213 raw1213Labels = mixedMoment B node980 node980Labels := by
  calc
    mixedMoment B raw1213 raw1213Labels = mixedMoment B raw1213step0 raw1213step0Labels := by
      have ha : raw1213step0 = (fun i j => raw1213 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1213step0 raw1213; decide +kernel
      have hl : raw1213step0Labels = raw1213Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1213 raw1213Labels permutation152 permutation4
    _ = mixedMoment B node980 node980Labels := by rfl

theorem canonical1214 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1214 raw1214Labels = mixedMoment B node1616 node1616Labels := by
  calc
    mixedMoment B raw1214 raw1214Labels = mixedMoment B raw1214step0 raw1214step0Labels := by
      have ha : raw1214step0 = (fun i j => raw1214 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1214step0 raw1214; decide +kernel
      have hl : raw1214step0Labels = raw1214Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1214 raw1214Labels permutation152 permutation6
    mixedMoment B raw1214step0 raw1214step0Labels = mixedMoment B raw1214step1 raw1214step1Labels := by
      have ha : raw1214step1 = -raw1214step0 := by apply Matrix.ext; change ∀ i j, raw1214step1 i j = -(raw1214step0 i j); unfold raw1214step1 raw1214step0; decide +kernel
      have hl : raw1214step1Labels = raw1214step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1214step1 raw1214step1Labels = mixedMoment B raw1214step2 raw1214step2Labels := by
      have ha : raw1214step2 = raw1214step1 := by apply Matrix.ext; unfold raw1214step2 raw1214step1; decide +kernel
      have hl : raw1214step1Labels = labelEmbedding1 ∘ raw1214step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1214step1 raw1214step1Labels raw1214step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1616 node1616Labels := by rfl

theorem canonical1260 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1260 raw1260Labels = mixedMoment B node4458 node4458Labels := by
  calc
    mixedMoment B raw1260 raw1260Labels = mixedMoment B raw1260step0 raw1260step0Labels := by
      have ha : raw1260step0 = (fun i j => raw1260 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1260step0 raw1260; decide +kernel
      have hl : raw1260step0Labels = raw1260Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1260 raw1260Labels permutation32 permutation4
    mixedMoment B raw1260step0 raw1260step0Labels = mixedMoment B raw1260step1 raw1260step1Labels := by
      have ha : raw1260step1 = raw1260step0 := by apply Matrix.ext; unfold raw1260step1 raw1260step0; decide +kernel
      have hl : raw1260step0Labels = labelEmbedding7 ∘ raw1260step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1260step0 raw1260step0Labels raw1260step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4458 node4458Labels := by rfl

theorem canonical1261 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1261 raw1261Labels = mixedMoment B node1041 node1041Labels := by
  calc
    mixedMoment B raw1261 raw1261Labels = mixedMoment B raw1261step0 raw1261step0Labels := by
      have ha : raw1261step0 = (fun i j => raw1261 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1261step0 raw1261; decide +kernel
      have hl : raw1261step0Labels = raw1261Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1261 raw1261Labels permutation32 permutation4
    _ = mixedMoment B node1041 node1041Labels := by rfl

theorem canonical1262 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1262 raw1262Labels = mixedMoment B node1724 node1724Labels := by
  calc
    mixedMoment B raw1262 raw1262Labels = mixedMoment B raw1262step0 raw1262step0Labels := by
      have ha : raw1262step0 = (fun i j => raw1262 (permutation38 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1262step0 raw1262; decide +kernel
      have hl : raw1262step0Labels = raw1262Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1262 raw1262Labels permutation38 permutation6
    mixedMoment B raw1262step0 raw1262step0Labels = mixedMoment B raw1262step1 raw1262step1Labels := by
      have ha : raw1262step1 = -raw1262step0 := by apply Matrix.ext; change ∀ i j, raw1262step1 i j = -(raw1262step0 i j); unfold raw1262step1 raw1262step0; decide +kernel
      have hl : raw1262step1Labels = raw1262step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1262step1 raw1262step1Labels = mixedMoment B raw1262step2 raw1262step2Labels := by
      have ha : raw1262step2 = raw1262step1 := by apply Matrix.ext; unfold raw1262step2 raw1262step1; decide +kernel
      have hl : raw1262step1Labels = labelEmbedding1 ∘ raw1262step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1262step1 raw1262step1Labels raw1262step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1724 node1724Labels := by rfl

theorem canonical1266 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1266 raw1266Labels = mixedMoment B node4461 node4461Labels := by
  calc
    mixedMoment B raw1266 raw1266Labels = mixedMoment B raw1266step0 raw1266step0Labels := by
      have ha : raw1266step0 = (fun i j => raw1266 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1266step0 raw1266; decide +kernel
      have hl : raw1266step0Labels = raw1266Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1266 raw1266Labels permutation32 permutation4
    mixedMoment B raw1266step0 raw1266step0Labels = mixedMoment B raw1266step1 raw1266step1Labels := by
      have ha : raw1266step1 = raw1266step0 := by apply Matrix.ext; unfold raw1266step1 raw1266step0; decide +kernel
      have hl : raw1266step0Labels = labelEmbedding7 ∘ raw1266step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1266step0 raw1266step0Labels raw1266step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4461 node4461Labels := by rfl

theorem canonical1267 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1267 raw1267Labels = mixedMoment B node1044 node1044Labels := by
  calc
    mixedMoment B raw1267 raw1267Labels = mixedMoment B raw1267step0 raw1267step0Labels := by
      have ha : raw1267step0 = (fun i j => raw1267 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1267step0 raw1267; decide +kernel
      have hl : raw1267step0Labels = raw1267Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1267 raw1267Labels permutation32 permutation4
    _ = mixedMoment B node1044 node1044Labels := by rfl

theorem canonical1268 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1268 raw1268Labels = mixedMoment B node1737 node1737Labels := by
  calc
    mixedMoment B raw1268 raw1268Labels = mixedMoment B raw1268step0 raw1268step0Labels := by
      have ha : raw1268step0 = (fun i j => raw1268 (permutation50 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1268step0 raw1268; decide +kernel
      have hl : raw1268step0Labels = raw1268Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1268 raw1268Labels permutation50 permutation6
    mixedMoment B raw1268step0 raw1268step0Labels = mixedMoment B raw1268step1 raw1268step1Labels := by
      have ha : raw1268step1 = -raw1268step0 := by apply Matrix.ext; change ∀ i j, raw1268step1 i j = -(raw1268step0 i j); unfold raw1268step1 raw1268step0; decide +kernel
      have hl : raw1268step1Labels = raw1268step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1268step1 raw1268step1Labels = mixedMoment B raw1268step2 raw1268step2Labels := by
      have ha : raw1268step2 = raw1268step1 := by apply Matrix.ext; unfold raw1268step2 raw1268step1; decide +kernel
      have hl : raw1268step1Labels = labelEmbedding1 ∘ raw1268step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1268step1 raw1268step1Labels raw1268step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1737 node1737Labels := by rfl

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

theorem singleton4113 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4113 node4113Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node550 node550Labels + mixedMoment B node658 node658Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw711 singletonSmall4113
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4113) = raw711Labels := by decide +kernel
  rw [hl, canonical711 B hB] at h
  have hc0 : mixedMoment B raw711 (Fin.cases (0 : Fin 2) singletonSmall4113) =
      mixedMoment B node550 node550Labels := by
    have ha : raw711 = raw712 := by apply Matrix.ext; unfold raw711 raw712; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4113 = raw712Labels := by decide +kernel
    rw [ha, hj, canonical712 B hB]
  have hc1 : mixedMoment B raw711 (Fin.cases (1 : Fin 2) singletonSmall4113) =
      mixedMoment B node658 node658Labels := by
    have ha : raw711 = raw713 := by apply Matrix.ext; unfold raw711 raw713; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4113 = raw713Labels := by decide +kernel
    rw [ha, hj, canonical713 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4119 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4119 node4119Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node554 node554Labels + mixedMoment B node668 node668Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw723 singletonSmall4119
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4119) = raw723Labels := by decide +kernel
  rw [hl, canonical723 B hB] at h
  have hc0 : mixedMoment B raw723 (Fin.cases (0 : Fin 2) singletonSmall4119) =
      mixedMoment B node554 node554Labels := by
    have ha : raw723 = raw724 := by apply Matrix.ext; unfold raw723 raw724; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4119 = raw724Labels := by decide +kernel
    rw [ha, hj, canonical724 B hB]
  have hc1 : mixedMoment B raw723 (Fin.cases (1 : Fin 2) singletonSmall4119) =
      mixedMoment B node668 node668Labels := by
    have ha : raw723 = raw725 := by apply Matrix.ext; unfold raw723 raw725; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4119 = raw725Labels := by decide +kernel
    rw [ha, hj, canonical725 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4126 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4126 node4126Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node557 node557Labels + mixedMoment B node677 node677Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw732 singletonSmall4126
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4126) = raw732Labels := by decide +kernel
  rw [hl, canonical732 B hB] at h
  have hc0 : mixedMoment B raw732 (Fin.cases (0 : Fin 2) singletonSmall4126) =
      mixedMoment B node557 node557Labels := by
    have ha : raw732 = raw733 := by apply Matrix.ext; unfold raw732 raw733; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4126 = raw733Labels := by decide +kernel
    rw [ha, hj, canonical733 B hB]
  have hc1 : mixedMoment B raw732 (Fin.cases (1 : Fin 2) singletonSmall4126) =
      mixedMoment B node677 node677Labels := by
    have ha : raw732 = raw734 := by apply Matrix.ext; unfold raw732 raw734; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4126 = raw734Labels := by decide +kernel
    rw [ha, hj, canonical734 B hB]
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

theorem singleton4210 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4210 node4210Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node713 node713Labels + mixedMoment B node751 node751Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw891 singletonSmall4210
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4210) = raw891Labels := by decide +kernel
  rw [hl, canonical891 B hB] at h
  have hc0 : mixedMoment B raw891 (Fin.cases (0 : Fin 2) singletonSmall4210) =
      mixedMoment B node713 node713Labels := by
    have ha : raw891 = raw892 := by apply Matrix.ext; unfold raw891 raw892; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4210 = raw892Labels := by decide +kernel
    rw [ha, hj, canonical892 B hB]
  have hc1 : mixedMoment B raw891 (Fin.cases (1 : Fin 2) singletonSmall4210) =
      mixedMoment B node751 node751Labels := by
    have ha : raw891 = raw893 := by apply Matrix.ext; unfold raw891 raw893; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4210 = raw893Labels := by decide +kernel
    rw [ha, hj, canonical893 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4217 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4217 node4217Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node719 node719Labels + mixedMoment B node756 node756Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw900 singletonSmall4217
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4217) = raw900Labels := by decide +kernel
  rw [hl, canonical900 B hB] at h
  have hc0 : mixedMoment B raw900 (Fin.cases (0 : Fin 2) singletonSmall4217) =
      mixedMoment B node719 node719Labels := by
    have ha : raw900 = raw901 := by apply Matrix.ext; unfold raw900 raw901; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4217 = raw901Labels := by decide +kernel
    rw [ha, hj, canonical901 B hB]
  have hc1 : mixedMoment B raw900 (Fin.cases (1 : Fin 2) singletonSmall4217) =
      mixedMoment B node756 node756Labels := by
    have ha : raw900 = raw902 := by apply Matrix.ext; unfold raw900 raw902; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4217 = raw902Labels := by decide +kernel
    rw [ha, hj, canonical902 B hB]
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

theorem singleton4249 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4249 node4249Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node783 node783Labels + mixedMoment B node803 node803Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw969 singletonSmall4249
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4249) = raw969Labels := by decide +kernel
  rw [hl, canonical969 B hB] at h
  have hc0 : mixedMoment B raw969 (Fin.cases (0 : Fin 2) singletonSmall4249) =
      mixedMoment B node783 node783Labels := by
    have ha : raw969 = raw970 := by apply Matrix.ext; unfold raw969 raw970; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4249 = raw970Labels := by decide +kernel
    rw [ha, hj, canonical970 B hB]
  have hc1 : mixedMoment B raw969 (Fin.cases (1 : Fin 2) singletonSmall4249) =
      mixedMoment B node803 node803Labels := by
    have ha : raw969 = raw971 := by apply Matrix.ext; unfold raw969 raw971; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4249 = raw971Labels := by decide +kernel
    rw [ha, hj, canonical971 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4252 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4252 node4252Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node786 node786Labels + mixedMoment B node822 node822Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw975 singletonSmall4252
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4252) = raw975Labels := by decide +kernel
  rw [hl, canonical975 B hB] at h
  have hc0 : mixedMoment B raw975 (Fin.cases (0 : Fin 2) singletonSmall4252) =
      mixedMoment B node786 node786Labels := by
    have ha : raw975 = raw976 := by apply Matrix.ext; unfold raw975 raw976; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4252 = raw976Labels := by decide +kernel
    rw [ha, hj, canonical976 B hB]
  have hc1 : mixedMoment B raw975 (Fin.cases (1 : Fin 2) singletonSmall4252) =
      mixedMoment B node822 node822Labels := by
    have ha : raw975 = raw977 := by apply Matrix.ext; unfold raw975 raw977; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4252 = raw977Labels := by decide +kernel
    rw [ha, hj, canonical977 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4265 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4265 node4265Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node807 node807Labels + mixedMoment B node807 node807Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw990 singletonSmall4265
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4265) = raw990Labels := by decide +kernel
  rw [hl, canonical990 B hB] at h
  have hc0 : mixedMoment B raw990 (Fin.cases (0 : Fin 2) singletonSmall4265) =
      mixedMoment B node807 node807Labels := by
    have ha : raw990 = raw991 := by apply Matrix.ext; unfold raw990 raw991; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4265 = raw991Labels := by decide +kernel
    rw [ha, hj, canonical991 B hB]
  have hc1 : mixedMoment B raw990 (Fin.cases (1 : Fin 2) singletonSmall4265) =
      mixedMoment B node807 node807Labels := by
    have ha : raw990 = raw992 := by apply Matrix.ext; unfold raw990 raw992; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4265 = raw992Labels := by decide +kernel
    rw [ha, hj, canonical992 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4268 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4268 node4268Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node811 node811Labels + mixedMoment B node824 node824Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw993 singletonSmall4268
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4268) = raw993Labels := by decide +kernel
  rw [hl, canonical993 B hB] at h
  have hc0 : mixedMoment B raw993 (Fin.cases (0 : Fin 2) singletonSmall4268) =
      mixedMoment B node811 node811Labels := by
    have ha : raw993 = raw994 := by apply Matrix.ext; unfold raw993 raw994; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4268 = raw994Labels := by decide +kernel
    rw [ha, hj, canonical994 B hB]
  have hc1 : mixedMoment B raw993 (Fin.cases (1 : Fin 2) singletonSmall4268) =
      mixedMoment B node824 node824Labels := by
    have ha : raw993 = raw995 := by apply Matrix.ext; unfold raw993 raw995; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4268 = raw995Labels := by decide +kernel
    rw [ha, hj, canonical995 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4275 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4275 node4275Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node827 node827Labels + mixedMoment B node827 node827Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1002 singletonSmall4275
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4275) = raw1002Labels := by decide +kernel
  rw [hl, canonical1002 B hB] at h
  have hc0 : mixedMoment B raw1002 (Fin.cases (0 : Fin 2) singletonSmall4275) =
      mixedMoment B node827 node827Labels := by
    have ha : raw1002 = raw1003 := by apply Matrix.ext; unfold raw1002 raw1003; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4275 = raw1003Labels := by decide +kernel
    rw [ha, hj, canonical1003 B hB]
  have hc1 : mixedMoment B raw1002 (Fin.cases (1 : Fin 2) singletonSmall4275) =
      mixedMoment B node827 node827Labels := by
    have ha : raw1002 = raw1004 := by apply Matrix.ext; unfold raw1002 raw1004; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4275 = raw1004Labels := by decide +kernel
    rw [ha, hj, canonical1004 B hB]
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

theorem singleton4399 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4399 node4399Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node980 node980Labels + mixedMoment B node1616 node1616Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1212 singletonSmall4399
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4399) = raw1212Labels := by decide +kernel
  rw [hl, canonical1212 B hB] at h
  have hc0 : mixedMoment B raw1212 (Fin.cases (0 : Fin 2) singletonSmall4399) =
      mixedMoment B node980 node980Labels := by
    have ha : raw1212 = raw1213 := by apply Matrix.ext; unfold raw1212 raw1213; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4399 = raw1213Labels := by decide +kernel
    rw [ha, hj, canonical1213 B hB]
  have hc1 : mixedMoment B raw1212 (Fin.cases (1 : Fin 2) singletonSmall4399) =
      mixedMoment B node1616 node1616Labels := by
    have ha : raw1212 = raw1214 := by apply Matrix.ext; unfold raw1212 raw1214; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4399 = raw1214Labels := by decide +kernel
    rw [ha, hj, canonical1214 B hB]
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

theorem singleton4458 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4458 node4458Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1041 node1041Labels + mixedMoment B node1724 node1724Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1260 singletonSmall4458
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4458) = raw1260Labels := by decide +kernel
  rw [hl, canonical1260 B hB] at h
  have hc0 : mixedMoment B raw1260 (Fin.cases (0 : Fin 2) singletonSmall4458) =
      mixedMoment B node1041 node1041Labels := by
    have ha : raw1260 = raw1261 := by apply Matrix.ext; unfold raw1260 raw1261; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4458 = raw1261Labels := by decide +kernel
    rw [ha, hj, canonical1261 B hB]
  have hc1 : mixedMoment B raw1260 (Fin.cases (1 : Fin 2) singletonSmall4458) =
      mixedMoment B node1724 node1724Labels := by
    have ha : raw1260 = raw1262 := by apply Matrix.ext; unfold raw1260 raw1262; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4458 = raw1262Labels := by decide +kernel
    rw [ha, hj, canonical1262 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4461 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4461 node4461Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1044 node1044Labels + mixedMoment B node1737 node1737Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1266 singletonSmall4461
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4461) = raw1266Labels := by decide +kernel
  rw [hl, canonical1266 B hB] at h
  have hc0 : mixedMoment B raw1266 (Fin.cases (0 : Fin 2) singletonSmall4461) =
      mixedMoment B node1044 node1044Labels := by
    have ha : raw1266 = raw1267 := by apply Matrix.ext; unfold raw1266 raw1267; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4461 = raw1267Labels := by decide +kernel
    rw [ha, hj, canonical1267 B hB]
  have hc1 : mixedMoment B raw1266 (Fin.cases (1 : Fin 2) singletonSmall4461) =
      mixedMoment B node1737 node1737Labels := by
    have ha : raw1266 = raw1268 := by apply Matrix.ext; unfold raw1266 raw1268; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4461 = raw1268Labels := by decide +kernel
    rw [ha, hj, canonical1268 B hB]
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

theorem sound658 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node658 node658Labels = Sparse.eval nodeValue658 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 658) = mixedMoment B node658 node658Labels := rfl
  simpa [nodeValue658, Sparse.eval] using hc.symm

theorem sound668 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node668 node668Labels = Sparse.eval nodeValue668 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 668) = mixedMoment B node668 node668Labels := rfl
  simpa [nodeValue668, Sparse.eval] using hc.symm

theorem sound677 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node677 node677Labels = Sparse.eval nodeValue677 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 677) = mixedMoment B node677 node677Labels := rfl
  simpa [nodeValue677, Sparse.eval] using hc.symm

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

theorem sound713 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node713 node713Labels = Sparse.eval nodeValue713 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 713) = mixedMoment B node713 node713Labels := rfl
  simpa [nodeValue713, Sparse.eval] using hc.symm

theorem sound719 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node719 node719Labels = Sparse.eval nodeValue719 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 719) = mixedMoment B node719 node719Labels := rfl
  simpa [nodeValue719, Sparse.eval] using hc.symm

theorem sound751 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node751 node751Labels = Sparse.eval nodeValue751 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 751) = mixedMoment B node751 node751Labels := rfl
  simpa [nodeValue751, Sparse.eval] using hc.symm

theorem sound756 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node756 node756Labels = Sparse.eval nodeValue756 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 756) = mixedMoment B node756 node756Labels := rfl
  simpa [nodeValue756, Sparse.eval] using hc.symm

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

theorem sound783 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node783 node783Labels = Sparse.eval nodeValue783 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 783) = mixedMoment B node783 node783Labels := rfl
  simpa [nodeValue783, Sparse.eval] using hc.symm

theorem sound786 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node786 node786Labels = Sparse.eval nodeValue786 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 786) = mixedMoment B node786 node786Labels := rfl
  simpa [nodeValue786, Sparse.eval] using hc.symm

theorem sound803 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node803 node803Labels = Sparse.eval nodeValue803 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 803) = mixedMoment B node803 node803Labels := rfl
  simpa [nodeValue803, Sparse.eval] using hc.symm

theorem sound807 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node807 node807Labels = Sparse.eval nodeValue807 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 807) = mixedMoment B node807 node807Labels := rfl
  simpa [nodeValue807, Sparse.eval] using hc.symm

theorem sound811 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node811 node811Labels = Sparse.eval nodeValue811 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 811) = mixedMoment B node811 node811Labels := rfl
  simpa [nodeValue811, Sparse.eval] using hc.symm

theorem sound822 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node822 node822Labels = Sparse.eval nodeValue822 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 822) = mixedMoment B node822 node822Labels := rfl
  simpa [nodeValue822, Sparse.eval] using hc.symm

theorem sound824 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node824 node824Labels = Sparse.eval nodeValue824 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 824) = mixedMoment B node824 node824Labels := rfl
  simpa [nodeValue824, Sparse.eval] using hc.symm

theorem sound827 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node827 node827Labels = Sparse.eval nodeValue827 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 827) = mixedMoment B node827 node827Labels := rfl
  simpa [nodeValue827, Sparse.eval] using hc.symm

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

theorem sound980 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node980 node980Labels = Sparse.eval nodeValue980 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 980) = mixedMoment B node980 node980Labels := rfl
  simpa [nodeValue980, Sparse.eval] using hc.symm

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

theorem sound1041 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1041 node1041Labels = Sparse.eval nodeValue1041 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1041) = mixedMoment B node1041 node1041Labels := rfl
  simpa [nodeValue1041, Sparse.eval] using hc.symm

theorem sound1044 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1044 node1044Labels = Sparse.eval nodeValue1044 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1044) = mixedMoment B node1044 node1044Labels := rfl
  simpa [nodeValue1044, Sparse.eval] using hc.symm

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

theorem sound1616 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1616 node1616Labels = Sparse.eval nodeValue1616 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1616) = mixedMoment B node1616 node1616Labels := rfl
  simpa [nodeValue1616, Sparse.eval] using hc.symm

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

theorem sound1724 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1724 node1724Labels = Sparse.eval nodeValue1724 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1724) = mixedMoment B node1724 node1724Labels := rfl
  simpa [nodeValue1724, Sparse.eval] using hc.symm

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

theorem sound1737 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1737 node1737Labels = Sparse.eval nodeValue1737 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1737) = mixedMoment B node1737 node1737Labels := rfl
  simpa [nodeValue1737, Sparse.eval] using hc.symm

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

theorem sound550 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node550 node550Labels = Sparse.eval nodeValue550 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 550) = mixedMoment B node550 node550Labels := rfl
  simpa [nodeValue550, Sparse.eval] using hc.symm

theorem sound554 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node554 node554Labels = Sparse.eval nodeValue554 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 554) = mixedMoment B node554 node554Labels := rfl
  simpa [nodeValue554, Sparse.eval] using hc.symm

theorem sound557 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node557 node557Labels = Sparse.eval nodeValue557 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 557) = mixedMoment B node557 node557Labels := rfl
  simpa [nodeValue557, Sparse.eval] using hc.symm

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

theorem sound4069 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4069 node4069Labels = Sparse.eval nodeValue4069 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4069) = mixedMoment B node4069 node4069Labels := rfl
  simpa [nodeValue4069, Sparse.eval] using hc.symm

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

theorem zero4118 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4118 node4118Labels = 0 := by
  exact mixedMoment_order_one B hB node4118 node4118Labels 1
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

theorem sound4113 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4113 node4113Labels = Sparse.eval nodeValue4113 (mixedVector B) := by
  have h := singleton4113 B _hB
  rw [sound550 B _hB _hF, sound658 B _hB _hF] at h
  norm_num [nodeValue4113, nodeValue550, nodeValue658, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4118 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4118 node4118Labels = Sparse.eval nodeValue4118 (mixedVector B) := by
  simpa only [nodeValue4118, Sparse.eval_nil] using zero4118 B _hB _hF

theorem sound4119 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4119 node4119Labels = Sparse.eval nodeValue4119 (mixedVector B) := by
  have h := singleton4119 B _hB
  rw [sound554 B _hB _hF, sound668 B _hB _hF] at h
  norm_num [nodeValue4119, nodeValue554, nodeValue668, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4126 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4126 node4126Labels = Sparse.eval nodeValue4126 (mixedVector B) := by
  have h := singleton4126 B _hB
  rw [sound557 B _hB _hF, sound677 B _hB _hF] at h
  norm_num [nodeValue4126, nodeValue557, nodeValue677, Sparse.eval] at h ⊢
  linarith only [h]

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

theorem zero4209 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4209 node4209Labels = 0 := by
  exact mixedMoment_order_one B hB node4209 node4209Labels 1
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

theorem sound4209 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4209 node4209Labels = Sparse.eval nodeValue4209 (mixedVector B) := by
  simpa only [nodeValue4209, Sparse.eval_nil] using zero4209 B _hB _hF

theorem sound4210 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4210 node4210Labels = Sparse.eval nodeValue4210 (mixedVector B) := by
  have h := singleton4210 B _hB
  rw [sound713 B _hB _hF, sound751 B _hB _hF] at h
  norm_num [nodeValue4210, nodeValue713, nodeValue751, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4217 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4217 node4217Labels = Sparse.eval nodeValue4217 (mixedVector B) := by
  have h := singleton4217 B _hB
  rw [sound719 B _hB _hF, sound756 B _hB _hF] at h
  norm_num [nodeValue4217, nodeValue719, nodeValue756, Sparse.eval] at h ⊢
  linarith only [h]

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

theorem zero4264 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4264 node4264Labels = 0 := by
  exact mixedMoment_order_one B hB node4264 node4264Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero4267 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4267 node4267Labels = 0 := by
  exact mixedMoment_order_one B hB node4267 node4267Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero4283 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4283 node4283Labels = 0 := by
  exact mixedMoment_order_one B hB node4283 node4283Labels 1
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

theorem sound4249 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4249 node4249Labels = Sparse.eval nodeValue4249 (mixedVector B) := by
  have h := singleton4249 B _hB
  rw [sound783 B _hB _hF, sound803 B _hB _hF] at h
  norm_num [nodeValue4249, nodeValue783, nodeValue803, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4252 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4252 node4252Labels = Sparse.eval nodeValue4252 (mixedVector B) := by
  have h := singleton4252 B _hB
  rw [sound786 B _hB _hF, sound822 B _hB _hF] at h
  norm_num [nodeValue4252, nodeValue786, nodeValue822, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4264 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4264 node4264Labels = Sparse.eval nodeValue4264 (mixedVector B) := by
  simpa only [nodeValue4264, Sparse.eval_nil] using zero4264 B _hB _hF

theorem sound4265 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4265 node4265Labels = Sparse.eval nodeValue4265 (mixedVector B) := by
  have h := singleton4265 B _hB
  rw [sound807 B _hB _hF] at h
  norm_num [nodeValue4265, nodeValue807, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4267 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4267 node4267Labels = Sparse.eval nodeValue4267 (mixedVector B) := by
  simpa only [nodeValue4267, Sparse.eval_nil] using zero4267 B _hB _hF

theorem sound4268 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4268 node4268Labels = Sparse.eval nodeValue4268 (mixedVector B) := by
  have h := singleton4268 B _hB
  rw [sound811 B _hB _hF, sound824 B _hB _hF] at h
  norm_num [nodeValue4268, nodeValue811, nodeValue824, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4275 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4275 node4275Labels = Sparse.eval nodeValue4275 (mixedVector B) := by
  have h := singleton4275 B _hB
  rw [sound827 B _hB _hF] at h
  norm_num [nodeValue4275, nodeValue827, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4283 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4283 node4283Labels = Sparse.eval nodeValue4283 (mixedVector B) := by
  simpa only [nodeValue4283, Sparse.eval_nil] using zero4283 B _hB _hF

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

theorem sound4399 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4399 node4399Labels = Sparse.eval nodeValue4399 (mixedVector B) := by
  have h := singleton4399 B _hB
  rw [sound980 B _hB _hF, sound1616 B _hB _hF] at h
  norm_num [nodeValue4399, nodeValue980, nodeValue1616, Sparse.eval] at h ⊢
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

theorem sound4458 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4458 node4458Labels = Sparse.eval nodeValue4458 (mixedVector B) := by
  have h := singleton4458 B _hB
  rw [sound1041 B _hB _hF, sound1724 B _hB _hF] at h
  norm_num [nodeValue4458, nodeValue1041, nodeValue1724, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4461 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4461 node4461Labels = Sparse.eval nodeValue4461 (mixedVector B) := by
  have h := singleton4461 B _hB
  rw [sound1044 B _hB _hF, sound1737 B _hB _hF] at h
  norm_num [nodeValue4461, nodeValue1044, nodeValue1737, Sparse.eval] at h ⊢
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

theorem zero4502 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4502 node4502Labels = 0 := by
  exact mixedMoment_order_one B hB node4502 node4502Labels 1
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

theorem sound4502 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4502 node4502Labels = Sparse.eval nodeValue4502 (mixedVector B) := by
  simpa only [nodeValue4502, Sparse.eval_nil] using zero4502 B _hB _hF

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources56
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sourceEq1818 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1818 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1818 + difference 0 1) (sourceB1818 + difference 1 0) sourceC1818) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4502) := by
    have ha : (tripleCharges (sourceA1818 + difference 0 1) (sourceB1818 + difference 1 0) sourceC1818) = raw24260 := by
      apply Matrix.ext; unfold tripleCharges sourceA1818 sourceB1818 sourceC1818 difference raw24260; decide +kernel
    rw [ha]
    exact (canonical24260 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1818 + difference 0 2) (sourceB1818 + difference 2 0) sourceC1818) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4399) := by
    have ha : (tripleCharges (sourceA1818 + difference 0 2) (sourceB1818 + difference 2 0) sourceC1818) = raw24605 := by
      apply Matrix.ext; unfold tripleCharges sourceA1818 sourceB1818 sourceC1818 difference raw24605; decide +kernel
    rw [ha]
    exact (canonical24605 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1818 + difference 0 3) (sourceB1818 + difference 3 0) sourceC1818) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4458) := by
    have ha : (tripleCharges (sourceA1818 + difference 0 3) (sourceB1818 + difference 3 0) sourceC1818) = raw24252 := by
      apply Matrix.ext; unfold tripleCharges sourceA1818 sourceB1818 sourceC1818 difference raw24252; decide +kernel
    rw [ha]
    exact (canonical24252 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1818 + difference 0 4) (sourceB1818 + difference 4 0) sourceC1818) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4458) := by
    have ha : (tripleCharges (sourceA1818 + difference 0 4) (sourceB1818 + difference 4 0) sourceC1818) = raw25108 := by
      apply Matrix.ext; unfold tripleCharges sourceA1818 sourceB1818 sourceC1818 difference raw25108; decide +kernel
    rw [ha]
    exact (canonical25108 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1818 + difference 0 5) (sourceB1818 + difference 5 0) sourceC1818) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4461) := by
    have ha : (tripleCharges (sourceA1818 + difference 0 5) (sourceB1818 + difference 5 0) sourceC1818) = raw25285 := by
      apply Matrix.ext; unfold tripleCharges sourceA1818 sourceB1818 sourceC1818 difference raw25285; decide +kernel
    rw [ha]
    exact (canonical25285 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1818 + difference 1 0) (sourceB1818 + difference 0 1) sourceC1818) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4126) := by
    have ha : (tripleCharges (sourceA1818 + difference 1 0) (sourceB1818 + difference 0 1) sourceC1818) = raw26281 := by
      apply Matrix.ext; unfold tripleCharges sourceA1818 sourceB1818 sourceC1818 difference raw26281; decide +kernel
    rw [ha]
    exact (canonical26281 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1818 + difference 1 2) (sourceB1818 + difference 2 1) sourceC1818) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4217) := by
    have ha : (tripleCharges (sourceA1818 + difference 1 2) (sourceB1818 + difference 2 1) sourceC1818) = raw26282 := by
      apply Matrix.ext; unfold tripleCharges sourceA1818 sourceB1818 sourceC1818 difference raw26282; decide +kernel
    rw [ha]
    exact (canonical26282 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1818 + difference 1 3) (sourceB1818 + difference 3 1) sourceC1818) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4268) := by
    have ha : (tripleCharges (sourceA1818 + difference 1 3) (sourceB1818 + difference 3 1) sourceC1818) = raw26283 := by
      apply Matrix.ext; unfold tripleCharges sourceA1818 sourceB1818 sourceC1818 difference raw26283; decide +kernel
    rw [ha]
    exact (canonical26283 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1818 + difference 1 4) (sourceB1818 + difference 4 1) sourceC1818) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4268) := by
    have ha : (tripleCharges (sourceA1818 + difference 1 4) (sourceB1818 + difference 4 1) sourceC1818) = raw25273 := by
      apply Matrix.ext; unfold tripleCharges sourceA1818 sourceB1818 sourceC1818 difference raw25273; decide +kernel
    rw [ha]
    exact (canonical25273 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1818 + difference 1 5) (sourceB1818 + difference 5 1) sourceC1818) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4275) := by
    have ha : (tripleCharges (sourceA1818 + difference 1 5) (sourceB1818 + difference 5 1) sourceC1818) = raw25089 := by
      apply Matrix.ext; unfold tripleCharges sourceA1818 sourceB1818 sourceC1818 difference raw25089; decide +kernel
    rw [ha]
    exact (canonical25089 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1818 + difference 2 0) (sourceB1818 + difference 0 2) sourceC1818) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4113) := by
    have ha : (tripleCharges (sourceA1818 + difference 2 0) (sourceB1818 + difference 0 2) sourceC1818) = raw26284 := by
      apply Matrix.ext; unfold tripleCharges sourceA1818 sourceB1818 sourceC1818 difference raw26284; decide +kernel
    rw [ha]
    exact (canonical26284 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1818 + difference 2 1) (sourceB1818 + difference 1 2) sourceC1818) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4267) := by
    have ha : (tripleCharges (sourceA1818 + difference 2 1) (sourceB1818 + difference 1 2) sourceC1818) = raw26285 := by
      apply Matrix.ext; unfold tripleCharges sourceA1818 sourceB1818 sourceC1818 difference raw26285; decide +kernel
    rw [ha]
    exact (canonical26285 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1818 + difference 2 3) (sourceB1818 + difference 3 2) sourceC1818) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4249) := by
    have ha : (tripleCharges (sourceA1818 + difference 2 3) (sourceB1818 + difference 3 2) sourceC1818) = raw26286 := by
      apply Matrix.ext; unfold tripleCharges sourceA1818 sourceB1818 sourceC1818 difference raw26286; decide +kernel
    rw [ha]
    exact (canonical26286 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1818 + difference 2 4) (sourceB1818 + difference 4 2) sourceC1818) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4249) := by
    have ha : (tripleCharges (sourceA1818 + difference 2 4) (sourceB1818 + difference 4 2) sourceC1818) = raw25277 := by
      apply Matrix.ext; unfold tripleCharges sourceA1818 sourceB1818 sourceC1818 difference raw25277; decide +kernel
    rw [ha]
    exact (canonical25277 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1818 + difference 2 5) (sourceB1818 + difference 5 2) sourceC1818) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4252) := by
    have ha : (tripleCharges (sourceA1818 + difference 2 5) (sourceB1818 + difference 5 2) sourceC1818) = raw25094 := by
      apply Matrix.ext; unfold tripleCharges sourceA1818 sourceB1818 sourceC1818 difference raw25094; decide +kernel
    rw [ha]
    exact (canonical25094 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1818 + difference 3 0) (sourceB1818 + difference 0 3) sourceC1818) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4119) := by
    have ha : (tripleCharges (sourceA1818 + difference 3 0) (sourceB1818 + difference 0 3) sourceC1818) = raw26287 := by
      apply Matrix.ext; unfold tripleCharges sourceA1818 sourceB1818 sourceC1818 difference raw26287; decide +kernel
    rw [ha]
    exact (canonical26287 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1818 + difference 3 1) (sourceB1818 + difference 1 3) sourceC1818) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4283) := by
    have ha : (tripleCharges (sourceA1818 + difference 3 1) (sourceB1818 + difference 1 3) sourceC1818) = raw25713 := by
      apply Matrix.ext; unfold tripleCharges sourceA1818 sourceB1818 sourceC1818 difference raw25713; decide +kernel
    rw [ha]
    exact (canonical25713 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1818 + difference 3 2) (sourceB1818 + difference 2 3) sourceC1818) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4210) := by
    have ha : (tripleCharges (sourceA1818 + difference 3 2) (sourceB1818 + difference 2 3) sourceC1818) = raw26288 := by
      apply Matrix.ext; unfold tripleCharges sourceA1818 sourceB1818 sourceC1818 difference raw26288; decide +kernel
    rw [ha]
    exact (canonical26288 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1818 + difference 3 4) (sourceB1818 + difference 4 3) sourceC1818) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4265) := by
    have ha : (tripleCharges (sourceA1818 + difference 3 4) (sourceB1818 + difference 4 3) sourceC1818) = raw25281 := by
      apply Matrix.ext; unfold tripleCharges sourceA1818 sourceB1818 sourceC1818 difference raw25281; decide +kernel
    rw [ha]
    exact (canonical25281 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1818 + difference 3 5) (sourceB1818 + difference 5 3) sourceC1818) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4268) := by
    have ha : (tripleCharges (sourceA1818 + difference 3 5) (sourceB1818 + difference 5 3) sourceC1818) = raw25099 := by
      apply Matrix.ext; unfold tripleCharges sourceA1818 sourceB1818 sourceC1818 difference raw25099; decide +kernel
    rw [ha]
    exact (canonical25099 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1818 + difference 4 0) (sourceB1818 + difference 0 4) sourceC1818) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4119) := by
    have ha : (tripleCharges (sourceA1818 + difference 4 0) (sourceB1818 + difference 0 4) sourceC1818) = raw26289 := by
      apply Matrix.ext; unfold tripleCharges sourceA1818 sourceB1818 sourceC1818 difference raw26289; decide +kernel
    rw [ha]
    exact (canonical26289 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1818 + difference 4 1) (sourceB1818 + difference 1 4) sourceC1818) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4283) := by
    have ha : (tripleCharges (sourceA1818 + difference 4 1) (sourceB1818 + difference 1 4) sourceC1818) = raw26290 := by
      apply Matrix.ext; unfold tripleCharges sourceA1818 sourceB1818 sourceC1818 difference raw26290; decide +kernel
    rw [ha]
    exact (canonical26290 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1818 + difference 4 2) (sourceB1818 + difference 2 4) sourceC1818) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4210) := by
    have ha : (tripleCharges (sourceA1818 + difference 4 2) (sourceB1818 + difference 2 4) sourceC1818) = raw26291 := by
      apply Matrix.ext; unfold tripleCharges sourceA1818 sourceB1818 sourceC1818 difference raw26291; decide +kernel
    rw [ha]
    exact (canonical26291 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1818 + difference 4 3) (sourceB1818 + difference 3 4) sourceC1818) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4265) := by
    have ha : (tripleCharges (sourceA1818 + difference 4 3) (sourceB1818 + difference 3 4) sourceC1818) = raw26292 := by
      apply Matrix.ext; unfold tripleCharges sourceA1818 sourceB1818 sourceC1818 difference raw26292; decide +kernel
    rw [ha]
    exact (canonical26292 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1818 + difference 4 5) (sourceB1818 + difference 5 4) sourceC1818) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4268) := by
    have ha : (tripleCharges (sourceA1818 + difference 4 5) (sourceB1818 + difference 5 4) sourceC1818) = raw25104 := by
      apply Matrix.ext; unfold tripleCharges sourceA1818 sourceB1818 sourceC1818 difference raw25104; decide +kernel
    rw [ha]
    exact (canonical25104 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1818 + difference 5 0) (sourceB1818 + difference 0 5) sourceC1818) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4118) := by
    have ha : (tripleCharges (sourceA1818 + difference 5 0) (sourceB1818 + difference 0 5) sourceC1818) = raw26293 := by
      apply Matrix.ext; unfold tripleCharges sourceA1818 sourceB1818 sourceC1818 difference raw26293; decide +kernel
    rw [ha]
    exact (canonical26293 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1818 + difference 5 1) (sourceB1818 + difference 1 5) sourceC1818) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4069) := by
    have ha : (tripleCharges (sourceA1818 + difference 5 1) (sourceB1818 + difference 1 5) sourceC1818) = raw26167 := by
      apply Matrix.ext; unfold tripleCharges sourceA1818 sourceB1818 sourceC1818 difference raw26167; decide +kernel
    rw [ha]
    exact (canonical26167 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1818 + difference 5 2) (sourceB1818 + difference 2 5) sourceC1818) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4209) := by
    have ha : (tripleCharges (sourceA1818 + difference 5 2) (sourceB1818 + difference 2 5) sourceC1818) = raw26165 := by
      apply Matrix.ext; unfold tripleCharges sourceA1818 sourceB1818 sourceC1818 difference raw26165; decide +kernel
    rw [ha]
    exact (canonical26165 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1818 + difference 5 3) (sourceB1818 + difference 3 5) sourceC1818) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4264) := by
    have ha : (tripleCharges (sourceA1818 + difference 5 3) (sourceB1818 + difference 3 5) sourceC1818) = raw25478 := by
      apply Matrix.ext; unfold tripleCharges sourceA1818 sourceB1818 sourceC1818 difference raw25478; decide +kernel
    rw [ha]
    exact (canonical25478 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1818 + difference 5 4) (sourceB1818 + difference 4 5) sourceC1818) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4264) := by
    have ha : (tripleCharges (sourceA1818 + difference 5 4) (sourceB1818 + difference 4 5) sourceC1818) = raw25286 := by
      apply Matrix.ext; unfold tripleCharges sourceA1818 sourceB1818 sourceC1818 difference raw25286; decide +kernel
    rw [ha]
    exact (canonical25286 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1818 sourceB1818 sourceC1818
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1818, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic96
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reindexCheck1539 : Integer.Sparse.reindex keyMap MixedData.row1539 = numericRow1539 := by decide +kernel

theorem numericCheck1539 (x : Master → ℝ) : Integer.Sparse.eval numericRow1539 x =
    (4 : ℝ) * reducedSource1539 x := by
  norm_num [numericRow1539, reducedSource1539, Integer.Sparse.eval, Sparse.eval, nodeValue4069, nodeValue4113, nodeValue4118, nodeValue4119, nodeValue4126, nodeValue4209, nodeValue4210, nodeValue4217, nodeValue4249, nodeValue4252, nodeValue4264, nodeValue4265, nodeValue4267, nodeValue4268, nodeValue4275, nodeValue4283, nodeValue4399, nodeValue4458, nodeValue4461, nodeValue4502]
  ring

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Rows96
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero1539 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1539 (mixedVector B) = 0 := by
  have h4069 : mixedVector B (Sum.inr 4069) = Sparse.eval nodeValue4069 (mixedVector B) := by
    change mixedMoment B node4069 node4069Labels = _
    exact sound4069 B hB hF
  have h4113 : mixedVector B (Sum.inr 4113) = Sparse.eval nodeValue4113 (mixedVector B) := by
    change mixedMoment B node4113 node4113Labels = _
    exact sound4113 B hB hF
  have h4118 : mixedVector B (Sum.inr 4118) = Sparse.eval nodeValue4118 (mixedVector B) := by
    change mixedMoment B node4118 node4118Labels = _
    exact sound4118 B hB hF
  have h4119 : mixedVector B (Sum.inr 4119) = Sparse.eval nodeValue4119 (mixedVector B) := by
    change mixedMoment B node4119 node4119Labels = _
    exact sound4119 B hB hF
  have h4126 : mixedVector B (Sum.inr 4126) = Sparse.eval nodeValue4126 (mixedVector B) := by
    change mixedMoment B node4126 node4126Labels = _
    exact sound4126 B hB hF
  have h4209 : mixedVector B (Sum.inr 4209) = Sparse.eval nodeValue4209 (mixedVector B) := by
    change mixedMoment B node4209 node4209Labels = _
    exact sound4209 B hB hF
  have h4210 : mixedVector B (Sum.inr 4210) = Sparse.eval nodeValue4210 (mixedVector B) := by
    change mixedMoment B node4210 node4210Labels = _
    exact sound4210 B hB hF
  have h4217 : mixedVector B (Sum.inr 4217) = Sparse.eval nodeValue4217 (mixedVector B) := by
    change mixedMoment B node4217 node4217Labels = _
    exact sound4217 B hB hF
  have h4249 : mixedVector B (Sum.inr 4249) = Sparse.eval nodeValue4249 (mixedVector B) := by
    change mixedMoment B node4249 node4249Labels = _
    exact sound4249 B hB hF
  have h4252 : mixedVector B (Sum.inr 4252) = Sparse.eval nodeValue4252 (mixedVector B) := by
    change mixedMoment B node4252 node4252Labels = _
    exact sound4252 B hB hF
  have h4264 : mixedVector B (Sum.inr 4264) = Sparse.eval nodeValue4264 (mixedVector B) := by
    change mixedMoment B node4264 node4264Labels = _
    exact sound4264 B hB hF
  have h4265 : mixedVector B (Sum.inr 4265) = Sparse.eval nodeValue4265 (mixedVector B) := by
    change mixedMoment B node4265 node4265Labels = _
    exact sound4265 B hB hF
  have h4267 : mixedVector B (Sum.inr 4267) = Sparse.eval nodeValue4267 (mixedVector B) := by
    change mixedMoment B node4267 node4267Labels = _
    exact sound4267 B hB hF
  have h4268 : mixedVector B (Sum.inr 4268) = Sparse.eval nodeValue4268 (mixedVector B) := by
    change mixedMoment B node4268 node4268Labels = _
    exact sound4268 B hB hF
  have h4275 : mixedVector B (Sum.inr 4275) = Sparse.eval nodeValue4275 (mixedVector B) := by
    change mixedMoment B node4275 node4275Labels = _
    exact sound4275 B hB hF
  have h4283 : mixedVector B (Sum.inr 4283) = Sparse.eval nodeValue4283 (mixedVector B) := by
    change mixedMoment B node4283 node4283Labels = _
    exact sound4283 B hB hF
  have h4399 : mixedVector B (Sum.inr 4399) = Sparse.eval nodeValue4399 (mixedVector B) := by
    change mixedMoment B node4399 node4399Labels = _
    exact sound4399 B hB hF
  have h4458 : mixedVector B (Sum.inr 4458) = Sparse.eval nodeValue4458 (mixedVector B) := by
    change mixedMoment B node4458 node4458Labels = _
    exact sound4458 B hB hF
  have h4461 : mixedVector B (Sum.inr 4461) = Sparse.eval nodeValue4461 (mixedVector B) := by
    change mixedMoment B node4461 node4461Labels = _
    exact sound4461 B hB hF
  have h4502 : mixedVector B (Sum.inr 4502) = Sparse.eval nodeValue4502 (mixedVector B) := by
    change mixedMoment B node4502 node4502Labels = _
    exact sound4502 B hB hF
  simpa only [sourceForm1818, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4069, h4113, h4118, h4119, h4126, h4209, h4210, h4217, h4249, h4252, h4264, h4265, h4267, h4268, h4275, h4283, h4399, h4458, h4461, h4502, reducedSource1539] using sourceEq1818 B hB

theorem rowSound1539_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1539 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1539, numericCheck1539, reducedZero1539 B hB hF, mul_zero]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedSourceBridge.rowSound1539_e_oai := @OAI.MUB6.Certificate.MixedSourceBridge.rowSound1539_e_oai
