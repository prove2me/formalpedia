-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedSourceBridge.rowSound326_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T01:13:10.841088+00:00
-- url     : https://prove2.me/submissions/2d028227-6da4-48e5-a641-99cd2bf594aa

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E070
import Definitions.Def_OAIQ106E086
import Definitions.Def_OAIQ106E188
import Definitions.Def_OAIQ106E191
import Definitions.Def_OAIQ106E194
import Definitions.Def_OAIQ106E117
import Definitions.Def_OAIQ106E119
import Definitions.Def_OAIQ106E121
import Definitions.Def_OAIQ106E126
import Definitions.Def_OAIQ106E140
import Definitions.Def_OAIQ106E147
import Definitions.Def_OAIQ106E170
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound5439_e

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

theorem IsHadamard.column_orthogonal {H : CMatrix} (hH : IsHadamard H)
    (i j : Coord) :
    ∑ k, conj (H k i) * H k j = if i = j then 6 else 0 := by
  have h := congrArg (fun M : CMatrix => M i j) hH.2
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical16
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical2175 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2175 raw2175Labels = mixedMoment B node5149 node5149Labels := by
  calc
    mixedMoment B raw2175 raw2175Labels = mixedMoment B raw2175step0 raw2175step0Labels := by
      have ha : raw2175step0 = (fun i j => raw2175 (permutation152 i) (permutation5 j)) := by apply Matrix.ext; unfold raw2175step0 raw2175; decide +kernel
      have hl : raw2175step0Labels = raw2175Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2175 raw2175Labels permutation152 permutation5
    mixedMoment B raw2175step0 raw2175step0Labels = mixedMoment B raw2175step1 raw2175step1Labels := by
      have ha : raw2175step1 = raw2175step0 := by apply Matrix.ext; unfold raw2175step1 raw2175step0; decide +kernel
      have hl : raw2175step0Labels = labelEmbedding8 ∘ raw2175step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2175step0 raw2175step0Labels raw2175step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5149 node5149Labels := by rfl

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

theorem canonical2176 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2176 raw2176Labels = mixedMoment B node2924 node2924Labels := by
  calc
    mixedMoment B raw2176 raw2176Labels = mixedMoment B raw2176step0 raw2176step0Labels := by
      have ha : raw2176step0 = (fun i j => raw2176 (permutation154 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2176step0 raw2176; decide +kernel
      have hl : raw2176step0Labels = raw2176Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2176 raw2176Labels permutation154 permutation4
    _ = mixedMoment B node2924 node2924Labels := by rfl

theorem canonical2177 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2177 raw2177Labels = mixedMoment B node3605 node3605Labels := by
  calc
    mixedMoment B raw2177 raw2177Labels = mixedMoment B raw2177step0 raw2177step0Labels := by
      have ha : raw2177step0 = (fun i j => raw2177 (permutation162 i) (permutation3 j)) := by apply Matrix.ext; unfold raw2177step0 raw2177; decide +kernel
      have hl : raw2177step0Labels = raw2177Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2177 raw2177Labels permutation162 permutation3
    mixedMoment B raw2177step0 raw2177step0Labels = mixedMoment B raw2177step1 raw2177step1Labels := by
      have ha : raw2177step1 = -raw2177step0 := by apply Matrix.ext; change ∀ i j, raw2177step1 i j = -(raw2177step0 i j); unfold raw2177step1 raw2177step0; decide +kernel
      have hl : raw2177step1Labels = raw2177step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2177step1 raw2177step1Labels = mixedMoment B raw2177step2 raw2177step2Labels := by
      have ha : raw2177step2 = raw2177step1 := by apply Matrix.ext; unfold raw2177step2 raw2177step1; decide +kernel
      have hl : raw2177step1Labels = labelEmbedding1 ∘ raw2177step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2177step1 raw2177step1Labels raw2177step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3605 node3605Labels := by rfl

theorem canonical2289 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2289 raw2289Labels = mixedMoment B node5284 node5284Labels := by
  calc
    mixedMoment B raw2289 raw2289Labels = mixedMoment B raw2289step0 raw2289step0Labels := by
      have ha : raw2289step0 = (fun i j => raw2289 (permutation32 i) (permutation5 j)) := by apply Matrix.ext; unfold raw2289step0 raw2289; decide +kernel
      have hl : raw2289step0Labels = raw2289Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2289 raw2289Labels permutation32 permutation5
    mixedMoment B raw2289step0 raw2289step0Labels = mixedMoment B raw2289step1 raw2289step1Labels := by
      have ha : raw2289step1 = raw2289step0 := by apply Matrix.ext; unfold raw2289step1 raw2289step0; decide +kernel
      have hl : raw2289step0Labels = labelEmbedding8 ∘ raw2289step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2289step0 raw2289step0Labels raw2289step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5284 node5284Labels := by rfl

theorem canonical2290 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2290 raw2290Labels = mixedMoment B node3077 node3077Labels := by
  calc
    mixedMoment B raw2290 raw2290Labels = mixedMoment B raw2290step0 raw2290step0Labels := by
      have ha : raw2290step0 = (fun i j => raw2290 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2290step0 raw2290; decide +kernel
      have hl : raw2290step0Labels = raw2290Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2290 raw2290Labels permutation32 permutation4
    _ = mixedMoment B node3077 node3077Labels := by rfl

theorem canonical2291 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2291 raw2291Labels = mixedMoment B node3625 node3625Labels := by
  calc
    mixedMoment B raw2291 raw2291Labels = mixedMoment B raw2291step0 raw2291step0Labels := by
      have ha : raw2291step0 = (fun i j => raw2291 (permutation48 i) (permutation3 j)) := by apply Matrix.ext; unfold raw2291step0 raw2291; decide +kernel
      have hl : raw2291step0Labels = raw2291Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2291 raw2291Labels permutation48 permutation3
    mixedMoment B raw2291step0 raw2291step0Labels = mixedMoment B raw2291step1 raw2291step1Labels := by
      have ha : raw2291step1 = -raw2291step0 := by apply Matrix.ext; change ∀ i j, raw2291step1 i j = -(raw2291step0 i j); unfold raw2291step1 raw2291step0; decide +kernel
      have hl : raw2291step1Labels = raw2291step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2291step1 raw2291step1Labels = mixedMoment B raw2291step2 raw2291step2Labels := by
      have ha : raw2291step2 = raw2291step1 := by apply Matrix.ext; unfold raw2291step2 raw2291step1; decide +kernel
      have hl : raw2291step1Labels = labelEmbedding1 ∘ raw2291step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2291step1 raw2291step1Labels raw2291step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3625 node3625Labels := by rfl

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

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical57
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical7409 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7409 raw7409Labels = mixedMoment B node5429 node5429Labels := by
  calc
    mixedMoment B raw7409 raw7409Labels = mixedMoment B raw7409step0 raw7409step0Labels := by
      have ha : raw7409step0 = (fun i j => raw7409 (permutation682 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7409step0 raw7409; decide +kernel
      have hl : raw7409step0Labels = raw7409Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7409 raw7409Labels permutation682 permutation2
    mixedMoment B raw7409step0 raw7409step0Labels = mixedMoment B raw7409step1 raw7409step1Labels := by
      have ha : raw7409step1 = -raw7409step0 := by apply Matrix.ext; change ∀ i j, raw7409step1 i j = -(raw7409step0 i j); unfold raw7409step1 raw7409step0; decide +kernel
      have hl : raw7409step1Labels = raw7409step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5429 node5429Labels := by rfl

theorem canonical7410 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7410 raw7410Labels = mixedMoment B node5424 node5424Labels := by
  calc
    mixedMoment B raw7410 raw7410Labels = mixedMoment B raw7410step0 raw7410step0Labels := by
      have ha : raw7410step0 = (fun i j => raw7410 (permutation676 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7410step0 raw7410; decide +kernel
      have hl : raw7410step0Labels = raw7410Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7410 raw7410Labels permutation676 permutation2
    mixedMoment B raw7410step0 raw7410step0Labels = mixedMoment B raw7410step1 raw7410step1Labels := by
      have ha : raw7410step1 = -raw7410step0 := by apply Matrix.ext; change ∀ i j, raw7410step1 i j = -(raw7410step0 i j); unfold raw7410step1 raw7410step0; decide +kernel
      have hl : raw7410step1Labels = raw7410step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5424 node5424Labels := by rfl

theorem canonical7411 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7411 raw7411Labels = mixedMoment B node5424 node5424Labels := by
  calc
    mixedMoment B raw7411 raw7411Labels = mixedMoment B raw7411step0 raw7411step0Labels := by
      have ha : raw7411step0 = (fun i j => raw7411 (permutation674 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7411step0 raw7411; decide +kernel
      have hl : raw7411step0Labels = raw7411Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7411 raw7411Labels permutation674 permutation2
    mixedMoment B raw7411step0 raw7411step0Labels = mixedMoment B raw7411step1 raw7411step1Labels := by
      have ha : raw7411step1 = -raw7411step0 := by apply Matrix.ext; change ∀ i j, raw7411step1 i j = -(raw7411step0 i j); unfold raw7411step1 raw7411step0; decide +kernel
      have hl : raw7411step1Labels = raw7411step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5424 node5424Labels := by rfl

theorem canonical7412 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7412 raw7412Labels = mixedMoment B node5439 node5439Labels := by
  calc
    mixedMoment B raw7412 raw7412Labels = mixedMoment B raw7412step0 raw7412step0Labels := by
      have hz : ∀ j, raw7412 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw7412step0 = (fun i j => raw7412 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw7412step0 raw7412; decide +kernel
      have hl : raw7412step0Labels = raw7412Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7412 raw7412Labels permutation520 hz
    mixedMoment B raw7412step0 raw7412step0Labels = mixedMoment B raw7412step1 raw7412step1Labels := by
      have ha : raw7412step1 = (fun i j => raw7412step0 (permutation137 i) (permutation7 j)) := by apply Matrix.ext; unfold raw7412step1 raw7412step0; decide +kernel
      have hl : raw7412step1Labels = raw7412step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7412step0 raw7412step0Labels permutation137 permutation7
    mixedMoment B raw7412step1 raw7412step1Labels = mixedMoment B raw7412step2 raw7412step2Labels := by
      have ha : raw7412step2 = raw7412step1 := by apply Matrix.ext; unfold raw7412step2 raw7412step1; decide +kernel
      have hl : raw7412step1Labels = labelEmbedding10 ∘ raw7412step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7412step1 raw7412step1Labels raw7412step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5439 node5439Labels := by rfl

theorem canonical7413 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7413 raw7413Labels = mixedMoment B node5481 node5481Labels := by
  calc
    mixedMoment B raw7413 raw7413Labels = mixedMoment B raw7413step0 raw7413step0Labels := by
      have ha : raw7413step0 = (fun i j => raw7413 (permutation617 i) (permutation6 j)) := by apply Matrix.ext; unfold raw7413step0 raw7413; decide +kernel
      have hl : raw7413step0Labels = raw7413Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7413 raw7413Labels permutation617 permutation6
    mixedMoment B raw7413step0 raw7413step0Labels = mixedMoment B raw7413step1 raw7413step1Labels := by
      have ha : raw7413step1 = raw7413step0 := by apply Matrix.ext; unfold raw7413step1 raw7413step0; decide +kernel
      have hl : raw7413step0Labels = labelEmbedding9 ∘ raw7413step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7413step0 raw7413step0Labels raw7413step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5481 node5481Labels := by rfl

theorem canonical7414 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7414 raw7414Labels = mixedMoment B node4439 node4439Labels := by
  calc
    mixedMoment B raw7414 raw7414Labels = mixedMoment B raw7414step0 raw7414step0Labels := by
      have ha : raw7414step0 = (fun i j => raw7414 (permutation182 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7414step0 raw7414; decide +kernel
      have hl : raw7414step0Labels = raw7414Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7414 raw7414Labels permutation182 permutation3
    mixedMoment B raw7414step0 raw7414step0Labels = mixedMoment B raw7414step1 raw7414step1Labels := by
      have ha : raw7414step1 = raw7414step0 := by apply Matrix.ext; unfold raw7414step1 raw7414step0; decide +kernel
      have hl : raw7414step0Labels = labelEmbedding6 ∘ raw7414step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7414step0 raw7414step0Labels raw7414step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4439 node4439Labels := by rfl

theorem canonical7415 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7415 raw7415Labels = mixedMoment B node5149 node5149Labels := by
  calc
    mixedMoment B raw7415 raw7415Labels = mixedMoment B raw7415step0 raw7415step0Labels := by
      have ha : raw7415step0 = (fun i j => raw7415 (permutation182 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7415step0 raw7415; decide +kernel
      have hl : raw7415step0Labels = raw7415Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7415 raw7415Labels permutation182 permutation3
    mixedMoment B raw7415step0 raw7415step0Labels = mixedMoment B raw7415step1 raw7415step1Labels := by
      have ha : raw7415step1 = raw7415step0 := by apply Matrix.ext; unfold raw7415step1 raw7415step0; decide +kernel
      have hl : raw7415step0Labels = labelEmbedding6 ∘ raw7415step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7415step0 raw7415step0Labels raw7415step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5149 node5149Labels := by rfl

theorem canonical7416 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7416 raw7416Labels = mixedMoment B node5149 node5149Labels := by
  calc
    mixedMoment B raw7416 raw7416Labels = mixedMoment B raw7416step0 raw7416step0Labels := by
      have ha : raw7416step0 = (fun i j => raw7416 (permutation206 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7416step0 raw7416; decide +kernel
      have hl : raw7416step0Labels = raw7416Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7416 raw7416Labels permutation206 permutation3
    mixedMoment B raw7416step0 raw7416step0Labels = mixedMoment B raw7416step1 raw7416step1Labels := by
      have ha : raw7416step1 = raw7416step0 := by apply Matrix.ext; unfold raw7416step1 raw7416step0; decide +kernel
      have hl : raw7416step0Labels = labelEmbedding6 ∘ raw7416step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7416step0 raw7416step0Labels raw7416step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5149 node5149Labels := by rfl

theorem canonical7417 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7417 raw7417Labels = mixedMoment B node5284 node5284Labels := by
  calc
    mixedMoment B raw7417 raw7417Labels = mixedMoment B raw7417step0 raw7417step0Labels := by
      have hz : ∀ j, raw7417 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw7417step0 = (fun i j => raw7417 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw7417step0 raw7417; decide +kernel
      have hl : raw7417step0Labels = raw7417Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7417 raw7417Labels permutation520 hz
    mixedMoment B raw7417step0 raw7417step0Labels = mixedMoment B raw7417step1 raw7417step1Labels := by
      have ha : raw7417step1 = (fun i j => raw7417step0 (permutation40 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7417step1 raw7417step0; decide +kernel
      have hl : raw7417step1Labels = raw7417step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7417step0 raw7417step0Labels permutation40 permutation3
    mixedMoment B raw7417step1 raw7417step1Labels = mixedMoment B raw7417step2 raw7417step2Labels := by
      have ha : raw7417step2 = raw7417step1 := by apply Matrix.ext; unfold raw7417step2 raw7417step1; decide +kernel
      have hl : raw7417step1Labels = labelEmbedding6 ∘ raw7417step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7417step1 raw7417step1Labels raw7417step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5284 node5284Labels := by rfl

theorem canonical7418 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7418 raw7418Labels = mixedMoment B node5281 node5281Labels := by
  calc
    mixedMoment B raw7418 raw7418Labels = mixedMoment B raw7418step0 raw7418step0Labels := by
      have ha : raw7418step0 = (fun i j => raw7418 (permutation186 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7418step0 raw7418; decide +kernel
      have hl : raw7418step0Labels = raw7418Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7418 raw7418Labels permutation186 permutation3
    mixedMoment B raw7418step0 raw7418step0Labels = mixedMoment B raw7418step1 raw7418step1Labels := by
      have ha : raw7418step1 = raw7418step0 := by apply Matrix.ext; unfold raw7418step1 raw7418step0; decide +kernel
      have hl : raw7418step0Labels = labelEmbedding6 ∘ raw7418step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7418step0 raw7418step0Labels raw7418step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5281 node5281Labels := by rfl

theorem canonical7419 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7419 raw7419Labels = mixedMoment B node4400 node4400Labels := by
  calc
    mixedMoment B raw7419 raw7419Labels = mixedMoment B raw7419step0 raw7419step0Labels := by
      have ha : raw7419step0 = (fun i j => raw7419 (permutation160 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7419step0 raw7419; decide +kernel
      have hl : raw7419step0Labels = raw7419Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7419 raw7419Labels permutation160 permutation3
    mixedMoment B raw7419step0 raw7419step0Labels = mixedMoment B raw7419step1 raw7419step1Labels := by
      have ha : raw7419step1 = raw7419step0 := by apply Matrix.ext; unfold raw7419step1 raw7419step0; decide +kernel
      have hl : raw7419step0Labels = labelEmbedding6 ∘ raw7419step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7419step0 raw7419step0Labels raw7419step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4400 node4400Labels := by rfl

theorem canonical7420 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7420 raw7420Labels = mixedMoment B node4999 node4999Labels := by
  calc
    mixedMoment B raw7420 raw7420Labels = mixedMoment B raw7420step0 raw7420step0Labels := by
      have ha : raw7420step0 = (fun i j => raw7420 (permutation160 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7420step0 raw7420; decide +kernel
      have hl : raw7420step0Labels = raw7420Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7420 raw7420Labels permutation160 permutation3
    mixedMoment B raw7420step0 raw7420step0Labels = mixedMoment B raw7420step1 raw7420step1Labels := by
      have ha : raw7420step1 = raw7420step0 := by apply Matrix.ext; unfold raw7420step1 raw7420step0; decide +kernel
      have hl : raw7420step0Labels = labelEmbedding6 ∘ raw7420step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7420step0 raw7420step0Labels raw7420step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4999 node4999Labels := by rfl

theorem canonical7421 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7421 raw7421Labels = mixedMoment B node5138 node5138Labels := by
  calc
    mixedMoment B raw7421 raw7421Labels = mixedMoment B raw7421step0 raw7421step0Labels := by
      have ha : raw7421step0 = (fun i j => raw7421 (permutation202 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7421step0 raw7421; decide +kernel
      have hl : raw7421step0Labels = raw7421Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7421 raw7421Labels permutation202 permutation3
    mixedMoment B raw7421step0 raw7421step0Labels = mixedMoment B raw7421step1 raw7421step1Labels := by
      have ha : raw7421step1 = raw7421step0 := by apply Matrix.ext; unfold raw7421step1 raw7421step0; decide +kernel
      have hl : raw7421step0Labels = labelEmbedding6 ∘ raw7421step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7421step0 raw7421step0Labels raw7421step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5138 node5138Labels := by rfl

theorem canonical7422 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7422 raw7422Labels = mixedMoment B node5260 node5260Labels := by
  calc
    mixedMoment B raw7422 raw7422Labels = mixedMoment B raw7422step0 raw7422step0Labels := by
      have hz : ∀ j, raw7422 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw7422step0 = (fun i j => raw7422 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw7422step0 raw7422; decide +kernel
      have hl : raw7422step0Labels = raw7422Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7422 raw7422Labels permutation520 hz
    mixedMoment B raw7422step0 raw7422step0Labels = mixedMoment B raw7422step1 raw7422step1Labels := by
      have ha : raw7422step1 = (fun i j => raw7422step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7422step1 raw7422step0; decide +kernel
      have hl : raw7422step1Labels = raw7422step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7422step0 raw7422step0Labels permutation34 permutation3
    mixedMoment B raw7422step1 raw7422step1Labels = mixedMoment B raw7422step2 raw7422step2Labels := by
      have ha : raw7422step2 = raw7422step1 := by apply Matrix.ext; unfold raw7422step2 raw7422step1; decide +kernel
      have hl : raw7422step1Labels = labelEmbedding6 ∘ raw7422step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7422step1 raw7422step1Labels raw7422step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5260 node5260Labels := by rfl

theorem canonical7423 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7423 raw7423Labels = mixedMoment B node5255 node5255Labels := by
  calc
    mixedMoment B raw7423 raw7423Labels = mixedMoment B raw7423step0 raw7423step0Labels := by
      have ha : raw7423step0 = (fun i j => raw7423 (permutation163 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7423step0 raw7423; decide +kernel
      have hl : raw7423step0Labels = raw7423Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7423 raw7423Labels permutation163 permutation3
    mixedMoment B raw7423step0 raw7423step0Labels = mixedMoment B raw7423step1 raw7423step1Labels := by
      have ha : raw7423step1 = raw7423step0 := by apply Matrix.ext; unfold raw7423step1 raw7423step0; decide +kernel
      have hl : raw7423step0Labels = labelEmbedding6 ∘ raw7423step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7423step0 raw7423step0Labels raw7423step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5255 node5255Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical58
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical7424 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7424 raw7424Labels = mixedMoment B node4400 node4400Labels := by
  calc
    mixedMoment B raw7424 raw7424Labels = mixedMoment B raw7424step0 raw7424step0Labels := by
      have ha : raw7424step0 = (fun i j => raw7424 (permutation154 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7424step0 raw7424; decide +kernel
      have hl : raw7424step0Labels = raw7424Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7424 raw7424Labels permutation154 permutation3
    mixedMoment B raw7424step0 raw7424step0Labels = mixedMoment B raw7424step1 raw7424step1Labels := by
      have ha : raw7424step1 = raw7424step0 := by apply Matrix.ext; unfold raw7424step1 raw7424step0; decide +kernel
      have hl : raw7424step0Labels = labelEmbedding6 ∘ raw7424step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7424step0 raw7424step0Labels raw7424step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4400 node4400Labels := by rfl

theorem canonical7425 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7425 raw7425Labels = mixedMoment B node4999 node4999Labels := by
  calc
    mixedMoment B raw7425 raw7425Labels = mixedMoment B raw7425step0 raw7425step0Labels := by
      have ha : raw7425step0 = (fun i j => raw7425 (permutation154 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7425step0 raw7425; decide +kernel
      have hl : raw7425step0Labels = raw7425Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7425 raw7425Labels permutation154 permutation3
    mixedMoment B raw7425step0 raw7425step0Labels = mixedMoment B raw7425step1 raw7425step1Labels := by
      have ha : raw7425step1 = raw7425step0 := by apply Matrix.ext; unfold raw7425step1 raw7425step0; decide +kernel
      have hl : raw7425step0Labels = labelEmbedding6 ∘ raw7425step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7425step0 raw7425step0Labels raw7425step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4999 node4999Labels := by rfl

theorem canonical7426 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7426 raw7426Labels = mixedMoment B node5138 node5138Labels := by
  calc
    mixedMoment B raw7426 raw7426Labels = mixedMoment B raw7426step0 raw7426step0Labels := by
      have ha : raw7426step0 = (fun i j => raw7426 (permutation178 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7426step0 raw7426; decide +kernel
      have hl : raw7426step0Labels = raw7426Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7426 raw7426Labels permutation178 permutation3
    mixedMoment B raw7426step0 raw7426step0Labels = mixedMoment B raw7426step1 raw7426step1Labels := by
      have ha : raw7426step1 = raw7426step0 := by apply Matrix.ext; unfold raw7426step1 raw7426step0; decide +kernel
      have hl : raw7426step0Labels = labelEmbedding6 ∘ raw7426step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7426step0 raw7426step0Labels raw7426step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5138 node5138Labels := by rfl

theorem canonical7427 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7427 raw7427Labels = mixedMoment B node5260 node5260Labels := by
  calc
    mixedMoment B raw7427 raw7427Labels = mixedMoment B raw7427step0 raw7427step0Labels := by
      have hz : ∀ j, raw7427 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw7427step0 = (fun i j => raw7427 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw7427step0 raw7427; decide +kernel
      have hl : raw7427step0Labels = raw7427Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7427 raw7427Labels permutation520 hz
    mixedMoment B raw7427step0 raw7427step0Labels = mixedMoment B raw7427step1 raw7427step1Labels := by
      have ha : raw7427step1 = (fun i j => raw7427step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7427step1 raw7427step0; decide +kernel
      have hl : raw7427step1Labels = raw7427step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7427step0 raw7427step0Labels permutation32 permutation3
    mixedMoment B raw7427step1 raw7427step1Labels = mixedMoment B raw7427step2 raw7427step2Labels := by
      have ha : raw7427step2 = raw7427step1 := by apply Matrix.ext; unfold raw7427step2 raw7427step1; decide +kernel
      have hl : raw7427step1Labels = labelEmbedding6 ∘ raw7427step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7427step1 raw7427step1Labels raw7427step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5260 node5260Labels := by rfl

theorem canonical7428 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7428 raw7428Labels = mixedMoment B node5255 node5255Labels := by
  calc
    mixedMoment B raw7428 raw7428Labels = mixedMoment B raw7428step0 raw7428step0Labels := by
      have ha : raw7428step0 = (fun i j => raw7428 (permutation157 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7428step0 raw7428; decide +kernel
      have hl : raw7428step0Labels = raw7428Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7428 raw7428Labels permutation157 permutation3
    mixedMoment B raw7428step0 raw7428step0Labels = mixedMoment B raw7428step1 raw7428step1Labels := by
      have ha : raw7428step1 = raw7428step0 := by apply Matrix.ext; unfold raw7428step1 raw7428step0; decide +kernel
      have hl : raw7428step0Labels = labelEmbedding6 ∘ raw7428step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7428step0 raw7428step0Labels raw7428step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5255 node5255Labels := by rfl

theorem canonical7429 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7429 raw7429Labels = mixedMoment B node4392 node4392Labels := by
  calc
    mixedMoment B raw7429 raw7429Labels = mixedMoment B raw7429step0 raw7429step0Labels := by
      have ha : raw7429step0 = (fun i j => raw7429 (permutation153 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7429step0 raw7429; decide +kernel
      have hl : raw7429step0Labels = raw7429Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7429 raw7429Labels permutation153 permutation3
    mixedMoment B raw7429step0 raw7429step0Labels = mixedMoment B raw7429step1 raw7429step1Labels := by
      have ha : raw7429step1 = raw7429step0 := by apply Matrix.ext; unfold raw7429step1 raw7429step0; decide +kernel
      have hl : raw7429step0Labels = labelEmbedding6 ∘ raw7429step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7429step0 raw7429step0Labels raw7429step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4392 node4392Labels := by rfl

theorem canonical7430 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7430 raw7430Labels = mixedMoment B node4993 node4993Labels := by
  calc
    mixedMoment B raw7430 raw7430Labels = mixedMoment B raw7430step0 raw7430step0Labels := by
      have ha : raw7430step0 = (fun i j => raw7430 (permutation153 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7430step0 raw7430; decide +kernel
      have hl : raw7430step0Labels = raw7430Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7430 raw7430Labels permutation153 permutation3
    mixedMoment B raw7430step0 raw7430step0Labels = mixedMoment B raw7430step1 raw7430step1Labels := by
      have ha : raw7430step1 = raw7430step0 := by apply Matrix.ext; unfold raw7430step1 raw7430step0; decide +kernel
      have hl : raw7430step0Labels = labelEmbedding6 ∘ raw7430step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7430step0 raw7430step0Labels raw7430step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4993 node4993Labels := by rfl

theorem canonical7431 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7431 raw7431Labels = mixedMoment B node5129 node5129Labels := by
  calc
    mixedMoment B raw7431 raw7431Labels = mixedMoment B raw7431step0 raw7431step0Labels := by
      have ha : raw7431step0 = (fun i j => raw7431 (permutation177 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7431step0 raw7431; decide +kernel
      have hl : raw7431step0Labels = raw7431Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7431 raw7431Labels permutation177 permutation3
    mixedMoment B raw7431step0 raw7431step0Labels = mixedMoment B raw7431step1 raw7431step1Labels := by
      have ha : raw7431step1 = raw7431step0 := by apply Matrix.ext; unfold raw7431step1 raw7431step0; decide +kernel
      have hl : raw7431step0Labels = labelEmbedding6 ∘ raw7431step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7431step0 raw7431step0Labels raw7431step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5129 node5129Labels := by rfl

theorem canonical7432 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7432 raw7432Labels = mixedMoment B node5129 node5129Labels := by
  calc
    mixedMoment B raw7432 raw7432Labels = mixedMoment B raw7432step0 raw7432step0Labels := by
      have ha : raw7432step0 = (fun i j => raw7432 (permutation201 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7432step0 raw7432; decide +kernel
      have hl : raw7432step0Labels = raw7432Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7432 raw7432Labels permutation201 permutation3
    mixedMoment B raw7432step0 raw7432step0Labels = mixedMoment B raw7432step1 raw7432step1Labels := by
      have ha : raw7432step1 = raw7432step0 := by apply Matrix.ext; unfold raw7432step1 raw7432step0; decide +kernel
      have hl : raw7432step0Labels = labelEmbedding6 ∘ raw7432step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7432step0 raw7432step0Labels raw7432step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5129 node5129Labels := by rfl

theorem canonical7433 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7433 raw7433Labels = mixedMoment B node5249 node5249Labels := by
  calc
    mixedMoment B raw7433 raw7433Labels = mixedMoment B raw7433step0 raw7433step0Labels := by
      have ha : raw7433step0 = (fun i j => raw7433 (permutation153 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7433step0 raw7433; decide +kernel
      have hl : raw7433step0Labels = raw7433Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7433 raw7433Labels permutation153 permutation3
    mixedMoment B raw7433step0 raw7433step0Labels = mixedMoment B raw7433step1 raw7433step1Labels := by
      have ha : raw7433step1 = raw7433step0 := by apply Matrix.ext; unfold raw7433step1 raw7433step0; decide +kernel
      have hl : raw7433step0Labels = labelEmbedding6 ∘ raw7433step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7433step0 raw7433step0Labels raw7433step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5249 node5249Labels := by rfl

theorem canonical7434 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7434 raw7434Labels = mixedMoment B node4391 node4391Labels := by
  calc
    mixedMoment B raw7434 raw7434Labels = mixedMoment B raw7434step0 raw7434step0Labels := by
      have ha : raw7434step0 = (fun i j => raw7434 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7434step0 raw7434; decide +kernel
      have hl : raw7434step0Labels = raw7434Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7434 raw7434Labels permutation152 permutation3
    mixedMoment B raw7434step0 raw7434step0Labels = mixedMoment B raw7434step1 raw7434step1Labels := by
      have ha : raw7434step1 = raw7434step0 := by apply Matrix.ext; unfold raw7434step1 raw7434step0; decide +kernel
      have hl : raw7434step0Labels = labelEmbedding6 ∘ raw7434step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7434step0 raw7434step0Labels raw7434step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4391 node4391Labels := by rfl

theorem canonical7435 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7435 raw7435Labels = mixedMoment B node4992 node4992Labels := by
  calc
    mixedMoment B raw7435 raw7435Labels = mixedMoment B raw7435step0 raw7435step0Labels := by
      have ha : raw7435step0 = (fun i j => raw7435 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7435step0 raw7435; decide +kernel
      have hl : raw7435step0Labels = raw7435Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7435 raw7435Labels permutation152 permutation3
    mixedMoment B raw7435step0 raw7435step0Labels = mixedMoment B raw7435step1 raw7435step1Labels := by
      have ha : raw7435step1 = raw7435step0 := by apply Matrix.ext; unfold raw7435step1 raw7435step0; decide +kernel
      have hl : raw7435step0Labels = labelEmbedding6 ∘ raw7435step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7435step0 raw7435step0Labels raw7435step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4992 node4992Labels := by rfl

theorem canonical7436 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7436 raw7436Labels = mixedMoment B node5128 node5128Labels := by
  calc
    mixedMoment B raw7436 raw7436Labels = mixedMoment B raw7436step0 raw7436step0Labels := by
      have ha : raw7436step0 = (fun i j => raw7436 (permutation676 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7436step0 raw7436; decide +kernel
      have hl : raw7436step0Labels = raw7436Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7436 raw7436Labels permutation676 permutation2
    mixedMoment B raw7436step0 raw7436step0Labels = mixedMoment B raw7436step1 raw7436step1Labels := by
      have ha : raw7436step1 = -raw7436step0 := by apply Matrix.ext; change ∀ i j, raw7436step1 i j = -(raw7436step0 i j); unfold raw7436step1 raw7436step0; decide +kernel
      have hl : raw7436step1Labels = raw7436step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5128 node5128Labels := by rfl

theorem canonical7437 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7437 raw7437Labels = mixedMoment B node5128 node5128Labels := by
  calc
    mixedMoment B raw7437 raw7437Labels = mixedMoment B raw7437step0 raw7437step0Labels := by
      have ha : raw7437step0 = (fun i j => raw7437 (permutation674 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7437step0 raw7437; decide +kernel
      have hl : raw7437step0Labels = raw7437Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7437 raw7437Labels permutation674 permutation2
    mixedMoment B raw7437step0 raw7437step0Labels = mixedMoment B raw7437step1 raw7437step1Labels := by
      have ha : raw7437step1 = -raw7437step0 := by apply Matrix.ext; change ∀ i j, raw7437step1 i j = -(raw7437step0 i j); unfold raw7437step1 raw7437step0; decide +kernel
      have hl : raw7437step1Labels = raw7437step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5128 node5128Labels := by rfl

theorem canonical7438 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7438 raw7438Labels = mixedMoment B node5252 node5252Labels := by
  calc
    mixedMoment B raw7438 raw7438Labels = mixedMoment B raw7438step0 raw7438step0Labels := by
      have hz : ∀ j, raw7438 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw7438step0 = (fun i j => raw7438 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw7438step0 raw7438; decide +kernel
      have hl : raw7438step0Labels = raw7438Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7438 raw7438Labels permutation520 hz
    mixedMoment B raw7438step0 raw7438step0Labels = mixedMoment B raw7438step1 raw7438step1Labels := by
      have ha : raw7438step1 = (fun i j => raw7438step0 (permutation137 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7438step1 raw7438step0; decide +kernel
      have hl : raw7438step1Labels = raw7438step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7438step0 raw7438step0Labels permutation137 permutation2
    mixedMoment B raw7438step1 raw7438step1Labels = mixedMoment B raw7438step2 raw7438step2Labels := by
      have ha : raw7438step2 = -raw7438step1 := by apply Matrix.ext; change ∀ i j, raw7438step2 i j = -(raw7438step1 i j); unfold raw7438step2 raw7438step1; decide +kernel
      have hl : raw7438step2Labels = raw7438step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5252 node5252Labels := by rfl

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

theorem singleton5149 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5149 node5149Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2924 node2924Labels + mixedMoment B node3605 node3605Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2175 singletonSmall5149
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5149) = raw2175Labels := by decide +kernel
  rw [hl, canonical2175 B hB] at h
  have hc0 : mixedMoment B raw2175 (Fin.cases (0 : Fin 2) singletonSmall5149) =
      mixedMoment B node2924 node2924Labels := by
    have ha : raw2175 = raw2176 := by apply Matrix.ext; unfold raw2175 raw2176; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5149 = raw2176Labels := by decide +kernel
    rw [ha, hj, canonical2176 B hB]
  have hc1 : mixedMoment B raw2175 (Fin.cases (1 : Fin 2) singletonSmall5149) =
      mixedMoment B node3605 node3605Labels := by
    have ha : raw2175 = raw2177 := by apply Matrix.ext; unfold raw2175 raw2177; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5149 = raw2177Labels := by decide +kernel
    rw [ha, hj, canonical2177 B hB]
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

theorem singleton5284 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5284 node5284Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3077 node3077Labels + mixedMoment B node3625 node3625Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2289 singletonSmall5284
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5284) = raw2289Labels := by decide +kernel
  rw [hl, canonical2289 B hB] at h
  have hc0 : mixedMoment B raw2289 (Fin.cases (0 : Fin 2) singletonSmall5284) =
      mixedMoment B node3077 node3077Labels := by
    have ha : raw2289 = raw2290 := by apply Matrix.ext; unfold raw2289 raw2290; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5284 = raw2290Labels := by decide +kernel
    rw [ha, hj, canonical2290 B hB]
  have hc1 : mixedMoment B raw2289 (Fin.cases (1 : Fin 2) singletonSmall5284) =
      mixedMoment B node3625 node3625Labels := by
    have ha : raw2289 = raw2291 := by apply Matrix.ext; unfold raw2289 raw2291; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5284 = raw2291Labels := by decide +kernel
    rw [ha, hj, canonical2291 B hB]
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

theorem zero5481 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node5481 node5481Labels = 0 := by
  exact mixedMoment_alpha B hF node5481 node5481Labels 2 permutation158
    (by decide +kernel)

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound45
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound2924 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2924 node2924Labels = Sparse.eval nodeValue2924 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2924) = mixedMoment B node2924 node2924Labels := rfl
  simpa [nodeValue2924, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound48
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound3077 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3077 node3077Labels = Sparse.eval nodeValue3077 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3077) = mixedMoment B node3077 node3077Labels := rfl
  simpa [nodeValue3077, Sparse.eval] using hc.symm

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

theorem sound3605 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3605 node3605Labels = Sparse.eval nodeValue3605 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3605) = mixedMoment B node3605 node3605Labels := rfl
  simpa [nodeValue3605, Sparse.eval] using hc.symm

theorem sound3625 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3625 node3625Labels = Sparse.eval nodeValue3625 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3625) = mixedMoment B node3625 node3625Labels := rfl
  simpa [nodeValue3625, Sparse.eval] using hc.symm

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

theorem sound4391 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4391 node4391Labels = Sparse.eval nodeValue4391 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4391) = mixedMoment B node4391 node4391Labels := rfl
  simpa [nodeValue4391, Sparse.eval] using hc.symm

theorem sound4392 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4392 node4392Labels = Sparse.eval nodeValue4392 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4392) = mixedMoment B node4392 node4392Labels := rfl
  simpa [nodeValue4392, Sparse.eval] using hc.symm

theorem sound4400 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4400 node4400Labels = Sparse.eval nodeValue4400 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4400) = mixedMoment B node4400 node4400Labels := rfl
  simpa [nodeValue4400, Sparse.eval] using hc.symm

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

theorem sound4439 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4439 node4439Labels = Sparse.eval nodeValue4439 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4439) = mixedMoment B node4439 node4439Labels := rfl
  simpa [nodeValue4439, Sparse.eval] using hc.symm

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

theorem sound4992 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4992 node4992Labels = Sparse.eval nodeValue4992 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4992) = mixedMoment B node4992 node4992Labels := rfl
  simpa [nodeValue4992, Sparse.eval] using hc.symm

theorem sound4993 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4993 node4993Labels = Sparse.eval nodeValue4993 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4993) = mixedMoment B node4993 node4993Labels := rfl
  simpa [nodeValue4993, Sparse.eval] using hc.symm

theorem sound4999 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4999 node4999Labels = Sparse.eval nodeValue4999 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4999) = mixedMoment B node4999 node4999Labels := rfl
  simpa [nodeValue4999, Sparse.eval] using hc.symm

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

theorem sound5129 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5129 node5129Labels = Sparse.eval nodeValue5129 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5129) = mixedMoment B node5129 node5129Labels := rfl
  simpa [nodeValue5129, Sparse.eval] using hc.symm

theorem sound5138 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5138 node5138Labels = Sparse.eval nodeValue5138 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5138) = mixedMoment B node5138 node5138Labels := rfl
  simpa [nodeValue5138, Sparse.eval] using hc.symm

theorem sound5149 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5149 node5149Labels = Sparse.eval nodeValue5149 (mixedVector B) := by
  have h := singleton5149 B _hB
  rw [sound2924 B _hB _hF, sound3605 B _hB _hF] at h
  norm_num [nodeValue5149, nodeValue2924, nodeValue3605, Sparse.eval] at h ⊢
  linarith only [h]

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

theorem sound5249 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5249 node5249Labels = Sparse.eval nodeValue5249 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5249) = mixedMoment B node5249 node5249Labels := rfl
  simpa [nodeValue5249, Sparse.eval] using hc.symm

theorem sound5252 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5252 node5252Labels = Sparse.eval nodeValue5252 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5252) = mixedMoment B node5252 node5252Labels := rfl
  simpa [nodeValue5252, Sparse.eval] using hc.symm

theorem sound5255 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5255 node5255Labels = Sparse.eval nodeValue5255 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5255) = mixedMoment B node5255 node5255Labels := rfl
  simpa [nodeValue5255, Sparse.eval] using hc.symm

theorem sound5260 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5260 node5260Labels = Sparse.eval nodeValue5260 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5260) = mixedMoment B node5260 node5260Labels := rfl
  simpa [nodeValue5260, Sparse.eval] using hc.symm

theorem sound5281 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5281 node5281Labels = Sparse.eval nodeValue5281 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5281) = mixedMoment B node5281 node5281Labels := rfl
  simpa [nodeValue5281, Sparse.eval] using hc.symm

theorem sound5284 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5284 node5284Labels = Sparse.eval nodeValue5284 (mixedVector B) := by
  have h := singleton5284 B _hB
  rw [sound3077 B _hB _hF, sound3625 B _hB _hF] at h
  norm_num [nodeValue5284, nodeValue3077, nodeValue3625, Sparse.eval] at h ⊢
  linarith only [h]

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

theorem sound5424 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5424 node5424Labels = Sparse.eval nodeValue5424 (mixedVector B) := by
  have h := singleton5424 B _hB
  rw [sound3838 B _hB _hF, sound3843 B _hB _hF] at h
  norm_num [nodeValue5424, nodeValue3838, nodeValue3843, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5429 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5429 node5429Labels = Sparse.eval nodeValue5429 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5429) = mixedMoment B node5429 node5429Labels := rfl
  simpa [nodeValue5429, Sparse.eval] using hc.symm

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

theorem sound5481 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5481 node5481Labels = Sparse.eval nodeValue5481 (mixedVector B) := by
  simpa only [nodeValue5481, Sparse.eval_nil] using zero5481 B _hB _hF

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources12
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sourceEq389 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm389 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA389 + difference 0 1) (sourceB389 + difference 1 0) sourceC389) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5429) := by
    have ha : (tripleCharges (sourceA389 + difference 0 1) (sourceB389 + difference 1 0) sourceC389) = raw7409 := by
      apply Matrix.ext; unfold tripleCharges sourceA389 sourceB389 sourceC389 difference raw7409; decide +kernel
    rw [ha]
    exact (canonical7409 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA389 + difference 0 2) (sourceB389 + difference 2 0) sourceC389) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5424) := by
    have ha : (tripleCharges (sourceA389 + difference 0 2) (sourceB389 + difference 2 0) sourceC389) = raw7410 := by
      apply Matrix.ext; unfold tripleCharges sourceA389 sourceB389 sourceC389 difference raw7410; decide +kernel
    rw [ha]
    exact (canonical7410 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA389 + difference 0 3) (sourceB389 + difference 3 0) sourceC389) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5424) := by
    have ha : (tripleCharges (sourceA389 + difference 0 3) (sourceB389 + difference 3 0) sourceC389) = raw7411 := by
      apply Matrix.ext; unfold tripleCharges sourceA389 sourceB389 sourceC389 difference raw7411; decide +kernel
    rw [ha]
    exact (canonical7411 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA389 + difference 0 4) (sourceB389 + difference 4 0) sourceC389) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5439) := by
    have ha : (tripleCharges (sourceA389 + difference 0 4) (sourceB389 + difference 4 0) sourceC389) = raw7412 := by
      apply Matrix.ext; unfold tripleCharges sourceA389 sourceB389 sourceC389 difference raw7412; decide +kernel
    rw [ha]
    exact (canonical7412 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA389 + difference 0 5) (sourceB389 + difference 5 0) sourceC389) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5481) := by
    have ha : (tripleCharges (sourceA389 + difference 0 5) (sourceB389 + difference 5 0) sourceC389) = raw7413 := by
      apply Matrix.ext; unfold tripleCharges sourceA389 sourceB389 sourceC389 difference raw7413; decide +kernel
    rw [ha]
    exact (canonical7413 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA389 + difference 1 0) (sourceB389 + difference 0 1) sourceC389) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4439) := by
    have ha : (tripleCharges (sourceA389 + difference 1 0) (sourceB389 + difference 0 1) sourceC389) = raw7414 := by
      apply Matrix.ext; unfold tripleCharges sourceA389 sourceB389 sourceC389 difference raw7414; decide +kernel
    rw [ha]
    exact (canonical7414 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA389 + difference 1 2) (sourceB389 + difference 2 1) sourceC389) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5149) := by
    have ha : (tripleCharges (sourceA389 + difference 1 2) (sourceB389 + difference 2 1) sourceC389) = raw7415 := by
      apply Matrix.ext; unfold tripleCharges sourceA389 sourceB389 sourceC389 difference raw7415; decide +kernel
    rw [ha]
    exact (canonical7415 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA389 + difference 1 3) (sourceB389 + difference 3 1) sourceC389) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5149) := by
    have ha : (tripleCharges (sourceA389 + difference 1 3) (sourceB389 + difference 3 1) sourceC389) = raw7416 := by
      apply Matrix.ext; unfold tripleCharges sourceA389 sourceB389 sourceC389 difference raw7416; decide +kernel
    rw [ha]
    exact (canonical7416 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA389 + difference 1 4) (sourceB389 + difference 4 1) sourceC389) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5284) := by
    have ha : (tripleCharges (sourceA389 + difference 1 4) (sourceB389 + difference 4 1) sourceC389) = raw7417 := by
      apply Matrix.ext; unfold tripleCharges sourceA389 sourceB389 sourceC389 difference raw7417; decide +kernel
    rw [ha]
    exact (canonical7417 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA389 + difference 1 5) (sourceB389 + difference 5 1) sourceC389) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5281) := by
    have ha : (tripleCharges (sourceA389 + difference 1 5) (sourceB389 + difference 5 1) sourceC389) = raw7418 := by
      apply Matrix.ext; unfold tripleCharges sourceA389 sourceB389 sourceC389 difference raw7418; decide +kernel
    rw [ha]
    exact (canonical7418 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA389 + difference 2 0) (sourceB389 + difference 0 2) sourceC389) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4400) := by
    have ha : (tripleCharges (sourceA389 + difference 2 0) (sourceB389 + difference 0 2) sourceC389) = raw7419 := by
      apply Matrix.ext; unfold tripleCharges sourceA389 sourceB389 sourceC389 difference raw7419; decide +kernel
    rw [ha]
    exact (canonical7419 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA389 + difference 2 1) (sourceB389 + difference 1 2) sourceC389) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4999) := by
    have ha : (tripleCharges (sourceA389 + difference 2 1) (sourceB389 + difference 1 2) sourceC389) = raw7420 := by
      apply Matrix.ext; unfold tripleCharges sourceA389 sourceB389 sourceC389 difference raw7420; decide +kernel
    rw [ha]
    exact (canonical7420 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA389 + difference 2 3) (sourceB389 + difference 3 2) sourceC389) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5138) := by
    have ha : (tripleCharges (sourceA389 + difference 2 3) (sourceB389 + difference 3 2) sourceC389) = raw7421 := by
      apply Matrix.ext; unfold tripleCharges sourceA389 sourceB389 sourceC389 difference raw7421; decide +kernel
    rw [ha]
    exact (canonical7421 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA389 + difference 2 4) (sourceB389 + difference 4 2) sourceC389) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5260) := by
    have ha : (tripleCharges (sourceA389 + difference 2 4) (sourceB389 + difference 4 2) sourceC389) = raw7422 := by
      apply Matrix.ext; unfold tripleCharges sourceA389 sourceB389 sourceC389 difference raw7422; decide +kernel
    rw [ha]
    exact (canonical7422 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA389 + difference 2 5) (sourceB389 + difference 5 2) sourceC389) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5255) := by
    have ha : (tripleCharges (sourceA389 + difference 2 5) (sourceB389 + difference 5 2) sourceC389) = raw7423 := by
      apply Matrix.ext; unfold tripleCharges sourceA389 sourceB389 sourceC389 difference raw7423; decide +kernel
    rw [ha]
    exact (canonical7423 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA389 + difference 3 0) (sourceB389 + difference 0 3) sourceC389) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4400) := by
    have ha : (tripleCharges (sourceA389 + difference 3 0) (sourceB389 + difference 0 3) sourceC389) = raw7424 := by
      apply Matrix.ext; unfold tripleCharges sourceA389 sourceB389 sourceC389 difference raw7424; decide +kernel
    rw [ha]
    exact (canonical7424 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA389 + difference 3 1) (sourceB389 + difference 1 3) sourceC389) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4999) := by
    have ha : (tripleCharges (sourceA389 + difference 3 1) (sourceB389 + difference 1 3) sourceC389) = raw7425 := by
      apply Matrix.ext; unfold tripleCharges sourceA389 sourceB389 sourceC389 difference raw7425; decide +kernel
    rw [ha]
    exact (canonical7425 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA389 + difference 3 2) (sourceB389 + difference 2 3) sourceC389) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5138) := by
    have ha : (tripleCharges (sourceA389 + difference 3 2) (sourceB389 + difference 2 3) sourceC389) = raw7426 := by
      apply Matrix.ext; unfold tripleCharges sourceA389 sourceB389 sourceC389 difference raw7426; decide +kernel
    rw [ha]
    exact (canonical7426 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA389 + difference 3 4) (sourceB389 + difference 4 3) sourceC389) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5260) := by
    have ha : (tripleCharges (sourceA389 + difference 3 4) (sourceB389 + difference 4 3) sourceC389) = raw7427 := by
      apply Matrix.ext; unfold tripleCharges sourceA389 sourceB389 sourceC389 difference raw7427; decide +kernel
    rw [ha]
    exact (canonical7427 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA389 + difference 3 5) (sourceB389 + difference 5 3) sourceC389) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5255) := by
    have ha : (tripleCharges (sourceA389 + difference 3 5) (sourceB389 + difference 5 3) sourceC389) = raw7428 := by
      apply Matrix.ext; unfold tripleCharges sourceA389 sourceB389 sourceC389 difference raw7428; decide +kernel
    rw [ha]
    exact (canonical7428 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA389 + difference 4 0) (sourceB389 + difference 0 4) sourceC389) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4392) := by
    have ha : (tripleCharges (sourceA389 + difference 4 0) (sourceB389 + difference 0 4) sourceC389) = raw7429 := by
      apply Matrix.ext; unfold tripleCharges sourceA389 sourceB389 sourceC389 difference raw7429; decide +kernel
    rw [ha]
    exact (canonical7429 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA389 + difference 4 1) (sourceB389 + difference 1 4) sourceC389) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4993) := by
    have ha : (tripleCharges (sourceA389 + difference 4 1) (sourceB389 + difference 1 4) sourceC389) = raw7430 := by
      apply Matrix.ext; unfold tripleCharges sourceA389 sourceB389 sourceC389 difference raw7430; decide +kernel
    rw [ha]
    exact (canonical7430 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA389 + difference 4 2) (sourceB389 + difference 2 4) sourceC389) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5129) := by
    have ha : (tripleCharges (sourceA389 + difference 4 2) (sourceB389 + difference 2 4) sourceC389) = raw7431 := by
      apply Matrix.ext; unfold tripleCharges sourceA389 sourceB389 sourceC389 difference raw7431; decide +kernel
    rw [ha]
    exact (canonical7431 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA389 + difference 4 3) (sourceB389 + difference 3 4) sourceC389) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5129) := by
    have ha : (tripleCharges (sourceA389 + difference 4 3) (sourceB389 + difference 3 4) sourceC389) = raw7432 := by
      apply Matrix.ext; unfold tripleCharges sourceA389 sourceB389 sourceC389 difference raw7432; decide +kernel
    rw [ha]
    exact (canonical7432 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA389 + difference 4 5) (sourceB389 + difference 5 4) sourceC389) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5249) := by
    have ha : (tripleCharges (sourceA389 + difference 4 5) (sourceB389 + difference 5 4) sourceC389) = raw7433 := by
      apply Matrix.ext; unfold tripleCharges sourceA389 sourceB389 sourceC389 difference raw7433; decide +kernel
    rw [ha]
    exact (canonical7433 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA389 + difference 5 0) (sourceB389 + difference 0 5) sourceC389) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4391) := by
    have ha : (tripleCharges (sourceA389 + difference 5 0) (sourceB389 + difference 0 5) sourceC389) = raw7434 := by
      apply Matrix.ext; unfold tripleCharges sourceA389 sourceB389 sourceC389 difference raw7434; decide +kernel
    rw [ha]
    exact (canonical7434 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA389 + difference 5 1) (sourceB389 + difference 1 5) sourceC389) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4992) := by
    have ha : (tripleCharges (sourceA389 + difference 5 1) (sourceB389 + difference 1 5) sourceC389) = raw7435 := by
      apply Matrix.ext; unfold tripleCharges sourceA389 sourceB389 sourceC389 difference raw7435; decide +kernel
    rw [ha]
    exact (canonical7435 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA389 + difference 5 2) (sourceB389 + difference 2 5) sourceC389) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5128) := by
    have ha : (tripleCharges (sourceA389 + difference 5 2) (sourceB389 + difference 2 5) sourceC389) = raw7436 := by
      apply Matrix.ext; unfold tripleCharges sourceA389 sourceB389 sourceC389 difference raw7436; decide +kernel
    rw [ha]
    exact (canonical7436 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA389 + difference 5 3) (sourceB389 + difference 3 5) sourceC389) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5128) := by
    have ha : (tripleCharges (sourceA389 + difference 5 3) (sourceB389 + difference 3 5) sourceC389) = raw7437 := by
      apply Matrix.ext; unfold tripleCharges sourceA389 sourceB389 sourceC389 difference raw7437; decide +kernel
    rw [ha]
    exact (canonical7437 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA389 + difference 5 4) (sourceB389 + difference 4 5) sourceC389) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5252) := by
    have ha : (tripleCharges (sourceA389 + difference 5 4) (sourceB389 + difference 4 5) sourceC389) = raw7438 := by
      apply Matrix.ext; unfold tripleCharges sourceA389 sourceB389 sourceC389 difference raw7438; decide +kernel
    rw [ha]
    exact (canonical7438 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA389 sourceB389 sourceC389
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm389, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic20
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reindexCheck326 : Integer.Sparse.reindex keyMap MixedData.row326 = numericRow326 := by decide +kernel

theorem numericCheck326 (x : Master → ℝ) : Integer.Sparse.eval numericRow326 x =
    (17280 : ℝ) * reducedSource326 x := by
  norm_num [numericRow326, reducedSource326, Integer.Sparse.eval, Sparse.eval, nodeValue4391, nodeValue4392, nodeValue4400, nodeValue4439, nodeValue4992, nodeValue4993, nodeValue4999, nodeValue5128, nodeValue5129, nodeValue5138, nodeValue5149, nodeValue5249, nodeValue5252, nodeValue5255, nodeValue5260, nodeValue5281, nodeValue5284, nodeValue5424, nodeValue5429, nodeValue5439, nodeValue5481]
  ring

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Rows20
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero326 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource326 (mixedVector B) = 0 := by
  have h4391 : mixedVector B (Sum.inr 4391) = Sparse.eval nodeValue4391 (mixedVector B) := by
    change mixedMoment B node4391 node4391Labels = _
    exact sound4391 B hB hF
  have h4392 : mixedVector B (Sum.inr 4392) = Sparse.eval nodeValue4392 (mixedVector B) := by
    change mixedMoment B node4392 node4392Labels = _
    exact sound4392 B hB hF
  have h4400 : mixedVector B (Sum.inr 4400) = Sparse.eval nodeValue4400 (mixedVector B) := by
    change mixedMoment B node4400 node4400Labels = _
    exact sound4400 B hB hF
  have h4439 : mixedVector B (Sum.inr 4439) = Sparse.eval nodeValue4439 (mixedVector B) := by
    change mixedMoment B node4439 node4439Labels = _
    exact sound4439 B hB hF
  have h4992 : mixedVector B (Sum.inr 4992) = Sparse.eval nodeValue4992 (mixedVector B) := by
    change mixedMoment B node4992 node4992Labels = _
    exact sound4992 B hB hF
  have h4993 : mixedVector B (Sum.inr 4993) = Sparse.eval nodeValue4993 (mixedVector B) := by
    change mixedMoment B node4993 node4993Labels = _
    exact sound4993 B hB hF
  have h4999 : mixedVector B (Sum.inr 4999) = Sparse.eval nodeValue4999 (mixedVector B) := by
    change mixedMoment B node4999 node4999Labels = _
    exact sound4999 B hB hF
  have h5128 : mixedVector B (Sum.inr 5128) = Sparse.eval nodeValue5128 (mixedVector B) := by
    change mixedMoment B node5128 node5128Labels = _
    exact sound5128 B hB hF
  have h5129 : mixedVector B (Sum.inr 5129) = Sparse.eval nodeValue5129 (mixedVector B) := by
    change mixedMoment B node5129 node5129Labels = _
    exact sound5129 B hB hF
  have h5138 : mixedVector B (Sum.inr 5138) = Sparse.eval nodeValue5138 (mixedVector B) := by
    change mixedMoment B node5138 node5138Labels = _
    exact sound5138 B hB hF
  have h5149 : mixedVector B (Sum.inr 5149) = Sparse.eval nodeValue5149 (mixedVector B) := by
    change mixedMoment B node5149 node5149Labels = _
    exact sound5149 B hB hF
  have h5249 : mixedVector B (Sum.inr 5249) = Sparse.eval nodeValue5249 (mixedVector B) := by
    change mixedMoment B node5249 node5249Labels = _
    exact sound5249 B hB hF
  have h5252 : mixedVector B (Sum.inr 5252) = Sparse.eval nodeValue5252 (mixedVector B) := by
    change mixedMoment B node5252 node5252Labels = _
    exact sound5252 B hB hF
  have h5255 : mixedVector B (Sum.inr 5255) = Sparse.eval nodeValue5255 (mixedVector B) := by
    change mixedMoment B node5255 node5255Labels = _
    exact sound5255 B hB hF
  have h5260 : mixedVector B (Sum.inr 5260) = Sparse.eval nodeValue5260 (mixedVector B) := by
    change mixedMoment B node5260 node5260Labels = _
    exact sound5260 B hB hF
  have h5281 : mixedVector B (Sum.inr 5281) = Sparse.eval nodeValue5281 (mixedVector B) := by
    change mixedMoment B node5281 node5281Labels = _
    exact sound5281 B hB hF
  have h5284 : mixedVector B (Sum.inr 5284) = Sparse.eval nodeValue5284 (mixedVector B) := by
    change mixedMoment B node5284 node5284Labels = _
    exact sound5284 B hB hF
  have h5424 : mixedVector B (Sum.inr 5424) = Sparse.eval nodeValue5424 (mixedVector B) := by
    change mixedMoment B node5424 node5424Labels = _
    exact sound5424 B hB hF
  have h5429 : mixedVector B (Sum.inr 5429) = Sparse.eval nodeValue5429 (mixedVector B) := by
    change mixedMoment B node5429 node5429Labels = _
    exact sound5429 B hB hF
  have h5439 : mixedVector B (Sum.inr 5439) = Sparse.eval nodeValue5439 (mixedVector B) := by
    change mixedMoment B node5439 node5439Labels = _
    exact sound5439_e B hB hF
  have h5481 : mixedVector B (Sum.inr 5481) = Sparse.eval nodeValue5481 (mixedVector B) := by
    change mixedMoment B node5481 node5481Labels = _
    exact sound5481 B hB hF
  simpa only [sourceForm389, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4391, h4392, h4400, h4439, h4992, h4993, h4999, h5128, h5129, h5138, h5149, h5249, h5252, h5255, h5260, h5281, h5284, h5424, h5429, h5439, h5481, reducedSource326] using sourceEq389 B hB

theorem rowSound326_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row326 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck326, numericCheck326, reducedZero326 B hB hF, mul_zero]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedSourceBridge.rowSound326_e_oai := @OAI.MUB6.Certificate.MixedSourceBridge.rowSound326_e_oai
