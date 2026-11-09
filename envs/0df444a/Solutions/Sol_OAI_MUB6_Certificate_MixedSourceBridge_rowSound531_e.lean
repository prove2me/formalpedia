-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedSourceBridge.rowSound531_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T01:56:16.758389+00:00
-- url     : https://prove2.me/submissions/076dfc75-8255-46b6-aa06-9a4762e20255

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E070
import Definitions.Def_OAIQ106E086
import Definitions.Def_OAIQ106E087
import Definitions.Def_OAIQ106E088
import Definitions.Def_OAIQ106E089
import Definitions.Def_OAIQ106E096
import Definitions.Def_OAIQ106E187
import Definitions.Def_OAIQ106E097
import Definitions.Def_OAIQ106E190
import Definitions.Def_OAIQ106E191
import Definitions.Def_OAIQ106E099
import Definitions.Def_OAIQ106E101
import Definitions.Def_OAIQ106E102
import Definitions.Def_OAIQ106E103
import Definitions.Def_OAIQ106E116
import Definitions.Def_OAIQ106E119
import Definitions.Def_OAIQ106E121
import Definitions.Def_OAIQ106E127
import Definitions.Def_OAIQ106E140
import Definitions.Def_OAIQ106E141
import Definitions.Def_OAIQ106E142
import Definitions.Def_OAIQ106E143
import Definitions.Def_OAIQ106E144
import Definitions.Def_OAIQ106E145
import Definitions.Def_OAIQ106E146
import Definitions.Def_OAIQ106E147
import Definitions.Def_OAIQ106E148
import Definitions.Def_OAIQ106E170
import Definitions.Def_OAIQ106E171
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound5492_e

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

theorem IsHadamard.transpose {H : CMatrix} (hH : IsHadamard H) :
    IsHadamard H.transpose := by
  refine ⟨fun i j => hH.1 j i, ?_⟩
  ext i j
  simpa [Matrix.mul_apply, Matrix.one_apply, mul_comm, eq_comm] using
    hH.row_orthogonal j i

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

theorem transition_reverse (b c : Basis) :
    transition c b = (transition b c).conjTranspose := by
  ext i j
  simp [transition, Matrix.conjTranspose_apply]

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

theorem average_prod (f : ι × κ → ℝ) :
    average f = average (fun i => average (fun k => f (i, k))) := by
  simp only [average, Fintype.card_prod, Nat.cast_mul, mul_inv_rev,
    Fintype.sum_prod_type, ← Finset.mul_sum]
  ring

theorem average_comm (f : ι → κ → ℝ) :
    average (fun i => average (fun k => f i k)) =
      average (fun k => average (fun i => f i k)) := by
  simp only [average, ← Finset.mul_sum]
  rw [Finset.sum_comm]
  ring

theorem sum_eq_card_mul_average (f : ι → ℝ) :
    (∑ i, f i) = (Fintype.card ι : ℝ) * average f := by
  classical
  by_cases hc : Fintype.card ι = 0
  · have : IsEmpty ι := Fintype.card_eq_zero_iff.mp hc
    simp [average]
  · have hcr : (Fintype.card ι : ℝ) ≠ 0 := by exact_mod_cast hc
    simp only [average, ← mul_assoc, mul_inv_cancel₀ hcr, one_mul]

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Moments_MomentSymmetry
attribute [-simp] _root_.OAI.MUB6.embedCharge_apply _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero _root_.OAI.MUB6.offDiagSum_zero _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators ComplexConjugate

namespace MUB6

theorem injectiveMoment_iterated {p q : ℕ} (H : CMatrix)
    (A : Matrix (Fin p) (Fin q) ℤ) :
    injectiveMoment H A = average (fun ρ : Fin p ↪ Coord =>
      average (fun κ : Fin q ↪ Coord =>
        ((exponentMonomial H A ρ κ).re +
          (exponentMonomial H.transpose A ρ κ).re) / 2)) :=
  average_prod _

theorem injectiveMoment_reverse_iterated {p q : ℕ} (H : CMatrix)
    (A : Matrix (Fin p) (Fin q) ℤ) :
    (average (fun κ : Fin q ↪ Coord => average (fun ρ : Fin p ↪ Coord =>
      ((exponentMonomial H A ρ κ).re +
        (exponentMonomial H.transpose A ρ κ).re) / 2))) = injectiveMoment H A := by
  rw [average_comm]
  exact (injectiveMoment_iterated H A).symm

theorem exponentMonomial_transpose {p q : ℕ} (H : CMatrix)
    (A : Matrix (Fin p) (Fin q) ℤ) (ρ : Fin p ↪ Coord) (κ : Fin q ↪ Coord) :
    exponentMonomial H A.transpose κ ρ = exponentMonomial H.transpose A ρ κ := by
  exact Finset.prod_comm

theorem injectiveMoment_transpose {p q : ℕ} (H : CMatrix)
    (A : Matrix (Fin p) (Fin q) ℤ) :
    injectiveMoment H A.transpose = injectiveMoment H A := by
  rw [injectiveMoment_iterated, injectiveMoment_iterated, average_comm]
  apply average_congr
  intro ρ
  apply average_congr
  intro κ
  rw [exponentMonomial_transpose, exponentMonomial_transpose]
  simp only [Matrix.transpose_transpose, add_comm]

theorem exponentMonomial_neg {p q : ℕ} (H : CMatrix)
    (hH : ∀ i j, Complex.normSq (H i j) = 1)
    (A : Matrix (Fin p) (Fin q) ℤ) (ρ : Fin p ↪ Coord) (κ : Fin q ↪ Coord) :
    exponentMonomial H (-A) ρ κ = conj (exponentMonomial H A ρ κ) := by
  simp only [exponentMonomial, Matrix.neg_apply, zpow_neg, map_prod, map_zpow₀]
  apply Finset.prod_congr rfl
  intro u _
  apply Finset.prod_congr rfl
  intro v _
  rw [← unit_inv_eq_conj (hH (ρ u) (κ v)), inv_zpow]

theorem injectiveMoment_neg {p q : ℕ} {H : CMatrix} (hH : IsHadamard H)
    (A : Matrix (Fin p) (Fin q) ℤ) : injectiveMoment H (-A) = injectiveMoment H A := by
  apply average_congr
  intro s
  rw [exponentMonomial_neg H hH.1, exponentMonomial_neg H.transpose hH.transpose.1]
  simp

theorem exponentMonomial_row_permutation {p q : ℕ} (H : CMatrix)
    (A : Matrix (Fin p) (Fin q) ℤ) (σ : Equiv.Perm (Fin p))
    (ρ : Fin p ↪ Coord) (κ : Fin q ↪ Coord) :
    exponentMonomial H (fun i j => A (σ i) j) ρ κ =
      exponentMonomial H A (Equiv.embeddingCongr σ (Equiv.refl Coord) ρ) κ := by
  unfold exponentMonomial
  simpa only [Equiv.embeddingCongr_apply, Function.Embedding.congr_apply,
    Function.comp_apply, Function.Embedding.trans_apply, Equiv.toEmbedding_apply,
    Equiv.refl_apply, Equiv.symm_apply_apply] using
    Equiv.prod_comp σ (fun i => ∏ j, H (ρ (σ.symm i)) (κ j) ^ A i j)

theorem injectiveMoment_row_permutation {p q : ℕ} (H : CMatrix)
    (A : Matrix (Fin p) (Fin q) ℤ) (σ : Equiv.Perm (Fin p)) :
    injectiveMoment H (fun i j => A (σ i) j) = injectiveMoment H A := by
  rw [injectiveMoment_iterated H (fun i j => A (σ i) j), injectiveMoment_iterated H A]
  simp_rw [exponentMonomial_row_permutation H A σ,
    exponentMonomial_row_permutation H.transpose A σ]
  exact average_equiv (Equiv.embeddingCongr σ (Equiv.refl Coord))
    (fun ρ : Fin p ↪ Coord => average (fun κ : Fin q ↪ Coord =>
      ((exponentMonomial H A ρ κ).re +
        (exponentMonomial H.transpose A ρ κ).re) / 2))

theorem injectiveMoment_column_permutation {p q : ℕ} (H : CMatrix)
    (A : Matrix (Fin p) (Fin q) ℤ) (σ : Equiv.Perm (Fin q)) :
    injectiveMoment H (fun i j => A i (σ j)) = injectiveMoment H A := by
  rw [← injectiveMoment_transpose H (fun i j => A i (σ j))]
  change injectiveMoment H (fun i j => A.transpose (σ i) j) = _
  rw [injectiveMoment_row_permutation, injectiveMoment_transpose]

theorem exponentMonomial_zero_first_row {p q : ℕ} (H : CMatrix)
    (A : Matrix (Fin (p + 1)) (Fin q) ℤ) (hA : ∀ j, A 0 j = 0)
    (ρ : Fin (p + 1) ↪ Coord) (κ : Fin q ↪ Coord) :
    exponentMonomial H A ρ κ =
      exponentMonomial H (fun i j => A i.succ j) (Sampling.dropFirst ρ) κ := by
  simp only [exponentMonomial, Fin.prod_univ_succ, hA, zpow_zero,
    Finset.prod_const_one, one_mul]
  rfl

theorem injectiveMoment_zero_first_row {p q : ℕ} (hp : p < 6) (H : CMatrix)
    (A : Matrix (Fin (p + 1)) (Fin q) ℤ) (hA : ∀ j, A 0 j = 0) :
    injectiveMoment H A = injectiveMoment H (fun i j => A i.succ j) := by
  rw [injectiveMoment_iterated H A,
    injectiveMoment_iterated H (fun i j => A i.succ j)]
  simp_rw [exponentMonomial_zero_first_row H A hA,
    exponentMonomial_zero_first_row H.transpose A hA]
  exact Sampling.average_dropFirst hp
    (fun ρ : Fin p ↪ Coord => average (fun κ : Fin q ↪ Coord =>
      ((exponentMonomial H (fun i j => A i.succ j) ρ κ).re +
        (exponentMonomial H.transpose (fun i j => A i.succ j) ρ κ).re) / 2))

end MUB6

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Certificate_Canonical
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Small semantic steps used by the generated canonicalization traces. Each
step preserves the actual averaged injective moment. The finite side conditions
(state dimensions, permutation inverses, and zero entries) are checked separately.
-/
noncomputable section
namespace MUB6.Certificate

/-- Move a zero row to the front and delete it. -/
theorem moment_delete_zero_row {p q : ℕ} (hp : p < 6) (H : CMatrix)
    (A : Matrix (Fin (p + 1)) (Fin q) ℤ) (σ : Equiv.Perm (Fin (p + 1)))
    (hzero : ∀ j, A (σ 0) j = 0) :
    injectiveMoment H A = injectiveMoment H (fun i j => A (σ i.succ) j) := by
  calc
    injectiveMoment H A = injectiveMoment H (fun i j => A (σ i) j) :=
      (injectiveMoment_row_permutation H A σ).symm
    _ = injectiveMoment H (fun i j => A (σ i.succ) j) :=
      injectiveMoment_zero_first_row hp H _ hzero

/-- The column version uses the transpose symmetry already present in the
manuscript's normalization. -/
theorem moment_delete_zero_column {p q : ℕ} (hq : q < 6) (H : CMatrix)
    (A : Matrix (Fin p) (Fin (q + 1)) ℤ) (σ : Equiv.Perm (Fin (q + 1)))
    (hzero : ∀ i, A i (σ 0) = 0) :
    injectiveMoment H A = injectiveMoment H (fun i j => A i (σ j.succ)) := by
  calc
    injectiveMoment H A = injectiveMoment H A.transpose :=
      (injectiveMoment_transpose H A).symm
    _ = injectiveMoment H (fun i j => A.transpose (σ i.succ) j) :=
      moment_delete_zero_row hq H A.transpose σ hzero
    _ = injectiveMoment H (fun i j => A i (σ j.succ)) :=
      injectiveMoment_transpose H (fun i j => A i (σ j.succ))

/-- Simultaneous row and column relabeling. -/
theorem moment_permute {p q : ℕ} (H : CMatrix)
    (A : Matrix (Fin p) (Fin q) ℤ)
    (σ : Equiv.Perm (Fin p)) (τ : Equiv.Perm (Fin q)) :
    injectiveMoment H A = injectiveMoment H (fun i j => A (σ i) (τ j)) := by
  calc
    injectiveMoment H A = injectiveMoment H (fun i j => A (σ i) j) :=
      (injectiveMoment_row_permutation H A σ).symm
    _ = injectiveMoment H (fun i j => A (σ i) (τ j)) :=
      (injectiveMoment_column_permutation H (fun i j => A (σ i) j) τ).symm

end MUB6.Certificate

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Certificate_Interpretation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Reindexing and averaging preserve the interpretation of sparse forms.
These algebraic facts connect finite checked coefficients to actual moments. -/
namespace MUB6.Certificate

namespace Sparse

variable {ι κ Ω : Type*}

theorem eval_average [Fintype Ω] (v : Sparse ι) (x : Ω → ι → ℝ) :
    eval v (fun i => average (fun ω => x ω i)) =
      average (fun ω => eval v (x ω)) := by
  induction v with
  | nil => simp
  | cons p v ih =>
    simp only [eval_cons, average_add, average_mul, ih]

end Sparse

end MUB6.Certificate

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Moments_PartitionExpansion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators ComplexConjugate
attribute [local instance] Classical.propDecidable

namespace MUB6

theorem prod_zpow_eq_zpow_sum {ι : Type*} (s : Finset ι) (a : ι → ℤ)
    {z : ℂ} (hz : z ≠ 0) : (∏ i ∈ s, z ^ a i) = z ^ (∑ i ∈ s, a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi, ih, zpow_add₀ hz]

theorem product_grouped {n k : ℕ} (label : Fin n → Fin k)
    (x : Fin k → ℂ) (hx : ∀ b, x b ≠ 0) (a : Fin n → ℤ) :
    (∏ j, x (label j) ^ a j) = ∏ b, x b ^ (∑ j with label j = b, a j) := by
  rw [← Finset.prod_fiberwise Finset.univ label]
  apply Finset.prod_congr rfl
  intro b _
  rw [← prod_zpow_eq_zpow_sum _ a (hx b)]
  apply Finset.prod_congr rfl
  intro j hj
  rw [(Finset.mem_filter.mp hj).2]

theorem rawMonomial_grouped {p n k : ℕ} {H : CMatrix} (hH : IsHadamard H)
    (A : Matrix (Fin p) (Fin n) ℤ) (label : Fin n → Fin k)
    (ρ : Fin p ↪ Coord) (κ : Fin k ↪ Coord) :
    rawMonomial H A ρ (fun j => κ (label j)) =
      exponentMonomial H (groupedColumns A label) ρ κ := by
  unfold rawMonomial exponentMonomial groupedColumns
  apply Finset.prod_congr rfl
  intro i _
  exact product_grouped label (fun b => H (ρ i) (κ b))
    (fun b => unit_ne_zero (hH.1 _ _)) (fun j => A i j)

theorem rowFourier_product_expand {p n : ℕ} (H : CMatrix)
    (A : Matrix (Fin p) (Fin n) ℤ) (ρ : Fin p ↪ Coord) :
    (∏ j, rowFourier H ρ (fun i => A i j)) =
      (6 : ℂ)⁻¹ ^ n * ∑ κ : Fin n → Coord, rawMonomial H A ρ κ := by
  simp only [rowFourier, Finset.prod_mul_distrib, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin]
  rw [Fintype.prod_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro κ _
  exact Finset.prod_comm

/-- The unnormalized equality-partition identity. The factor `(6)_k` in
the manuscript is exactly the cardinality of the inner injection type. -/
theorem rowFourier_partition_expand {p n : ℕ} {P : Type*} [Fintype P]
    {H : CMatrix} (hH : IsHadamard H) (A : Matrix (Fin p) (Fin n) ℤ)
    (ρ : Fin p ↪ Coord) (F : EqualityPatterns.Family (Fin n) P)
    (cover : ∀ f : Fin n → Coord, ∃ s, ∀ i j,
      F.label s i = F.label s j ↔ f i = f j) :
    (∏ j, rowFourier H ρ (fun i => A i j)) =
      (6 : ℂ)⁻¹ ^ n * ∑ s, ∑ κ : Fin (F.blocks s) ↪ Coord,
        exponentMonomial H (groupedColumns A (F.label s)) ρ κ := by
  rw [rowFourier_product_expand]
  have hs := (F.assignmentsEquiv cover).sum_comp
    (fun κ : Fin n → Coord => rawMonomial H A ρ κ)
  change (∑ s : Σ s, Fin (F.blocks s) ↪ Coord,
    rawMonomial H A ρ (fun i => s.2 (F.label s.1 i))) = _ at hs
  rw [Fintype.sum_sigma] at hs
  rw [← hs]
  congr 1
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro κ _
  exact rawMonomial_grouped hH A (F.label s) ρ κ

end MUB6

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Moments_SmallPartitions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.EqualityPatterns

theorem pattern3_0 {B : Type*} (f : Fin 3 → B)
    (h10 : f 1 = f 0)
    (_h20 : f 2 = f 0)
    (h21 : f 2 = f 1)
    : ∀ i j, family3.label 0 i = family3.label 0 j ↔ f i = f j := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp_all [family3, label3, raw3, blocks3, eq_comm]

theorem pattern3_1 {B : Type*} (f : Fin 3 → B)
    (h10 : f 1 = f 0)
    (h20 : f 2 ≠ f 0)
    (_h21 : f 2 ≠ f 1)
    : ∀ i j, family3.label 1 i = family3.label 1 j ↔ f i = f j := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp_all [family3, label3, raw3, blocks3, eq_comm]

theorem pattern3_2 {B : Type*} (f : Fin 3 → B)
    (_h10 : f 1 ≠ f 0)
    (h20 : f 2 = f 0)
    (h21 : f 2 ≠ f 1)
    : ∀ i j, family3.label 2 i = family3.label 2 j ↔ f i = f j := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp_all [family3, label3, raw3, blocks3, eq_comm]

theorem pattern3_3 {B : Type*} (f : Fin 3 → B)
    (h10 : f 1 ≠ f 0)
    (_h20 : f 2 ≠ f 0)
    (h21 : f 2 = f 1)
    : ∀ i j, family3.label 3 i = family3.label 3 j ↔ f i = f j := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp_all [family3, label3, raw3, blocks3, eq_comm]

theorem pattern3_4 {B : Type*} (f : Fin 3 → B)
    (h10 : f 1 ≠ f 0)
    (h20 : f 2 ≠ f 0)
    (h21 : f 2 ≠ f 1)
    : ∀ i j, family3.label 4 i = family3.label 4 j ↔ f i = f j := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp_all [family3, label3, raw3, blocks3, eq_comm] <;> grind

theorem covers3 {B : Type*} (f : Fin 3 → B) :
    ∃ p, ∀ i j, (family3.label p i = family3.label p j ↔ f i = f j) := by
  classical
  by_cases h10 : f 1 = f 0
  ·
    by_cases h20 : f 2 = f 0
    ·
      refine ⟨0, ?_⟩
      apply pattern3_0 f <;> simp_all [eq_comm]
    ·
      refine ⟨1, ?_⟩
      apply pattern3_1 f <;> simp_all [eq_comm]
  ·
    by_cases h20 : f 2 = f 0
    ·
      refine ⟨2, ?_⟩
      apply pattern3_2 f <;> simp_all [eq_comm]
    ·
      by_cases h21 : f 2 = f 1
      ·
        refine ⟨3, ?_⟩
        apply pattern3_3 f <;> simp_all [eq_comm]
      ·
        refine ⟨4, ?_⟩
        apply pattern3_4 f <;> simp_all [eq_comm]

end MUB6.EqualityPatterns

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Moments_NormalizedPartitions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators ComplexConjugate
attribute [local instance] Classical.propDecidable

namespace MUB6

theorem inverse_six_pow_real (n : ℕ) :
    (6 : ℂ)⁻¹ ^ n = (((6 : ℝ)⁻¹ ^ n : ℝ) : ℂ) := by
  simp

theorem partition_integrand {p n : ℕ} {P : Type*} [Fintype P]
    {H : CMatrix} (hH : IsHadamard H) (A : Matrix (Fin p) (Fin n) ℤ)
    (ρ : Fin p ↪ Coord) (F : EqualityPatterns.Family (Fin n) P)
    (cover : ∀ f : Fin n → Coord, ∃ s, ∀ i j,
      F.label s i = F.label s j ↔ f i = f j) :
    ((∏ j, rowFourier H ρ (fun i => A i j)).re +
      (∏ j, rowFourier H.transpose ρ (fun i => A i j)).re) / 2 =
      (6 : ℝ)⁻¹ ^ n * ∑ s, ∑ κ : Fin (F.blocks s) ↪ Coord,
        ((exponentMonomial H (groupedColumns A (F.label s)) ρ κ).re +
          (exponentMonomial H.transpose (groupedColumns A (F.label s)) ρ κ).re) / 2 := by
  rw [rowFourier_partition_expand hH A ρ F cover,
    rowFourier_partition_expand hH.transpose A ρ F cover, inverse_six_pow_real]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
    sub_zero, Complex.re_sum, div_eq_mul_inv, ← Finset.sum_mul,
    Finset.sum_add_distrib]
  ring

theorem average_injection_sum {p q : ℕ} (H : CMatrix)
    (A : Matrix (Fin p) (Fin q) ℤ) :
    average (fun ρ : Fin p ↪ Coord => ∑ κ : Fin q ↪ Coord,
      ((exponentMonomial H A ρ κ).re +
        (exponentMonomial H.transpose A ρ κ).re) / 2) =
      (Fintype.card (Fin q ↪ Coord) : ℝ) * injectiveMoment H A := by
  have he (ρ : Fin p ↪ Coord) := sum_eq_card_mul_average
    (fun κ : Fin q ↪ Coord =>
      ((exponentMonomial H A ρ κ).re +
        (exponentMonomial H.transpose A ρ κ).re) / 2)
  simp_rw [he]
  rw [average_mul, ← injectiveMoment_iterated H A]

/-- The normalized equality-pattern expansion. For k blocks the coefficient
is `card (Fin k ↪ Fin 6) / 6^n`, exactly `(6)_k / 6^n` in the source. -/
theorem averagedRowProducts_partition {p n : ℕ} {P : Type*} [Fintype P]
    {H : CMatrix} (hH : IsHadamard H) (A : Matrix (Fin p) (Fin n) ℤ)
    (F : EqualityPatterns.Family (Fin n) P)
    (cover : ∀ f : Fin n → Coord, ∃ s, ∀ i j,
      F.label s i = F.label s j ↔ f i = f j) :
    averagedRowProducts H A =
      ∑ s, ((Fintype.card (Fin (F.blocks s) ↪ Coord) : ℝ) / 6 ^ n) *
        injectiveMoment H (groupedColumns A (F.label s)) := by
  unfold averagedRowProducts
  simp_rw [partition_integrand hH A _ F cover]
  rw [average_mul, average_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s _
  rw [average_injection_sum H (groupedColumns A (F.label s))]
  simp only [div_eq_mul_inv, inv_pow]
  ring

end MUB6

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Moments_OrderedPairs
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators ComplexConjugate

namespace MUB6

theorem familyAverage_add (B : Fin 7 → Basis) (F G : CMatrix → ℝ) :
    familyAverage B (fun H => F H + G H) = familyAverage B F + familyAverage B G := by
  simp only [familyAverage, average_add]

theorem familyAverage_mul (B : Fin 7 → Basis) (c : ℝ) (F : CMatrix → ℝ) :
    familyAverage B (fun H => c * F H) = c * familyAverage B F := by
  simp only [familyAverage, average_mul]

theorem relativeMatrix_reverse (B : Fin 7 → Basis) (p : Fin 7 × Coord) :
    relativeMatrix B (reversePair p).1 (reversePair p).2 =
      (relativeMatrix B p.1 p.2).conjTranspose := by
  simp only [relativeMatrix, reversePair, Fin.succAbove_succAbove_predAbove]
  exact transition_reverse _ _

theorem familyAverage_transpose (B : Fin 7 → Basis) (F : CMatrix → ℝ)
    (hF : ∀ H, F (fun i j => conj (H i j)) = F H) :
    familyAverage B (fun H => F H.transpose) = familyAverage B F := by
  change (average (fun r : Fin 7 => average (fun s : Coord => F ((relativeMatrix B r s).transpose)))) =
    average (fun r : Fin 7 => average (fun s : Coord => F (relativeMatrix B r s)))
  rw [← average_prod (fun p : Fin 7 × Coord => F ((relativeMatrix B p.1 p.2).transpose)),
    ← average_prod (fun p : Fin 7 × Coord => F (relativeMatrix B p.1 p.2))]
  have h (p : Fin 7 × Coord) :
      F ((relativeMatrix B p.1 p.2).transpose) =
        F (relativeMatrix B (reversePair p).1 (reversePair p).2) := by
    rw [relativeMatrix_reverse]
    exact (hF ((relativeMatrix B p.1 p.2).transpose)).symm
  simp_rw [h]
  exact average_equiv reversePairEquiv (fun p => F (relativeMatrix B p.1 p.2))

theorem rowFourier_conjugate {p : ℕ} (H : CMatrix) (ρ : Fin p ↪ Coord) (a : Fin p → ℤ) :
    rowFourier (fun i j => conj (H i j)) ρ a = conj (rowFourier H ρ a) := by
  simp only [rowFourier, map_mul, map_sum, map_prod, map_zpow₀, map_inv₀, map_ofNat]

theorem unorientedRowProducts_conjugate {p n : ℕ} (H : CMatrix)
    (A : Matrix (Fin p) (Fin n) ℤ) :
    unorientedRowProducts (fun i j => conj (H i j)) A = unorientedRowProducts H A := by
  apply average_congr
  intro ρ
  simp only [rowFourier_conjugate, ← map_prod, Complex.conj_re]

theorem averagedRowProducts_split {p n : ℕ} (H : CMatrix)
    (A : Matrix (Fin p) (Fin n) ℤ) :
    averagedRowProducts H A =
      (1 / 2 : ℝ) * unorientedRowProducts H A +
        (1 / 2 : ℝ) * unorientedRowProducts H.transpose A := by
  have h (ρ : Fin p ↪ Coord) :
      ((∏ j, rowFourier H ρ (fun i => A i j)).re +
        (∏ j, rowFourier H.transpose ρ (fun i => A i j)).re) / 2 =
      (1 / 2 : ℝ) * (∏ j, rowFourier H ρ (fun i => A i j)).re +
        (1 / 2 : ℝ) * (∏ j, rowFourier H.transpose ρ (fun i => A i j)).re := by ring
  simp only [averagedRowProducts, h, average_add, average_mul, unorientedRowProducts]

theorem familyAverage_averagedRowProducts {p n : ℕ} (B : Fin 7 → Basis)
    (A : Matrix (Fin p) (Fin n) ℤ) :
    familyAverage B (fun H => averagedRowProducts H A) =
      familyAverage B (fun H => unorientedRowProducts H A) := by
  simp only [averagedRowProducts_split, familyAverage_add, familyAverage_mul]
  rw [familyAverage_transpose B (fun H => unorientedRowProducts H A)
    (fun H => unorientedRowProducts_conjugate H A)]
  ring

theorem mixedMoment_single_label {p n : ℕ} (B : Fin 7 → Basis)
    (A : Matrix (Fin p) (Fin n) ℤ) :
    mixedMoment B A (fun _ => (0 : Fin 1)) =
      familyAverage B (fun H => unorientedRowProducts H A) := by
  apply average_congr
  intro r
  have h (ρ : Fin p ↪ Coord) :
      average (fun τ : Fin 1 ↪ Coord =>
        (mixedIntegrand B A (fun _ => (0 : Fin 1)) r ρ τ).re) =
      average (fun s : Coord => (∏ j, rowFourier (relativeMatrix B r s) ρ (fun i => A i j)).re) := by
    exact average_equiv singletonEmbeddingEquiv
      (fun s => (∏ j, rowFourier (relativeMatrix B r s) ρ (fun i => A i j)).re)
  simp_rw [h]
  exact average_comm _

/-- Single-label mixed moments expand into the manuscript's transpose-averaged
pair moments with the exact falling-factorial weights. -/
theorem mixedMoment_single_label_partition {p n : ℕ} {P : Type*} [Fintype P]
    (B : Fin 7 → Basis) (hB : IsMUBFamily B) (A : Matrix (Fin p) (Fin n) ℤ)
    (F : EqualityPatterns.Family (Fin n) P)
    (cover : ∀ f : Fin n → Coord, ∃ s, ∀ i j,
      F.label s i = F.label s j ↔ f i = f j) :
    mixedMoment B A (fun _ => (0 : Fin 1)) =
      ∑ s, ((Fintype.card (Fin (F.blocks s) ↪ Coord) : ℝ) / 6 ^ n) *
        familyPairMoment B (groupedColumns A (F.label s)) := by
  rw [mixedMoment_single_label, ← familyAverage_averagedRowProducts]
  unfold familyAverage
  simp_rw [averagedRowProducts_partition (relativeMatrix_isHadamard B hB _ _) A F cover,
    average_sum, average_mul]
  rfl

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

theorem canonical2013 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2013 raw2013Labels = mixedMoment B node5000 node5000Labels := by
  calc
    mixedMoment B raw2013 raw2013Labels = mixedMoment B raw2013step0 raw2013step0Labels := by
      have ha : raw2013step0 = (fun i j => raw2013 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2013step0 raw2013; decide +kernel
      have hl : raw2013step0Labels = raw2013Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2013 raw2013Labels permutation32 permutation4
    mixedMoment B raw2013step0 raw2013step0Labels = mixedMoment B raw2013step1 raw2013step1Labels := by
      have ha : raw2013step1 = raw2013step0 := by apply Matrix.ext; unfold raw2013step1 raw2013step0; decide +kernel
      have hl : raw2013step0Labels = labelEmbedding7 ∘ raw2013step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2013step0 raw2013step0Labels raw2013step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5000 node5000Labels := by rfl

theorem canonical2014 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2014 raw2014Labels = mixedMoment B node2385 node2385Labels := by
  calc
    mixedMoment B raw2014 raw2014Labels = mixedMoment B raw2014step0 raw2014step0Labels := by
      have ha : raw2014step0 = (fun i j => raw2014 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2014step0 raw2014; decide +kernel
      have hl : raw2014step0Labels = raw2014Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2014 raw2014Labels permutation32 permutation4
    _ = mixedMoment B node2385 node2385Labels := by rfl

theorem canonical2015 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2015 raw2015Labels = mixedMoment B node3353 node3353Labels := by
  calc
    mixedMoment B raw2015 raw2015Labels = mixedMoment B raw2015step0 raw2015step0Labels := by
      have ha : raw2015step0 = (fun i j => raw2015 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2015step0 raw2015; decide +kernel
      have hl : raw2015step0Labels = raw2015Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2015 raw2015Labels permutation32 permutation6
    mixedMoment B raw2015step0 raw2015step0Labels = mixedMoment B raw2015step1 raw2015step1Labels := by
      have ha : raw2015step1 = -raw2015step0 := by apply Matrix.ext; change ∀ i j, raw2015step1 i j = -(raw2015step0 i j); unfold raw2015step1 raw2015step0; decide +kernel
      have hl : raw2015step1Labels = raw2015step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2015step1 raw2015step1Labels = mixedMoment B raw2015step2 raw2015step2Labels := by
      have ha : raw2015step2 = raw2015step1 := by apply Matrix.ext; unfold raw2015step2 raw2015step1; decide +kernel
      have hl : raw2015step1Labels = labelEmbedding1 ∘ raw2015step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2015step1 raw2015step1Labels raw2015step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3353 node3353Labels := by rfl

theorem canonical2022 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2022 raw2022Labels = mixedMoment B node5014 node5014Labels := by
  calc
    mixedMoment B raw2022 raw2022Labels = mixedMoment B raw2022step0 raw2022step0Labels := by
      have ha : raw2022step0 = (fun i j => raw2022 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2022step0 raw2022; decide +kernel
      have hl : raw2022step0Labels = raw2022Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2022 raw2022Labels permutation32 permutation4
    mixedMoment B raw2022step0 raw2022step0Labels = mixedMoment B raw2022step1 raw2022step1Labels := by
      have ha : raw2022step1 = raw2022step0 := by apply Matrix.ext; unfold raw2022step1 raw2022step0; decide +kernel
      have hl : raw2022step0Labels = labelEmbedding7 ∘ raw2022step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2022step0 raw2022step0Labels raw2022step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5014 node5014Labels := by rfl

theorem canonical2023 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2023 raw2023Labels = mixedMoment B node2399 node2399Labels := by
  calc
    mixedMoment B raw2023 raw2023Labels = mixedMoment B raw2023step0 raw2023step0Labels := by
      have ha : raw2023step0 = (fun i j => raw2023 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2023step0 raw2023; decide +kernel
      have hl : raw2023step0Labels = raw2023Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2023 raw2023Labels permutation32 permutation4
    _ = mixedMoment B node2399 node2399Labels := by rfl

theorem canonical2024 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2024 raw2024Labels = mixedMoment B node2467 node2467Labels := by
  calc
    mixedMoment B raw2024 raw2024Labels = mixedMoment B raw2024step0 raw2024step0Labels := by
      have ha : raw2024step0 = (fun i j => raw2024 (permutation151 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2024step0 raw2024; decide +kernel
      have hl : raw2024step0Labels = raw2024Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2024 raw2024Labels permutation151 permutation6
    mixedMoment B raw2024step0 raw2024step0Labels = mixedMoment B raw2024step1 raw2024step1Labels := by
      have ha : raw2024step1 = raw2024step0 := by apply Matrix.ext; unfold raw2024step1 raw2024step0; decide +kernel
      have hl : raw2024step0Labels = labelEmbedding1 ∘ raw2024step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2024step0 raw2024step0Labels raw2024step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2467 node2467Labels := by rfl

theorem canonical2028 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2028 raw2028Labels = mixedMoment B node5018 node5018Labels := by
  calc
    mixedMoment B raw2028 raw2028Labels = mixedMoment B raw2028step0 raw2028step0Labels := by
      have ha : raw2028step0 = (fun i j => raw2028 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2028step0 raw2028; decide +kernel
      have hl : raw2028step0Labels = raw2028Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2028 raw2028Labels permutation32 permutation4
    mixedMoment B raw2028step0 raw2028step0Labels = mixedMoment B raw2028step1 raw2028step1Labels := by
      have ha : raw2028step1 = raw2028step0 := by apply Matrix.ext; unfold raw2028step1 raw2028step0; decide +kernel
      have hl : raw2028step0Labels = labelEmbedding7 ∘ raw2028step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2028step0 raw2028step0Labels raw2028step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5018 node5018Labels := by rfl

theorem canonical2029 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2029 raw2029Labels = mixedMoment B node2404 node2404Labels := by
  calc
    mixedMoment B raw2029 raw2029Labels = mixedMoment B raw2029step0 raw2029step0Labels := by
      have ha : raw2029step0 = (fun i j => raw2029 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2029step0 raw2029; decide +kernel
      have hl : raw2029step0Labels = raw2029Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2029 raw2029Labels permutation32 permutation4
    _ = mixedMoment B node2404 node2404Labels := by rfl

theorem canonical2030 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2030 raw2030Labels = mixedMoment B node3357 node3357Labels := by
  calc
    mixedMoment B raw2030 raw2030Labels = mixedMoment B raw2030step0 raw2030step0Labels := by
      have ha : raw2030step0 = (fun i j => raw2030 (permutation33 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2030step0 raw2030; decide +kernel
      have hl : raw2030step0Labels = raw2030Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2030 raw2030Labels permutation33 permutation6
    mixedMoment B raw2030step0 raw2030step0Labels = mixedMoment B raw2030step1 raw2030step1Labels := by
      have ha : raw2030step1 = -raw2030step0 := by apply Matrix.ext; change ∀ i j, raw2030step1 i j = -(raw2030step0 i j); unfold raw2030step1 raw2030step0; decide +kernel
      have hl : raw2030step1Labels = raw2030step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2030step1 raw2030step1Labels = mixedMoment B raw2030step2 raw2030step2Labels := by
      have ha : raw2030step2 = raw2030step1 := by apply Matrix.ext; unfold raw2030step2 raw2030step1; decide +kernel
      have hl : raw2030step1Labels = labelEmbedding1 ∘ raw2030step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2030step1 raw2030step1Labels raw2030step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3357 node3357Labels := by rfl

theorem canonical2031 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2031 raw2031Labels = mixedMoment B node5021 node5021Labels := by
  calc
    mixedMoment B raw2031 raw2031Labels = mixedMoment B raw2031step0 raw2031step0Labels := by
      have ha : raw2031step0 = (fun i j => raw2031 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2031step0 raw2031; decide +kernel
      have hl : raw2031step0Labels = raw2031Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2031 raw2031Labels permutation8 permutation4
    mixedMoment B raw2031step0 raw2031step0Labels = mixedMoment B raw2031step1 raw2031step1Labels := by
      have ha : raw2031step1 = raw2031step0 := by apply Matrix.ext; unfold raw2031step1 raw2031step0; decide +kernel
      have hl : raw2031step0Labels = labelEmbedding7 ∘ raw2031step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2031step0 raw2031step0Labels raw2031step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5021 node5021Labels := by rfl

theorem canonical2032 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2032 raw2032Labels = mixedMoment B node2407 node2407Labels := by
  calc
    mixedMoment B raw2032 raw2032Labels = mixedMoment B raw2032step0 raw2032step0Labels := by
      have ha : raw2032step0 = (fun i j => raw2032 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2032step0 raw2032; decide +kernel
      have hl : raw2032step0Labels = raw2032Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2032 raw2032Labels permutation8 permutation4
    _ = mixedMoment B node2407 node2407Labels := by rfl

theorem canonical2033 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2033 raw2033Labels = mixedMoment B node3360 node3360Labels := by
  calc
    mixedMoment B raw2033 raw2033Labels = mixedMoment B raw2033step0 raw2033step0Labels := by
      have ha : raw2033step0 = (fun i j => raw2033 (permutation31 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2033step0 raw2033; decide +kernel
      have hl : raw2033step0Labels = raw2033Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2033 raw2033Labels permutation31 permutation6
    mixedMoment B raw2033step0 raw2033step0Labels = mixedMoment B raw2033step1 raw2033step1Labels := by
      have ha : raw2033step1 = raw2033step0 := by apply Matrix.ext; unfold raw2033step1 raw2033step0; decide +kernel
      have hl : raw2033step0Labels = labelEmbedding1 ∘ raw2033step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2033step0 raw2033step0Labels raw2033step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3360 node3360Labels := by rfl

theorem canonical2034 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2034 raw2034Labels = mixedMoment B node5023 node5023Labels := by
  calc
    mixedMoment B raw2034 raw2034Labels = mixedMoment B raw2034step0 raw2034step0Labels := by
      have ha : raw2034step0 = (fun i j => raw2034 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2034step0 raw2034; decide +kernel
      have hl : raw2034step0Labels = raw2034Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2034 raw2034Labels permutation8 permutation4
    mixedMoment B raw2034step0 raw2034step0Labels = mixedMoment B raw2034step1 raw2034step1Labels := by
      have ha : raw2034step1 = raw2034step0 := by apply Matrix.ext; unfold raw2034step1 raw2034step0; decide +kernel
      have hl : raw2034step0Labels = labelEmbedding7 ∘ raw2034step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2034step0 raw2034step0Labels raw2034step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5023 node5023Labels := by rfl

theorem canonical2035 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2035 raw2035Labels = mixedMoment B node2410 node2410Labels := by
  calc
    mixedMoment B raw2035 raw2035Labels = mixedMoment B raw2035step0 raw2035step0Labels := by
      have ha : raw2035step0 = (fun i j => raw2035 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2035step0 raw2035; decide +kernel
      have hl : raw2035step0Labels = raw2035Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2035 raw2035Labels permutation8 permutation4
    _ = mixedMoment B node2410 node2410Labels := by rfl

theorem canonical2036 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2036 raw2036Labels = mixedMoment B node2410 node2410Labels := by
  calc
    mixedMoment B raw2036 raw2036Labels = mixedMoment B raw2036step0 raw2036step0Labels := by
      have ha : raw2036step0 = (fun i j => raw2036 (permutation31 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2036step0 raw2036; decide +kernel
      have hl : raw2036step0Labels = raw2036Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2036 raw2036Labels permutation31 permutation6
    mixedMoment B raw2036step0 raw2036step0Labels = mixedMoment B raw2036step1 raw2036step1Labels := by
      have ha : raw2036step1 = raw2036step0 := by apply Matrix.ext; unfold raw2036step1 raw2036step0; decide +kernel
      have hl : raw2036step0Labels = labelEmbedding1 ∘ raw2036step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2036step0 raw2036step0Labels raw2036step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2410 node2410Labels := by rfl

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

theorem canonical2085 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2085 raw2085Labels = mixedMoment B node5059 node5059Labels := by
  calc
    mixedMoment B raw2085 raw2085Labels = mixedMoment B raw2085step0 raw2085step0Labels := by
      have ha : raw2085step0 = (fun i j => raw2085 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2085step0 raw2085; decide +kernel
      have hl : raw2085step0Labels = raw2085Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2085 raw2085Labels permutation152 permutation4
    mixedMoment B raw2085step0 raw2085step0Labels = mixedMoment B raw2085step1 raw2085step1Labels := by
      have ha : raw2085step1 = raw2085step0 := by apply Matrix.ext; unfold raw2085step1 raw2085step0; decide +kernel
      have hl : raw2085step0Labels = labelEmbedding7 ∘ raw2085step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2085step0 raw2085step0Labels raw2085step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5059 node5059Labels := by rfl

theorem canonical2086 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2086 raw2086Labels = mixedMoment B node2462 node2462Labels := by
  calc
    mixedMoment B raw2086 raw2086Labels = mixedMoment B raw2086step0 raw2086step0Labels := by
      have ha : raw2086step0 = (fun i j => raw2086 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2086step0 raw2086; decide +kernel
      have hl : raw2086step0Labels = raw2086Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2086 raw2086Labels permutation152 permutation4
    _ = mixedMoment B node2462 node2462Labels := by rfl

theorem canonical2087 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2087 raw2087Labels = mixedMoment B node3436 node3436Labels := by
  calc
    mixedMoment B raw2087 raw2087Labels = mixedMoment B raw2087step0 raw2087step0Labels := by
      have ha : raw2087step0 = (fun i j => raw2087 (permutation153 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2087step0 raw2087; decide +kernel
      have hl : raw2087step0Labels = raw2087Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2087 raw2087Labels permutation153 permutation6
    mixedMoment B raw2087step0 raw2087step0Labels = mixedMoment B raw2087step1 raw2087step1Labels := by
      have ha : raw2087step1 = -raw2087step0 := by apply Matrix.ext; change ∀ i j, raw2087step1 i j = -(raw2087step0 i j); unfold raw2087step1 raw2087step0; decide +kernel
      have hl : raw2087step1Labels = raw2087step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2087step1 raw2087step1Labels = mixedMoment B raw2087step2 raw2087step2Labels := by
      have ha : raw2087step2 = raw2087step1 := by apply Matrix.ext; unfold raw2087step2 raw2087step1; decide +kernel
      have hl : raw2087step1Labels = labelEmbedding1 ∘ raw2087step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2087step1 raw2087step1Labels raw2087step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3436 node3436Labels := by rfl

theorem canonical2127 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2127 raw2127Labels = mixedMoment B node5102 node5102Labels := by
  calc
    mixedMoment B raw2127 raw2127Labels = mixedMoment B raw2127step0 raw2127step0Labels := by
      have ha : raw2127step0 = (fun i j => raw2127 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2127step0 raw2127; decide +kernel
      have hl : raw2127step0Labels = raw2127Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2127 raw2127Labels permutation32 permutation4
    mixedMoment B raw2127step0 raw2127step0Labels = mixedMoment B raw2127step1 raw2127step1Labels := by
      have ha : raw2127step1 = raw2127step0 := by apply Matrix.ext; unfold raw2127step1 raw2127step0; decide +kernel
      have hl : raw2127step0Labels = labelEmbedding7 ∘ raw2127step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2127step0 raw2127step0Labels raw2127step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5102 node5102Labels := by rfl

theorem canonical2128 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2128 raw2128Labels = mixedMoment B node2512 node2512Labels := by
  calc
    mixedMoment B raw2128 raw2128Labels = mixedMoment B raw2128step0 raw2128step0Labels := by
      have ha : raw2128step0 = (fun i j => raw2128 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2128step0 raw2128; decide +kernel
      have hl : raw2128step0Labels = raw2128Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2128 raw2128Labels permutation32 permutation4
    _ = mixedMoment B node2512 node2512Labels := by rfl

theorem canonical2129 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2129 raw2129Labels = mixedMoment B node3471 node3471Labels := by
  calc
    mixedMoment B raw2129 raw2129Labels = mixedMoment B raw2129step0 raw2129step0Labels := by
      have ha : raw2129step0 = (fun i j => raw2129 (permutation33 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2129step0 raw2129; decide +kernel
      have hl : raw2129step0Labels = raw2129Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2129 raw2129Labels permutation33 permutation6
    mixedMoment B raw2129step0 raw2129step0Labels = mixedMoment B raw2129step1 raw2129step1Labels := by
      have ha : raw2129step1 = -raw2129step0 := by apply Matrix.ext; change ∀ i j, raw2129step1 i j = -(raw2129step0 i j); unfold raw2129step1 raw2129step0; decide +kernel
      have hl : raw2129step1Labels = raw2129step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2129step1 raw2129step1Labels = mixedMoment B raw2129step2 raw2129step2Labels := by
      have ha : raw2129step2 = raw2129step1 := by apply Matrix.ext; unfold raw2129step2 raw2129step1; decide +kernel
      have hl : raw2129step1Labels = labelEmbedding1 ∘ raw2129step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2129step1 raw2129step1Labels raw2129step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3471 node3471Labels := by rfl

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

theorem canonical2277 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2277 raw2277Labels = mixedMoment B node5261 node5261Labels := by
  calc
    mixedMoment B raw2277 raw2277Labels = mixedMoment B raw2277step0 raw2277step0Labels := by
      have ha : raw2277step0 = (fun i j => raw2277 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2277step0 raw2277; decide +kernel
      have hl : raw2277step0Labels = raw2277Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2277 raw2277Labels permutation8 permutation4
    mixedMoment B raw2277step0 raw2277step0Labels = mixedMoment B raw2277step1 raw2277step1Labels := by
      have ha : raw2277step1 = raw2277step0 := by apply Matrix.ext; unfold raw2277step1 raw2277step0; decide +kernel
      have hl : raw2277step0Labels = labelEmbedding7 ∘ raw2277step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2277step0 raw2277step0Labels raw2277step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5261 node5261Labels := by rfl

theorem canonical2278 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2278 raw2278Labels = mixedMoment B node2726 node2726Labels := by
  calc
    mixedMoment B raw2278 raw2278Labels = mixedMoment B raw2278step0 raw2278step0Labels := by
      have ha : raw2278step0 = (fun i j => raw2278 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2278step0 raw2278; decide +kernel
      have hl : raw2278step0Labels = raw2278Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2278 raw2278Labels permutation8 permutation4
    _ = mixedMoment B node2726 node2726Labels := by rfl

theorem canonical2279 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2279 raw2279Labels = mixedMoment B node3545 node3545Labels := by
  calc
    mixedMoment B raw2279 raw2279Labels = mixedMoment B raw2279step0 raw2279step0Labels := by
      have ha : raw2279step0 = (fun i j => raw2279 (permutation31 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2279step0 raw2279; decide +kernel
      have hl : raw2279step0Labels = raw2279Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2279 raw2279Labels permutation31 permutation6
    mixedMoment B raw2279step0 raw2279step0Labels = mixedMoment B raw2279step1 raw2279step1Labels := by
      have ha : raw2279step1 = raw2279step0 := by apply Matrix.ext; unfold raw2279step1 raw2279step0; decide +kernel
      have hl : raw2279step0Labels = labelEmbedding1 ∘ raw2279step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2279step0 raw2279step0Labels raw2279step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3545 node3545Labels := by rfl

theorem canonical2280 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2280 raw2280Labels = mixedMoment B node5271 node5271Labels := by
  calc
    mixedMoment B raw2280 raw2280Labels = mixedMoment B raw2280step0 raw2280step0Labels := by
      have ha : raw2280step0 = (fun i j => raw2280 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2280step0 raw2280; decide +kernel
      have hl : raw2280step0Labels = raw2280Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2280 raw2280Labels permutation32 permutation4
    mixedMoment B raw2280step0 raw2280step0Labels = mixedMoment B raw2280step1 raw2280step1Labels := by
      have ha : raw2280step1 = raw2280step0 := by apply Matrix.ext; unfold raw2280step1 raw2280step0; decide +kernel
      have hl : raw2280step0Labels = labelEmbedding7 ∘ raw2280step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2280step0 raw2280step0Labels raw2280step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5271 node5271Labels := by rfl

theorem canonical2281 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2281 raw2281Labels = mixedMoment B node2739 node2739Labels := by
  calc
    mixedMoment B raw2281 raw2281Labels = mixedMoment B raw2281step0 raw2281step0Labels := by
      have ha : raw2281step0 = (fun i j => raw2281 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2281step0 raw2281; decide +kernel
      have hl : raw2281step0Labels = raw2281Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2281 raw2281Labels permutation32 permutation4
    _ = mixedMoment B node2739 node2739Labels := by rfl

theorem canonical2282 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2282 raw2282Labels = mixedMoment B node3534 node3534Labels := by
  calc
    mixedMoment B raw2282 raw2282Labels = mixedMoment B raw2282step0 raw2282step0Labels := by
      have ha : raw2282step0 = (fun i j => raw2282 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2282step0 raw2282; decide +kernel
      have hl : raw2282step0Labels = raw2282Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2282 raw2282Labels permutation32 permutation6
    mixedMoment B raw2282step0 raw2282step0Labels = mixedMoment B raw2282step1 raw2282step1Labels := by
      have ha : raw2282step1 = -raw2282step0 := by apply Matrix.ext; change ∀ i j, raw2282step1 i j = -(raw2282step0 i j); unfold raw2282step1 raw2282step0; decide +kernel
      have hl : raw2282step1Labels = raw2282step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2282step1 raw2282step1Labels = mixedMoment B raw2282step2 raw2282step2Labels := by
      have ha : raw2282step2 = raw2282step1 := by apply Matrix.ext; unfold raw2282step2 raw2282step1; decide +kernel
      have hl : raw2282step1Labels = labelEmbedding1 ∘ raw2282step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2282step1 raw2282step1Labels raw2282step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3534 node3534Labels := by rfl

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

theorem canonical2301 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2301 raw2301Labels = mixedMoment B node5293 node5293Labels := by
  calc
    mixedMoment B raw2301 raw2301Labels = mixedMoment B raw2301step0 raw2301step0Labels := by
      have ha : raw2301step0 = (fun i j => raw2301 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2301step0 raw2301; decide +kernel
      have hl : raw2301step0Labels = raw2301Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2301 raw2301Labels permutation8 permutation4
    mixedMoment B raw2301step0 raw2301step0Labels = mixedMoment B raw2301step1 raw2301step1Labels := by
      have ha : raw2301step1 = raw2301step0 := by apply Matrix.ext; unfold raw2301step1 raw2301step0; decide +kernel
      have hl : raw2301step0Labels = labelEmbedding7 ∘ raw2301step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2301step0 raw2301step0Labels raw2301step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5293 node5293Labels := by rfl

theorem canonical2302 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2302 raw2302Labels = mixedMoment B node2767 node2767Labels := by
  calc
    mixedMoment B raw2302 raw2302Labels = mixedMoment B raw2302step0 raw2302step0Labels := by
      have ha : raw2302step0 = (fun i j => raw2302 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2302step0 raw2302; decide +kernel
      have hl : raw2302step0Labels = raw2302Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2302 raw2302Labels permutation8 permutation4
    _ = mixedMoment B node2767 node2767Labels := by rfl

theorem canonical2303 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2303 raw2303Labels = mixedMoment B node3627 node3627Labels := by
  calc
    mixedMoment B raw2303 raw2303Labels = mixedMoment B raw2303step0 raw2303step0Labels := by
      have ha : raw2303step0 = (fun i j => raw2303 (permutation10 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2303step0 raw2303; decide +kernel
      have hl : raw2303step0Labels = raw2303Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2303 raw2303Labels permutation10 permutation6
    mixedMoment B raw2303step0 raw2303step0Labels = mixedMoment B raw2303step1 raw2303step1Labels := by
      have ha : raw2303step1 = -raw2303step0 := by apply Matrix.ext; change ∀ i j, raw2303step1 i j = -(raw2303step0 i j); unfold raw2303step1 raw2303step0; decide +kernel
      have hl : raw2303step1Labels = raw2303step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2303step1 raw2303step1Labels = mixedMoment B raw2303step2 raw2303step2Labels := by
      have ha : raw2303step2 = raw2303step1 := by apply Matrix.ext; unfold raw2303step2 raw2303step1; decide +kernel
      have hl : raw2303step1Labels = labelEmbedding1 ∘ raw2303step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2303step1 raw2303step1Labels raw2303step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3627 node3627Labels := by rfl

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

theorem canonical2322 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2322 raw2322Labels = mixedMoment B node5306 node5306Labels := by
  calc
    mixedMoment B raw2322 raw2322Labels = mixedMoment B raw2322step0 raw2322step0Labels := by
      have ha : raw2322step0 = (fun i j => raw2322 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2322step0 raw2322; decide +kernel
      have hl : raw2322step0Labels = raw2322Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2322 raw2322Labels permutation8 permutation4
    mixedMoment B raw2322step0 raw2322step0Labels = mixedMoment B raw2322step1 raw2322step1Labels := by
      have ha : raw2322step1 = raw2322step0 := by apply Matrix.ext; unfold raw2322step1 raw2322step0; decide +kernel
      have hl : raw2322step0Labels = labelEmbedding7 ∘ raw2322step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2322step0 raw2322step0Labels raw2322step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5306 node5306Labels := by rfl

theorem canonical2323 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2323 raw2323Labels = mixedMoment B node2784 node2784Labels := by
  calc
    mixedMoment B raw2323 raw2323Labels = mixedMoment B raw2323step0 raw2323step0Labels := by
      have ha : raw2323step0 = (fun i j => raw2323 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2323step0 raw2323; decide +kernel
      have hl : raw2323step0Labels = raw2323Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2323 raw2323Labels permutation8 permutation4
    _ = mixedMoment B node2784 node2784Labels := by rfl

theorem canonical2324 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2324 raw2324Labels = mixedMoment B node3623 node3623Labels := by
  calc
    mixedMoment B raw2324 raw2324Labels = mixedMoment B raw2324step0 raw2324step0Labels := by
      have ha : raw2324step0 = (fun i j => raw2324 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2324step0 raw2324; decide +kernel
      have hl : raw2324step0Labels = raw2324Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2324 raw2324Labels permutation8 permutation6
    mixedMoment B raw2324step0 raw2324step0Labels = mixedMoment B raw2324step1 raw2324step1Labels := by
      have ha : raw2324step1 = -raw2324step0 := by apply Matrix.ext; change ∀ i j, raw2324step1 i j = -(raw2324step0 i j); unfold raw2324step1 raw2324step0; decide +kernel
      have hl : raw2324step1Labels = raw2324step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2324step1 raw2324step1Labels = mixedMoment B raw2324step2 raw2324step2Labels := by
      have ha : raw2324step2 = raw2324step1 := by apply Matrix.ext; unfold raw2324step2 raw2324step1; decide +kernel
      have hl : raw2324step1Labels = labelEmbedding1 ∘ raw2324step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2324step1 raw2324step1Labels raw2324step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3623 node3623Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical270 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw270 raw270Labels = mixedMoment B node2767 node2767Labels := by
  calc
    mixedMoment B raw270 raw270Labels = mixedMoment B raw270step0 raw270step0Labels := by
      have ha : raw270step0 = (fun i j => raw270 (permutation8 i) (permutation5 j)) := by apply Matrix.ext; unfold raw270step0 raw270; decide +kernel
      have hl : raw270step0Labels = raw270Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw270 raw270Labels permutation8 permutation5
    mixedMoment B raw270step0 raw270step0Labels = mixedMoment B raw270step1 raw270step1Labels := by
      have ha : raw270step1 = raw270step0 := by apply Matrix.ext; unfold raw270step1 raw270step0; decide +kernel
      have hl : raw270step0Labels = labelEmbedding1 ∘ raw270step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw270step0 raw270step0Labels raw270step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2767 node2767Labels := by rfl

theorem canonical271 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw271 raw271Labels = mixedMoment B node404 node404Labels := by
  calc
    mixedMoment B raw271 raw271Labels = mixedMoment B raw271step0 raw271step0Labels := by
      have ha : raw271step0 = (fun i j => raw271 (permutation8 i) (permutation5 j)) := by apply Matrix.ext; unfold raw271step0 raw271; decide +kernel
      have hl : raw271step0Labels = raw271Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw271 raw271Labels permutation8 permutation5
    _ = mixedMoment B node404 node404Labels := by rfl

theorem canonical282 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw282 raw282Labels = mixedMoment B node2784 node2784Labels := by
  calc
    mixedMoment B raw282 raw282Labels = mixedMoment B raw282step0 raw282step0Labels := by
      have ha : raw282step0 = (fun i j => raw282 (permutation8 i) (permutation5 j)) := by apply Matrix.ext; unfold raw282step0 raw282; decide +kernel
      have hl : raw282step0Labels = raw282Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw282 raw282Labels permutation8 permutation5
    mixedMoment B raw282step0 raw282step0Labels = mixedMoment B raw282step1 raw282step1Labels := by
      have ha : raw282step1 = raw282step0 := by apply Matrix.ext; unfold raw282step1 raw282step0; decide +kernel
      have hl : raw282step0Labels = labelEmbedding1 ∘ raw282step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw282step0 raw282step0Labels raw282step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2784 node2784Labels := by rfl

theorem canonical283 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw283 raw283Labels = mixedMoment B node416 node416Labels := by
  calc
    mixedMoment B raw283 raw283Labels = mixedMoment B raw283step0 raw283step0Labels := by
      have ha : raw283step0 = (fun i j => raw283 (permutation8 i) (permutation5 j)) := by apply Matrix.ext; unfold raw283step0 raw283; decide +kernel
      have hl : raw283step0Labels = raw283Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw283 raw283Labels permutation8 permutation5
    _ = mixedMoment B node416 node416Labels := by rfl

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

theorem canonical2592 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2592 raw2592Labels = mixedMoment B node5475 node5475Labels := by
  calc
    mixedMoment B raw2592 raw2592Labels = mixedMoment B raw2592step0 raw2592step0Labels := by
      have ha : raw2592step0 = (fun i j => raw2592 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2592step0 raw2592; decide +kernel
      have hl : raw2592step0Labels = raw2592Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2592 raw2592Labels permutation8 permutation4
    mixedMoment B raw2592step0 raw2592step0Labels = mixedMoment B raw2592step1 raw2592step1Labels := by
      have ha : raw2592step1 = raw2592step0 := by apply Matrix.ext; unfold raw2592step1 raw2592step0; decide +kernel
      have hl : raw2592step0Labels = labelEmbedding7 ∘ raw2592step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2592step0 raw2592step0Labels raw2592step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5475 node5475Labels := by rfl

theorem canonical2593 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2593 raw2593Labels = mixedMoment B node3963 node3963Labels := by
  calc
    mixedMoment B raw2593 raw2593Labels = mixedMoment B raw2593step0 raw2593step0Labels := by
      have ha : raw2593step0 = (fun i j => raw2593 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2593step0 raw2593; decide +kernel
      have hl : raw2593step0Labels = raw2593Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2593 raw2593Labels permutation8 permutation4
    _ = mixedMoment B node3963 node3963Labels := by rfl

theorem canonical2594 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2594 raw2594Labels = mixedMoment B node3963 node3963Labels := by
  calc
    mixedMoment B raw2594 raw2594Labels = mixedMoment B raw2594step0 raw2594step0Labels := by
      have ha : raw2594step0 = (fun i j => raw2594 (permutation24 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2594step0 raw2594; decide +kernel
      have hl : raw2594step0Labels = raw2594Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2594 raw2594Labels permutation24 permutation6
    mixedMoment B raw2594step0 raw2594step0Labels = mixedMoment B raw2594step1 raw2594step1Labels := by
      have ha : raw2594step1 = raw2594step0 := by apply Matrix.ext; unfold raw2594step1 raw2594step0; decide +kernel
      have hl : raw2594step0Labels = labelEmbedding1 ∘ raw2594step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2594step0 raw2594step0Labels raw2594step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3963 node3963Labels := by rfl

theorem canonical2616 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2616 raw2616Labels = mixedMoment B node5491 node5491Labels := by
  calc
    _ = mixedMoment B node5491 node5491Labels := by rfl

theorem canonical2617 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2617 raw2617Labels = mixedMoment B node4014 node4014Labels := by
  calc
    _ = mixedMoment B node4014 node4014Labels := by rfl

theorem canonical2618 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2618 raw2618Labels = mixedMoment B node4014 node4014Labels := by
  calc
    mixedMoment B raw2618 raw2618Labels = mixedMoment B raw2618step0 raw2618step0Labels := by
      have ha : raw2618step0 = (fun i j => raw2618 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw2618step0 raw2618; decide +kernel
      have hl : raw2618step0Labels = raw2618Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2618 raw2618Labels permutation10 permutation3
    mixedMoment B raw2618step0 raw2618step0Labels = mixedMoment B raw2618step1 raw2618step1Labels := by
      have ha : raw2618step1 = raw2618step0 := by apply Matrix.ext; unfold raw2618step1 raw2618step0; decide +kernel
      have hl : raw2618step0Labels = labelEmbedding1 ∘ raw2618step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2618step0 raw2618step0Labels raw2618step1Labels labelEmbedding1 hl
    _ = mixedMoment B node4014 node4014Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical4
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical626 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw626 raw626Labels = mixedMoment B node4014 node4014Labels := by
  calc
    mixedMoment B raw626 raw626Labels = mixedMoment B raw626step0 raw626step0Labels := by
      have ha : raw626step0 = (fun i j => raw626 (permutation8 i) (permutation5 j)) := by apply Matrix.ext; unfold raw626step0 raw626; decide +kernel
      have hl : raw626step0Labels = raw626Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw626 raw626Labels permutation8 permutation5
    mixedMoment B raw626step0 raw626step0Labels = mixedMoment B raw626step1 raw626step1Labels := by
      have ha : raw626step1 = raw626step0 := by apply Matrix.ext; unfold raw626step1 raw626step0; decide +kernel
      have hl : raw626step0Labels = labelEmbedding1 ∘ raw626step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw626step0 raw626step0Labels raw626step1Labels labelEmbedding1 hl
    _ = mixedMoment B node4014 node4014Labels := by rfl

theorem canonical627 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw627 raw627Labels = mixedMoment B node527 node527Labels := by
  calc
    mixedMoment B raw627 raw627Labels = mixedMoment B raw627step0 raw627step0Labels := by
      have ha : raw627step0 = (fun i j => raw627 (permutation10 i) (permutation4 j)) := by apply Matrix.ext; unfold raw627step0 raw627; decide +kernel
      have hl : raw627step0Labels = raw627Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw627 raw627Labels permutation10 permutation4
    _ = mixedMoment B node527 node527Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical81
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical10450 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10450 raw10450Labels = mixedMoment B node5473 node5473Labels := by
  calc
    mixedMoment B raw10450 raw10450Labels = mixedMoment B raw10450step0 raw10450step0Labels := by
      have hz : ∀ j, raw10450 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10450step0 = (fun i j => raw10450 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10450step0 raw10450; decide +kernel
      have hl : raw10450step0Labels = raw10450Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10450 raw10450Labels permutation346 hz
    mixedMoment B raw10450step0 raw10450step0Labels = mixedMoment B raw10450step1 raw10450step1Labels := by
      have ha : raw10450step1 = (fun i j => raw10450step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10450step1 raw10450step0; decide +kernel
      have hl : raw10450step1Labels = raw10450step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10450step0 raw10450step0Labels permutation151 permutation3
    mixedMoment B raw10450step1 raw10450step1Labels = mixedMoment B raw10450step2 raw10450step2Labels := by
      have ha : raw10450step2 = -raw10450step1 := by apply Matrix.ext; change ∀ i j, raw10450step2 i j = -(raw10450step1 i j); unfold raw10450step2 raw10450step1; decide +kernel
      have hl : raw10450step2Labels = raw10450step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw10450step2 raw10450step2Labels = mixedMoment B raw10450step3 raw10450step3Labels := by
      have ha : raw10450step3 = raw10450step2 := by apply Matrix.ext; unfold raw10450step3 raw10450step2; decide +kernel
      have hl : raw10450step2Labels = labelEmbedding6 ∘ raw10450step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10450step2 raw10450step2Labels raw10450step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5473 node5473Labels := by rfl

theorem canonical10451 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10451 raw10451Labels = mixedMoment B node5473 node5473Labels := by
  calc
    mixedMoment B raw10451 raw10451Labels = mixedMoment B raw10451step0 raw10451step0Labels := by
      have hz : ∀ j, raw10451 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw10451step0 = (fun i j => raw10451 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw10451step0 raw10451; decide +kernel
      have hl : raw10451step0Labels = raw10451Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10451 raw10451Labels permutation265 hz
    mixedMoment B raw10451step0 raw10451step0Labels = mixedMoment B raw10451step1 raw10451step1Labels := by
      have ha : raw10451step1 = (fun i j => raw10451step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10451step1 raw10451step0; decide +kernel
      have hl : raw10451step1Labels = raw10451step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10451step0 raw10451step0Labels permutation151 permutation3
    mixedMoment B raw10451step1 raw10451step1Labels = mixedMoment B raw10451step2 raw10451step2Labels := by
      have ha : raw10451step2 = -raw10451step1 := by apply Matrix.ext; change ∀ i j, raw10451step2 i j = -(raw10451step1 i j); unfold raw10451step2 raw10451step1; decide +kernel
      have hl : raw10451step2Labels = raw10451step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw10451step2 raw10451step2Labels = mixedMoment B raw10451step3 raw10451step3Labels := by
      have ha : raw10451step3 = raw10451step2 := by apply Matrix.ext; unfold raw10451step3 raw10451step2; decide +kernel
      have hl : raw10451step2Labels = labelEmbedding6 ∘ raw10451step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10451step2 raw10451step2Labels raw10451step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5473 node5473Labels := by rfl

theorem canonical10452 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10452 raw10452Labels = mixedMoment B node5475 node5475Labels := by
  calc
    mixedMoment B raw10452 raw10452Labels = mixedMoment B raw10452step0 raw10452step0Labels := by
      have hz : ∀ j, raw10452 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10452step0 = (fun i j => raw10452 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10452step0 raw10452; decide +kernel
      have hl : raw10452step0Labels = raw10452Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10452 raw10452Labels permutation346 hz
    mixedMoment B raw10452step0 raw10452step0Labels = mixedMoment B raw10452step1 raw10452step1Labels := by
      have hz : ∀ j, raw10452step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw10452step1 = (fun i j => raw10452step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw10452step1 raw10452step0; decide +kernel
      have hl : raw10452step1Labels = raw10452step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10452step0 raw10452step0Labels permutation56 hz
    mixedMoment B raw10452step1 raw10452step1Labels = mixedMoment B raw10452step2 raw10452step2Labels := by
      have ha : raw10452step2 = (fun i j => raw10452step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10452step2 raw10452step1; decide +kernel
      have hl : raw10452step2Labels = raw10452step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10452step1 raw10452step1Labels permutation8 permutation3
    mixedMoment B raw10452step2 raw10452step2Labels = mixedMoment B raw10452step3 raw10452step3Labels := by
      have ha : raw10452step3 = raw10452step2 := by apply Matrix.ext; unfold raw10452step3 raw10452step2; decide +kernel
      have hl : raw10452step2Labels = labelEmbedding6 ∘ raw10452step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10452step2 raw10452step2Labels raw10452step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5475 node5475Labels := by rfl

theorem canonical10453 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10453 raw10453Labels = mixedMoment B node5491 node5491Labels := by
  calc
    mixedMoment B raw10453 raw10453Labels = mixedMoment B raw10453step0 raw10453step0Labels := by
      have hz : ∀ j, raw10453 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10453step0 = (fun i j => raw10453 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10453step0 raw10453; decide +kernel
      have hl : raw10453step0Labels = raw10453Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10453 raw10453Labels permutation346 hz
    mixedMoment B raw10453step0 raw10453step0Labels = mixedMoment B raw10453step1 raw10453step1Labels := by
      have hz : ∀ j, raw10453step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw10453step1 = (fun i j => raw10453step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw10453step1 raw10453step0; decide +kernel
      have hl : raw10453step1Labels = raw10453step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10453step0 raw10453step0Labels permutation56 hz
    mixedMoment B raw10453step1 raw10453step1Labels = mixedMoment B raw10453step2 raw10453step2Labels := by
      have ha : raw10453step2 = (fun i j => raw10453step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw10453step2 raw10453step1; decide +kernel
      have hl : raw10453step2Labels = raw10453step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10453step1 raw10453step1Labels permutation10 permutation2
    _ = mixedMoment B node5491 node5491Labels := by rfl

theorem canonical10454 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10454 raw10454Labels = mixedMoment B node5492 node5492Labels := by
  calc
    mixedMoment B raw10454 raw10454Labels = mixedMoment B raw10454step0 raw10454step0Labels := by
      have hz : ∀ j, raw10454 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10454step0 = (fun i j => raw10454 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10454step0 raw10454; decide +kernel
      have hl : raw10454step0Labels = raw10454Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10454 raw10454Labels permutation346 hz
    mixedMoment B raw10454step0 raw10454step0Labels = mixedMoment B raw10454step1 raw10454step1Labels := by
      have hz : ∀ j, raw10454step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw10454step1 = (fun i j => raw10454step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw10454step1 raw10454step0; decide +kernel
      have hl : raw10454step1Labels = raw10454step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10454step0 raw10454step0Labels permutation56 hz
    mixedMoment B raw10454step1 raw10454step1Labels = mixedMoment B raw10454step2 raw10454step2Labels := by
      have ha : raw10454step2 = (fun i j => raw10454step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10454step2 raw10454step1; decide +kernel
      have hl : raw10454step2Labels = raw10454step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10454step1 raw10454step1Labels permutation9 permutation3
    mixedMoment B raw10454step2 raw10454step2Labels = mixedMoment B raw10454step3 raw10454step3Labels := by
      have ha : raw10454step3 = raw10454step2 := by apply Matrix.ext; unfold raw10454step3 raw10454step2; decide +kernel
      have hl : raw10454step2Labels = labelEmbedding6 ∘ raw10454step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10454step2 raw10454step2Labels raw10454step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5492 node5492Labels := by rfl

theorem canonical10455 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10455 raw10455Labels = mixedMoment B node4424 node4424Labels := by
  calc
    mixedMoment B raw10455 raw10455Labels = mixedMoment B raw10455step0 raw10455step0Labels := by
      have hz : ∀ j, raw10455 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10455step0 = (fun i j => raw10455 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10455step0 raw10455; decide +kernel
      have hl : raw10455step0Labels = raw10455Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10455 raw10455Labels permutation346 hz
    mixedMoment B raw10455step0 raw10455step0Labels = mixedMoment B raw10455step1 raw10455step1Labels := by
      have ha : raw10455step1 = (fun i j => raw10455step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10455step1 raw10455step0; decide +kernel
      have hl : raw10455step1Labels = raw10455step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10455step0 raw10455step0Labels permutation38 permutation3
    mixedMoment B raw10455step1 raw10455step1Labels = mixedMoment B raw10455step2 raw10455step2Labels := by
      have ha : raw10455step2 = raw10455step1 := by apply Matrix.ext; unfold raw10455step2 raw10455step1; decide +kernel
      have hl : raw10455step1Labels = labelEmbedding6 ∘ raw10455step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10455step1 raw10455step1Labels raw10455step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4424 node4424Labels := by rfl

theorem canonical10456 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10456 raw10456Labels = mixedMoment B node5059 node5059Labels := by
  calc
    mixedMoment B raw10456 raw10456Labels = mixedMoment B raw10456step0 raw10456step0Labels := by
      have ha : raw10456step0 = (fun i j => raw10456 (permutation182 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10456step0 raw10456; decide +kernel
      have hl : raw10456step0Labels = raw10456Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10456 raw10456Labels permutation182 permutation3
    mixedMoment B raw10456step0 raw10456step0Labels = mixedMoment B raw10456step1 raw10456step1Labels := by
      have ha : raw10456step1 = raw10456step0 := by apply Matrix.ext; unfold raw10456step1 raw10456step0; decide +kernel
      have hl : raw10456step0Labels = labelEmbedding6 ∘ raw10456step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10456step0 raw10456step0Labels raw10456step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5059 node5059Labels := by rfl

theorem canonical10457 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10457 raw10457Labels = mixedMoment B node5018 node5018Labels := by
  calc
    mixedMoment B raw10457 raw10457Labels = mixedMoment B raw10457step0 raw10457step0Labels := by
      have hz : ∀ j, raw10457 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10457step0 = (fun i j => raw10457 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10457step0 raw10457; decide +kernel
      have hl : raw10457step0Labels = raw10457Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10457 raw10457Labels permutation346 hz
    mixedMoment B raw10457step0 raw10457step0Labels = mixedMoment B raw10457step1 raw10457step1Labels := by
      have ha : raw10457step1 = (fun i j => raw10457step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10457step1 raw10457step0; decide +kernel
      have hl : raw10457step1Labels = raw10457step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10457step0 raw10457step0Labels permutation38 permutation3
    mixedMoment B raw10457step1 raw10457step1Labels = mixedMoment B raw10457step2 raw10457step2Labels := by
      have ha : raw10457step2 = raw10457step1 := by apply Matrix.ext; unfold raw10457step2 raw10457step1; decide +kernel
      have hl : raw10457step1Labels = labelEmbedding6 ∘ raw10457step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10457step1 raw10457step1Labels raw10457step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5018 node5018Labels := by rfl

theorem canonical10458 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10458 raw10458Labels = mixedMoment B node5259 node5259Labels := by
  calc
    mixedMoment B raw10458 raw10458Labels = mixedMoment B raw10458step0 raw10458step0Labels := by
      have hz : ∀ j, raw10458 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10458step0 = (fun i j => raw10458 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10458step0 raw10458; decide +kernel
      have hl : raw10458step0Labels = raw10458Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10458 raw10458Labels permutation346 hz
    mixedMoment B raw10458step0 raw10458step0Labels = mixedMoment B raw10458step1 raw10458step1Labels := by
      have ha : raw10458step1 = (fun i j => raw10458step0 (permutation40 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10458step1 raw10458step0; decide +kernel
      have hl : raw10458step1Labels = raw10458step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10458step0 raw10458step0Labels permutation40 permutation3
    mixedMoment B raw10458step1 raw10458step1Labels = mixedMoment B raw10458step2 raw10458step2Labels := by
      have ha : raw10458step2 = raw10458step1 := by apply Matrix.ext; unfold raw10458step2 raw10458step1; decide +kernel
      have hl : raw10458step1Labels = labelEmbedding6 ∘ raw10458step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10458step1 raw10458step1Labels raw10458step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5259 node5259Labels := by rfl

theorem canonical10459 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10459 raw10459Labels = mixedMoment B node5271 node5271Labels := by
  calc
    mixedMoment B raw10459 raw10459Labels = mixedMoment B raw10459step0 raw10459step0Labels := by
      have hz : ∀ j, raw10459 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10459step0 = (fun i j => raw10459 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10459step0 raw10459; decide +kernel
      have hl : raw10459step0Labels = raw10459Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10459 raw10459Labels permutation346 hz
    mixedMoment B raw10459step0 raw10459step0Labels = mixedMoment B raw10459step1 raw10459step1Labels := by
      have ha : raw10459step1 = (fun i j => raw10459step0 (permutation42 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10459step1 raw10459step0; decide +kernel
      have hl : raw10459step1Labels = raw10459step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10459step0 raw10459step0Labels permutation42 permutation3
    mixedMoment B raw10459step1 raw10459step1Labels = mixedMoment B raw10459step2 raw10459step2Labels := by
      have ha : raw10459step2 = raw10459step1 := by apply Matrix.ext; unfold raw10459step2 raw10459step1; decide +kernel
      have hl : raw10459step1Labels = labelEmbedding6 ∘ raw10459step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10459step1 raw10459step1Labels raw10459step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5271 node5271Labels := by rfl

theorem canonical10460 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10460 raw10460Labels = mixedMoment B node4424 node4424Labels := by
  calc
    mixedMoment B raw10460 raw10460Labels = mixedMoment B raw10460step0 raw10460step0Labels := by
      have hz : ∀ j, raw10460 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw10460step0 = (fun i j => raw10460 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw10460step0 raw10460; decide +kernel
      have hl : raw10460step0Labels = raw10460Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10460 raw10460Labels permutation265 hz
    mixedMoment B raw10460step0 raw10460step0Labels = mixedMoment B raw10460step1 raw10460step1Labels := by
      have ha : raw10460step1 = (fun i j => raw10460step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10460step1 raw10460step0; decide +kernel
      have hl : raw10460step1Labels = raw10460step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10460step0 raw10460step0Labels permutation38 permutation3
    mixedMoment B raw10460step1 raw10460step1Labels = mixedMoment B raw10460step2 raw10460step2Labels := by
      have ha : raw10460step2 = raw10460step1 := by apply Matrix.ext; unfold raw10460step2 raw10460step1; decide +kernel
      have hl : raw10460step1Labels = labelEmbedding6 ∘ raw10460step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10460step1 raw10460step1Labels raw10460step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4424 node4424Labels := by rfl

theorem canonical10461 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10461 raw10461Labels = mixedMoment B node5059 node5059Labels := by
  calc
    mixedMoment B raw10461 raw10461Labels = mixedMoment B raw10461step0 raw10461step0Labels := by
      have ha : raw10461step0 = (fun i j => raw10461 (permutation158 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10461step0 raw10461; decide +kernel
      have hl : raw10461step0Labels = raw10461Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10461 raw10461Labels permutation158 permutation3
    mixedMoment B raw10461step0 raw10461step0Labels = mixedMoment B raw10461step1 raw10461step1Labels := by
      have ha : raw10461step1 = raw10461step0 := by apply Matrix.ext; unfold raw10461step1 raw10461step0; decide +kernel
      have hl : raw10461step0Labels = labelEmbedding6 ∘ raw10461step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10461step0 raw10461step0Labels raw10461step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5059 node5059Labels := by rfl

theorem canonical10462 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10462 raw10462Labels = mixedMoment B node5018 node5018Labels := by
  calc
    mixedMoment B raw10462 raw10462Labels = mixedMoment B raw10462step0 raw10462step0Labels := by
      have hz : ∀ j, raw10462 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw10462step0 = (fun i j => raw10462 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw10462step0 raw10462; decide +kernel
      have hl : raw10462step0Labels = raw10462Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10462 raw10462Labels permutation265 hz
    mixedMoment B raw10462step0 raw10462step0Labels = mixedMoment B raw10462step1 raw10462step1Labels := by
      have ha : raw10462step1 = (fun i j => raw10462step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10462step1 raw10462step0; decide +kernel
      have hl : raw10462step1Labels = raw10462step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10462step0 raw10462step0Labels permutation38 permutation3
    mixedMoment B raw10462step1 raw10462step1Labels = mixedMoment B raw10462step2 raw10462step2Labels := by
      have ha : raw10462step2 = raw10462step1 := by apply Matrix.ext; unfold raw10462step2 raw10462step1; decide +kernel
      have hl : raw10462step1Labels = labelEmbedding6 ∘ raw10462step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10462step1 raw10462step1Labels raw10462step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5018 node5018Labels := by rfl

theorem canonical10463 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10463 raw10463Labels = mixedMoment B node5259 node5259Labels := by
  calc
    mixedMoment B raw10463 raw10463Labels = mixedMoment B raw10463step0 raw10463step0Labels := by
      have hz : ∀ j, raw10463 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw10463step0 = (fun i j => raw10463 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw10463step0 raw10463; decide +kernel
      have hl : raw10463step0Labels = raw10463Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10463 raw10463Labels permutation265 hz
    mixedMoment B raw10463step0 raw10463step0Labels = mixedMoment B raw10463step1 raw10463step1Labels := by
      have ha : raw10463step1 = (fun i j => raw10463step0 (permutation40 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10463step1 raw10463step0; decide +kernel
      have hl : raw10463step1Labels = raw10463step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10463step0 raw10463step0Labels permutation40 permutation3
    mixedMoment B raw10463step1 raw10463step1Labels = mixedMoment B raw10463step2 raw10463step2Labels := by
      have ha : raw10463step2 = raw10463step1 := by apply Matrix.ext; unfold raw10463step2 raw10463step1; decide +kernel
      have hl : raw10463step1Labels = labelEmbedding6 ∘ raw10463step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10463step1 raw10463step1Labels raw10463step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5259 node5259Labels := by rfl

theorem canonical10464 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10464 raw10464Labels = mixedMoment B node5271 node5271Labels := by
  calc
    mixedMoment B raw10464 raw10464Labels = mixedMoment B raw10464step0 raw10464step0Labels := by
      have hz : ∀ j, raw10464 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw10464step0 = (fun i j => raw10464 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw10464step0 raw10464; decide +kernel
      have hl : raw10464step0Labels = raw10464Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10464 raw10464Labels permutation265 hz
    mixedMoment B raw10464step0 raw10464step0Labels = mixedMoment B raw10464step1 raw10464step1Labels := by
      have ha : raw10464step1 = (fun i j => raw10464step0 (permutation42 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10464step1 raw10464step0; decide +kernel
      have hl : raw10464step1Labels = raw10464step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10464step0 raw10464step0Labels permutation42 permutation3
    mixedMoment B raw10464step1 raw10464step1Labels = mixedMoment B raw10464step2 raw10464step2Labels := by
      have ha : raw10464step2 = raw10464step1 := by apply Matrix.ext; unfold raw10464step2 raw10464step1; decide +kernel
      have hl : raw10464step1Labels = labelEmbedding6 ∘ raw10464step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10464step1 raw10464step1Labels raw10464step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5271 node5271Labels := by rfl

theorem canonical10465 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10465 raw10465Labels = mixedMoment B node4499 node4499Labels := by
  calc
    mixedMoment B raw10465 raw10465Labels = mixedMoment B raw10465step0 raw10465step0Labels := by
      have hz : ∀ j, raw10465 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10465step0 = (fun i j => raw10465 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10465step0 raw10465; decide +kernel
      have hl : raw10465step0Labels = raw10465Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10465 raw10465Labels permutation346 hz
    mixedMoment B raw10465step0 raw10465step0Labels = mixedMoment B raw10465step1 raw10465step1Labels := by
      have hz : ∀ j, raw10465step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw10465step1 = (fun i j => raw10465step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw10465step1 raw10465step0; decide +kernel
      have hl : raw10465step1Labels = raw10465step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10465step0 raw10465step0Labels permutation56 hz
    mixedMoment B raw10465step1 raw10465step1Labels = mixedMoment B raw10465step2 raw10465step2Labels := by
      have ha : raw10465step2 = (fun i j => raw10465step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10465step2 raw10465step1; decide +kernel
      have hl : raw10465step2Labels = raw10465step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10465step1 raw10465step1Labels permutation8 permutation3
    mixedMoment B raw10465step2 raw10465step2Labels = mixedMoment B raw10465step3 raw10465step3Labels := by
      have ha : raw10465step3 = raw10465step2 := by apply Matrix.ext; unfold raw10465step3 raw10465step2; decide +kernel
      have hl : raw10465step2Labels = labelEmbedding6 ∘ raw10465step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10465step2 raw10465step2Labels raw10465step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4499 node4499Labels := by rfl

theorem canonical10466 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10466 raw10466Labels = mixedMoment B node5102 node5102Labels := by
  calc
    mixedMoment B raw10466 raw10466Labels = mixedMoment B raw10466step0 raw10466step0Labels := by
      have hz : ∀ j, raw10466 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10466step0 = (fun i j => raw10466 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10466step0 raw10466; decide +kernel
      have hl : raw10466step0Labels = raw10466Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10466 raw10466Labels permutation346 hz
    mixedMoment B raw10466step0 raw10466step0Labels = mixedMoment B raw10466step1 raw10466step1Labels := by
      have ha : raw10466step1 = (fun i j => raw10466step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10466step1 raw10466step0; decide +kernel
      have hl : raw10466step1Labels = raw10466step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10466step0 raw10466step0Labels permutation32 permutation3
    mixedMoment B raw10466step1 raw10466step1Labels = mixedMoment B raw10466step2 raw10466step2Labels := by
      have ha : raw10466step2 = raw10466step1 := by apply Matrix.ext; unfold raw10466step2 raw10466step1; decide +kernel
      have hl : raw10466step1Labels = labelEmbedding6 ∘ raw10466step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10466step1 raw10466step1Labels raw10466step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5102 node5102Labels := by rfl

theorem canonical10467 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10467 raw10467Labels = mixedMoment B node5102 node5102Labels := by
  calc
    mixedMoment B raw10467 raw10467Labels = mixedMoment B raw10467step0 raw10467step0Labels := by
      have hz : ∀ j, raw10467 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw10467step0 = (fun i j => raw10467 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw10467step0 raw10467; decide +kernel
      have hl : raw10467step0Labels = raw10467Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10467 raw10467Labels permutation265 hz
    mixedMoment B raw10467step0 raw10467step0Labels = mixedMoment B raw10467step1 raw10467step1Labels := by
      have ha : raw10467step1 = (fun i j => raw10467step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10467step1 raw10467step0; decide +kernel
      have hl : raw10467step1Labels = raw10467step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10467step0 raw10467step0Labels permutation32 permutation3
    mixedMoment B raw10467step1 raw10467step1Labels = mixedMoment B raw10467step2 raw10467step2Labels := by
      have ha : raw10467step2 = raw10467step1 := by apply Matrix.ext; unfold raw10467step2 raw10467step1; decide +kernel
      have hl : raw10467step1Labels = labelEmbedding6 ∘ raw10467step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10467step1 raw10467step1Labels raw10467step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5102 node5102Labels := by rfl

theorem canonical10468 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10468 raw10468Labels = mixedMoment B node5293 node5293Labels := by
  calc
    mixedMoment B raw10468 raw10468Labels = mixedMoment B raw10468step0 raw10468step0Labels := by
      have hz : ∀ j, raw10468 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10468step0 = (fun i j => raw10468 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10468step0 raw10468; decide +kernel
      have hl : raw10468step0Labels = raw10468Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10468 raw10468Labels permutation346 hz
    mixedMoment B raw10468step0 raw10468step0Labels = mixedMoment B raw10468step1 raw10468step1Labels := by
      have hz : ∀ j, raw10468step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw10468step1 = (fun i j => raw10468step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw10468step1 raw10468step0; decide +kernel
      have hl : raw10468step1Labels = raw10468step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10468step0 raw10468step0Labels permutation56 hz
    mixedMoment B raw10468step1 raw10468step1Labels = mixedMoment B raw10468step2 raw10468step2Labels := by
      have ha : raw10468step2 = (fun i j => raw10468step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10468step2 raw10468step1; decide +kernel
      have hl : raw10468step2Labels = raw10468step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10468step1 raw10468step1Labels permutation10 permutation3
    mixedMoment B raw10468step2 raw10468step2Labels = mixedMoment B raw10468step3 raw10468step3Labels := by
      have ha : raw10468step3 = raw10468step2 := by apply Matrix.ext; unfold raw10468step3 raw10468step2; decide +kernel
      have hl : raw10468step2Labels = labelEmbedding6 ∘ raw10468step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10468step2 raw10468step2Labels raw10468step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5293 node5293Labels := by rfl

theorem canonical10469 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10469 raw10469Labels = mixedMoment B node5306 node5306Labels := by
  calc
    mixedMoment B raw10469 raw10469Labels = mixedMoment B raw10469step0 raw10469step0Labels := by
      have hz : ∀ j, raw10469 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10469step0 = (fun i j => raw10469 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10469step0 raw10469; decide +kernel
      have hl : raw10469step0Labels = raw10469Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10469 raw10469Labels permutation346 hz
    mixedMoment B raw10469step0 raw10469step0Labels = mixedMoment B raw10469step1 raw10469step1Labels := by
      have hz : ∀ j, raw10469step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw10469step1 = (fun i j => raw10469step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw10469step1 raw10469step0; decide +kernel
      have hl : raw10469step1Labels = raw10469step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10469step0 raw10469step0Labels permutation56 hz
    mixedMoment B raw10469step1 raw10469step1Labels = mixedMoment B raw10469step2 raw10469step2Labels := by
      have ha : raw10469step2 = (fun i j => raw10469step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10469step2 raw10469step1; decide +kernel
      have hl : raw10469step2Labels = raw10469step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10469step1 raw10469step1Labels permutation9 permutation3
    mixedMoment B raw10469step2 raw10469step2Labels = mixedMoment B raw10469step3 raw10469step3Labels := by
      have ha : raw10469step3 = raw10469step2 := by apply Matrix.ext; unfold raw10469step3 raw10469step2; decide +kernel
      have hl : raw10469step2Labels = labelEmbedding6 ∘ raw10469step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10469step2 raw10469step2Labels raw10469step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5306 node5306Labels := by rfl

theorem canonical10470 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10470 raw10470Labels = mixedMoment B node4431 node4431Labels := by
  calc
    mixedMoment B raw10470 raw10470Labels = mixedMoment B raw10470step0 raw10470step0Labels := by
      have hz : ∀ j, raw10470 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10470step0 = (fun i j => raw10470 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10470step0 raw10470; decide +kernel
      have hl : raw10470step0Labels = raw10470Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10470 raw10470Labels permutation346 hz
    mixedMoment B raw10470step0 raw10470step0Labels = mixedMoment B raw10470step1 raw10470step1Labels := by
      have hz : ∀ j, raw10470step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw10470step1 = (fun i j => raw10470step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw10470step1 raw10470step0; decide +kernel
      have hl : raw10470step1Labels = raw10470step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10470step0 raw10470step0Labels permutation56 hz
    mixedMoment B raw10470step1 raw10470step1Labels = mixedMoment B raw10470step2 raw10470step2Labels := by
      have ha : raw10470step2 = (fun i j => raw10470step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10470step2 raw10470step1; decide +kernel
      have hl : raw10470step2Labels = raw10470step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10470step1 raw10470step1Labels permutation9 permutation3
    mixedMoment B raw10470step2 raw10470step2Labels = mixedMoment B raw10470step3 raw10470step3Labels := by
      have ha : raw10470step3 = raw10470step2 := by apply Matrix.ext; unfold raw10470step3 raw10470step2; decide +kernel
      have hl : raw10470step2Labels = labelEmbedding6 ∘ raw10470step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10470step2 raw10470step2Labels raw10470step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4431 node4431Labels := by rfl

theorem canonical10471 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10471 raw10471Labels = mixedMoment B node5014 node5014Labels := by
  calc
    mixedMoment B raw10471 raw10471Labels = mixedMoment B raw10471step0 raw10471step0Labels := by
      have hz : ∀ j, raw10471 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10471step0 = (fun i j => raw10471 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10471step0 raw10471; decide +kernel
      have hl : raw10471step0Labels = raw10471Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10471 raw10471Labels permutation346 hz
    mixedMoment B raw10471step0 raw10471step0Labels = mixedMoment B raw10471step1 raw10471step1Labels := by
      have ha : raw10471step1 = (fun i j => raw10471step0 (permutation127 i) (permutation5 j)) := by apply Matrix.ext; unfold raw10471step1 raw10471step0; decide +kernel
      have hl : raw10471step1Labels = raw10471step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10471step0 raw10471step0Labels permutation127 permutation5
    mixedMoment B raw10471step1 raw10471step1Labels = mixedMoment B raw10471step2 raw10471step2Labels := by
      have ha : raw10471step2 = raw10471step1 := by apply Matrix.ext; unfold raw10471step2 raw10471step1; decide +kernel
      have hl : raw10471step1Labels = labelEmbedding8 ∘ raw10471step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10471step1 raw10471step1Labels raw10471step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5014 node5014Labels := by rfl

theorem canonical10472 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10472 raw10472Labels = mixedMoment B node5014 node5014Labels := by
  calc
    mixedMoment B raw10472 raw10472Labels = mixedMoment B raw10472step0 raw10472step0Labels := by
      have hz : ∀ j, raw10472 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw10472step0 = (fun i j => raw10472 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw10472step0 raw10472; decide +kernel
      have hl : raw10472step0Labels = raw10472Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10472 raw10472Labels permutation265 hz
    mixedMoment B raw10472step0 raw10472step0Labels = mixedMoment B raw10472step1 raw10472step1Labels := by
      have ha : raw10472step1 = (fun i j => raw10472step0 (permutation127 i) (permutation5 j)) := by apply Matrix.ext; unfold raw10472step1 raw10472step0; decide +kernel
      have hl : raw10472step1Labels = raw10472step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10472step0 raw10472step0Labels permutation127 permutation5
    mixedMoment B raw10472step1 raw10472step1Labels = mixedMoment B raw10472step2 raw10472step2Labels := by
      have ha : raw10472step2 = raw10472step1 := by apply Matrix.ext; unfold raw10472step2 raw10472step1; decide +kernel
      have hl : raw10472step1Labels = labelEmbedding8 ∘ raw10472step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10472step1 raw10472step1Labels raw10472step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5014 node5014Labels := by rfl

theorem canonical10473 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10473 raw10473Labels = mixedMoment B node5023 node5023Labels := by
  calc
    mixedMoment B raw10473 raw10473Labels = mixedMoment B raw10473step0 raw10473step0Labels := by
      have hz : ∀ j, raw10473 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10473step0 = (fun i j => raw10473 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10473step0 raw10473; decide +kernel
      have hl : raw10473step0Labels = raw10473Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10473 raw10473Labels permutation346 hz
    mixedMoment B raw10473step0 raw10473step0Labels = mixedMoment B raw10473step1 raw10473step1Labels := by
      have hz : ∀ j, raw10473step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw10473step1 = (fun i j => raw10473step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw10473step1 raw10473step0; decide +kernel
      have hl : raw10473step1Labels = raw10473step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10473step0 raw10473step0Labels permutation56 hz
    mixedMoment B raw10473step1 raw10473step1Labels = mixedMoment B raw10473step2 raw10473step2Labels := by
      have ha : raw10473step2 = (fun i j => raw10473step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10473step2 raw10473step1; decide +kernel
      have hl : raw10473step2Labels = raw10473step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10473step1 raw10473step1Labels permutation9 permutation3
    mixedMoment B raw10473step2 raw10473step2Labels = mixedMoment B raw10473step3 raw10473step3Labels := by
      have ha : raw10473step3 = raw10473step2 := by apply Matrix.ext; unfold raw10473step3 raw10473step2; decide +kernel
      have hl : raw10473step2Labels = labelEmbedding6 ∘ raw10473step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10473step2 raw10473step2Labels raw10473step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5023 node5023Labels := by rfl

theorem canonical10474 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10474 raw10474Labels = mixedMoment B node5272 node5272Labels := by
  calc
    mixedMoment B raw10474 raw10474Labels = mixedMoment B raw10474step0 raw10474step0Labels := by
      have hz : ∀ j, raw10474 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10474step0 = (fun i j => raw10474 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10474step0 raw10474; decide +kernel
      have hl : raw10474step0Labels = raw10474Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10474 raw10474Labels permutation346 hz
    mixedMoment B raw10474step0 raw10474step0Labels = mixedMoment B raw10474step1 raw10474step1Labels := by
      have hz : ∀ j, raw10474step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw10474step1 = (fun i j => raw10474step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw10474step1 raw10474step0; decide +kernel
      have hl : raw10474step1Labels = raw10474step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10474step0 raw10474step0Labels permutation56 hz
    mixedMoment B raw10474step1 raw10474step1Labels = mixedMoment B raw10474step2 raw10474step2Labels := by
      have ha : raw10474step2 = (fun i j => raw10474step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10474step2 raw10474step1; decide +kernel
      have hl : raw10474step2Labels = raw10474step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10474step1 raw10474step1Labels permutation9 permutation3
    mixedMoment B raw10474step2 raw10474step2Labels = mixedMoment B raw10474step3 raw10474step3Labels := by
      have ha : raw10474step3 = raw10474step2 := by apply Matrix.ext; unfold raw10474step3 raw10474step2; decide +kernel
      have hl : raw10474step2Labels = labelEmbedding6 ∘ raw10474step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10474step2 raw10474step2Labels raw10474step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5272 node5272Labels := by rfl

theorem canonical10475 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10475 raw10475Labels = mixedMoment B node4428 node4428Labels := by
  calc
    mixedMoment B raw10475 raw10475Labels = mixedMoment B raw10475step0 raw10475step0Labels := by
      have hz : ∀ j, raw10475 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10475step0 = (fun i j => raw10475 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10475step0 raw10475; decide +kernel
      have hl : raw10475step0Labels = raw10475Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10475 raw10475Labels permutation346 hz
    mixedMoment B raw10475step0 raw10475step0Labels = mixedMoment B raw10475step1 raw10475step1Labels := by
      have hz : ∀ j, raw10475step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw10475step1 = (fun i j => raw10475step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw10475step1 raw10475step0; decide +kernel
      have hl : raw10475step1Labels = raw10475step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10475step0 raw10475step0Labels permutation56 hz
    mixedMoment B raw10475step1 raw10475step1Labels = mixedMoment B raw10475step2 raw10475step2Labels := by
      have ha : raw10475step2 = (fun i j => raw10475step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10475step2 raw10475step1; decide +kernel
      have hl : raw10475step2Labels = raw10475step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10475step1 raw10475step1Labels permutation8 permutation3
    mixedMoment B raw10475step2 raw10475step2Labels = mixedMoment B raw10475step3 raw10475step3Labels := by
      have ha : raw10475step3 = raw10475step2 := by apply Matrix.ext; unfold raw10475step3 raw10475step2; decide +kernel
      have hl : raw10475step2Labels = labelEmbedding6 ∘ raw10475step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10475step2 raw10475step2Labels raw10475step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4428 node4428Labels := by rfl

theorem canonical10476 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10476 raw10476Labels = mixedMoment B node5000 node5000Labels := by
  calc
    mixedMoment B raw10476 raw10476Labels = mixedMoment B raw10476step0 raw10476step0Labels := by
      have hz : ∀ j, raw10476 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10476step0 = (fun i j => raw10476 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10476step0 raw10476; decide +kernel
      have hl : raw10476step0Labels = raw10476Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10476 raw10476Labels permutation346 hz
    mixedMoment B raw10476step0 raw10476step0Labels = mixedMoment B raw10476step1 raw10476step1Labels := by
      have ha : raw10476step1 = (fun i j => raw10476step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10476step1 raw10476step0; decide +kernel
      have hl : raw10476step1Labels = raw10476step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10476step0 raw10476step0Labels permutation151 permutation3
    mixedMoment B raw10476step1 raw10476step1Labels = mixedMoment B raw10476step2 raw10476step2Labels := by
      have ha : raw10476step2 = -raw10476step1 := by apply Matrix.ext; change ∀ i j, raw10476step2 i j = -(raw10476step1 i j); unfold raw10476step2 raw10476step1; decide +kernel
      have hl : raw10476step2Labels = raw10476step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw10476step2 raw10476step2Labels = mixedMoment B raw10476step3 raw10476step3Labels := by
      have ha : raw10476step3 = raw10476step2 := by apply Matrix.ext; unfold raw10476step3 raw10476step2; decide +kernel
      have hl : raw10476step2Labels = labelEmbedding6 ∘ raw10476step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10476step2 raw10476step2Labels raw10476step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5000 node5000Labels := by rfl

theorem canonical10477 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10477 raw10477Labels = mixedMoment B node5000 node5000Labels := by
  calc
    mixedMoment B raw10477 raw10477Labels = mixedMoment B raw10477step0 raw10477step0Labels := by
      have hz : ∀ j, raw10477 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw10477step0 = (fun i j => raw10477 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw10477step0 raw10477; decide +kernel
      have hl : raw10477step0Labels = raw10477Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10477 raw10477Labels permutation265 hz
    mixedMoment B raw10477step0 raw10477step0Labels = mixedMoment B raw10477step1 raw10477step1Labels := by
      have ha : raw10477step1 = (fun i j => raw10477step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10477step1 raw10477step0; decide +kernel
      have hl : raw10477step1Labels = raw10477step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10477step0 raw10477step0Labels permutation151 permutation3
    mixedMoment B raw10477step1 raw10477step1Labels = mixedMoment B raw10477step2 raw10477step2Labels := by
      have ha : raw10477step2 = -raw10477step1 := by apply Matrix.ext; change ∀ i j, raw10477step2 i j = -(raw10477step1 i j); unfold raw10477step2 raw10477step1; decide +kernel
      have hl : raw10477step2Labels = raw10477step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw10477step2 raw10477step2Labels = mixedMoment B raw10477step3 raw10477step3Labels := by
      have ha : raw10477step3 = raw10477step2 := by apply Matrix.ext; unfold raw10477step3 raw10477step2; decide +kernel
      have hl : raw10477step2Labels = labelEmbedding6 ∘ raw10477step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10477step2 raw10477step2Labels raw10477step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5000 node5000Labels := by rfl

theorem canonical10478 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10478 raw10478Labels = mixedMoment B node5021 node5021Labels := by
  calc
    mixedMoment B raw10478 raw10478Labels = mixedMoment B raw10478step0 raw10478step0Labels := by
      have hz : ∀ j, raw10478 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10478step0 = (fun i j => raw10478 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10478step0 raw10478; decide +kernel
      have hl : raw10478step0Labels = raw10478Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10478 raw10478Labels permutation346 hz
    mixedMoment B raw10478step0 raw10478step0Labels = mixedMoment B raw10478step1 raw10478step1Labels := by
      have hz : ∀ j, raw10478step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw10478step1 = (fun i j => raw10478step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw10478step1 raw10478step0; decide +kernel
      have hl : raw10478step1Labels = raw10478step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10478step0 raw10478step0Labels permutation56 hz
    mixedMoment B raw10478step1 raw10478step1Labels = mixedMoment B raw10478step2 raw10478step2Labels := by
      have ha : raw10478step2 = (fun i j => raw10478step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10478step2 raw10478step1; decide +kernel
      have hl : raw10478step2Labels = raw10478step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10478step1 raw10478step1Labels permutation8 permutation3
    mixedMoment B raw10478step2 raw10478step2Labels = mixedMoment B raw10478step3 raw10478step3Labels := by
      have ha : raw10478step3 = raw10478step2 := by apply Matrix.ext; unfold raw10478step3 raw10478step2; decide +kernel
      have hl : raw10478step2Labels = labelEmbedding6 ∘ raw10478step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10478step2 raw10478step2Labels raw10478step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5021 node5021Labels := by rfl

theorem canonical10479 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10479 raw10479Labels = mixedMoment B node5261 node5261Labels := by
  calc
    mixedMoment B raw10479 raw10479Labels = mixedMoment B raw10479step0 raw10479step0Labels := by
      have hz : ∀ j, raw10479 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10479step0 = (fun i j => raw10479 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10479step0 raw10479; decide +kernel
      have hl : raw10479step0Labels = raw10479Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10479 raw10479Labels permutation346 hz
    mixedMoment B raw10479step0 raw10479step0Labels = mixedMoment B raw10479step1 raw10479step1Labels := by
      have hz : ∀ j, raw10479step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw10479step1 = (fun i j => raw10479step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw10479step1 raw10479step0; decide +kernel
      have hl : raw10479step1Labels = raw10479step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10479step0 raw10479step0Labels permutation56 hz
    mixedMoment B raw10479step1 raw10479step1Labels = mixedMoment B raw10479step2 raw10479step2Labels := by
      have ha : raw10479step2 = (fun i j => raw10479step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10479step2 raw10479step1; decide +kernel
      have hl : raw10479step2Labels = raw10479step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10479step1 raw10479step1Labels permutation8 permutation3
    mixedMoment B raw10479step2 raw10479step2Labels = mixedMoment B raw10479step3 raw10479step3Labels := by
      have ha : raw10479step3 = raw10479step2 := by apply Matrix.ext; unfold raw10479step3 raw10479step2; decide +kernel
      have hl : raw10479step2Labels = labelEmbedding6 ∘ raw10479step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10479step2 raw10479step2Labels raw10479step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5261 node5261Labels := by rfl

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

theorem canonical1236 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1236 raw1236Labels = mixedMoment B node4424 node4424Labels := by
  calc
    mixedMoment B raw1236 raw1236Labels = mixedMoment B raw1236step0 raw1236step0Labels := by
      have ha : raw1236step0 = (fun i j => raw1236 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1236step0 raw1236; decide +kernel
      have hl : raw1236step0Labels = raw1236Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1236 raw1236Labels permutation32 permutation4
    mixedMoment B raw1236step0 raw1236step0Labels = mixedMoment B raw1236step1 raw1236step1Labels := by
      have ha : raw1236step1 = raw1236step0 := by apply Matrix.ext; unfold raw1236step1 raw1236step0; decide +kernel
      have hl : raw1236step0Labels = labelEmbedding7 ∘ raw1236step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1236step0 raw1236step0Labels raw1236step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4424 node4424Labels := by rfl

theorem canonical1237 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1237 raw1237Labels = mixedMoment B node1005 node1005Labels := by
  calc
    mixedMoment B raw1237 raw1237Labels = mixedMoment B raw1237step0 raw1237step0Labels := by
      have ha : raw1237step0 = (fun i j => raw1237 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1237step0 raw1237; decide +kernel
      have hl : raw1237step0Labels = raw1237Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1237 raw1237Labels permutation32 permutation4
    _ = mixedMoment B node1005 node1005Labels := by rfl

theorem canonical1238 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1238 raw1238Labels = mixedMoment B node1623 node1623Labels := by
  calc
    mixedMoment B raw1238 raw1238Labels = mixedMoment B raw1238step0 raw1238step0Labels := by
      have ha : raw1238step0 = (fun i j => raw1238 (permutation33 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1238step0 raw1238; decide +kernel
      have hl : raw1238step0Labels = raw1238Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1238 raw1238Labels permutation33 permutation6
    mixedMoment B raw1238step0 raw1238step0Labels = mixedMoment B raw1238step1 raw1238step1Labels := by
      have ha : raw1238step1 = -raw1238step0 := by apply Matrix.ext; change ∀ i j, raw1238step1 i j = -(raw1238step0 i j); unfold raw1238step1 raw1238step0; decide +kernel
      have hl : raw1238step1Labels = raw1238step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1238step1 raw1238step1Labels = mixedMoment B raw1238step2 raw1238step2Labels := by
      have ha : raw1238step2 = raw1238step1 := by apply Matrix.ext; unfold raw1238step2 raw1238step1; decide +kernel
      have hl : raw1238step1Labels = labelEmbedding1 ∘ raw1238step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1238step1 raw1238step1Labels raw1238step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1623 node1623Labels := by rfl

theorem canonical1239 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1239 raw1239Labels = mixedMoment B node4428 node4428Labels := by
  calc
    mixedMoment B raw1239 raw1239Labels = mixedMoment B raw1239step0 raw1239step0Labels := by
      have ha : raw1239step0 = (fun i j => raw1239 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1239step0 raw1239; decide +kernel
      have hl : raw1239step0Labels = raw1239Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1239 raw1239Labels permutation8 permutation4
    mixedMoment B raw1239step0 raw1239step0Labels = mixedMoment B raw1239step1 raw1239step1Labels := by
      have ha : raw1239step1 = raw1239step0 := by apply Matrix.ext; unfold raw1239step1 raw1239step0; decide +kernel
      have hl : raw1239step0Labels = labelEmbedding7 ∘ raw1239step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1239step0 raw1239step0Labels raw1239step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4428 node4428Labels := by rfl

theorem canonical1240 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1240 raw1240Labels = mixedMoment B node1009 node1009Labels := by
  calc
    mixedMoment B raw1240 raw1240Labels = mixedMoment B raw1240step0 raw1240step0Labels := by
      have ha : raw1240step0 = (fun i j => raw1240 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1240step0 raw1240; decide +kernel
      have hl : raw1240step0Labels = raw1240Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1240 raw1240Labels permutation8 permutation4
    _ = mixedMoment B node1009 node1009Labels := by rfl

theorem canonical1241 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1241 raw1241Labels = mixedMoment B node1630 node1630Labels := by
  calc
    mixedMoment B raw1241 raw1241Labels = mixedMoment B raw1241step0 raw1241step0Labels := by
      have ha : raw1241step0 = (fun i j => raw1241 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1241step0 raw1241; decide +kernel
      have hl : raw1241step0Labels = raw1241Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1241 raw1241Labels permutation8 permutation6
    mixedMoment B raw1241step0 raw1241step0Labels = mixedMoment B raw1241step1 raw1241step1Labels := by
      have ha : raw1241step1 = -raw1241step0 := by apply Matrix.ext; change ∀ i j, raw1241step1 i j = -(raw1241step0 i j); unfold raw1241step1 raw1241step0; decide +kernel
      have hl : raw1241step1Labels = raw1241step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1241step1 raw1241step1Labels = mixedMoment B raw1241step2 raw1241step2Labels := by
      have ha : raw1241step2 = raw1241step1 := by apply Matrix.ext; unfold raw1241step2 raw1241step1; decide +kernel
      have hl : raw1241step1Labels = labelEmbedding1 ∘ raw1241step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1241step1 raw1241step1Labels raw1241step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1630 node1630Labels := by rfl

theorem canonical1242 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1242 raw1242Labels = mixedMoment B node4431 node4431Labels := by
  calc
    mixedMoment B raw1242 raw1242Labels = mixedMoment B raw1242step0 raw1242step0Labels := by
      have ha : raw1242step0 = (fun i j => raw1242 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1242step0 raw1242; decide +kernel
      have hl : raw1242step0Labels = raw1242Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1242 raw1242Labels permutation8 permutation4
    mixedMoment B raw1242step0 raw1242step0Labels = mixedMoment B raw1242step1 raw1242step1Labels := by
      have ha : raw1242step1 = raw1242step0 := by apply Matrix.ext; unfold raw1242step1 raw1242step0; decide +kernel
      have hl : raw1242step0Labels = labelEmbedding7 ∘ raw1242step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1242step0 raw1242step0Labels raw1242step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4431 node4431Labels := by rfl

theorem canonical1243 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1243 raw1243Labels = mixedMoment B node1012 node1012Labels := by
  calc
    mixedMoment B raw1243 raw1243Labels = mixedMoment B raw1243step0 raw1243step0Labels := by
      have ha : raw1243step0 = (fun i j => raw1243 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1243step0 raw1243; decide +kernel
      have hl : raw1243step0Labels = raw1243Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1243 raw1243Labels permutation8 permutation4
    _ = mixedMoment B node1012 node1012Labels := by rfl

theorem canonical1244 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1244 raw1244Labels = mixedMoment B node1627 node1627Labels := by
  calc
    mixedMoment B raw1244 raw1244Labels = mixedMoment B raw1244step0 raw1244step0Labels := by
      have ha : raw1244step0 = (fun i j => raw1244 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1244step0 raw1244; decide +kernel
      have hl : raw1244step0Labels = raw1244Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1244 raw1244Labels permutation8 permutation6
    mixedMoment B raw1244step0 raw1244step0Labels = mixedMoment B raw1244step1 raw1244step1Labels := by
      have ha : raw1244step1 = -raw1244step0 := by apply Matrix.ext; change ∀ i j, raw1244step1 i j = -(raw1244step0 i j); unfold raw1244step1 raw1244step0; decide +kernel
      have hl : raw1244step1Labels = raw1244step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1244step1 raw1244step1Labels = mixedMoment B raw1244step2 raw1244step2Labels := by
      have ha : raw1244step2 = raw1244step1 := by apply Matrix.ext; unfold raw1244step2 raw1244step1; decide +kernel
      have hl : raw1244step1Labels = labelEmbedding1 ∘ raw1244step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1244step1 raw1244step1Labels raw1244step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1627 node1627Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_FiniteSums
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sum_fin_five {R : Type*} [AddCommMonoid R] (f : Fin 5 → R) :
    ∑ i, f i = f 0 + f 1 + f 2 + f 3 + f 4 := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change f 0 + (f 1 + (f 2 + (f 3 + f 4))) = _
  ac_rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_GroupedColumns
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Explicit grouping formulas for the two- and three-column equality
patterns. These discharge the dependent finite-label calculations once,
so concrete certificate rows need only ordinary integer arithmetic. -/

open scoped BigOperators
namespace MUB6

theorem groupedColumns_family3_0 {p : ℕ} (A : Matrix (Fin p) (Fin 3) ℤ) :
    groupedColumns A (EqualityPatterns.family3.label 0) =
      (fun i (_ : Fin 1) => A i 0 + A i 1 + A i 2) := by
  change groupedColumns A (fun _ : Fin 3 => (0 : Fin 1)) = _
  ext i b
  have hb : b = 0 := Subsingleton.elim _ _
  subst b
  simp [groupedColumns, Fin.sum_univ_succ, add_assoc]

theorem groupedColumns_family3_1 {p : ℕ} (A : Matrix (Fin p) (Fin 3) ℤ) :
    groupedColumns A (EqualityPatterns.family3.label 1) =
      (fun i => ![A i 0 + A i 1, A i 2]) := by
  change groupedColumns A (![0, 0, 1] : Fin 3 → Fin 2) = _
  ext i b
  fin_cases b <;> simp [groupedColumns, Finset.sum_filter, Fin.sum_univ_succ]

theorem groupedColumns_family3_2 {p : ℕ} (A : Matrix (Fin p) (Fin 3) ℤ) :
    groupedColumns A (EqualityPatterns.family3.label 2) =
      (fun i => ![A i 0 + A i 2, A i 1]) := by
  change groupedColumns A (![0, 1, 0] : Fin 3 → Fin 2) = _
  ext i b
  fin_cases b <;> simp [groupedColumns, Finset.sum_filter, Fin.sum_univ_succ]

theorem groupedColumns_family3_3 {p : ℕ} (A : Matrix (Fin p) (Fin 3) ℤ) :
    groupedColumns A (EqualityPatterns.family3.label 3) =
      (fun i => ![A i 0, A i 1 + A i 2]) := by
  change groupedColumns A (![0, 1, 1] : Fin 3 → Fin 2) = _
  ext i b
  fin_cases b <;> simp [groupedColumns, Finset.sum_filter, Fin.sum_univ_succ]

theorem groupedColumns_family3_4 {p : ℕ} (A : Matrix (Fin p) (Fin 3) ℤ) :
    groupedColumns A (EqualityPatterns.family3.label 4) = A := by
  change groupedColumns A (fun j : Fin 3 => j) = _
  ext i b
  simp [groupedColumns, Finset.sum_filter]

end MUB6

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_PairAverage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace MUB6.Certificate.MixedSemantics

theorem eval_familyPairVector (B : Fin 7 → Basis) (v : Sparse (Fin 909)) :
    Sparse.eval v (familyPairVector B) =
      familyAverage B (fun H => Sparse.eval v (PairSemantics.momentVector H)) := by
  unfold familyPairVector familyAverage
  rw [Sparse.eval_average]
  apply average_congr
  intro r
  exact Sparse.eval_average v _

theorem familyPairMoment_of_pointwise {p n : ℕ} (B : Fin 7 → Basis)
    (hB : IsMUBFamily B) (A : Matrix (Fin p) (Fin n) ℤ) (v : Sparse (Fin 909))
    (h : ∀ H, IsHadamard H →
      injectiveMoment H A = Sparse.eval v (PairSemantics.momentVector H)) :
    familyPairMoment B A = Sparse.eval v (familyPairVector B) := by
  rw [eval_familyPairVector]
  unfold familyPairMoment familyAverage
  apply average_congr
  intro r
  apply average_congr
  intro s
  exact h _ (relativeMatrix_isHadamard B hB r s)

end MUB6.Certificate.MixedSemantics

end

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_SingleRules
attribute [-simp] _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

/-- The five equality patterns for three sampled column indices. -/
theorem single_label_three {p : ℕ} (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (A : Matrix (Fin p) (Fin 3) ℤ) :
    mixedMoment B A (fun _ => (0 : Fin 1)) =
      (1 / 36 : ℝ) * familyPairMoment B (groupedColumns A (EqualityPatterns.family3.label 0)) +
      (5 / 36 : ℝ) * familyPairMoment B (groupedColumns A (EqualityPatterns.family3.label 1)) +
      (5 / 36 : ℝ) * familyPairMoment B (groupedColumns A (EqualityPatterns.family3.label 2)) +
      (5 / 36 : ℝ) * familyPairMoment B (groupedColumns A (EqualityPatterns.family3.label 3)) +
      (5 / 9 : ℝ) * familyPairMoment B (groupedColumns A (EqualityPatterns.family3.label 4)) := by
  have h := mixedMoment_single_label_partition B hB A
    EqualityPatterns.family3 EqualityPatterns.covers3
  rw [sum_fin_five] at h
  norm_num [Fintype.card_embedding_eq, Coord, EqualityPatterns.family3,
    EqualityPatterns.blocks3, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.cons_val_four, Nat.descFactorial] at h
  exact h

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical162
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical5197 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5197 = injectiveMoment H node11 := by
  calc
    injectiveMoment H raw5197 = injectiveMoment H raw5197step0 := by
      have hz : ∀ j, raw5197 (permutation21 0) j = 0 := by decide +kernel
      have heq : raw5197step0 = (fun i j => raw5197 (permutation21 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw5197 permutation21 hz
    _ = injectiveMoment H node11 := by rfl

theorem canonical5199 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5199 = injectiveMoment H node11 := by
  rfl

theorem canonical5210 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5210 = injectiveMoment H node4 := by
  rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical239
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical7678 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7678 = injectiveMoment H node65 := by
  rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical24
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical781 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw781 = injectiveMoment H node181 := by
  calc
    injectiveMoment H raw781 = injectiveMoment H raw781step0 := by
      have heq : raw781step0 = -raw781 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw781).symm
    injectiveMoment H raw781step0 = injectiveMoment H raw781step1 := by
      have heq : raw781step1 = (fun i j => raw781step0 (permutation11 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw781step0 permutation11 permutation8
    _ = injectiveMoment H node181 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical240
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical7709 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7709 = injectiveMoment H node5 := by
  calc
    injectiveMoment H raw7709 = injectiveMoment H raw7709step0 := by
      have hz : ∀ j, raw7709 (permutation5 0) j = 0 := by decide +kernel
      have heq : raw7709step0 = (fun i j => raw7709 (permutation5 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7709 permutation5 hz
    _ = injectiveMoment H node5 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical249
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical7977 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7977 = injectiveMoment H node10 := by
  calc
    injectiveMoment H raw7977 = injectiveMoment H raw7977step0 := by
      have heq : raw7977step0 = raw7977.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7977).symm
    injectiveMoment H raw7977step0 = injectiveMoment H raw7977step1 := by
      have heq : raw7977step1 = (fun i j => raw7977step0 (permutation5 i) (permutation2 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7977step0 permutation5 permutation2
    _ = injectiveMoment H node10 := by rfl

theorem canonical7980 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7980 = injectiveMoment H node0 := by
  calc
    injectiveMoment H raw7980 = injectiveMoment H raw7980step0 := by
      have hz : ∀ j, raw7980 (permutation27 0) j = 0 := by decide +kernel
      have heq : raw7980step0 = (fun i j => raw7980 (permutation27 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7980 permutation27 hz
    injectiveMoment H raw7980step0 = injectiveMoment H raw7980step1 := by
      have hz : ∀ j, raw7980step0 (permutation7 0) j = 0 := by decide +kernel
      have heq : raw7980step1 = (fun i j => raw7980step0 (permutation7 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7980step0 permutation7 hz
    injectiveMoment H raw7980step1 = injectiveMoment H raw7980step2 := by
      have hz : ∀ j, raw7980step1 (permutation2 0) j = 0 := by decide +kernel
      have heq : raw7980step2 = (fun i j => raw7980step1 (permutation2 i.succ) j) := by ext i j; fin_cases i; fin_cases j; decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7980step1 permutation2 hz
    injectiveMoment H raw7980step2 = injectiveMoment H raw7980step3 := by
      have hz : ∀ j, raw7980step2 (permutation0 0) j = 0 := by decide +kernel
      have heq : raw7980step3 = (fun i j => raw7980step2 (permutation0 i.succ) j) := by ext i j; fin_cases i
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7980step2 permutation0 hz
    injectiveMoment H raw7980step3 = injectiveMoment H raw7980step4 := by
      have hz : ∀ i, raw7980step3 i (permutation0 0) = 0 := by decide +kernel
      have heq : raw7980step4 = (fun i j => raw7980step3 i (permutation0 j.succ)) := by ext i j; fin_cases i
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw7980step3 permutation0 hz
    _ = injectiveMoment H node0 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical27
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical895 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw895 = injectiveMoment H node10 := by
  calc
    injectiveMoment H raw895 = injectiveMoment H raw895step0 := by
      have hz : ∀ j, raw895 (permutation15 0) j = 0 := by decide +kernel
      have heq : raw895step0 = (fun i j => raw895 (permutation15 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw895 permutation15 hz
    _ = injectiveMoment H node10 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical28
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical914 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw914 = injectiveMoment H node26 := by
  rfl

theorem canonical917 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw917 = injectiveMoment H node10 := by
  rfl

theorem canonical924 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw924 = injectiveMoment H node10 := by
  calc
    injectiveMoment H raw924 = injectiveMoment H raw924step0 := by
      have heq : raw924step0 = (fun i j => raw924 (permutation4 i) (permutation1 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw924 permutation4 permutation1
    _ = injectiveMoment H node10 := by rfl

theorem canonical926 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw926 = injectiveMoment H node3 := by
  rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Moments_MomentContraction
attribute [-simp] _root_.OAI.MUB6.embedCharge_apply _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero _root_.OAI.MUB6.offDiagSum_zero _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Orthogonality relations for injective moments. The saturated relation uses
only six-row moments, even though its generating exponent array has seven rows. -/

noncomputable section
open scoped BigOperators ComplexConjugate

namespace MUB6

theorem rowMonomial_difference {q : ℕ} {H : CMatrix} (hH : IsHadamard H)
    (v w : Fin q) (t : Coord) (κ : Fin q ↪ Coord) :
    rowMonomial H (Pi.single v 1 - Pi.single w 1) t κ =
      H t (κ v) * conj (H t (κ w)) := by
  classical
  simp only [rowMonomial, Pi.sub_apply, zpow_sub₀ (unit_ne_zero (hH.1 _ _)),
    Finset.prod_div_distrib]
  have hv : (∏ j, H t (κ j) ^ ((Pi.single v 1 : Fin q → ℤ) j)) = H t (κ v) := by
    simp [Pi.single_apply]
  have hw : (∏ j, H t (κ j) ^ ((Pi.single w 1 : Fin q → ℤ) j)) = H t (κ w) := by
    simp [Pi.single_apply]
  rw [hv, hw, div_eq_mul_inv, unit_inv_eq_conj (hH.1 _ _)]

theorem rowMonomial_sum_zero {q : ℕ} {H : CMatrix} (hH : IsHadamard H)
    (v w : Fin q) (hvw : v ≠ w) (κ : Fin q ↪ Coord) :
    (∑ t, rowMonomial H (Pi.single v 1 - Pi.single w 1) t κ) = 0 := by
  simp_rw [rowMonomial_difference hH]
  have hkwv : κ w ≠ κ v := fun h => hvw (κ.injective h.symm)
  simpa only [hkwv, ite_false, if_false, mul_comm] using hH.column_orthogonal (κ w) (κ v)

theorem contractionMonomial_sum_zero {p q : ℕ} {H : CMatrix} (hH : IsHadamard H)
    (A : Matrix (Fin (p + 1)) (Fin q) ℤ) (v w : Fin q) (hvw : v ≠ w)
    (hA : A 0 = Pi.single v 1 - Pi.single w 1)
    (ρ : Fin p ↪ Coord) (κ : Fin q ↪ Coord) :
    (∑ t, contractionMonomial H A ρ κ t) = 0 := by
  simp only [contractionMonomial, hA, ← Finset.mul_sum, rowMonomial_sum_zero hH v w hvw,
    mul_zero]

theorem contractionMonomial_new {p q : ℕ} (H : CMatrix)
    (A : Matrix (Fin (p + 1)) (Fin q) ℤ)
    (ρ : Fin (p + 1) ↪ Coord) (κ : Fin q ↪ Coord) :
    contractionMonomial H A (Sampling.dropFirst ρ) κ (ρ 0) =
      exponentMonomial H A ρ κ := by
  simp only [contractionMonomial, exponentMonomial, rowMonomial, Fin.prod_univ_succ,
    Sampling.dropFirst_apply]
  exact mul_comm _ _

theorem contractionMonomial_occupied {p q : ℕ} {H : CMatrix} (hH : IsHadamard H)
    (A : Matrix (Fin (p + 1)) (Fin q) ℤ)
    (ρ : Fin p ↪ Coord) (κ : Fin q ↪ Coord) (j : Fin p) :
    contractionMonomial H A ρ κ (ρ j) = exponentMonomial H (mergeFirst A j) ρ κ := by
  classical
  simp only [contractionMonomial, exponentMonomial, mergeFirst,
    zpow_add₀ (unit_ne_zero (hH.1 _ _)), Finset.prod_mul_distrib]
  congr 1
  simp [rowMonomial]

theorem contractionIntegrand_sum_zero {p q : ℕ} {H : CMatrix} (hH : IsHadamard H)
    (A : Matrix (Fin (p + 1)) (Fin q) ℤ) (v w : Fin q) (hvw : v ≠ w)
    (hA : A 0 = Pi.single v 1 - Pi.single w 1)
    (ρ : Fin p ↪ Coord) (κ : Fin q ↪ Coord) :
    (∑ t, contractionIntegrand H A ρ κ t) = 0 := by
  simp only [contractionIntegrand, div_eq_mul_inv, ← Finset.sum_mul, Finset.sum_add_distrib,
    ← Complex.re_sum, contractionMonomial_sum_zero hH A v w hvw hA,
    contractionMonomial_sum_zero hH.transpose A v w hvw hA, Complex.zero_re,
    zero_add, zero_mul]

/-- The coefficient is 6-p, where p is the number of rows other than the
contracted row. Equivalently it is 7 minus the original row count. -/
theorem injectiveMoment_first_row_contraction {p q : ℕ} (hp : p < 6)
    {H : CMatrix} (hH : IsHadamard H)
    (A : Matrix (Fin (p + 1)) (Fin q) ℤ) (v w : Fin q) (hvw : v ≠ w)
    (hA : A 0 = Pi.single v 1 - Pi.single w 1) :
    ((6 - p : ℕ) : ℝ) * injectiveMoment H A +
      (∑ j, injectiveMoment H (mergeFirst A j)) = 0 := by
  have ht (κ : Fin q ↪ Coord) := Sampling.average_contraction hp
    (fun ρ t => contractionIntegrand H A ρ κ t)
    (fun ρ => contractionIntegrand_sum_zero hH A v w hvw hA ρ κ)
  have hav : average (fun κ : Fin q ↪ Coord =>
      ((6 - p : ℕ) : ℝ) *
        average (fun ρ : Fin (p + 1) ↪ Coord =>
          contractionIntegrand H A (Sampling.dropFirst ρ) κ (ρ 0)) +
        ∑ j : Fin p, average (fun ρ : Fin p ↪ Coord =>
          contractionIntegrand H A ρ κ (ρ j))) = 0 := by
    simp only [ht, average_zero]
  rw [average_add, average_mul, average_sum] at hav
  simp only [contractionIntegrand, contractionMonomial_new,
    contractionMonomial_occupied hH, contractionMonomial_occupied hH.transpose] at hav
  simp only [injectiveMoment_reverse_iterated] at hav
  exact hav

end MUB6

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical161
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical5169 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5169 = injectiveMoment H node4 := by
  clear _hH
  calc
    injectiveMoment H raw5169 = injectiveMoment H raw5169step0 := by
      have hz : ∀ j, raw5169 (permutation21 0) j = 0 := by decide +kernel
      have heq : raw5169step0 = (fun i j => raw5169 (permutation21 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw5169 permutation21 hz
    injectiveMoment H raw5169step0 = injectiveMoment H raw5169step1 := by
      have hz : ∀ j, raw5169step0 (permutation5 0) j = 0 := by decide +kernel
      have heq : raw5169step1 = (fun i j => raw5169step0 (permutation5 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw5169step0 permutation5 hz
    _ = injectiveMoment H node4 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical170
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical5458 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5458 = injectiveMoment H node10 := by
  calc
    injectiveMoment H raw5458 = injectiveMoment H raw5458step0 := by
      have heq : raw5458step0 = raw5458.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5458).symm
    injectiveMoment H raw5458step0 = injectiveMoment H raw5458step1 := by
      have heq : raw5458step1 = (fun i j => raw5458step0 (permutation6 i) (permutation2 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5458step0 permutation6 permutation2
    _ = injectiveMoment H node10 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical187
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical5990 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5990 = injectiveMoment H node10 := by
  calc
    injectiveMoment H raw5990 = injectiveMoment H raw5990step0 := by
      have heq : raw5990step0 = raw5990.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5990).symm
    injectiveMoment H raw5990step0 = injectiveMoment H raw5990step1 := by
      have heq : raw5990step1 = (fun i j => raw5990step0 (permutation7 i) (permutation2 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5990step0 permutation7 permutation2
    _ = injectiveMoment H node10 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical215
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical6885 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6885 = injectiveMoment H node11 := by
  calc
    injectiveMoment H raw6885 = injectiveMoment H raw6885step0 := by
      have heq : raw6885step0 = raw6885.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6885).symm
    injectiveMoment H raw6885step0 = injectiveMoment H raw6885step1 := by
      have heq : raw6885step1 = (fun i j => raw6885step0 (permutation7 i) (permutation2 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6885step0 permutation7 permutation2
    _ = injectiveMoment H node11 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical241
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical7718 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7718 = injectiveMoment H node5 := by
  rfl

theorem canonical7731 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7731 = injectiveMoment H node65 := by
  calc
    injectiveMoment H raw7731 = injectiveMoment H raw7731step0 := by
      have heq : raw7731step0 = (fun i j => raw7731 (permutation11 i) (permutation1 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7731 permutation11 permutation1
    _ = injectiveMoment H node65 := by rfl

theorem canonical7735 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7735 = injectiveMoment H node5 := by
  calc
    injectiveMoment H raw7735 = injectiveMoment H raw7735step0 := by
      have hz : ∀ j, raw7735 (permutation7 0) j = 0 := by decide +kernel
      have heq : raw7735step0 = (fun i j => raw7735 (permutation7 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7735 permutation7 hz
    _ = injectiveMoment H node5 := by rfl

theorem canonical7738 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7738 = injectiveMoment H node65 := by
  calc
    injectiveMoment H raw7738 = injectiveMoment H raw7738step0 := by
      have heq : raw7738step0 = (fun i j => raw7738 (permutation13 i) (permutation1 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7738 permutation13 permutation1
    _ = injectiveMoment H node65 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical256
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical8215 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8215 = injectiveMoment H node4 := by
  calc
    injectiveMoment H raw8215 = injectiveMoment H raw8215step0 := by
      have hz : ∀ i, raw8215 i (permutation3 0) = 0 := by decide +kernel
      have heq : raw8215step0 = (fun i j => raw8215 i (permutation3 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw8215 permutation3 hz
    _ = injectiveMoment H node4 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical279
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical8946 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8946 = injectiveMoment H node0 := by
  calc
    injectiveMoment H raw8946 = injectiveMoment H raw8946step0 := by
      have hz : ∀ j, raw8946 (permutation0 0) j = 0 := by decide +kernel
      have heq : raw8946step0 = (fun i j => raw8946 (permutation0 i.succ) j) := by ext i j; fin_cases i
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw8946 permutation0 hz
    injectiveMoment H raw8946step0 = injectiveMoment H raw8946step1 := by
      have hz : ∀ i, raw8946step0 i (permutation2 0) = 0 := by decide +kernel
      have heq : raw8946step1 = (fun i j => raw8946step0 i (permutation2 j.succ)) := by ext i j; fin_cases i
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw8946step0 permutation2 hz
    injectiveMoment H raw8946step1 = injectiveMoment H raw8946step2 := by
      have hz : ∀ i, raw8946step1 i (permutation0 0) = 0 := by decide +kernel
      have heq : raw8946step2 = (fun i j => raw8946step1 i (permutation0 j.succ)) := by ext i j; fin_cases i
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw8946step1 permutation0 hz
    _ = injectiveMoment H node0 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound0
attribute [-simp] _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_toRational _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

theorem sound0 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node0 = Sparse.eval value0 (momentVector H) := by
  have hc : momentVector H 0 = injectiveMoment H node0 := rfl
  simp [value0, Sparse.eval, hc]

theorem sound3 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node3 = Sparse.eval value3 (momentVector H) := by
  have hc : momentVector H 2 = injectiveMoment H node3 := rfl
  simp [value3, Sparse.eval, hc]

theorem sound4 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node4 = Sparse.eval value4 (momentVector H) := by
  have hc : momentVector H 1 = injectiveMoment H node4 := rfl
  simp [value4, Sparse.eval, hc]

theorem sound5 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node5 = Sparse.eval value5 (momentVector H) := by
  have heq : pivotMatrix5 = (fun u v => node5 (pivotPermutation5 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node5 = injectiveMoment H pivotMatrix5 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix5 0 = Pi.single (1 : Fin 2) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 1 < 6) hH pivotMatrix5 1 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix5 (0 : Fin 1)) =
      Sparse.eval value0 (momentVector H) := by
    have heq : mergeFirst pivotMatrix5 (0 : Fin 1) = raw8946 := by ext i j; fin_cases i; fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical8946 hH).trans (sound0 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (5 : ℝ) * injectiveMoment H node5 + (injectiveMoment H (mergeFirst pivotMatrix5 (0 : Fin 1))) = 0 at hc
  rw [hm0] at hc
  norm_num [value5, value0, Sparse.eval] at hc ⊢
  linarith

theorem sound10 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node10 = Sparse.eval value10 (momentVector H) := by
  have heq : pivotMatrix10 = (fun u v => node10 (pivotPermutation10 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node10 = injectiveMoment H pivotMatrix10 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix10 0 = Pi.single (0 : Fin 2) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 2 < 6) hH pivotMatrix10 0 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix10 (0 : Fin 2)) =
      Sparse.eval value4 (momentVector H) := by
    have heq : mergeFirst pivotMatrix10 (0 : Fin 2) = raw5210 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical5210 hH).trans (sound4 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix10 (1 : Fin 2)) =
      Sparse.eval value3 (momentVector H) := by
    have heq : mergeFirst pivotMatrix10 (1 : Fin 2) = raw926 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical926 hH).trans (sound3 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (4 : ℝ) * injectiveMoment H node10 + (injectiveMoment H (mergeFirst pivotMatrix10 (0 : Fin 2)) + (injectiveMoment H (mergeFirst pivotMatrix10 (1 : Fin 2)))) = 0 at hc
  rw [hm0, hm1] at hc
  norm_num [value10, value3, value4, Sparse.eval] at hc ⊢
  linarith

theorem sound11 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node11 = Sparse.eval value11 (momentVector H) := by
  have heq : pivotMatrix11 = (fun u v => node11 (pivotPermutation11 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node11 = injectiveMoment H pivotMatrix11 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix11 0 = Pi.single (0 : Fin 2) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 2 < 6) hH pivotMatrix11 0 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix11 (0 : Fin 2)) =
      Sparse.eval value5 (momentVector H) := by
    have heq : mergeFirst pivotMatrix11 (0 : Fin 2) = raw7718 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical7718 hH).trans (sound5 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix11 (1 : Fin 2)) =
      Sparse.eval value4 (momentVector H) := by
    have heq : mergeFirst pivotMatrix11 (1 : Fin 2) = raw5210 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical5210 hH).trans (sound4 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (4 : ℝ) * injectiveMoment H node11 + (injectiveMoment H (mergeFirst pivotMatrix11 (0 : Fin 2)) + (injectiveMoment H (mergeFirst pivotMatrix11 (1 : Fin 2)))) = 0 at hc
  rw [hm0, hm1] at hc
  norm_num [value11, value4, value5, Sparse.eval] at hc ⊢
  linarith

theorem sound26 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node26 = Sparse.eval value26 (momentVector H) := by
  have heq : pivotMatrix26 = (fun u v => node26 (pivotPermutation26 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node26 = injectiveMoment H pivotMatrix26 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix26 0 = Pi.single (0 : Fin 2) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix26 0 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix26 (0 : Fin 3)) =
      Sparse.eval value11 (momentVector H) := by
    have heq : mergeFirst pivotMatrix26 (0 : Fin 3) = raw5199 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical5199 hH).trans (sound11 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix26 (1 : Fin 3)) =
      Sparse.eval value10 (momentVector H) := by
    have heq : mergeFirst pivotMatrix26 (1 : Fin 3) = raw924 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical924 hH).trans (sound10 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix26 (2 : Fin 3)) =
      Sparse.eval value10 (momentVector H) := by
    have heq : mergeFirst pivotMatrix26 (2 : Fin 3) = raw917 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical917 hH).trans (sound10 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node26 + (injectiveMoment H (mergeFirst pivotMatrix26 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix26 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix26 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value26, value10, value11, Sparse.eval] at hc ⊢
  linarith

theorem sound36 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node36 = Sparse.eval value36 (momentVector H) := by
  have hc : momentVector H 3 = injectiveMoment H node36 := rfl
  simp [value36, Sparse.eval, hc]

theorem sound56 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node56 = Sparse.eval value56 (momentVector H) := by
  have heq : pivotMatrix56 = (fun u v => node56 (pivotPermutation56 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node56 = injectiveMoment H pivotMatrix56 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix56 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 2 < 6) hH pivotMatrix56 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix56 (0 : Fin 2)) =
      Sparse.eval value11 (momentVector H) := by
    have heq : mergeFirst pivotMatrix56 (0 : Fin 2) = raw6885 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical6885 hH).trans (sound11 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix56 (1 : Fin 2)) =
      Sparse.eval value10 (momentVector H) := by
    have heq : mergeFirst pivotMatrix56 (1 : Fin 2) = raw5990 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical5990 hH).trans (sound10 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (4 : ℝ) * injectiveMoment H node56 + (injectiveMoment H (mergeFirst pivotMatrix56 (0 : Fin 2)) + (injectiveMoment H (mergeFirst pivotMatrix56 (1 : Fin 2)))) = 0 at hc
  rw [hm0, hm1] at hc
  norm_num [value56, value10, value11, Sparse.eval] at hc ⊢
  linarith

theorem sound57 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node57 = Sparse.eval value57 (momentVector H) := by
  have heq : pivotMatrix57 = (fun u v => node57 (pivotPermutation57 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node57 = injectiveMoment H pivotMatrix57 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix57 0 = Pi.single (0 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 2 < 6) hH pivotMatrix57 0 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix57 (0 : Fin 2)) =
      Sparse.eval value4 (momentVector H) := by
    have heq : mergeFirst pivotMatrix57 (0 : Fin 2) = raw8215 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical8215 hH).trans (sound4 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix57 (1 : Fin 2)) =
      Sparse.eval value10 (momentVector H) := by
    have heq : mergeFirst pivotMatrix57 (1 : Fin 2) = raw5990 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical5990 hH).trans (sound10 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (4 : ℝ) * injectiveMoment H node57 + (injectiveMoment H (mergeFirst pivotMatrix57 (0 : Fin 2)) + (injectiveMoment H (mergeFirst pivotMatrix57 (1 : Fin 2)))) = 0 at hc
  rw [hm0, hm1] at hc
  norm_num [value57, value10, value4, Sparse.eval] at hc ⊢
  linarith

theorem sound62 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node62 = Sparse.eval value62 (momentVector H) := by
  have heq : pivotMatrix62 = (fun u v => node62 (pivotPermutation62 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node62 = injectiveMoment H pivotMatrix62 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix62 0 = Pi.single (0 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 2 < 6) hH pivotMatrix62 0 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix62 (0 : Fin 2)) =
      Sparse.eval value4 (momentVector H) := by
    have heq : mergeFirst pivotMatrix62 (0 : Fin 2) = raw8215 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical8215 hH).trans (sound4 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix62 (1 : Fin 2)) =
      Sparse.eval value11 (momentVector H) := by
    have heq : mergeFirst pivotMatrix62 (1 : Fin 2) = raw6885 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical6885 hH).trans (sound11 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (4 : ℝ) * injectiveMoment H node62 + (injectiveMoment H (mergeFirst pivotMatrix62 (0 : Fin 2)) + (injectiveMoment H (mergeFirst pivotMatrix62 (1 : Fin 2)))) = 0 at hc
  rw [hm0, hm1] at hc
  norm_num [value62, value11, value4, Sparse.eval] at hc ⊢
  linarith

theorem sound63 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node63 = Sparse.eval value63 (momentVector H) := by
  have heq : pivotMatrix63 = (fun u v => node63.transpose (pivotPermutation63 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node63 = injectiveMoment H pivotMatrix63 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix63 0 = Pi.single (2 : Fin 3) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 2 < 6) hH pivotMatrix63 2 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix63 (0 : Fin 2)) =
      Sparse.eval value10 (momentVector H) := by
    have heq : mergeFirst pivotMatrix63 (0 : Fin 2) = raw5458 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical5458 hH).trans (sound10 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix63 (1 : Fin 2)) =
      Sparse.eval value10 (momentVector H) := by
    have heq : mergeFirst pivotMatrix63 (1 : Fin 2) = raw7977 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical7977 hH).trans (sound10 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (4 : ℝ) * injectiveMoment H node63 + (injectiveMoment H (mergeFirst pivotMatrix63 (0 : Fin 2)) + (injectiveMoment H (mergeFirst pivotMatrix63 (1 : Fin 2)))) = 0 at hc
  rw [hm0, hm1] at hc
  norm_num [value63, value10, Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical129
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical4134 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4134 = injectiveMoment H node62 := by
  calc
    injectiveMoment H raw4134 = injectiveMoment H raw4134step0 := by
      have heq : raw4134step0 = (fun i j => raw4134 (permutation7 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4134 permutation7 permutation6
    _ = injectiveMoment H node62 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical25
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical808 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw808 = injectiveMoment H node176 := by
  calc
    injectiveMoment H raw808 = injectiveMoment H raw808step0 := by
      have heq : raw808step0 = -raw808 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw808).symm
    injectiveMoment H raw808step0 = injectiveMoment H raw808step1 := by
      have heq : raw808step1 = (fun i j => raw808step0 (permutation9 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw808step0 permutation9 permutation8
    _ = injectiveMoment H node176 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical89
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical2861 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2861 = injectiveMoment H node63 := by
  calc
    injectiveMoment H raw2861 = injectiveMoment H raw2861step0 := by
      have heq : raw2861step0 = raw2861.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2861).symm
    injectiveMoment H raw2861step0 = injectiveMoment H raw2861step1 := by
      have heq : raw2861step1 = (fun i j => raw2861step0 (permutation6 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2861step0 permutation6 permutation5
    _ = injectiveMoment H node63 := by rfl

theorem canonical2862 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2862 = injectiveMoment H node56 := by
  calc
    injectiveMoment H raw2862 = injectiveMoment H raw2862step0 := by
      have heq : raw2862step0 = (fun i j => raw2862 (permutation3 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2862 permutation3 permutation5
    _ = injectiveMoment H node56 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound1
attribute [-simp] _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_toRational _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

theorem sound65 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node65 = Sparse.eval value65 (momentVector H) := by
  have heq : pivotMatrix65 = (fun u v => node65 (pivotPermutation65 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node65 = injectiveMoment H pivotMatrix65 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix65 0 = Pi.single (1 : Fin 2) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix65 1 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix65 (0 : Fin 3)) =
      Sparse.eval value11 (momentVector H) := by
    have heq : mergeFirst pivotMatrix65 (0 : Fin 3) = raw5199 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical5199 hH).trans (sound11 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix65 (1 : Fin 3)) =
      Sparse.eval value5 (momentVector H) := by
    have heq : mergeFirst pivotMatrix65 (1 : Fin 3) = raw7709 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical7709 hH).trans (sound5 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix65 (2 : Fin 3)) =
      Sparse.eval value5 (momentVector H) := by
    have heq : mergeFirst pivotMatrix65 (2 : Fin 3) = raw7735 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical7735 hH).trans (sound5 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node65 + (injectiveMoment H (mergeFirst pivotMatrix65 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix65 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix65 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value65, value11, value5, Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical130
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical4160 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4160 = injectiveMoment H node62 := by
  calc
    injectiveMoment H raw4160 = injectiveMoment H raw4160step0 := by
      have heq : raw4160step0 = -raw4160 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4160).symm
    injectiveMoment H raw4160step0 = injectiveMoment H raw4160step1 := by
      have heq : raw4160step1 = (fun i j => raw4160step0 (permutation7 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4160step0 permutation7 permutation5
    _ = injectiveMoment H node62 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical154
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical4943 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4943 = injectiveMoment H node227 := by
  rfl

theorem canonical4950 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4950 = injectiveMoment H node11 := by
  calc
    injectiveMoment H raw4950 = injectiveMoment H raw4950step0 := by
      have heq : raw4950step0 = raw4950.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4950).symm
    injectiveMoment H raw4950step0 = injectiveMoment H raw4950step1 := by
      have hz : ∀ i, raw4950step0 i (permutation5 0) = 0 := by decide +kernel
      have heq : raw4950step1 = (fun i j => raw4950step0 i (permutation5 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw4950step0 permutation5 hz
    _ = injectiveMoment H node11 := by rfl

theorem canonical4956 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4956 = injectiveMoment H node62 := by
  calc
    injectiveMoment H raw4956 = injectiveMoment H raw4956step0 := by
      have heq : raw4956step0 = -raw4956 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4956).symm
    injectiveMoment H raw4956step0 = injectiveMoment H raw4956step1 := by
      have heq : raw4956step1 = (fun i j => raw4956step0 (permutation4 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4956step0 permutation4 permutation8
    _ = injectiveMoment H node62 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical88
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical2823 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2823 = injectiveMoment H node57 := by
  calc
    injectiveMoment H raw2823 = injectiveMoment H raw2823step0 := by
      have heq : raw2823step0 = (fun i j => raw2823 (permutation4 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2823 permutation4 permutation5
    _ = injectiveMoment H node57 := by rfl

theorem canonical2845 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2845 = injectiveMoment H node36 := by
  rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound2
attribute [-simp] _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_toRational _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

theorem sound176 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node176 = Sparse.eval value176 (momentVector H) := by
  have heq : pivotMatrix176 = (fun u v => node176 (pivotPermutation176 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node176 = injectiveMoment H pivotMatrix176 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix176 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix176 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix176 (0 : Fin 3)) =
      Sparse.eval value62 (momentVector H) := by
    have heq : mergeFirst pivotMatrix176 (0 : Fin 3) = raw4134 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical4134 hH).trans (sound62 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix176 (1 : Fin 3)) =
      Sparse.eval value36 (momentVector H) := by
    have heq : mergeFirst pivotMatrix176 (1 : Fin 3) = raw2845 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical2845 hH).trans (sound36 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix176 (2 : Fin 3)) =
      Sparse.eval value57 (momentVector H) := by
    have heq : mergeFirst pivotMatrix176 (2 : Fin 3) = raw2823 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical2823 hH).trans (sound57 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node176 + (injectiveMoment H (mergeFirst pivotMatrix176 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix176 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix176 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value176, value36, value57, value62, Sparse.eval] at hc ⊢
  linarith

theorem sound181 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node181 = Sparse.eval value181 (momentVector H) := by
  have heq : pivotMatrix181 = (fun u v => node181 (pivotPermutation181 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node181 = injectiveMoment H pivotMatrix181 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix181 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix181 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix181 (0 : Fin 3)) =
      Sparse.eval value62 (momentVector H) := by
    have heq : mergeFirst pivotMatrix181 (0 : Fin 3) = raw4160 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical4160 hH).trans (sound62 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix181 (1 : Fin 3)) =
      Sparse.eval value56 (momentVector H) := by
    have heq : mergeFirst pivotMatrix181 (1 : Fin 3) = raw2862 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical2862 hH).trans (sound56 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix181 (2 : Fin 3)) =
      Sparse.eval value63 (momentVector H) := by
    have heq : mergeFirst pivotMatrix181 (2 : Fin 3) = raw2861 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical2861 hH).trans (sound63 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node181 + (injectiveMoment H (mergeFirst pivotMatrix181 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix181 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix181 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value181, value56, value62, value63, Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound3
attribute [-simp] _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_toRational _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

theorem sound227 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node227 = Sparse.eval value227 (momentVector H) := by
  have heq : pivotMatrix227 = (fun u v => node227 (pivotPermutation227 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node227 = injectiveMoment H pivotMatrix227 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix227 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix227 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix227 (0 : Fin 3)) =
      Sparse.eval value62 (momentVector H) := by
    have heq : mergeFirst pivotMatrix227 (0 : Fin 3) = raw4134 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical4134 hH).trans (sound62 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix227 (1 : Fin 3)) =
      Sparse.eval value11 (momentVector H) := by
    have heq : mergeFirst pivotMatrix227 (1 : Fin 3) = raw4950 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical4950 hH).trans (sound11 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix227 (2 : Fin 3)) =
      Sparse.eval value62 (momentVector H) := by
    have heq : mergeFirst pivotMatrix227 (2 : Fin 3) = raw4956 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical4956 hH).trans (sound62 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node227 + (injectiveMoment H (mergeFirst pivotMatrix227 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix227 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix227 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value227, value11, value62, Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_SingleGroup24
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singlePair404 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node404 node404Labels = Sparse.eval singlePairValue404 (familyPairVector B) := by
  have hp := single_label_three B hB node404
  have hl : node404Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node404 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node404 (EqualityPatterns.family3.label 0) = PairSemantics.raw7980 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node404 PairSemantics.raw7980; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7980 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node404 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value11 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node404 (EqualityPatterns.family3.label 1) = PairSemantics.raw5197 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node404 PairSemantics.raw5197; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5197 hH).trans (PairSemantics.sound11 hH)
  have hm2 : familyPairMoment B (groupedColumns node404 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value65 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node404 (EqualityPatterns.family3.label 2) = PairSemantics.raw7678 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node404 PairSemantics.raw7678; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7678 hH).trans (PairSemantics.sound65 hH)
  have hm3 : familyPairMoment B (groupedColumns node404 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value10 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node404 (EqualityPatterns.family3.label 3) = PairSemantics.raw895 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node404 PairSemantics.raw895; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical895 hH).trans (PairSemantics.sound10 hH)
  have hm4 : familyPairMoment B (groupedColumns node404 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value181 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node404 (EqualityPatterns.family3.label 4) = PairSemantics.raw781 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node404 PairSemantics.raw781; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical781 hH).trans (PairSemantics.sound181 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue404, PairSemantics.value0, PairSemantics.value10, PairSemantics.value11, PairSemantics.value65, PairSemantics.value181, Sparse.eval] at hp ⊢
  linarith only [hp]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_SingleGroup25
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singlePair416 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node416 node416Labels = Sparse.eval singlePairValue416 (familyPairVector B) := by
  have hp := single_label_three B hB node416
  have hl : node416Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node416 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node416 (EqualityPatterns.family3.label 0) = PairSemantics.raw7980 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node416 PairSemantics.raw7980; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7980 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node416 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value4 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node416 (EqualityPatterns.family3.label 1) = PairSemantics.raw5169 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node416 PairSemantics.raw5169; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5169 hH).trans (PairSemantics.sound4 hH)
  have hm2 : familyPairMoment B (groupedColumns node416 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value65 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node416 (EqualityPatterns.family3.label 2) = PairSemantics.raw7738 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node416 PairSemantics.raw7738; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7738 hH).trans (PairSemantics.sound65 hH)
  have hm3 : familyPairMoment B (groupedColumns node416 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value26 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node416 (EqualityPatterns.family3.label 3) = PairSemantics.raw914 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node416 PairSemantics.raw914; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical914 hH).trans (PairSemantics.sound26 hH)
  have hm4 : familyPairMoment B (groupedColumns node416 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value176 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node416 (EqualityPatterns.family3.label 4) = PairSemantics.raw808 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node416 PairSemantics.raw808; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical808 hH).trans (PairSemantics.sound176 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue416, PairSemantics.value0, PairSemantics.value4, PairSemantics.value26, PairSemantics.value65, PairSemantics.value176, Sparse.eval] at hp ⊢
  linarith only [hp]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_SingleGroup32
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singlePair527 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node527 node527Labels = Sparse.eval singlePairValue527 (familyPairVector B) := by
  have hp := single_label_three B hB node527
  have hl : node527Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node527 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node527 (EqualityPatterns.family3.label 0) = PairSemantics.raw7980 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node527 PairSemantics.raw7980; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7980 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node527 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value65 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node527 (EqualityPatterns.family3.label 1) = PairSemantics.raw7678 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node527 PairSemantics.raw7678; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7678 hH).trans (PairSemantics.sound65 hH)
  have hm2 : familyPairMoment B (groupedColumns node527 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value65 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node527 (EqualityPatterns.family3.label 2) = PairSemantics.raw7731 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node527 PairSemantics.raw7731; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7731 hH).trans (PairSemantics.sound65 hH)
  have hm3 : familyPairMoment B (groupedColumns node527 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value4 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node527 (EqualityPatterns.family3.label 3) = PairSemantics.raw5169 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node527 PairSemantics.raw5169; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5169 hH).trans (PairSemantics.sound4 hH)
  have hm4 : familyPairMoment B (groupedColumns node527 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value227 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node527 (EqualityPatterns.family3.label 4) = PairSemantics.raw4943 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node527 PairSemantics.raw4943; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical4943 hH).trans (PairSemantics.sound227 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue527, PairSemantics.value0, PairSemantics.value4, PairSemantics.value65, PairSemantics.value227, Sparse.eval] at hp ⊢
  linarith only [hp]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons43
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singleton2767 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node2767 node2767Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node404 node404Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw270 singletonSmall2767
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall2767) = raw270Labels := by decide +kernel
  rw [hl, canonical270 B hB] at h
  have hc0 : mixedMoment B raw270 (Fin.cases (0 : Fin 1) singletonSmall2767) =
      mixedMoment B node404 node404Labels := by
    have ha : raw270 = raw271 := by apply Matrix.ext; unfold raw270 raw271; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall2767 = raw271Labels := by decide +kernel
    rw [ha, hj, canonical271 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

theorem singleton2784 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node2784 node2784Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node416 node416Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw282 singletonSmall2784
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall2784) = raw282Labels := by decide +kernel
  rw [hl, canonical282 B hB] at h
  have hc0 : mixedMoment B raw282 (Fin.cases (0 : Fin 1) singletonSmall2784) =
      mixedMoment B node416 node416Labels := by
    have ha : raw282 = raw283 := by apply Matrix.ext; unfold raw282 raw283; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall2784 = raw283Labels := by decide +kernel
    rw [ha, hj, canonical283 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons62
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singleton4014 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4014 node4014Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node527 node527Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw626 singletonSmall4014
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4014) = raw626Labels := by decide +kernel
  rw [hl, canonical626 B hB] at h
  have hc0 : mixedMoment B raw626 (Fin.cases (0 : Fin 1) singletonSmall4014) =
      mixedMoment B node527 node527Labels := by
    have ha : raw626 = raw627 := by apply Matrix.ext; unfold raw626 raw627; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall4014 = raw627Labels := by decide +kernel
    rw [ha, hj, canonical627 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
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

theorem singleton4424 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4424 node4424Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1005 node1005Labels + mixedMoment B node1623 node1623Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1236 singletonSmall4424
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4424) = raw1236Labels := by decide +kernel
  rw [hl, canonical1236 B hB] at h
  have hc0 : mixedMoment B raw1236 (Fin.cases (0 : Fin 2) singletonSmall4424) =
      mixedMoment B node1005 node1005Labels := by
    have ha : raw1236 = raw1237 := by apply Matrix.ext; unfold raw1236 raw1237; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4424 = raw1237Labels := by decide +kernel
    rw [ha, hj, canonical1237 B hB]
  have hc1 : mixedMoment B raw1236 (Fin.cases (1 : Fin 2) singletonSmall4424) =
      mixedMoment B node1623 node1623Labels := by
    have ha : raw1236 = raw1238 := by apply Matrix.ext; unfold raw1236 raw1238; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4424 = raw1238Labels := by decide +kernel
    rw [ha, hj, canonical1238 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4428 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4428 node4428Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1009 node1009Labels + mixedMoment B node1630 node1630Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1239 singletonSmall4428
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4428) = raw1239Labels := by decide +kernel
  rw [hl, canonical1239 B hB] at h
  have hc0 : mixedMoment B raw1239 (Fin.cases (0 : Fin 2) singletonSmall4428) =
      mixedMoment B node1009 node1009Labels := by
    have ha : raw1239 = raw1240 := by apply Matrix.ext; unfold raw1239 raw1240; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4428 = raw1240Labels := by decide +kernel
    rw [ha, hj, canonical1240 B hB]
  have hc1 : mixedMoment B raw1239 (Fin.cases (1 : Fin 2) singletonSmall4428) =
      mixedMoment B node1630 node1630Labels := by
    have ha : raw1239 = raw1241 := by apply Matrix.ext; unfold raw1239 raw1241; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4428 = raw1241Labels := by decide +kernel
    rw [ha, hj, canonical1241 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4431 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4431 node4431Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1012 node1012Labels + mixedMoment B node1627 node1627Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1242 singletonSmall4431
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4431) = raw1242Labels := by decide +kernel
  rw [hl, canonical1242 B hB] at h
  have hc0 : mixedMoment B raw1242 (Fin.cases (0 : Fin 2) singletonSmall4431) =
      mixedMoment B node1012 node1012Labels := by
    have ha : raw1242 = raw1243 := by apply Matrix.ext; unfold raw1242 raw1243; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4431 = raw1243Labels := by decide +kernel
    rw [ha, hj, canonical1243 B hB]
  have hc1 : mixedMoment B raw1242 (Fin.cases (1 : Fin 2) singletonSmall4431) =
      mixedMoment B node1627 node1627Labels := by
    have ha : raw1242 = raw1244 := by apply Matrix.ext; unfold raw1242 raw1244; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4431 = raw1244Labels := by decide +kernel
    rw [ha, hj, canonical1244 B hB]
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

theorem singleton5000 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5000 node5000Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2385 node2385Labels + mixedMoment B node3353 node3353Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2013 singletonSmall5000
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5000) = raw2013Labels := by decide +kernel
  rw [hl, canonical2013 B hB] at h
  have hc0 : mixedMoment B raw2013 (Fin.cases (0 : Fin 2) singletonSmall5000) =
      mixedMoment B node2385 node2385Labels := by
    have ha : raw2013 = raw2014 := by apply Matrix.ext; unfold raw2013 raw2014; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5000 = raw2014Labels := by decide +kernel
    rw [ha, hj, canonical2014 B hB]
  have hc1 : mixedMoment B raw2013 (Fin.cases (1 : Fin 2) singletonSmall5000) =
      mixedMoment B node3353 node3353Labels := by
    have ha : raw2013 = raw2015 := by apply Matrix.ext; unfold raw2013 raw2015; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5000 = raw2015Labels := by decide +kernel
    rw [ha, hj, canonical2015 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton5014 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5014 node5014Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2399 node2399Labels + mixedMoment B node2467 node2467Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2022 singletonSmall5014
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5014) = raw2022Labels := by decide +kernel
  rw [hl, canonical2022 B hB] at h
  have hc0 : mixedMoment B raw2022 (Fin.cases (0 : Fin 2) singletonSmall5014) =
      mixedMoment B node2399 node2399Labels := by
    have ha : raw2022 = raw2023 := by apply Matrix.ext; unfold raw2022 raw2023; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5014 = raw2023Labels := by decide +kernel
    rw [ha, hj, canonical2023 B hB]
  have hc1 : mixedMoment B raw2022 (Fin.cases (1 : Fin 2) singletonSmall5014) =
      mixedMoment B node2467 node2467Labels := by
    have ha : raw2022 = raw2024 := by apply Matrix.ext; unfold raw2022 raw2024; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5014 = raw2024Labels := by decide +kernel
    rw [ha, hj, canonical2024 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton5018 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5018 node5018Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2404 node2404Labels + mixedMoment B node3357 node3357Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2028 singletonSmall5018
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5018) = raw2028Labels := by decide +kernel
  rw [hl, canonical2028 B hB] at h
  have hc0 : mixedMoment B raw2028 (Fin.cases (0 : Fin 2) singletonSmall5018) =
      mixedMoment B node2404 node2404Labels := by
    have ha : raw2028 = raw2029 := by apply Matrix.ext; unfold raw2028 raw2029; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5018 = raw2029Labels := by decide +kernel
    rw [ha, hj, canonical2029 B hB]
  have hc1 : mixedMoment B raw2028 (Fin.cases (1 : Fin 2) singletonSmall5018) =
      mixedMoment B node3357 node3357Labels := by
    have ha : raw2028 = raw2030 := by apply Matrix.ext; unfold raw2028 raw2030; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5018 = raw2030Labels := by decide +kernel
    rw [ha, hj, canonical2030 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton5021 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5021 node5021Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2407 node2407Labels + mixedMoment B node3360 node3360Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2031 singletonSmall5021
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5021) = raw2031Labels := by decide +kernel
  rw [hl, canonical2031 B hB] at h
  have hc0 : mixedMoment B raw2031 (Fin.cases (0 : Fin 2) singletonSmall5021) =
      mixedMoment B node2407 node2407Labels := by
    have ha : raw2031 = raw2032 := by apply Matrix.ext; unfold raw2031 raw2032; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5021 = raw2032Labels := by decide +kernel
    rw [ha, hj, canonical2032 B hB]
  have hc1 : mixedMoment B raw2031 (Fin.cases (1 : Fin 2) singletonSmall5021) =
      mixedMoment B node3360 node3360Labels := by
    have ha : raw2031 = raw2033 := by apply Matrix.ext; unfold raw2031 raw2033; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5021 = raw2033Labels := by decide +kernel
    rw [ha, hj, canonical2033 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton5023 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5023 node5023Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2410 node2410Labels + mixedMoment B node2410 node2410Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2034 singletonSmall5023
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5023) = raw2034Labels := by decide +kernel
  rw [hl, canonical2034 B hB] at h
  have hc0 : mixedMoment B raw2034 (Fin.cases (0 : Fin 2) singletonSmall5023) =
      mixedMoment B node2410 node2410Labels := by
    have ha : raw2034 = raw2035 := by apply Matrix.ext; unfold raw2034 raw2035; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5023 = raw2035Labels := by decide +kernel
    rw [ha, hj, canonical2035 B hB]
  have hc1 : mixedMoment B raw2034 (Fin.cases (1 : Fin 2) singletonSmall5023) =
      mixedMoment B node2410 node2410Labels := by
    have ha : raw2034 = raw2036 := by apply Matrix.ext; unfold raw2034 raw2036; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5023 = raw2036Labels := by decide +kernel
    rw [ha, hj, canonical2036 B hB]
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

theorem singleton5059 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5059 node5059Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2462 node2462Labels + mixedMoment B node3436 node3436Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2085 singletonSmall5059
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5059) = raw2085Labels := by decide +kernel
  rw [hl, canonical2085 B hB] at h
  have hc0 : mixedMoment B raw2085 (Fin.cases (0 : Fin 2) singletonSmall5059) =
      mixedMoment B node2462 node2462Labels := by
    have ha : raw2085 = raw2086 := by apply Matrix.ext; unfold raw2085 raw2086; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5059 = raw2086Labels := by decide +kernel
    rw [ha, hj, canonical2086 B hB]
  have hc1 : mixedMoment B raw2085 (Fin.cases (1 : Fin 2) singletonSmall5059) =
      mixedMoment B node3436 node3436Labels := by
    have ha : raw2085 = raw2087 := by apply Matrix.ext; unfold raw2085 raw2087; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5059 = raw2087Labels := by decide +kernel
    rw [ha, hj, canonical2087 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton5102 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5102 node5102Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2512 node2512Labels + mixedMoment B node3471 node3471Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2127 singletonSmall5102
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5102) = raw2127Labels := by decide +kernel
  rw [hl, canonical2127 B hB] at h
  have hc0 : mixedMoment B raw2127 (Fin.cases (0 : Fin 2) singletonSmall5102) =
      mixedMoment B node2512 node2512Labels := by
    have ha : raw2127 = raw2128 := by apply Matrix.ext; unfold raw2127 raw2128; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5102 = raw2128Labels := by decide +kernel
    rw [ha, hj, canonical2128 B hB]
  have hc1 : mixedMoment B raw2127 (Fin.cases (1 : Fin 2) singletonSmall5102) =
      mixedMoment B node3471 node3471Labels := by
    have ha : raw2127 = raw2129 := by apply Matrix.ext; unfold raw2127 raw2129; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5102 = raw2129Labels := by decide +kernel
    rw [ha, hj, canonical2129 B hB]
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

theorem singleton5261 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5261 node5261Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2726 node2726Labels + mixedMoment B node3545 node3545Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2277 singletonSmall5261
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5261) = raw2277Labels := by decide +kernel
  rw [hl, canonical2277 B hB] at h
  have hc0 : mixedMoment B raw2277 (Fin.cases (0 : Fin 2) singletonSmall5261) =
      mixedMoment B node2726 node2726Labels := by
    have ha : raw2277 = raw2278 := by apply Matrix.ext; unfold raw2277 raw2278; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5261 = raw2278Labels := by decide +kernel
    rw [ha, hj, canonical2278 B hB]
  have hc1 : mixedMoment B raw2277 (Fin.cases (1 : Fin 2) singletonSmall5261) =
      mixedMoment B node3545 node3545Labels := by
    have ha : raw2277 = raw2279 := by apply Matrix.ext; unfold raw2277 raw2279; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5261 = raw2279Labels := by decide +kernel
    rw [ha, hj, canonical2279 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton5271 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5271 node5271Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2739 node2739Labels + mixedMoment B node3534 node3534Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2280 singletonSmall5271
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5271) = raw2280Labels := by decide +kernel
  rw [hl, canonical2280 B hB] at h
  have hc0 : mixedMoment B raw2280 (Fin.cases (0 : Fin 2) singletonSmall5271) =
      mixedMoment B node2739 node2739Labels := by
    have ha : raw2280 = raw2281 := by apply Matrix.ext; unfold raw2280 raw2281; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5271 = raw2281Labels := by decide +kernel
    rw [ha, hj, canonical2281 B hB]
  have hc1 : mixedMoment B raw2280 (Fin.cases (1 : Fin 2) singletonSmall5271) =
      mixedMoment B node3534 node3534Labels := by
    have ha : raw2280 = raw2282 := by apply Matrix.ext; unfold raw2280 raw2282; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5271 = raw2282Labels := by decide +kernel
    rw [ha, hj, canonical2282 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

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

theorem singleton5293 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5293 node5293Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2767 node2767Labels + mixedMoment B node3627 node3627Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2301 singletonSmall5293
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5293) = raw2301Labels := by decide +kernel
  rw [hl, canonical2301 B hB] at h
  have hc0 : mixedMoment B raw2301 (Fin.cases (0 : Fin 2) singletonSmall5293) =
      mixedMoment B node2767 node2767Labels := by
    have ha : raw2301 = raw2302 := by apply Matrix.ext; unfold raw2301 raw2302; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5293 = raw2302Labels := by decide +kernel
    rw [ha, hj, canonical2302 B hB]
  have hc1 : mixedMoment B raw2301 (Fin.cases (1 : Fin 2) singletonSmall5293) =
      mixedMoment B node3627 node3627Labels := by
    have ha : raw2301 = raw2303 := by apply Matrix.ext; unfold raw2301 raw2303; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5293 = raw2303Labels := by decide +kernel
    rw [ha, hj, canonical2303 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton5306 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5306 node5306Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2784 node2784Labels + mixedMoment B node3623 node3623Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2322 singletonSmall5306
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5306) = raw2322Labels := by decide +kernel
  rw [hl, canonical2322 B hB] at h
  have hc0 : mixedMoment B raw2322 (Fin.cases (0 : Fin 2) singletonSmall5306) =
      mixedMoment B node2784 node2784Labels := by
    have ha : raw2322 = raw2323 := by apply Matrix.ext; unfold raw2322 raw2323; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5306 = raw2323Labels := by decide +kernel
    rw [ha, hj, canonical2323 B hB]
  have hc1 : mixedMoment B raw2322 (Fin.cases (1 : Fin 2) singletonSmall5306) =
      mixedMoment B node3623 node3623Labels := by
    have ha : raw2322 = raw2324 := by apply Matrix.ext; unfold raw2322 raw2324; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5306 = raw2324Labels := by decide +kernel
    rw [ha, hj, canonical2324 B hB]
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

theorem singleton5475 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5475 node5475Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3963 node3963Labels + mixedMoment B node3963 node3963Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2592 singletonSmall5475
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5475) = raw2592Labels := by decide +kernel
  rw [hl, canonical2592 B hB] at h
  have hc0 : mixedMoment B raw2592 (Fin.cases (0 : Fin 2) singletonSmall5475) =
      mixedMoment B node3963 node3963Labels := by
    have ha : raw2592 = raw2593 := by apply Matrix.ext; unfold raw2592 raw2593; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5475 = raw2593Labels := by decide +kernel
    rw [ha, hj, canonical2593 B hB]
  have hc1 : mixedMoment B raw2592 (Fin.cases (1 : Fin 2) singletonSmall5475) =
      mixedMoment B node3963 node3963Labels := by
    have ha : raw2592 = raw2594 := by apply Matrix.ext; unfold raw2592 raw2594; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5475 = raw2594Labels := by decide +kernel
    rw [ha, hj, canonical2594 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton5491 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5491 node5491Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node4014 node4014Labels + mixedMoment B node4014 node4014Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2616 singletonSmall5491
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5491) = raw2616Labels := by decide +kernel
  rw [hl, canonical2616 B hB] at h
  have hc0 : mixedMoment B raw2616 (Fin.cases (0 : Fin 2) singletonSmall5491) =
      mixedMoment B node4014 node4014Labels := by
    have ha : raw2616 = raw2617 := by apply Matrix.ext; unfold raw2616 raw2617; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5491 = raw2617Labels := by decide +kernel
    rw [ha, hj, canonical2617 B hB]
  have hc1 : mixedMoment B raw2616 (Fin.cases (1 : Fin 2) singletonSmall5491) =
      mixedMoment B node4014 node4014Labels := by
    have ha : raw2616 = raw2618 := by apply Matrix.ext; unfold raw2616 raw2618; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5491 = raw2618Labels := by decide +kernel
    rw [ha, hj, canonical2618 B hB]
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

theorem sound1005 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1005 node1005Labels = Sparse.eval nodeValue1005 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1005) = mixedMoment B node1005 node1005Labels := rfl
  simpa [nodeValue1005, Sparse.eval] using hc.symm

theorem sound1009 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1009 node1009Labels = Sparse.eval nodeValue1009 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1009) = mixedMoment B node1009 node1009Labels := rfl
  simpa [nodeValue1009, Sparse.eval] using hc.symm

theorem sound1012 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1012 node1012Labels = Sparse.eval nodeValue1012 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1012) = mixedMoment B node1012 node1012Labels := rfl
  simpa [nodeValue1012, Sparse.eval] using hc.symm

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

theorem sound1083 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1083 node1083Labels = Sparse.eval nodeValue1083 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1083) = mixedMoment B node1083 node1083Labels := rfl
  simpa [nodeValue1083, Sparse.eval] using hc.symm

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

theorem sound1623 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1623 node1623Labels = Sparse.eval nodeValue1623 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1623) = mixedMoment B node1623 node1623Labels := rfl
  simpa [nodeValue1623, Sparse.eval] using hc.symm

theorem sound1627 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1627 node1627Labels = Sparse.eval nodeValue1627 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1627) = mixedMoment B node1627 node1627Labels := rfl
  simpa [nodeValue1627, Sparse.eval] using hc.symm

theorem sound1630 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1630 node1630Labels = Sparse.eval nodeValue1630 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1630) = mixedMoment B node1630 node1630Labels := rfl
  simpa [nodeValue1630, Sparse.eval] using hc.symm

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

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound37
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound2385 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2385 node2385Labels = Sparse.eval nodeValue2385 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2385) = mixedMoment B node2385 node2385Labels := rfl
  simpa [nodeValue2385, Sparse.eval] using hc.symm

theorem sound2399 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2399 node2399Labels = Sparse.eval nodeValue2399 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2399) = mixedMoment B node2399 node2399Labels := rfl
  simpa [nodeValue2399, Sparse.eval] using hc.symm

theorem sound2404 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2404 node2404Labels = Sparse.eval nodeValue2404 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2404) = mixedMoment B node2404 node2404Labels := rfl
  simpa [nodeValue2404, Sparse.eval] using hc.symm

theorem sound2407 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2407 node2407Labels = Sparse.eval nodeValue2407 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2407) = mixedMoment B node2407 node2407Labels := rfl
  simpa [nodeValue2407, Sparse.eval] using hc.symm

theorem sound2410 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2410 node2410Labels = Sparse.eval nodeValue2410 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2410) = mixedMoment B node2410 node2410Labels := rfl
  simpa [nodeValue2410, Sparse.eval] using hc.symm

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

theorem sound2462 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2462 node2462Labels = Sparse.eval nodeValue2462 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2462) = mixedMoment B node2462 node2462Labels := rfl
  simpa [nodeValue2462, Sparse.eval] using hc.symm

theorem sound2467 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2467 node2467Labels = Sparse.eval nodeValue2467 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2467) = mixedMoment B node2467 node2467Labels := rfl
  simpa [nodeValue2467, Sparse.eval] using hc.symm

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

theorem sound2512 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2512 node2512Labels = Sparse.eval nodeValue2512 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2512) = mixedMoment B node2512 node2512Labels := rfl
  simpa [nodeValue2512, Sparse.eval] using hc.symm

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

theorem sound2726 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2726 node2726Labels = Sparse.eval nodeValue2726 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2726) = mixedMoment B node2726 node2726Labels := rfl
  simpa [nodeValue2726, Sparse.eval] using hc.symm

theorem sound2739 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2739 node2739Labels = Sparse.eval nodeValue2739 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2739) = mixedMoment B node2739 node2739Labels := rfl
  simpa [nodeValue2739, Sparse.eval] using hc.symm

theorem sound2740 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2740 node2740Labels = Sparse.eval nodeValue2740 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2740) = mixedMoment B node2740 node2740Labels := rfl
  simpa [nodeValue2740, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound6
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound404 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node404 node404Labels = Sparse.eval nodeValue404 (mixedVector B) := by
  calc
    _ = Sparse.eval singlePairValue404 (familyPairVector B) := singlePair404 B _hB
    _ = _ := by
      norm_num [singlePairValue404, nodeValue404, Sparse.eval, mixedVector]
      ring

theorem sound416 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node416 node416Labels = Sparse.eval nodeValue416 (mixedVector B) := by
  calc
    _ = Sparse.eval singlePairValue416 (familyPairVector B) := singlePair416 B _hB
    _ = _ := by
      norm_num [singlePairValue416, nodeValue416, Sparse.eval, mixedVector]
      ring

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

theorem sound2767 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2767 node2767Labels = Sparse.eval nodeValue2767 (mixedVector B) := by
  have h := singleton2767 B _hB
  rw [sound404 B _hB _hF] at h
  norm_num [nodeValue2767, nodeValue404, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound2784 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2784 node2784Labels = Sparse.eval nodeValue2784 (mixedVector B) := by
  have h := singleton2784 B _hB
  rw [sound416 B _hB _hF] at h
  norm_num [nodeValue2784, nodeValue416, Sparse.eval] at h ⊢
  linarith only [h]

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

theorem sound3353 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3353 node3353Labels = Sparse.eval nodeValue3353 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3353) = mixedMoment B node3353 node3353Labels := rfl
  simpa [nodeValue3353, Sparse.eval] using hc.symm

theorem sound3357 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3357 node3357Labels = Sparse.eval nodeValue3357 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3357) = mixedMoment B node3357 node3357Labels := rfl
  simpa [nodeValue3357, Sparse.eval] using hc.symm

theorem sound3360 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3360 node3360Labels = Sparse.eval nodeValue3360 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3360) = mixedMoment B node3360 node3360Labels := rfl
  simpa [nodeValue3360, Sparse.eval] using hc.symm

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

theorem sound3436 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3436 node3436Labels = Sparse.eval nodeValue3436 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3436) = mixedMoment B node3436 node3436Labels := rfl
  simpa [nodeValue3436, Sparse.eval] using hc.symm

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

theorem sound3471 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3471 node3471Labels = Sparse.eval nodeValue3471 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3471) = mixedMoment B node3471 node3471Labels := rfl
  simpa [nodeValue3471, Sparse.eval] using hc.symm

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

theorem sound3534 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3534 node3534Labels = Sparse.eval nodeValue3534 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3534) = mixedMoment B node3534 node3534Labels := rfl
  simpa [nodeValue3534, Sparse.eval] using hc.symm

theorem sound3544 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3544 node3544Labels = Sparse.eval nodeValue3544 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3544) = mixedMoment B node3544 node3544Labels := rfl
  simpa [nodeValue3544, Sparse.eval] using hc.symm

theorem sound3545 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3545 node3545Labels = Sparse.eval nodeValue3545 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3545) = mixedMoment B node3545 node3545Labels := rfl
  simpa [nodeValue3545, Sparse.eval] using hc.symm

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

theorem sound3623 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3623 node3623Labels = Sparse.eval nodeValue3623 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3623) = mixedMoment B node3623 node3623Labels := rfl
  simpa [nodeValue3623, Sparse.eval] using hc.symm

theorem sound3627 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3627 node3627Labels = Sparse.eval nodeValue3627 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3627) = mixedMoment B node3627 node3627Labels := rfl
  simpa [nodeValue3627, Sparse.eval] using hc.symm

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

theorem sound527 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node527 node527Labels = Sparse.eval nodeValue527 (mixedVector B) := by
  calc
    _ = Sparse.eval singlePairValue527 (familyPairVector B) := singlePair527 B _hB
    _ = _ := by norm_num [singlePairValue527, nodeValue527, Sparse.eval, mixedVector]

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

theorem sound3963 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3963 node3963Labels = Sparse.eval nodeValue3963 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3963) = mixedMoment B node3963 node3963Labels := rfl
  simpa [nodeValue3963, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound62
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound4014 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4014 node4014Labels = Sparse.eval nodeValue4014 (mixedVector B) := by
  have h := singleton4014 B _hB
  rw [sound527 B _hB _hF] at h
  norm_num [nodeValue4014, nodeValue527, Sparse.eval] at h ⊢
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

theorem sound4424 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4424 node4424Labels = Sparse.eval nodeValue4424 (mixedVector B) := by
  have h := singleton4424 B _hB
  rw [sound1005 B _hB _hF, sound1623 B _hB _hF] at h
  norm_num [nodeValue4424, nodeValue1005, nodeValue1623, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4428 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4428 node4428Labels = Sparse.eval nodeValue4428 (mixedVector B) := by
  have h := singleton4428 B _hB
  rw [sound1009 B _hB _hF, sound1630 B _hB _hF] at h
  norm_num [nodeValue4428, nodeValue1009, nodeValue1630, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4431 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4431 node4431Labels = Sparse.eval nodeValue4431 (mixedVector B) := by
  have h := singleton4431 B _hB
  rw [sound1012 B _hB _hF, sound1627 B _hB _hF] at h
  norm_num [nodeValue4431, nodeValue1012, nodeValue1627, Sparse.eval] at h ⊢
  linarith only [h]

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

theorem sound4499 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4499 node4499Labels = Sparse.eval nodeValue4499 (mixedVector B) := by
  have h := singleton4499 B _hB
  rw [sound1083 B _hB _hF, sound1728 B _hB _hF] at h
  norm_num [nodeValue4499, nodeValue1083, nodeValue1728, Sparse.eval] at h ⊢
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

theorem sound5000 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5000 node5000Labels = Sparse.eval nodeValue5000 (mixedVector B) := by
  have h := singleton5000 B _hB
  rw [sound2385 B _hB _hF, sound3353 B _hB _hF] at h
  norm_num [nodeValue5000, nodeValue2385, nodeValue3353, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5014 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5014 node5014Labels = Sparse.eval nodeValue5014 (mixedVector B) := by
  have h := singleton5014 B _hB
  rw [sound2399 B _hB _hF, sound2467 B _hB _hF] at h
  norm_num [nodeValue5014, nodeValue2399, nodeValue2467, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5018 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5018 node5018Labels = Sparse.eval nodeValue5018 (mixedVector B) := by
  have h := singleton5018 B _hB
  rw [sound2404 B _hB _hF, sound3357 B _hB _hF] at h
  norm_num [nodeValue5018, nodeValue2404, nodeValue3357, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5021 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5021 node5021Labels = Sparse.eval nodeValue5021 (mixedVector B) := by
  have h := singleton5021 B _hB
  rw [sound2407 B _hB _hF, sound3360 B _hB _hF] at h
  norm_num [nodeValue5021, nodeValue2407, nodeValue3360, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5023 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5023 node5023Labels = Sparse.eval nodeValue5023 (mixedVector B) := by
  have h := singleton5023 B _hB
  rw [sound2410 B _hB _hF] at h
  norm_num [nodeValue5023, nodeValue2410, Sparse.eval] at h ⊢
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

theorem sound5059 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5059 node5059Labels = Sparse.eval nodeValue5059 (mixedVector B) := by
  have h := singleton5059 B _hB
  rw [sound2462 B _hB _hF, sound3436 B _hB _hF] at h
  norm_num [nodeValue5059, nodeValue2462, nodeValue3436, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5102 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5102 node5102Labels = Sparse.eval nodeValue5102 (mixedVector B) := by
  have h := singleton5102 B _hB
  rw [sound2512 B _hB _hF, sound3471 B _hB _hF] at h
  norm_num [nodeValue5102, nodeValue2512, nodeValue3471, Sparse.eval] at h ⊢
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

theorem sound5259 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5259 node5259Labels = Sparse.eval nodeValue5259 (mixedVector B) := by
  have h := singleton5259 B _hB
  rw [sound2723 B _hB _hF, sound3544 B _hB _hF] at h
  norm_num [nodeValue5259, nodeValue2723, nodeValue3544, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5261 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5261 node5261Labels = Sparse.eval nodeValue5261 (mixedVector B) := by
  have h := singleton5261 B _hB
  rw [sound2726 B _hB _hF, sound3545 B _hB _hF] at h
  norm_num [nodeValue5261, nodeValue2726, nodeValue3545, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5271 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5271 node5271Labels = Sparse.eval nodeValue5271 (mixedVector B) := by
  have h := singleton5271 B _hB
  rw [sound2739 B _hB _hF, sound3534 B _hB _hF] at h
  norm_num [nodeValue5271, nodeValue2739, nodeValue3534, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5272 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5272 node5272Labels = Sparse.eval nodeValue5272 (mixedVector B) := by
  have h := singleton5272 B _hB
  rw [sound2740 B _hB _hF] at h
  norm_num [nodeValue5272, nodeValue2740, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5293 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5293 node5293Labels = Sparse.eval nodeValue5293 (mixedVector B) := by
  have h := singleton5293 B _hB
  rw [sound2767 B _hB _hF, sound3627 B _hB _hF] at h
  norm_num [nodeValue5293, nodeValue2767, nodeValue3627, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5306 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5306 node5306Labels = Sparse.eval nodeValue5306 (mixedVector B) := by
  have h := singleton5306 B _hB
  rw [sound2784 B _hB _hF, sound3623 B _hB _hF] at h
  norm_num [nodeValue5306, nodeValue2784, nodeValue3623, Sparse.eval] at h ⊢
  linarith only [h]

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

theorem sound5473 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5473 node5473Labels = Sparse.eval nodeValue5473 (mixedVector B) := by
  have h := singleton5473 B _hB
  rw [sound3958 B _hB _hF, sound3961 B _hB _hF] at h
  norm_num [nodeValue5473, nodeValue3958, nodeValue3961, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5475 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5475 node5475Labels = Sparse.eval nodeValue5475 (mixedVector B) := by
  have h := singleton5475 B _hB
  rw [sound3963 B _hB _hF] at h
  norm_num [nodeValue5475, nodeValue3963, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5491 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5491 node5491Labels = Sparse.eval nodeValue5491 (mixedVector B) := by
  have h := singleton5491 B _hB
  rw [sound4014 B _hB _hF] at h
  norm_num [nodeValue5491, nodeValue4014, Sparse.eval] at h ⊢
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources19
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sourceEq622 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm622 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA622 + difference 0 1) (sourceB622 + difference 1 0) sourceC622) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5473) := by
    have ha : (tripleCharges (sourceA622 + difference 0 1) (sourceB622 + difference 1 0) sourceC622) = raw10450 := by
      apply Matrix.ext; unfold tripleCharges sourceA622 sourceB622 sourceC622 difference raw10450; decide +kernel
    rw [ha]
    exact (canonical10450 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA622 + difference 0 2) (sourceB622 + difference 2 0) sourceC622) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5473) := by
    have ha : (tripleCharges (sourceA622 + difference 0 2) (sourceB622 + difference 2 0) sourceC622) = raw10451 := by
      apply Matrix.ext; unfold tripleCharges sourceA622 sourceB622 sourceC622 difference raw10451; decide +kernel
    rw [ha]
    exact (canonical10451 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA622 + difference 0 3) (sourceB622 + difference 3 0) sourceC622) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5475) := by
    have ha : (tripleCharges (sourceA622 + difference 0 3) (sourceB622 + difference 3 0) sourceC622) = raw10452 := by
      apply Matrix.ext; unfold tripleCharges sourceA622 sourceB622 sourceC622 difference raw10452; decide +kernel
    rw [ha]
    exact (canonical10452 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA622 + difference 0 4) (sourceB622 + difference 4 0) sourceC622) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5491) := by
    have ha : (tripleCharges (sourceA622 + difference 0 4) (sourceB622 + difference 4 0) sourceC622) = raw10453 := by
      apply Matrix.ext; unfold tripleCharges sourceA622 sourceB622 sourceC622 difference raw10453; decide +kernel
    rw [ha]
    exact (canonical10453 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA622 + difference 0 5) (sourceB622 + difference 5 0) sourceC622) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5492) := by
    have ha : (tripleCharges (sourceA622 + difference 0 5) (sourceB622 + difference 5 0) sourceC622) = raw10454 := by
      apply Matrix.ext; unfold tripleCharges sourceA622 sourceB622 sourceC622 difference raw10454; decide +kernel
    rw [ha]
    exact (canonical10454 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA622 + difference 1 0) (sourceB622 + difference 0 1) sourceC622) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4424) := by
    have ha : (tripleCharges (sourceA622 + difference 1 0) (sourceB622 + difference 0 1) sourceC622) = raw10455 := by
      apply Matrix.ext; unfold tripleCharges sourceA622 sourceB622 sourceC622 difference raw10455; decide +kernel
    rw [ha]
    exact (canonical10455 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA622 + difference 1 2) (sourceB622 + difference 2 1) sourceC622) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5059) := by
    have ha : (tripleCharges (sourceA622 + difference 1 2) (sourceB622 + difference 2 1) sourceC622) = raw10456 := by
      apply Matrix.ext; unfold tripleCharges sourceA622 sourceB622 sourceC622 difference raw10456; decide +kernel
    rw [ha]
    exact (canonical10456 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA622 + difference 1 3) (sourceB622 + difference 3 1) sourceC622) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5018) := by
    have ha : (tripleCharges (sourceA622 + difference 1 3) (sourceB622 + difference 3 1) sourceC622) = raw10457 := by
      apply Matrix.ext; unfold tripleCharges sourceA622 sourceB622 sourceC622 difference raw10457; decide +kernel
    rw [ha]
    exact (canonical10457 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA622 + difference 1 4) (sourceB622 + difference 4 1) sourceC622) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5259) := by
    have ha : (tripleCharges (sourceA622 + difference 1 4) (sourceB622 + difference 4 1) sourceC622) = raw10458 := by
      apply Matrix.ext; unfold tripleCharges sourceA622 sourceB622 sourceC622 difference raw10458; decide +kernel
    rw [ha]
    exact (canonical10458 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA622 + difference 1 5) (sourceB622 + difference 5 1) sourceC622) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5271) := by
    have ha : (tripleCharges (sourceA622 + difference 1 5) (sourceB622 + difference 5 1) sourceC622) = raw10459 := by
      apply Matrix.ext; unfold tripleCharges sourceA622 sourceB622 sourceC622 difference raw10459; decide +kernel
    rw [ha]
    exact (canonical10459 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA622 + difference 2 0) (sourceB622 + difference 0 2) sourceC622) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4424) := by
    have ha : (tripleCharges (sourceA622 + difference 2 0) (sourceB622 + difference 0 2) sourceC622) = raw10460 := by
      apply Matrix.ext; unfold tripleCharges sourceA622 sourceB622 sourceC622 difference raw10460; decide +kernel
    rw [ha]
    exact (canonical10460 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA622 + difference 2 1) (sourceB622 + difference 1 2) sourceC622) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5059) := by
    have ha : (tripleCharges (sourceA622 + difference 2 1) (sourceB622 + difference 1 2) sourceC622) = raw10461 := by
      apply Matrix.ext; unfold tripleCharges sourceA622 sourceB622 sourceC622 difference raw10461; decide +kernel
    rw [ha]
    exact (canonical10461 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA622 + difference 2 3) (sourceB622 + difference 3 2) sourceC622) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5018) := by
    have ha : (tripleCharges (sourceA622 + difference 2 3) (sourceB622 + difference 3 2) sourceC622) = raw10462 := by
      apply Matrix.ext; unfold tripleCharges sourceA622 sourceB622 sourceC622 difference raw10462; decide +kernel
    rw [ha]
    exact (canonical10462 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA622 + difference 2 4) (sourceB622 + difference 4 2) sourceC622) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5259) := by
    have ha : (tripleCharges (sourceA622 + difference 2 4) (sourceB622 + difference 4 2) sourceC622) = raw10463 := by
      apply Matrix.ext; unfold tripleCharges sourceA622 sourceB622 sourceC622 difference raw10463; decide +kernel
    rw [ha]
    exact (canonical10463 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA622 + difference 2 5) (sourceB622 + difference 5 2) sourceC622) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5271) := by
    have ha : (tripleCharges (sourceA622 + difference 2 5) (sourceB622 + difference 5 2) sourceC622) = raw10464 := by
      apply Matrix.ext; unfold tripleCharges sourceA622 sourceB622 sourceC622 difference raw10464; decide +kernel
    rw [ha]
    exact (canonical10464 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA622 + difference 3 0) (sourceB622 + difference 0 3) sourceC622) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4499) := by
    have ha : (tripleCharges (sourceA622 + difference 3 0) (sourceB622 + difference 0 3) sourceC622) = raw10465 := by
      apply Matrix.ext; unfold tripleCharges sourceA622 sourceB622 sourceC622 difference raw10465; decide +kernel
    rw [ha]
    exact (canonical10465 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA622 + difference 3 1) (sourceB622 + difference 1 3) sourceC622) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5102) := by
    have ha : (tripleCharges (sourceA622 + difference 3 1) (sourceB622 + difference 1 3) sourceC622) = raw10466 := by
      apply Matrix.ext; unfold tripleCharges sourceA622 sourceB622 sourceC622 difference raw10466; decide +kernel
    rw [ha]
    exact (canonical10466 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA622 + difference 3 2) (sourceB622 + difference 2 3) sourceC622) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5102) := by
    have ha : (tripleCharges (sourceA622 + difference 3 2) (sourceB622 + difference 2 3) sourceC622) = raw10467 := by
      apply Matrix.ext; unfold tripleCharges sourceA622 sourceB622 sourceC622 difference raw10467; decide +kernel
    rw [ha]
    exact (canonical10467 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA622 + difference 3 4) (sourceB622 + difference 4 3) sourceC622) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5293) := by
    have ha : (tripleCharges (sourceA622 + difference 3 4) (sourceB622 + difference 4 3) sourceC622) = raw10468 := by
      apply Matrix.ext; unfold tripleCharges sourceA622 sourceB622 sourceC622 difference raw10468; decide +kernel
    rw [ha]
    exact (canonical10468 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA622 + difference 3 5) (sourceB622 + difference 5 3) sourceC622) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5306) := by
    have ha : (tripleCharges (sourceA622 + difference 3 5) (sourceB622 + difference 5 3) sourceC622) = raw10469 := by
      apply Matrix.ext; unfold tripleCharges sourceA622 sourceB622 sourceC622 difference raw10469; decide +kernel
    rw [ha]
    exact (canonical10469 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA622 + difference 4 0) (sourceB622 + difference 0 4) sourceC622) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4431) := by
    have ha : (tripleCharges (sourceA622 + difference 4 0) (sourceB622 + difference 0 4) sourceC622) = raw10470 := by
      apply Matrix.ext; unfold tripleCharges sourceA622 sourceB622 sourceC622 difference raw10470; decide +kernel
    rw [ha]
    exact (canonical10470 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA622 + difference 4 1) (sourceB622 + difference 1 4) sourceC622) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5014) := by
    have ha : (tripleCharges (sourceA622 + difference 4 1) (sourceB622 + difference 1 4) sourceC622) = raw10471 := by
      apply Matrix.ext; unfold tripleCharges sourceA622 sourceB622 sourceC622 difference raw10471; decide +kernel
    rw [ha]
    exact (canonical10471 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA622 + difference 4 2) (sourceB622 + difference 2 4) sourceC622) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5014) := by
    have ha : (tripleCharges (sourceA622 + difference 4 2) (sourceB622 + difference 2 4) sourceC622) = raw10472 := by
      apply Matrix.ext; unfold tripleCharges sourceA622 sourceB622 sourceC622 difference raw10472; decide +kernel
    rw [ha]
    exact (canonical10472 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA622 + difference 4 3) (sourceB622 + difference 3 4) sourceC622) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5023) := by
    have ha : (tripleCharges (sourceA622 + difference 4 3) (sourceB622 + difference 3 4) sourceC622) = raw10473 := by
      apply Matrix.ext; unfold tripleCharges sourceA622 sourceB622 sourceC622 difference raw10473; decide +kernel
    rw [ha]
    exact (canonical10473 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA622 + difference 4 5) (sourceB622 + difference 5 4) sourceC622) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5272) := by
    have ha : (tripleCharges (sourceA622 + difference 4 5) (sourceB622 + difference 5 4) sourceC622) = raw10474 := by
      apply Matrix.ext; unfold tripleCharges sourceA622 sourceB622 sourceC622 difference raw10474; decide +kernel
    rw [ha]
    exact (canonical10474 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA622 + difference 5 0) (sourceB622 + difference 0 5) sourceC622) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4428) := by
    have ha : (tripleCharges (sourceA622 + difference 5 0) (sourceB622 + difference 0 5) sourceC622) = raw10475 := by
      apply Matrix.ext; unfold tripleCharges sourceA622 sourceB622 sourceC622 difference raw10475; decide +kernel
    rw [ha]
    exact (canonical10475 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA622 + difference 5 1) (sourceB622 + difference 1 5) sourceC622) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5000) := by
    have ha : (tripleCharges (sourceA622 + difference 5 1) (sourceB622 + difference 1 5) sourceC622) = raw10476 := by
      apply Matrix.ext; unfold tripleCharges sourceA622 sourceB622 sourceC622 difference raw10476; decide +kernel
    rw [ha]
    exact (canonical10476 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA622 + difference 5 2) (sourceB622 + difference 2 5) sourceC622) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5000) := by
    have ha : (tripleCharges (sourceA622 + difference 5 2) (sourceB622 + difference 2 5) sourceC622) = raw10477 := by
      apply Matrix.ext; unfold tripleCharges sourceA622 sourceB622 sourceC622 difference raw10477; decide +kernel
    rw [ha]
    exact (canonical10477 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA622 + difference 5 3) (sourceB622 + difference 3 5) sourceC622) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5021) := by
    have ha : (tripleCharges (sourceA622 + difference 5 3) (sourceB622 + difference 3 5) sourceC622) = raw10478 := by
      apply Matrix.ext; unfold tripleCharges sourceA622 sourceB622 sourceC622 difference raw10478; decide +kernel
    rw [ha]
    exact (canonical10478 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA622 + difference 5 4) (sourceB622 + difference 4 5) sourceC622) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5261) := by
    have ha : (tripleCharges (sourceA622 + difference 5 4) (sourceB622 + difference 4 5) sourceC622) = raw10479 := by
      apply Matrix.ext; unfold tripleCharges sourceA622 sourceB622 sourceC622 difference raw10479; decide +kernel
    rw [ha]
    exact (canonical10479 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA622 sourceB622 sourceC622
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm622, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic33
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reindexCheck531 : Integer.Sparse.reindex keyMap MixedData.row531 = numericRow531 := by decide +kernel

theorem numericCheck531 (x : Master → ℝ) : Integer.Sparse.eval numericRow531 x =
    (8640 : ℝ) * reducedSource531 x := by
  norm_num [numericRow531, reducedSource531, Integer.Sparse.eval, Sparse.eval, nodeValue4424, nodeValue4428, nodeValue4431, nodeValue4499, nodeValue5000, nodeValue5014, nodeValue5018, nodeValue5021, nodeValue5023, nodeValue5059, nodeValue5102, nodeValue5259, nodeValue5261, nodeValue5271, nodeValue5272, nodeValue5293, nodeValue5306, nodeValue5473, nodeValue5475, nodeValue5491, nodeValue5492]
  ring

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Rows33
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero531 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource531 (mixedVector B) = 0 := by
  have h4424 : mixedVector B (Sum.inr 4424) = Sparse.eval nodeValue4424 (mixedVector B) := by
    change mixedMoment B node4424 node4424Labels = _
    exact sound4424 B hB hF
  have h4428 : mixedVector B (Sum.inr 4428) = Sparse.eval nodeValue4428 (mixedVector B) := by
    change mixedMoment B node4428 node4428Labels = _
    exact sound4428 B hB hF
  have h4431 : mixedVector B (Sum.inr 4431) = Sparse.eval nodeValue4431 (mixedVector B) := by
    change mixedMoment B node4431 node4431Labels = _
    exact sound4431 B hB hF
  have h4499 : mixedVector B (Sum.inr 4499) = Sparse.eval nodeValue4499 (mixedVector B) := by
    change mixedMoment B node4499 node4499Labels = _
    exact sound4499 B hB hF
  have h5000 : mixedVector B (Sum.inr 5000) = Sparse.eval nodeValue5000 (mixedVector B) := by
    change mixedMoment B node5000 node5000Labels = _
    exact sound5000 B hB hF
  have h5014 : mixedVector B (Sum.inr 5014) = Sparse.eval nodeValue5014 (mixedVector B) := by
    change mixedMoment B node5014 node5014Labels = _
    exact sound5014 B hB hF
  have h5018 : mixedVector B (Sum.inr 5018) = Sparse.eval nodeValue5018 (mixedVector B) := by
    change mixedMoment B node5018 node5018Labels = _
    exact sound5018 B hB hF
  have h5021 : mixedVector B (Sum.inr 5021) = Sparse.eval nodeValue5021 (mixedVector B) := by
    change mixedMoment B node5021 node5021Labels = _
    exact sound5021 B hB hF
  have h5023 : mixedVector B (Sum.inr 5023) = Sparse.eval nodeValue5023 (mixedVector B) := by
    change mixedMoment B node5023 node5023Labels = _
    exact sound5023 B hB hF
  have h5059 : mixedVector B (Sum.inr 5059) = Sparse.eval nodeValue5059 (mixedVector B) := by
    change mixedMoment B node5059 node5059Labels = _
    exact sound5059 B hB hF
  have h5102 : mixedVector B (Sum.inr 5102) = Sparse.eval nodeValue5102 (mixedVector B) := by
    change mixedMoment B node5102 node5102Labels = _
    exact sound5102 B hB hF
  have h5259 : mixedVector B (Sum.inr 5259) = Sparse.eval nodeValue5259 (mixedVector B) := by
    change mixedMoment B node5259 node5259Labels = _
    exact sound5259 B hB hF
  have h5261 : mixedVector B (Sum.inr 5261) = Sparse.eval nodeValue5261 (mixedVector B) := by
    change mixedMoment B node5261 node5261Labels = _
    exact sound5261 B hB hF
  have h5271 : mixedVector B (Sum.inr 5271) = Sparse.eval nodeValue5271 (mixedVector B) := by
    change mixedMoment B node5271 node5271Labels = _
    exact sound5271 B hB hF
  have h5272 : mixedVector B (Sum.inr 5272) = Sparse.eval nodeValue5272 (mixedVector B) := by
    change mixedMoment B node5272 node5272Labels = _
    exact sound5272 B hB hF
  have h5293 : mixedVector B (Sum.inr 5293) = Sparse.eval nodeValue5293 (mixedVector B) := by
    change mixedMoment B node5293 node5293Labels = _
    exact sound5293 B hB hF
  have h5306 : mixedVector B (Sum.inr 5306) = Sparse.eval nodeValue5306 (mixedVector B) := by
    change mixedMoment B node5306 node5306Labels = _
    exact sound5306 B hB hF
  have h5473 : mixedVector B (Sum.inr 5473) = Sparse.eval nodeValue5473 (mixedVector B) := by
    change mixedMoment B node5473 node5473Labels = _
    exact sound5473 B hB hF
  have h5475 : mixedVector B (Sum.inr 5475) = Sparse.eval nodeValue5475 (mixedVector B) := by
    change mixedMoment B node5475 node5475Labels = _
    exact sound5475 B hB hF
  have h5491 : mixedVector B (Sum.inr 5491) = Sparse.eval nodeValue5491 (mixedVector B) := by
    change mixedMoment B node5491 node5491Labels = _
    exact sound5491 B hB hF
  have h5492 : mixedVector B (Sum.inr 5492) = Sparse.eval nodeValue5492 (mixedVector B) := by
    change mixedMoment B node5492 node5492Labels = _
    exact sound5492_e B hB hF
  simpa only [sourceForm622, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4424, h4428, h4431, h4499, h5000, h5014, h5018, h5021, h5023, h5059, h5102, h5259, h5261, h5271, h5272, h5293, h5306, h5473, h5475, h5491, h5492, reducedSource531] using sourceEq622 B hB

theorem rowSound531_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row531 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck531, numericCheck531, reducedZero531 B hB hF, mul_zero]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedSourceBridge.rowSound531_e_oai := @OAI.MUB6.Certificate.MixedSourceBridge.rowSound531_e_oai
