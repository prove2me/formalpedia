-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedSourceBridge.rowSound1715_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-08T21:36:58.825213+00:00
-- url     : https://prove2.me/submissions/a00407d0-fe46-49eb-83b2-e72e21c77887

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E070
import Definitions.Def_OAIQ106E086
import Definitions.Def_OAIQ106E087
import Definitions.Def_OAIQ106E088
import Definitions.Def_OAIQ106E089
import Definitions.Def_OAIQ106E093
import Definitions.Def_OAIQ106E094
import Definitions.Def_OAIQ106E095
import Definitions.Def_OAIQ106E096
import Definitions.Def_OAIQ106E187
import Definitions.Def_OAIQ106E097
import Definitions.Def_OAIQ106E188
import Definitions.Def_OAIQ106E189
import Definitions.Def_OAIQ106E098
import Definitions.Def_OAIQ106E190
import Definitions.Def_OAIQ106E191
import Definitions.Def_OAIQ106E192
import Definitions.Def_OAIQ106E102
import Definitions.Def_OAIQ106E103
import Definitions.Def_OAIQ106E105
import Definitions.Def_OAIQ106E119
import Definitions.Def_OAIQ106E120
import Definitions.Def_OAIQ106E125
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
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound5169_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound5483_e

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical238 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw238 raw238Labels = mixedMoment B node2598 node2598Labels := by
  calc
    mixedMoment B raw238 raw238Labels = mixedMoment B raw238step0 raw238step0Labels := by
      have ha : raw238step0 = (fun i j => raw238 (permutation8 i) (permutation5 j)) := by apply Matrix.ext; unfold raw238step0 raw238; decide +kernel
      have hl : raw238step0Labels = raw238Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw238 raw238Labels permutation8 permutation5
    mixedMoment B raw238step0 raw238step0Labels = mixedMoment B raw238step1 raw238step1Labels := by
      have ha : raw238step1 = raw238step0 := by apply Matrix.ext; unfold raw238step1 raw238step0; decide +kernel
      have hl : raw238step0Labels = labelEmbedding1 ∘ raw238step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw238step0 raw238step0Labels raw238step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2598 node2598Labels := by rfl

theorem canonical239 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw239 raw239Labels = mixedMoment B node338 node338Labels := by
  calc
    mixedMoment B raw239 raw239Labels = mixedMoment B raw239step0 raw239step0Labels := by
      have ha : raw239step0 = (fun i j => raw239 (permutation8 i) (permutation5 j)) := by apply Matrix.ext; unfold raw239step0 raw239; decide +kernel
      have hl : raw239step0Labels = raw239Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw239 raw239Labels permutation8 permutation5
    _ = mixedMoment B node338 node338Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical133
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical17099 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17099 raw17099Labels = mixedMoment B node5081 node5081Labels := by
  calc
    mixedMoment B raw17099 raw17099Labels = mixedMoment B raw17099step0 raw17099step0Labels := by
      have hz : ∀ j, raw17099 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw17099step0 = (fun i j => raw17099 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw17099step0 raw17099; decide +kernel
      have hl : raw17099step0Labels = raw17099Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17099 raw17099Labels permutation346 hz
    mixedMoment B raw17099step0 raw17099step0Labels = mixedMoment B raw17099step1 raw17099step1Labels := by
      have ha : raw17099step1 = (fun i j => raw17099step0 (permutation150 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17099step1 raw17099step0; decide +kernel
      have hl : raw17099step1Labels = raw17099step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17099step0 raw17099step0Labels permutation150 permutation3
    mixedMoment B raw17099step1 raw17099step1Labels = mixedMoment B raw17099step2 raw17099step2Labels := by
      have ha : raw17099step2 = -raw17099step1 := by apply Matrix.ext; change ∀ i j, raw17099step2 i j = -(raw17099step1 i j); unfold raw17099step2 raw17099step1; decide +kernel
      have hl : raw17099step2Labels = raw17099step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw17099step2 raw17099step2Labels = mixedMoment B raw17099step3 raw17099step3Labels := by
      have ha : raw17099step3 = raw17099step2 := by apply Matrix.ext; unfold raw17099step3 raw17099step2; decide +kernel
      have hl : raw17099step2Labels = labelEmbedding6 ∘ raw17099step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17099step2 raw17099step2Labels raw17099step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5081 node5081Labels := by rfl

theorem canonical17100 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17100 raw17100Labels = mixedMoment B node5073 node5073Labels := by
  calc
    mixedMoment B raw17100 raw17100Labels = mixedMoment B raw17100step0 raw17100step0Labels := by
      have ha : raw17100step0 = (fun i j => raw17100 (permutation686 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17100step0 raw17100; decide +kernel
      have hl : raw17100step0Labels = raw17100Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17100 raw17100Labels permutation686 permutation3
    mixedMoment B raw17100step0 raw17100step0Labels = mixedMoment B raw17100step1 raw17100step1Labels := by
      have ha : raw17100step1 = -raw17100step0 := by apply Matrix.ext; change ∀ i j, raw17100step1 i j = -(raw17100step0 i j); unfold raw17100step1 raw17100step0; decide +kernel
      have hl : raw17100step1Labels = raw17100step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw17100step1 raw17100step1Labels = mixedMoment B raw17100step2 raw17100step2Labels := by
      have ha : raw17100step2 = raw17100step1 := by apply Matrix.ext; unfold raw17100step2 raw17100step1; decide +kernel
      have hl : raw17100step1Labels = labelEmbedding6 ∘ raw17100step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17100step1 raw17100step1Labels raw17100step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5073 node5073Labels := by rfl

theorem canonical17101 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17101 raw17101Labels = mixedMoment B node5102 node5102Labels := by
  calc
    mixedMoment B raw17101 raw17101Labels = mixedMoment B raw17101step0 raw17101step0Labels := by
      have hz : ∀ j, raw17101 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw17101step0 = (fun i j => raw17101 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw17101step0 raw17101; decide +kernel
      have hl : raw17101step0Labels = raw17101Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17101 raw17101Labels permutation346 hz
    mixedMoment B raw17101step0 raw17101step0Labels = mixedMoment B raw17101step1 raw17101step1Labels := by
      have ha : raw17101step1 = (fun i j => raw17101step0 (permutation149 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17101step1 raw17101step0; decide +kernel
      have hl : raw17101step1Labels = raw17101step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17101step0 raw17101step0Labels permutation149 permutation3
    mixedMoment B raw17101step1 raw17101step1Labels = mixedMoment B raw17101step2 raw17101step2Labels := by
      have ha : raw17101step2 = -raw17101step1 := by apply Matrix.ext; change ∀ i j, raw17101step2 i j = -(raw17101step1 i j); unfold raw17101step2 raw17101step1; decide +kernel
      have hl : raw17101step2Labels = raw17101step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw17101step2 raw17101step2Labels = mixedMoment B raw17101step3 raw17101step3Labels := by
      have ha : raw17101step3 = raw17101step2 := by apply Matrix.ext; unfold raw17101step3 raw17101step2; decide +kernel
      have hl : raw17101step2Labels = labelEmbedding6 ∘ raw17101step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17101step2 raw17101step2Labels raw17101step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5102 node5102Labels := by rfl

theorem canonical17102 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17102 raw17102Labels = mixedMoment B node5293 node5293Labels := by
  calc
    mixedMoment B raw17102 raw17102Labels = mixedMoment B raw17102step0 raw17102step0Labels := by
      have hz : ∀ j, raw17102 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw17102step0 = (fun i j => raw17102 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw17102step0 raw17102; decide +kernel
      have hl : raw17102step0Labels = raw17102Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17102 raw17102Labels permutation520 hz
    mixedMoment B raw17102step0 raw17102step0Labels = mixedMoment B raw17102step1 raw17102step1Labels := by
      have hz : ∀ j, raw17102step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw17102step1 = (fun i j => raw17102step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw17102step1 raw17102step0; decide +kernel
      have hl : raw17102step1Labels = raw17102step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17102step0 raw17102step0Labels permutation80 hz
    mixedMoment B raw17102step1 raw17102step1Labels = mixedMoment B raw17102step2 raw17102step2Labels := by
      have ha : raw17102step2 = (fun i j => raw17102step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17102step2 raw17102step1; decide +kernel
      have hl : raw17102step2Labels = raw17102step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17102step1 raw17102step1Labels permutation31 permutation3
    mixedMoment B raw17102step2 raw17102step2Labels = mixedMoment B raw17102step3 raw17102step3Labels := by
      have ha : raw17102step3 = -raw17102step2 := by apply Matrix.ext; change ∀ i j, raw17102step3 i j = -(raw17102step2 i j); unfold raw17102step3 raw17102step2; decide +kernel
      have hl : raw17102step3Labels = raw17102step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw17102step3 raw17102step3Labels = mixedMoment B raw17102step4 raw17102step4Labels := by
      have ha : raw17102step4 = raw17102step3 := by apply Matrix.ext; unfold raw17102step4 raw17102step3; decide +kernel
      have hl : raw17102step3Labels = labelEmbedding6 ∘ raw17102step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17102step3 raw17102step3Labels raw17102step4Labels labelEmbedding6 hl
    _ = mixedMoment B node5293 node5293Labels := by rfl

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

theorem canonical1833 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1833 raw1833Labels = mixedMoment B node4902 node4902Labels := by
  calc
    mixedMoment B raw1833 raw1833Labels = mixedMoment B raw1833step0 raw1833step0Labels := by
      have ha : raw1833step0 = (fun i j => raw1833 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1833step0 raw1833; decide +kernel
      have hl : raw1833step0Labels = raw1833Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1833 raw1833Labels permutation152 permutation4
    mixedMoment B raw1833step0 raw1833step0Labels = mixedMoment B raw1833step1 raw1833step1Labels := by
      have ha : raw1833step1 = raw1833step0 := by apply Matrix.ext; unfold raw1833step1 raw1833step0; decide +kernel
      have hl : raw1833step0Labels = labelEmbedding7 ∘ raw1833step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1833step0 raw1833step0Labels raw1833step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4902 node4902Labels := by rfl

theorem canonical1834 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1834 raw1834Labels = mixedMoment B node2295 node2295Labels := by
  calc
    mixedMoment B raw1834 raw1834Labels = mixedMoment B raw1834step0 raw1834step0Labels := by
      have ha : raw1834step0 = (fun i j => raw1834 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1834step0 raw1834; decide +kernel
      have hl : raw1834step0Labels = raw1834Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1834 raw1834Labels permutation152 permutation4
    _ = mixedMoment B node2295 node2295Labels := by rfl

theorem canonical1835 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1835 raw1835Labels = mixedMoment B node3315 node3315Labels := by
  calc
    mixedMoment B raw1835 raw1835Labels = mixedMoment B raw1835step0 raw1835step0Labels := by
      have ha : raw1835step0 = (fun i j => raw1835 (permutation158 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1835step0 raw1835; decide +kernel
      have hl : raw1835step0Labels = raw1835Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1835 raw1835Labels permutation158 permutation6
    mixedMoment B raw1835step0 raw1835step0Labels = mixedMoment B raw1835step1 raw1835step1Labels := by
      have ha : raw1835step1 = -raw1835step0 := by apply Matrix.ext; change ∀ i j, raw1835step1 i j = -(raw1835step0 i j); unfold raw1835step1 raw1835step0; decide +kernel
      have hl : raw1835step1Labels = raw1835step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1835step1 raw1835step1Labels = mixedMoment B raw1835step2 raw1835step2Labels := by
      have ha : raw1835step2 = raw1835step1 := by apply Matrix.ext; unfold raw1835step2 raw1835step1; decide +kernel
      have hl : raw1835step1Labels = labelEmbedding1 ∘ raw1835step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1835step1 raw1835step1Labels raw1835step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3315 node3315Labels := by rfl

theorem canonical1848 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1848 raw1848Labels = mixedMoment B node4907 node4907Labels := by
  calc
    mixedMoment B raw1848 raw1848Labels = mixedMoment B raw1848step0 raw1848step0Labels := by
      have ha : raw1848step0 = (fun i j => raw1848 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1848step0 raw1848; decide +kernel
      have hl : raw1848step0Labels = raw1848Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1848 raw1848Labels permutation32 permutation4
    mixedMoment B raw1848step0 raw1848step0Labels = mixedMoment B raw1848step1 raw1848step1Labels := by
      have ha : raw1848step1 = raw1848step0 := by apply Matrix.ext; unfold raw1848step1 raw1848step0; decide +kernel
      have hl : raw1848step0Labels = labelEmbedding7 ∘ raw1848step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1848step0 raw1848step0Labels raw1848step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4907 node4907Labels := by rfl

theorem canonical1849 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1849 raw1849Labels = mixedMoment B node2300 node2300Labels := by
  calc
    mixedMoment B raw1849 raw1849Labels = mixedMoment B raw1849step0 raw1849step0Labels := by
      have ha : raw1849step0 = (fun i j => raw1849 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1849step0 raw1849; decide +kernel
      have hl : raw1849step0Labels = raw1849Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1849 raw1849Labels permutation32 permutation4
    _ = mixedMoment B node2300 node2300Labels := by rfl

theorem canonical1850 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1850 raw1850Labels = mixedMoment B node3325 node3325Labels := by
  calc
    mixedMoment B raw1850 raw1850Labels = mixedMoment B raw1850step0 raw1850step0Labels := by
      have ha : raw1850step0 = (fun i j => raw1850 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1850step0 raw1850; decide +kernel
      have hl : raw1850step0Labels = raw1850Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1850 raw1850Labels permutation32 permutation6
    mixedMoment B raw1850step0 raw1850step0Labels = mixedMoment B raw1850step1 raw1850step1Labels := by
      have ha : raw1850step1 = -raw1850step0 := by apply Matrix.ext; change ∀ i j, raw1850step1 i j = -(raw1850step0 i j); unfold raw1850step1 raw1850step0; decide +kernel
      have hl : raw1850step1Labels = raw1850step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1850step1 raw1850step1Labels = mixedMoment B raw1850step2 raw1850step2Labels := by
      have ha : raw1850step2 = raw1850step1 := by apply Matrix.ext; unfold raw1850step2 raw1850step1; decide +kernel
      have hl : raw1850step1Labels = labelEmbedding1 ∘ raw1850step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1850step1 raw1850step1Labels raw1850step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3325 node3325Labels := by rfl

theorem canonical1863 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1863 raw1863Labels = mixedMoment B node4913 node4913Labels := by
  calc
    mixedMoment B raw1863 raw1863Labels = mixedMoment B raw1863step0 raw1863step0Labels := by
      have ha : raw1863step0 = (fun i j => raw1863 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1863step0 raw1863; decide +kernel
      have hl : raw1863step0Labels = raw1863Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1863 raw1863Labels permutation32 permutation4
    mixedMoment B raw1863step0 raw1863step0Labels = mixedMoment B raw1863step1 raw1863step1Labels := by
      have ha : raw1863step1 = raw1863step0 := by apply Matrix.ext; unfold raw1863step1 raw1863step0; decide +kernel
      have hl : raw1863step0Labels = labelEmbedding7 ∘ raw1863step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1863step0 raw1863step0Labels raw1863step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4913 node4913Labels := by rfl

theorem canonical1864 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1864 raw1864Labels = mixedMoment B node2306 node2306Labels := by
  calc
    mixedMoment B raw1864 raw1864Labels = mixedMoment B raw1864step0 raw1864step0Labels := by
      have ha : raw1864step0 = (fun i j => raw1864 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1864step0 raw1864; decide +kernel
      have hl : raw1864step0Labels = raw1864Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1864 raw1864Labels permutation32 permutation4
    _ = mixedMoment B node2306 node2306Labels := by rfl

theorem canonical1865 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1865 raw1865Labels = mixedMoment B node3318 node3318Labels := by
  calc
    mixedMoment B raw1865 raw1865Labels = mixedMoment B raw1865step0 raw1865step0Labels := by
      have ha : raw1865step0 = (fun i j => raw1865 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1865step0 raw1865; decide +kernel
      have hl : raw1865step0Labels = raw1865Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1865 raw1865Labels permutation32 permutation6
    mixedMoment B raw1865step0 raw1865step0Labels = mixedMoment B raw1865step1 raw1865step1Labels := by
      have ha : raw1865step1 = -raw1865step0 := by apply Matrix.ext; change ∀ i j, raw1865step1 i j = -(raw1865step0 i j); unfold raw1865step1 raw1865step0; decide +kernel
      have hl : raw1865step1Labels = raw1865step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1865step1 raw1865step1Labels = mixedMoment B raw1865step2 raw1865step2Labels := by
      have ha : raw1865step2 = raw1865step1 := by apply Matrix.ext; unfold raw1865step2 raw1865step1; decide +kernel
      have hl : raw1865step1Labels = labelEmbedding1 ∘ raw1865step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1865step1 raw1865step1Labels raw1865step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3318 node3318Labels := by rfl

theorem canonical1890 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1890 raw1890Labels = mixedMoment B node4927 node4927Labels := by
  calc
    mixedMoment B raw1890 raw1890Labels = mixedMoment B raw1890step0 raw1890step0Labels := by
      have ha : raw1890step0 = (fun i j => raw1890 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1890step0 raw1890; decide +kernel
      have hl : raw1890step0Labels = raw1890Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1890 raw1890Labels permutation152 permutation4
    mixedMoment B raw1890step0 raw1890step0Labels = mixedMoment B raw1890step1 raw1890step1Labels := by
      have ha : raw1890step1 = raw1890step0 := by apply Matrix.ext; unfold raw1890step1 raw1890step0; decide +kernel
      have hl : raw1890step0Labels = labelEmbedding7 ∘ raw1890step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1890step0 raw1890step0Labels raw1890step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4927 node4927Labels := by rfl

theorem canonical1891 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1891 raw1891Labels = mixedMoment B node2317 node2317Labels := by
  calc
    mixedMoment B raw1891 raw1891Labels = mixedMoment B raw1891step0 raw1891step0Labels := by
      have ha : raw1891step0 = (fun i j => raw1891 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1891step0 raw1891; decide +kernel
      have hl : raw1891step0Labels = raw1891Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1891 raw1891Labels permutation152 permutation4
    _ = mixedMoment B node2317 node2317Labels := by rfl

theorem canonical1892 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1892 raw1892Labels = mixedMoment B node3399 node3399Labels := by
  calc
    mixedMoment B raw1892 raw1892Labels = mixedMoment B raw1892step0 raw1892step0Labels := by
      have ha : raw1892step0 = (fun i j => raw1892 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1892step0 raw1892; decide +kernel
      have hl : raw1892step0Labels = raw1892Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1892 raw1892Labels permutation152 permutation6
    mixedMoment B raw1892step0 raw1892step0Labels = mixedMoment B raw1892step1 raw1892step1Labels := by
      have ha : raw1892step1 = -raw1892step0 := by apply Matrix.ext; change ∀ i j, raw1892step1 i j = -(raw1892step0 i j); unfold raw1892step1 raw1892step0; decide +kernel
      have hl : raw1892step1Labels = raw1892step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1892step1 raw1892step1Labels = mixedMoment B raw1892step2 raw1892step2Labels := by
      have ha : raw1892step2 = raw1892step1 := by apply Matrix.ext; unfold raw1892step2 raw1892step1; decide +kernel
      have hl : raw1892step1Labels = labelEmbedding1 ∘ raw1892step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1892step1 raw1892step1Labels raw1892step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3399 node3399Labels := by rfl

theorem canonical1908 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1908 raw1908Labels = mixedMoment B node4943 node4943Labels := by
  calc
    mixedMoment B raw1908 raw1908Labels = mixedMoment B raw1908step0 raw1908step0Labels := by
      have ha : raw1908step0 = (fun i j => raw1908 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1908step0 raw1908; decide +kernel
      have hl : raw1908step0Labels = raw1908Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1908 raw1908Labels permutation32 permutation4
    mixedMoment B raw1908step0 raw1908step0Labels = mixedMoment B raw1908step1 raw1908step1Labels := by
      have ha : raw1908step1 = raw1908step0 := by apply Matrix.ext; unfold raw1908step1 raw1908step0; decide +kernel
      have hl : raw1908step0Labels = labelEmbedding7 ∘ raw1908step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1908step0 raw1908step0Labels raw1908step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4943 node4943Labels := by rfl

theorem canonical1909 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1909 raw1909Labels = mixedMoment B node2334 node2334Labels := by
  calc
    mixedMoment B raw1909 raw1909Labels = mixedMoment B raw1909step0 raw1909step0Labels := by
      have ha : raw1909step0 = (fun i j => raw1909 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1909step0 raw1909; decide +kernel
      have hl : raw1909step0Labels = raw1909Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1909 raw1909Labels permutation32 permutation4
    _ = mixedMoment B node2334 node2334Labels := by rfl

theorem canonical1910 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1910 raw1910Labels = mixedMoment B node3411 node3411Labels := by
  calc
    mixedMoment B raw1910 raw1910Labels = mixedMoment B raw1910step0 raw1910step0Labels := by
      have ha : raw1910step0 = (fun i j => raw1910 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1910step0 raw1910; decide +kernel
      have hl : raw1910step0Labels = raw1910Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1910 raw1910Labels permutation32 permutation6
    mixedMoment B raw1910step0 raw1910step0Labels = mixedMoment B raw1910step1 raw1910step1Labels := by
      have ha : raw1910step1 = -raw1910step0 := by apply Matrix.ext; change ∀ i j, raw1910step1 i j = -(raw1910step0 i j); unfold raw1910step1 raw1910step0; decide +kernel
      have hl : raw1910step1Labels = raw1910step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1910step1 raw1910step1Labels = mixedMoment B raw1910step2 raw1910step2Labels := by
      have ha : raw1910step2 = raw1910step1 := by apply Matrix.ext; unfold raw1910step2 raw1910step1; decide +kernel
      have hl : raw1910step1Labels = labelEmbedding1 ∘ raw1910step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1910step1 raw1910step1Labels raw1910step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3411 node3411Labels := by rfl

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

theorem canonical1992 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1992 raw1992Labels = mixedMoment B node4986 node4986Labels := by
  calc
    mixedMoment B raw1992 raw1992Labels = mixedMoment B raw1992step0 raw1992step0Labels := by
      have ha : raw1992step0 = (fun i j => raw1992 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1992step0 raw1992; decide +kernel
      have hl : raw1992step0Labels = raw1992Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1992 raw1992Labels permutation152 permutation4
    mixedMoment B raw1992step0 raw1992step0Labels = mixedMoment B raw1992step1 raw1992step1Labels := by
      have ha : raw1992step1 = raw1992step0 := by apply Matrix.ext; unfold raw1992step1 raw1992step0; decide +kernel
      have hl : raw1992step0Labels = labelEmbedding7 ∘ raw1992step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1992step0 raw1992step0Labels raw1992step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4986 node4986Labels := by rfl

theorem canonical1993 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1993 raw1993Labels = mixedMoment B node2371 node2371Labels := by
  calc
    mixedMoment B raw1993 raw1993Labels = mixedMoment B raw1993step0 raw1993step0Labels := by
      have ha : raw1993step0 = (fun i j => raw1993 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1993step0 raw1993; decide +kernel
      have hl : raw1993step0Labels = raw1993Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1993 raw1993Labels permutation152 permutation4
    _ = mixedMoment B node2371 node2371Labels := by rfl

theorem canonical1994 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1994 raw1994Labels = mixedMoment B node3335 node3335Labels := by
  calc
    mixedMoment B raw1994 raw1994Labels = mixedMoment B raw1994step0 raw1994step0Labels := by
      have ha : raw1994step0 = (fun i j => raw1994 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1994step0 raw1994; decide +kernel
      have hl : raw1994step0Labels = raw1994Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1994 raw1994Labels permutation152 permutation6
    mixedMoment B raw1994step0 raw1994step0Labels = mixedMoment B raw1994step1 raw1994step1Labels := by
      have ha : raw1994step1 = -raw1994step0 := by apply Matrix.ext; change ∀ i j, raw1994step1 i j = -(raw1994step0 i j); unfold raw1994step1 raw1994step0; decide +kernel
      have hl : raw1994step1Labels = raw1994step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1994step1 raw1994step1Labels = mixedMoment B raw1994step2 raw1994step2Labels := by
      have ha : raw1994step2 = raw1994step1 := by apply Matrix.ext; unfold raw1994step2 raw1994step1; decide +kernel
      have hl : raw1994step1Labels = labelEmbedding1 ∘ raw1994step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1994step1 raw1994step1Labels raw1994step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3335 node3335Labels := by rfl

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

theorem canonical2052 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2052 raw2052Labels = mixedMoment B node5033 node5033Labels := by
  calc
    mixedMoment B raw2052 raw2052Labels = mixedMoment B raw2052step0 raw2052step0Labels := by
      have ha : raw2052step0 = (fun i j => raw2052 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2052step0 raw2052; decide +kernel
      have hl : raw2052step0Labels = raw2052Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2052 raw2052Labels permutation152 permutation4
    mixedMoment B raw2052step0 raw2052step0Labels = mixedMoment B raw2052step1 raw2052step1Labels := by
      have ha : raw2052step1 = raw2052step0 := by apply Matrix.ext; unfold raw2052step1 raw2052step0; decide +kernel
      have hl : raw2052step0Labels = labelEmbedding7 ∘ raw2052step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2052step0 raw2052step0Labels raw2052step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5033 node5033Labels := by rfl

theorem canonical2053 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2053 raw2053Labels = mixedMoment B node2425 node2425Labels := by
  calc
    mixedMoment B raw2053 raw2053Labels = mixedMoment B raw2053step0 raw2053step0Labels := by
      have ha : raw2053step0 = (fun i j => raw2053 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2053step0 raw2053; decide +kernel
      have hl : raw2053step0Labels = raw2053Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2053 raw2053Labels permutation152 permutation4
    _ = mixedMoment B node2425 node2425Labels := by rfl

theorem canonical2054 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2054 raw2054Labels = mixedMoment B node3449 node3449Labels := by
  calc
    mixedMoment B raw2054 raw2054Labels = mixedMoment B raw2054step0 raw2054step0Labels := by
      have ha : raw2054step0 = (fun i j => raw2054 (permutation688 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2054step0 raw2054; decide +kernel
      have hl : raw2054step0Labels = raw2054Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2054 raw2054Labels permutation688 permutation6
    mixedMoment B raw2054step0 raw2054step0Labels = mixedMoment B raw2054step1 raw2054step1Labels := by
      have ha : raw2054step1 = raw2054step0 := by apply Matrix.ext; unfold raw2054step1 raw2054step0; decide +kernel
      have hl : raw2054step0Labels = labelEmbedding1 ∘ raw2054step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2054step0 raw2054step0Labels raw2054step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3449 node3449Labels := by rfl

theorem canonical2073 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2073 raw2073Labels = mixedMoment B node5047 node5047Labels := by
  calc
    mixedMoment B raw2073 raw2073Labels = mixedMoment B raw2073step0 raw2073step0Labels := by
      have ha : raw2073step0 = (fun i j => raw2073 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2073step0 raw2073; decide +kernel
      have hl : raw2073step0Labels = raw2073Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2073 raw2073Labels permutation152 permutation4
    mixedMoment B raw2073step0 raw2073step0Labels = mixedMoment B raw2073step1 raw2073step1Labels := by
      have ha : raw2073step1 = raw2073step0 := by apply Matrix.ext; unfold raw2073step1 raw2073step0; decide +kernel
      have hl : raw2073step0Labels = labelEmbedding7 ∘ raw2073step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2073step0 raw2073step0Labels raw2073step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5047 node5047Labels := by rfl

theorem canonical2074 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2074 raw2074Labels = mixedMoment B node2449 node2449Labels := by
  calc
    mixedMoment B raw2074 raw2074Labels = mixedMoment B raw2074step0 raw2074step0Labels := by
      have ha : raw2074step0 = (fun i j => raw2074 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2074step0 raw2074; decide +kernel
      have hl : raw2074step0Labels = raw2074Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2074 raw2074Labels permutation152 permutation4
    _ = mixedMoment B node2449 node2449Labels := by rfl

theorem canonical2075 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2075 raw2075Labels = mixedMoment B node3432 node3432Labels := by
  calc
    mixedMoment B raw2075 raw2075Labels = mixedMoment B raw2075step0 raw2075step0Labels := by
      have ha : raw2075step0 = (fun i j => raw2075 (permutation688 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2075step0 raw2075; decide +kernel
      have hl : raw2075step0Labels = raw2075Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2075 raw2075Labels permutation688 permutation6
    mixedMoment B raw2075step0 raw2075step0Labels = mixedMoment B raw2075step1 raw2075step1Labels := by
      have ha : raw2075step1 = raw2075step0 := by apply Matrix.ext; unfold raw2075step1 raw2075step0; decide +kernel
      have hl : raw2075step0Labels = labelEmbedding1 ∘ raw2075step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2075step0 raw2075step0Labels raw2075step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3432 node3432Labels := by rfl

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

theorem canonical2109 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2109 raw2109Labels = mixedMoment B node5081 node5081Labels := by
  calc
    mixedMoment B raw2109 raw2109Labels = mixedMoment B raw2109step0 raw2109step0Labels := by
      have ha : raw2109step0 = (fun i j => raw2109 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2109step0 raw2109; decide +kernel
      have hl : raw2109step0Labels = raw2109Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2109 raw2109Labels permutation32 permutation4
    mixedMoment B raw2109step0 raw2109step0Labels = mixedMoment B raw2109step1 raw2109step1Labels := by
      have ha : raw2109step1 = raw2109step0 := by apply Matrix.ext; unfold raw2109step1 raw2109step0; decide +kernel
      have hl : raw2109step0Labels = labelEmbedding7 ∘ raw2109step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2109step0 raw2109step0Labels raw2109step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5081 node5081Labels := by rfl

theorem canonical2110 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2110 raw2110Labels = mixedMoment B node2489 node2489Labels := by
  calc
    mixedMoment B raw2110 raw2110Labels = mixedMoment B raw2110step0 raw2110step0Labels := by
      have ha : raw2110step0 = (fun i j => raw2110 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2110step0 raw2110; decide +kernel
      have hl : raw2110step0Labels = raw2110Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2110 raw2110Labels permutation32 permutation4
    _ = mixedMoment B node2489 node2489Labels := by rfl

theorem canonical2111 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2111 raw2111Labels = mixedMoment B node3482 node3482Labels := by
  calc
    mixedMoment B raw2111 raw2111Labels = mixedMoment B raw2111step0 raw2111step0Labels := by
      have ha : raw2111step0 = (fun i j => raw2111 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2111step0 raw2111; decide +kernel
      have hl : raw2111step0Labels = raw2111Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2111 raw2111Labels permutation32 permutation6
    mixedMoment B raw2111step0 raw2111step0Labels = mixedMoment B raw2111step1 raw2111step1Labels := by
      have ha : raw2111step1 = -raw2111step0 := by apply Matrix.ext; change ∀ i j, raw2111step1 i j = -(raw2111step0 i j); unfold raw2111step1 raw2111step0; decide +kernel
      have hl : raw2111step1Labels = raw2111step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2111step1 raw2111step1Labels = mixedMoment B raw2111step2 raw2111step2Labels := by
      have ha : raw2111step2 = raw2111step1 := by apply Matrix.ext; unfold raw2111step2 raw2111step1; decide +kernel
      have hl : raw2111step1Labels = labelEmbedding1 ∘ raw2111step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2111step1 raw2111step1Labels raw2111step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3482 node3482Labels := by rfl

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

theorem canonical2166 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2166 raw2166Labels = mixedMoment B node5137 node5137Labels := by
  calc
    mixedMoment B raw2166 raw2166Labels = mixedMoment B raw2166step0 raw2166step0Labels := by
      have ha : raw2166step0 = (fun i j => raw2166 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2166step0 raw2166; decide +kernel
      have hl : raw2166step0Labels = raw2166Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2166 raw2166Labels permutation152 permutation4
    mixedMoment B raw2166step0 raw2166step0Labels = mixedMoment B raw2166step1 raw2166step1Labels := by
      have ha : raw2166step1 = raw2166step0 := by apply Matrix.ext; unfold raw2166step1 raw2166step0; decide +kernel
      have hl : raw2166step0Labels = labelEmbedding7 ∘ raw2166step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2166step0 raw2166step0Labels raw2166step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5137 node5137Labels := by rfl

theorem canonical2167 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2167 raw2167Labels = mixedMoment B node2556 node2556Labels := by
  calc
    mixedMoment B raw2167 raw2167Labels = mixedMoment B raw2167step0 raw2167step0Labels := by
      have ha : raw2167step0 = (fun i j => raw2167 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2167step0 raw2167; decide +kernel
      have hl : raw2167step0Labels = raw2167Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2167 raw2167Labels permutation152 permutation4
    _ = mixedMoment B node2556 node2556Labels := by rfl

theorem canonical2168 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2168 raw2168Labels = mixedMoment B node3521 node3521Labels := by
  calc
    mixedMoment B raw2168 raw2168Labels = mixedMoment B raw2168step0 raw2168step0Labels := by
      have ha : raw2168step0 = (fun i j => raw2168 (permutation176 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2168step0 raw2168; decide +kernel
      have hl : raw2168step0Labels = raw2168Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2168 raw2168Labels permutation176 permutation6
    mixedMoment B raw2168step0 raw2168step0Labels = mixedMoment B raw2168step1 raw2168step1Labels := by
      have ha : raw2168step1 = -raw2168step0 := by apply Matrix.ext; change ∀ i j, raw2168step1 i j = -(raw2168step0 i j); unfold raw2168step1 raw2168step0; decide +kernel
      have hl : raw2168step1Labels = raw2168step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2168step1 raw2168step1Labels = mixedMoment B raw2168step2 raw2168step2Labels := by
      have ha : raw2168step2 = raw2168step1 := by apply Matrix.ext; unfold raw2168step2 raw2168step1; decide +kernel
      have hl : raw2168step1Labels = labelEmbedding1 ∘ raw2168step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2168step1 raw2168step1Labels raw2168step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3521 node3521Labels := by rfl

theorem canonical2169 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2169 raw2169Labels = mixedMoment B node5141 node5141Labels := by
  calc
    mixedMoment B raw2169 raw2169Labels = mixedMoment B raw2169step0 raw2169step0Labels := by
      have ha : raw2169step0 = (fun i j => raw2169 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2169step0 raw2169; decide +kernel
      have hl : raw2169step0Labels = raw2169Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2169 raw2169Labels permutation32 permutation4
    mixedMoment B raw2169step0 raw2169step0Labels = mixedMoment B raw2169step1 raw2169step1Labels := by
      have ha : raw2169step1 = raw2169step0 := by apply Matrix.ext; unfold raw2169step1 raw2169step0; decide +kernel
      have hl : raw2169step0Labels = labelEmbedding7 ∘ raw2169step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2169step0 raw2169step0Labels raw2169step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5141 node5141Labels := by rfl

theorem canonical2170 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2170 raw2170Labels = mixedMoment B node2561 node2561Labels := by
  calc
    mixedMoment B raw2170 raw2170Labels = mixedMoment B raw2170step0 raw2170step0Labels := by
      have ha : raw2170step0 = (fun i j => raw2170 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2170step0 raw2170; decide +kernel
      have hl : raw2170step0Labels = raw2170Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2170 raw2170Labels permutation32 permutation4
    _ = mixedMoment B node2561 node2561Labels := by rfl

theorem canonical2171 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2171 raw2171Labels = mixedMoment B node3522 node3522Labels := by
  calc
    mixedMoment B raw2171 raw2171Labels = mixedMoment B raw2171step0 raw2171step0Labels := by
      have ha : raw2171step0 = (fun i j => raw2171 (permutation38 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2171step0 raw2171; decide +kernel
      have hl : raw2171step0Labels = raw2171Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2171 raw2171Labels permutation38 permutation6
    mixedMoment B raw2171step0 raw2171step0Labels = mixedMoment B raw2171step1 raw2171step1Labels := by
      have ha : raw2171step1 = -raw2171step0 := by apply Matrix.ext; change ∀ i j, raw2171step1 i j = -(raw2171step0 i j); unfold raw2171step1 raw2171step0; decide +kernel
      have hl : raw2171step1Labels = raw2171step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2171step1 raw2171step1Labels = mixedMoment B raw2171step2 raw2171step2Labels := by
      have ha : raw2171step2 = raw2171step1 := by apply Matrix.ext; unfold raw2171step2 raw2171step1; decide +kernel
      have hl : raw2171step1Labels = labelEmbedding1 ∘ raw2171step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2171step1 raw2171step1Labels raw2171step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3522 node3522Labels := by rfl

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

theorem canonical2205 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2205 raw2205Labels = mixedMoment B node5171 node5171Labels := by
  calc
    mixedMoment B raw2205 raw2205Labels = mixedMoment B raw2205step0 raw2205step0Labels := by
      have ha : raw2205step0 = (fun i j => raw2205 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2205step0 raw2205; decide +kernel
      have hl : raw2205step0Labels = raw2205Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2205 raw2205Labels permutation8 permutation4
    mixedMoment B raw2205step0 raw2205step0Labels = mixedMoment B raw2205step1 raw2205step1Labels := by
      have ha : raw2205step1 = raw2205step0 := by apply Matrix.ext; unfold raw2205step1 raw2205step0; decide +kernel
      have hl : raw2205step0Labels = labelEmbedding7 ∘ raw2205step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2205step0 raw2205step0Labels raw2205step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5171 node5171Labels := by rfl

theorem canonical2206 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2206 raw2206Labels = mixedMoment B node2598 node2598Labels := by
  calc
    mixedMoment B raw2206 raw2206Labels = mixedMoment B raw2206step0 raw2206step0Labels := by
      have ha : raw2206step0 = (fun i j => raw2206 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2206step0 raw2206; decide +kernel
      have hl : raw2206step0Labels = raw2206Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2206 raw2206Labels permutation8 permutation4
    _ = mixedMoment B node2598 node2598Labels := by rfl

theorem canonical2207 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2207 raw2207Labels = mixedMoment B node3608 node3608Labels := by
  calc
    mixedMoment B raw2207 raw2207Labels = mixedMoment B raw2207step0 raw2207step0Labels := by
      have ha : raw2207step0 = (fun i j => raw2207 (permutation31 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2207step0 raw2207; decide +kernel
      have hl : raw2207step0Labels = raw2207Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2207 raw2207Labels permutation31 permutation6
    mixedMoment B raw2207step0 raw2207step0Labels = mixedMoment B raw2207step1 raw2207step1Labels := by
      have ha : raw2207step1 = raw2207step0 := by apply Matrix.ext; unfold raw2207step1 raw2207step0; decide +kernel
      have hl : raw2207step0Labels = labelEmbedding1 ∘ raw2207step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2207step0 raw2207step0Labels raw2207step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3608 node3608Labels := by rfl

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

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical224
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical28764 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28764 raw28764Labels = mixedMoment B node4322 node4322Labels := by
  calc
    mixedMoment B raw28764 raw28764Labels = mixedMoment B raw28764step0 raw28764step0Labels := by
      have ha : raw28764step0 = (fun i j => raw28764 (permutation158 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28764step0 raw28764; decide +kernel
      have hl : raw28764step0Labels = raw28764Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28764 raw28764Labels permutation158 permutation3
    mixedMoment B raw28764step0 raw28764step0Labels = mixedMoment B raw28764step1 raw28764step1Labels := by
      have ha : raw28764step1 = raw28764step0 := by apply Matrix.ext; unfold raw28764step1 raw28764step0; decide +kernel
      have hl : raw28764step0Labels = labelEmbedding6 ∘ raw28764step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28764step0 raw28764step0Labels raw28764step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4322 node4322Labels := by rfl

theorem canonical28765 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28765 raw28765Labels = mixedMoment B node4927 node4927Labels := by
  calc
    mixedMoment B raw28765 raw28765Labels = mixedMoment B raw28765step0 raw28765step0Labels := by
      have ha : raw28765step0 = (fun i j => raw28765 (permutation158 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28765step0 raw28765; decide +kernel
      have hl : raw28765step0Labels = raw28765Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28765 raw28765Labels permutation158 permutation3
    mixedMoment B raw28765step0 raw28765step0Labels = mixedMoment B raw28765step1 raw28765step1Labels := by
      have ha : raw28765step1 = raw28765step0 := by apply Matrix.ext; unfold raw28765step1 raw28765step0; decide +kernel
      have hl : raw28765step0Labels = labelEmbedding6 ∘ raw28765step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28765step0 raw28765step0Labels raw28765step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4927 node4927Labels := by rfl

theorem canonical28766 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28766 raw28766Labels = mixedMoment B node4986 node4986Labels := by
  calc
    mixedMoment B raw28766 raw28766Labels = mixedMoment B raw28766step0 raw28766step0Labels := by
      have ha : raw28766step0 = (fun i j => raw28766 (permutation200 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28766step0 raw28766; decide +kernel
      have hl : raw28766step0Labels = raw28766Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28766 raw28766Labels permutation200 permutation3
    mixedMoment B raw28766step0 raw28766step0Labels = mixedMoment B raw28766step1 raw28766step1Labels := by
      have ha : raw28766step1 = raw28766step0 := by apply Matrix.ext; unfold raw28766step1 raw28766step0; decide +kernel
      have hl : raw28766step0Labels = labelEmbedding6 ∘ raw28766step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28766step0 raw28766step0Labels raw28766step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4986 node4986Labels := by rfl

theorem canonical28767 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28767 raw28767Labels = mixedMoment B node5075 node5075Labels := by
  calc
    mixedMoment B raw28767 raw28767Labels = mixedMoment B raw28767step0 raw28767step0Labels := by
      have hz : ∀ j, raw28767 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw28767step0 = (fun i j => raw28767 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw28767step0 raw28767; decide +kernel
      have hl : raw28767step0Labels = raw28767Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28767 raw28767Labels permutation520 hz
    mixedMoment B raw28767step0 raw28767step0Labels = mixedMoment B raw28767step1 raw28767step1Labels := by
      have ha : raw28767step1 = (fun i j => raw28767step0 (permutation145 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28767step1 raw28767step0; decide +kernel
      have hl : raw28767step1Labels = raw28767step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28767step0 raw28767step0Labels permutation145 permutation3
    mixedMoment B raw28767step1 raw28767step1Labels = mixedMoment B raw28767step2 raw28767step2Labels := by
      have ha : raw28767step2 = -raw28767step1 := by apply Matrix.ext; change ∀ i j, raw28767step2 i j = -(raw28767step1 i j); unfold raw28767step2 raw28767step1; decide +kernel
      have hl : raw28767step2Labels = raw28767step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw28767step2 raw28767step2Labels = mixedMoment B raw28767step3 raw28767step3Labels := by
      have ha : raw28767step3 = raw28767step2 := by apply Matrix.ext; unfold raw28767step3 raw28767step2; decide +kernel
      have hl : raw28767step2Labels = labelEmbedding6 ∘ raw28767step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28767step2 raw28767step2Labels raw28767step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5075 node5075Labels := by rfl

theorem canonical28768 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28768 raw28768Labels = mixedMoment B node4346 node4346Labels := by
  calc
    mixedMoment B raw28768 raw28768Labels = mixedMoment B raw28768step0 raw28768step0Labels := by
      have hz : ∀ j, raw28768 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28768step0 = (fun i j => raw28768 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28768step0 raw28768; decide +kernel
      have hl : raw28768step0Labels = raw28768Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28768 raw28768Labels permutation346 hz
    mixedMoment B raw28768step0 raw28768step0Labels = mixedMoment B raw28768step1 raw28768step1Labels := by
      have ha : raw28768step1 = (fun i j => raw28768step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28768step1 raw28768step0; decide +kernel
      have hl : raw28768step1Labels = raw28768step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28768step0 raw28768step0Labels permutation32 permutation3
    mixedMoment B raw28768step1 raw28768step1Labels = mixedMoment B raw28768step2 raw28768step2Labels := by
      have ha : raw28768step2 = raw28768step1 := by apply Matrix.ext; unfold raw28768step2 raw28768step1; decide +kernel
      have hl : raw28768step1Labels = labelEmbedding6 ∘ raw28768step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28768step1 raw28768step1Labels raw28768step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4346 node4346Labels := by rfl

theorem canonical28769 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28769 raw28769Labels = mixedMoment B node4943 node4943Labels := by
  calc
    mixedMoment B raw28769 raw28769Labels = mixedMoment B raw28769step0 raw28769step0Labels := by
      have hz : ∀ j, raw28769 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28769step0 = (fun i j => raw28769 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28769step0 raw28769; decide +kernel
      have hl : raw28769step0Labels = raw28769Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28769 raw28769Labels permutation346 hz
    mixedMoment B raw28769step0 raw28769step0Labels = mixedMoment B raw28769step1 raw28769step1Labels := by
      have ha : raw28769step1 = (fun i j => raw28769step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28769step1 raw28769step0; decide +kernel
      have hl : raw28769step1Labels = raw28769step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28769step0 raw28769step0Labels permutation32 permutation3
    mixedMoment B raw28769step1 raw28769step1Labels = mixedMoment B raw28769step2 raw28769step2Labels := by
      have ha : raw28769step2 = raw28769step1 := by apply Matrix.ext; unfold raw28769step2 raw28769step1; decide +kernel
      have hl : raw28769step1Labels = labelEmbedding6 ∘ raw28769step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28769step1 raw28769step1Labels raw28769step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4943 node4943Labels := by rfl

theorem canonical28770 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28770 raw28770Labels = mixedMoment B node5033 node5033Labels := by
  calc
    mixedMoment B raw28770 raw28770Labels = mixedMoment B raw28770step0 raw28770step0Labels := by
      have ha : raw28770step0 = (fun i j => raw28770 (permutation176 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28770step0 raw28770; decide +kernel
      have hl : raw28770step0Labels = raw28770Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28770 raw28770Labels permutation176 permutation3
    mixedMoment B raw28770step0 raw28770step0Labels = mixedMoment B raw28770step1 raw28770step1Labels := by
      have ha : raw28770step1 = raw28770step0 := by apply Matrix.ext; unfold raw28770step1 raw28770step0; decide +kernel
      have hl : raw28770step0Labels = labelEmbedding6 ∘ raw28770step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28770step0 raw28770step0Labels raw28770step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5033 node5033Labels := by rfl

theorem canonical28771 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28771 raw28771Labels = mixedMoment B node5171 node5171Labels := by
  calc
    mixedMoment B raw28771 raw28771Labels = mixedMoment B raw28771step0 raw28771step0Labels := by
      have hz : ∀ j, raw28771 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw28771step0 = (fun i j => raw28771 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw28771step0 raw28771; decide +kernel
      have hl : raw28771step0Labels = raw28771Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28771 raw28771Labels permutation520 hz
    mixedMoment B raw28771step0 raw28771step0Labels = mixedMoment B raw28771step1 raw28771step1Labels := by
      have hz : ∀ j, raw28771step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw28771step1 = (fun i j => raw28771step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw28771step1 raw28771step0; decide +kernel
      have hl : raw28771step1Labels = raw28771step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28771step0 raw28771step0Labels permutation80 hz
    mixedMoment B raw28771step1 raw28771step1Labels = mixedMoment B raw28771step2 raw28771step2Labels := by
      have ha : raw28771step2 = (fun i j => raw28771step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28771step2 raw28771step1; decide +kernel
      have hl : raw28771step2Labels = raw28771step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28771step1 raw28771step1Labels permutation8 permutation3
    mixedMoment B raw28771step2 raw28771step2Labels = mixedMoment B raw28771step3 raw28771step3Labels := by
      have ha : raw28771step3 = raw28771step2 := by apply Matrix.ext; unfold raw28771step3 raw28771step2; decide +kernel
      have hl : raw28771step2Labels = labelEmbedding6 ∘ raw28771step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28771step2 raw28771step2Labels raw28771step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5171 node5171Labels := by rfl

theorem canonical28772 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28772 raw28772Labels = mixedMoment B node4325 node4325Labels := by
  calc
    mixedMoment B raw28772 raw28772Labels = mixedMoment B raw28772step0 raw28772step0Labels := by
      have hz : ∀ j, raw28772 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28772step0 = (fun i j => raw28772 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28772step0 raw28772; decide +kernel
      have hl : raw28772step0Labels = raw28772Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28772 raw28772Labels permutation346 hz
    mixedMoment B raw28772step0 raw28772step0Labels = mixedMoment B raw28772step1 raw28772step1Labels := by
      have ha : raw28772step1 = (fun i j => raw28772step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28772step1 raw28772step0; decide +kernel
      have hl : raw28772step1Labels = raw28772step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28772step0 raw28772step0Labels permutation32 permutation3
    mixedMoment B raw28772step1 raw28772step1Labels = mixedMoment B raw28772step2 raw28772step2Labels := by
      have ha : raw28772step2 = raw28772step1 := by apply Matrix.ext; unfold raw28772step2 raw28772step1; decide +kernel
      have hl : raw28772step1Labels = labelEmbedding6 ∘ raw28772step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28772step1 raw28772step1Labels raw28772step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4325 node4325Labels := by rfl

theorem canonical28773 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28773 raw28773Labels = mixedMoment B node4907 node4907Labels := by
  calc
    mixedMoment B raw28773 raw28773Labels = mixedMoment B raw28773step0 raw28773step0Labels := by
      have hz : ∀ j, raw28773 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28773step0 = (fun i j => raw28773 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28773step0 raw28773; decide +kernel
      have hl : raw28773step0Labels = raw28773Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28773 raw28773Labels permutation346 hz
    mixedMoment B raw28773step0 raw28773step0Labels = mixedMoment B raw28773step1 raw28773step1Labels := by
      have ha : raw28773step1 = (fun i j => raw28773step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28773step1 raw28773step0; decide +kernel
      have hl : raw28773step1Labels = raw28773step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28773step0 raw28773step0Labels permutation151 permutation3
    mixedMoment B raw28773step1 raw28773step1Labels = mixedMoment B raw28773step2 raw28773step2Labels := by
      have ha : raw28773step2 = -raw28773step1 := by apply Matrix.ext; change ∀ i j, raw28773step2 i j = -(raw28773step1 i j); unfold raw28773step2 raw28773step1; decide +kernel
      have hl : raw28773step2Labels = raw28773step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw28773step2 raw28773step2Labels = mixedMoment B raw28773step3 raw28773step3Labels := by
      have ha : raw28773step3 = raw28773step2 := by apply Matrix.ext; unfold raw28773step3 raw28773step2; decide +kernel
      have hl : raw28773step2Labels = labelEmbedding6 ∘ raw28773step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28773step2 raw28773step2Labels raw28773step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4907 node4907Labels := by rfl

theorem canonical28774 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28774 raw28774Labels = mixedMoment B node4902 node4902Labels := by
  calc
    mixedMoment B raw28774 raw28774Labels = mixedMoment B raw28774step0 raw28774step0Labels := by
      have ha : raw28774step0 = (fun i j => raw28774 (permutation686 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28774step0 raw28774; decide +kernel
      have hl : raw28774step0Labels = raw28774Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28774 raw28774Labels permutation686 permutation3
    mixedMoment B raw28774step0 raw28774step0Labels = mixedMoment B raw28774step1 raw28774step1Labels := by
      have ha : raw28774step1 = -raw28774step0 := by apply Matrix.ext; change ∀ i j, raw28774step1 i j = -(raw28774step0 i j); unfold raw28774step1 raw28774step0; decide +kernel
      have hl : raw28774step1Labels = raw28774step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw28774step1 raw28774step1Labels = mixedMoment B raw28774step2 raw28774step2Labels := by
      have ha : raw28774step2 = raw28774step1 := by apply Matrix.ext; unfold raw28774step2 raw28774step1; decide +kernel
      have hl : raw28774step1Labels = labelEmbedding6 ∘ raw28774step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28774step1 raw28774step1Labels raw28774step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4902 node4902Labels := by rfl

theorem canonical28775 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28775 raw28775Labels = mixedMoment B node4913 node4913Labels := by
  calc
    mixedMoment B raw28775 raw28775Labels = mixedMoment B raw28775step0 raw28775step0Labels := by
      have hz : ∀ j, raw28775 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28775step0 = (fun i j => raw28775 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28775step0 raw28775; decide +kernel
      have hl : raw28775step0Labels = raw28775Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28775 raw28775Labels permutation346 hz
    mixedMoment B raw28775step0 raw28775step0Labels = mixedMoment B raw28775step1 raw28775step1Labels := by
      have ha : raw28775step1 = (fun i j => raw28775step0 (permutation149 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28775step1 raw28775step0; decide +kernel
      have hl : raw28775step1Labels = raw28775step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28775step0 raw28775step0Labels permutation149 permutation3
    mixedMoment B raw28775step1 raw28775step1Labels = mixedMoment B raw28775step2 raw28775step2Labels := by
      have ha : raw28775step2 = -raw28775step1 := by apply Matrix.ext; change ∀ i j, raw28775step2 i j = -(raw28775step1 i j); unfold raw28775step2 raw28775step1; decide +kernel
      have hl : raw28775step2Labels = raw28775step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw28775step2 raw28775step2Labels = mixedMoment B raw28775step3 raw28775step3Labels := by
      have ha : raw28775step3 = raw28775step2 := by apply Matrix.ext; unfold raw28775step3 raw28775step2; decide +kernel
      have hl : raw28775step2Labels = labelEmbedding6 ∘ raw28775step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28775step2 raw28775step2Labels raw28775step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4913 node4913Labels := by rfl

theorem canonical28776 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28776 raw28776Labels = mixedMoment B node4289 node4289Labels := by
  calc
    mixedMoment B raw28776 raw28776Labels = mixedMoment B raw28776step0 raw28776step0Labels := by
      have hz : ∀ j, raw28776 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28776step0 = (fun i j => raw28776 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28776step0 raw28776; decide +kernel
      have hl : raw28776step0Labels = raw28776Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28776 raw28776Labels permutation346 hz
    mixedMoment B raw28776step0 raw28776step0Labels = mixedMoment B raw28776step1 raw28776step1Labels := by
      have ha : raw28776step1 = (fun i j => raw28776step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28776step1 raw28776step0; decide +kernel
      have hl : raw28776step1Labels = raw28776step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28776step0 raw28776step0Labels permutation151 permutation3
    mixedMoment B raw28776step1 raw28776step1Labels = mixedMoment B raw28776step2 raw28776step2Labels := by
      have ha : raw28776step2 = -raw28776step1 := by apply Matrix.ext; change ∀ i j, raw28776step2 i j = -(raw28776step1 i j); unfold raw28776step2 raw28776step1; decide +kernel
      have hl : raw28776step2Labels = raw28776step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw28776step2 raw28776step2Labels = mixedMoment B raw28776step3 raw28776step3Labels := by
      have ha : raw28776step3 = raw28776step2 := by apply Matrix.ext; unfold raw28776step3 raw28776step2; decide +kernel
      have hl : raw28776step2Labels = labelEmbedding6 ∘ raw28776step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28776step2 raw28776step2Labels raw28776step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4289 node4289Labels := by rfl

theorem canonical28777 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28777 raw28777Labels = mixedMoment B node4295 node4295Labels := by
  calc
    mixedMoment B raw28777 raw28777Labels = mixedMoment B raw28777step0 raw28777step0Labels := by
      have hz : ∀ j, raw28777 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28777step0 = (fun i j => raw28777 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28777step0 raw28777; decide +kernel
      have hl : raw28777step0Labels = raw28777Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28777 raw28777Labels permutation346 hz
    mixedMoment B raw28777step0 raw28777step0Labels = mixedMoment B raw28777step1 raw28777step1Labels := by
      have ha : raw28777step1 = (fun i j => raw28777step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28777step1 raw28777step0; decide +kernel
      have hl : raw28777step1Labels = raw28777step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28777step0 raw28777step0Labels permutation151 permutation3
    mixedMoment B raw28777step1 raw28777step1Labels = mixedMoment B raw28777step2 raw28777step2Labels := by
      have ha : raw28777step2 = -raw28777step1 := by apply Matrix.ext; change ∀ i j, raw28777step2 i j = -(raw28777step1 i j); unfold raw28777step2 raw28777step1; decide +kernel
      have hl : raw28777step2Labels = raw28777step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw28777step2 raw28777step2Labels = mixedMoment B raw28777step3 raw28777step3Labels := by
      have ha : raw28777step3 = raw28777step2 := by apply Matrix.ext; unfold raw28777step3 raw28777step2; decide +kernel
      have hl : raw28777step2Labels = labelEmbedding6 ∘ raw28777step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28777step2 raw28777step2Labels raw28777step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4295 node4295Labels := by rfl

theorem canonical28778 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28778 raw28778Labels = mixedMoment B node4287 node4287Labels := by
  calc
    mixedMoment B raw28778 raw28778Labels = mixedMoment B raw28778step0 raw28778step0Labels := by
      have ha : raw28778step0 = (fun i j => raw28778 (permutation686 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28778step0 raw28778; decide +kernel
      have hl : raw28778step0Labels = raw28778Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28778 raw28778Labels permutation686 permutation3
    mixedMoment B raw28778step0 raw28778step0Labels = mixedMoment B raw28778step1 raw28778step1Labels := by
      have ha : raw28778step1 = -raw28778step0 := by apply Matrix.ext; change ∀ i j, raw28778step1 i j = -(raw28778step0 i j); unfold raw28778step1 raw28778step0; decide +kernel
      have hl : raw28778step1Labels = raw28778step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw28778step1 raw28778step1Labels = mixedMoment B raw28778step2 raw28778step2Labels := by
      have ha : raw28778step2 = raw28778step1 := by apply Matrix.ext; unfold raw28778step2 raw28778step1; decide +kernel
      have hl : raw28778step1Labels = labelEmbedding6 ∘ raw28778step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28778step1 raw28778step1Labels raw28778step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4287 node4287Labels := by rfl

theorem canonical28779 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28779 raw28779Labels = mixedMoment B node4303 node4303Labels := by
  calc
    mixedMoment B raw28779 raw28779Labels = mixedMoment B raw28779step0 raw28779step0Labels := by
      have hz : ∀ j, raw28779 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28779step0 = (fun i j => raw28779 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28779step0 raw28779; decide +kernel
      have hl : raw28779step0Labels = raw28779Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28779 raw28779Labels permutation346 hz
    mixedMoment B raw28779step0 raw28779step0Labels = mixedMoment B raw28779step1 raw28779step1Labels := by
      have ha : raw28779step1 = (fun i j => raw28779step0 (permutation149 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28779step1 raw28779step0; decide +kernel
      have hl : raw28779step1Labels = raw28779step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28779step0 raw28779step0Labels permutation149 permutation3
    mixedMoment B raw28779step1 raw28779step1Labels = mixedMoment B raw28779step2 raw28779step2Labels := by
      have ha : raw28779step2 = -raw28779step1 := by apply Matrix.ext; change ∀ i j, raw28779step2 i j = -(raw28779step1 i j); unfold raw28779step2 raw28779step1; decide +kernel
      have hl : raw28779step2Labels = raw28779step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw28779step2 raw28779step2Labels = mixedMoment B raw28779step3 raw28779step3Labels := by
      have ha : raw28779step3 = raw28779step2 := by apply Matrix.ext; unfold raw28779step3 raw28779step2; decide +kernel
      have hl : raw28779step2Labels = labelEmbedding6 ∘ raw28779step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28779step2 raw28779step2Labels raw28779step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4303 node4303Labels := by rfl

theorem canonical28780 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28780 raw28780Labels = mixedMoment B node4460 node4460Labels := by
  calc
    mixedMoment B raw28780 raw28780Labels = mixedMoment B raw28780step0 raw28780step0Labels := by
      have hz : ∀ j, raw28780 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw28780step0 = (fun i j => raw28780 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw28780step0 raw28780; decide +kernel
      have hl : raw28780step0Labels = raw28780Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28780 raw28780Labels permutation520 hz
    mixedMoment B raw28780step0 raw28780step0Labels = mixedMoment B raw28780step1 raw28780step1Labels := by
      have hz : ∀ j, raw28780step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw28780step1 = (fun i j => raw28780step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw28780step1 raw28780step0; decide +kernel
      have hl : raw28780step1Labels = raw28780step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28780step0 raw28780step0Labels permutation80 hz
    mixedMoment B raw28780step1 raw28780step1Labels = mixedMoment B raw28780step2 raw28780step2Labels := by
      have ha : raw28780step2 = (fun i j => raw28780step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28780step2 raw28780step1; decide +kernel
      have hl : raw28780step2Labels = raw28780step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28780step1 raw28780step1Labels permutation31 permutation3
    mixedMoment B raw28780step2 raw28780step2Labels = mixedMoment B raw28780step3 raw28780step3Labels := by
      have ha : raw28780step3 = -raw28780step2 := by apply Matrix.ext; change ∀ i j, raw28780step3 i j = -(raw28780step2 i j); unfold raw28780step3 raw28780step2; decide +kernel
      have hl : raw28780step3Labels = raw28780step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw28780step3 raw28780step3Labels = mixedMoment B raw28780step4 raw28780step4Labels := by
      have ha : raw28780step4 = raw28780step3 := by apply Matrix.ext; unfold raw28780step4 raw28780step3; decide +kernel
      have hl : raw28780step3Labels = labelEmbedding6 ∘ raw28780step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28780step3 raw28780step3Labels raw28780step4Labels labelEmbedding6 hl
    _ = mixedMoment B node4460 node4460Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical24
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical3144 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3144 raw3144Labels = mixedMoment B node5259 node5259Labels := by
  calc
    mixedMoment B raw3144 raw3144Labels = mixedMoment B raw3144step0 raw3144step0Labels := by
      have hz : ∀ j, raw3144 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3144step0 = (fun i j => raw3144 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3144step0 raw3144; decide +kernel
      have hl : raw3144step0Labels = raw3144Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3144 raw3144Labels permutation346 hz
    mixedMoment B raw3144step0 raw3144step0Labels = mixedMoment B raw3144step1 raw3144step1Labels := by
      have ha : raw3144step1 = (fun i j => raw3144step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3144step1 raw3144step0; decide +kernel
      have hl : raw3144step1Labels = raw3144step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3144step0 raw3144step0Labels permutation38 permutation3
    mixedMoment B raw3144step1 raw3144step1Labels = mixedMoment B raw3144step2 raw3144step2Labels := by
      have ha : raw3144step2 = raw3144step1 := by apply Matrix.ext; unfold raw3144step2 raw3144step1; decide +kernel
      have hl : raw3144step1Labels = labelEmbedding6 ∘ raw3144step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3144step1 raw3144step1Labels raw3144step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5259 node5259Labels := by rfl

theorem canonical3145 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3145 raw3145Labels = mixedMoment B node5483 node5483Labels := by
  calc
    mixedMoment B raw3145 raw3145Labels = mixedMoment B raw3145step0 raw3145step0Labels := by
      have hz : ∀ j, raw3145 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3145step0 = (fun i j => raw3145 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3145step0 raw3145; decide +kernel
      have hl : raw3145step0Labels = raw3145Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3145 raw3145Labels permutation346 hz
    _ = mixedMoment B node5483 node5483Labels := by rfl

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

theorem canonical1023 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1023 raw1023Labels = mixedMoment B node4287 node4287Labels := by
  calc
    mixedMoment B raw1023 raw1023Labels = mixedMoment B raw1023step0 raw1023step0Labels := by
      have ha : raw1023step0 = (fun i j => raw1023 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1023step0 raw1023; decide +kernel
      have hl : raw1023step0Labels = raw1023Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1023 raw1023Labels permutation152 permutation4
    mixedMoment B raw1023step0 raw1023step0Labels = mixedMoment B raw1023step1 raw1023step1Labels := by
      have ha : raw1023step1 = raw1023step0 := by apply Matrix.ext; unfold raw1023step1 raw1023step0; decide +kernel
      have hl : raw1023step0Labels = labelEmbedding7 ∘ raw1023step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1023step0 raw1023step0Labels raw1023step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4287 node4287Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical76
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical9853 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9853 raw9853Labels = mixedMoment B node5137 node5137Labels := by
  calc
    mixedMoment B raw9853 raw9853Labels = mixedMoment B raw9853step0 raw9853step0Labels := by
      have ha : raw9853step0 = (fun i j => raw9853 (permutation158 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9853step0 raw9853; decide +kernel
      have hl : raw9853step0Labels = raw9853Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9853 raw9853Labels permutation158 permutation3
    mixedMoment B raw9853step0 raw9853step0Labels = mixedMoment B raw9853step1 raw9853step1Labels := by
      have ha : raw9853step1 = raw9853step0 := by apply Matrix.ext; unfold raw9853step1 raw9853step0; decide +kernel
      have hl : raw9853step0Labels = labelEmbedding6 ∘ raw9853step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9853step0 raw9853step0Labels raw9853step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5137 node5137Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical77
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical9857 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9857 raw9857Labels = mixedMoment B node5169 node5169Labels := by
  calc
    mixedMoment B raw9857 raw9857Labels = mixedMoment B raw9857step0 raw9857step0Labels := by
      have hz : ∀ j, raw9857 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw9857step0 = (fun i j => raw9857 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw9857step0 raw9857; decide +kernel
      have hl : raw9857step0Labels = raw9857Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9857 raw9857Labels permutation346 hz
    mixedMoment B raw9857step0 raw9857step0Labels = mixedMoment B raw9857step1 raw9857step1Labels := by
      have ha : raw9857step1 = (fun i j => raw9857step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9857step1 raw9857step0; decide +kernel
      have hl : raw9857step1Labels = raw9857step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9857step0 raw9857step0Labels permutation32 permutation3
    mixedMoment B raw9857step1 raw9857step1Labels = mixedMoment B raw9857step2 raw9857step2Labels := by
      have ha : raw9857step2 = raw9857step1 := by apply Matrix.ext; unfold raw9857step2 raw9857step1; decide +kernel
      have hl : raw9857step1Labels = labelEmbedding6 ∘ raw9857step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9857step1 raw9857step1Labels raw9857step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5169 node5169Labels := by rfl

theorem canonical9861 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9861 raw9861Labels = mixedMoment B node5141 node5141Labels := by
  calc
    mixedMoment B raw9861 raw9861Labels = mixedMoment B raw9861step0 raw9861step0Labels := by
      have hz : ∀ j, raw9861 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw9861step0 = (fun i j => raw9861 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw9861step0 raw9861; decide +kernel
      have hl : raw9861step0Labels = raw9861Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9861 raw9861Labels permutation346 hz
    mixedMoment B raw9861step0 raw9861step0Labels = mixedMoment B raw9861step1 raw9861step1Labels := by
      have ha : raw9861step1 = (fun i j => raw9861step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9861step1 raw9861step0; decide +kernel
      have hl : raw9861step1Labels = raw9861step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9861step0 raw9861step0Labels permutation33 permutation3
    mixedMoment B raw9861step1 raw9861step1Labels = mixedMoment B raw9861step2 raw9861step2Labels := by
      have ha : raw9861step2 = raw9861step1 := by apply Matrix.ext; unfold raw9861step2 raw9861step1; decide +kernel
      have hl : raw9861step1Labels = labelEmbedding6 ∘ raw9861step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9861step1 raw9861step1Labels raw9861step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5141 node5141Labels := by rfl

theorem canonical9864 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9864 raw9864Labels = mixedMoment B node4401 node4401Labels := by
  calc
    mixedMoment B raw9864 raw9864Labels = mixedMoment B raw9864step0 raw9864step0Labels := by
      have hz : ∀ j, raw9864 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw9864step0 = (fun i j => raw9864 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw9864step0 raw9864; decide +kernel
      have hl : raw9864step0Labels = raw9864Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9864 raw9864Labels permutation346 hz
    mixedMoment B raw9864step0 raw9864step0Labels = mixedMoment B raw9864step1 raw9864step1Labels := by
      have ha : raw9864step1 = (fun i j => raw9864step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9864step1 raw9864step0; decide +kernel
      have hl : raw9864step1Labels = raw9864step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9864step0 raw9864step0Labels permutation38 permutation3
    mixedMoment B raw9864step1 raw9864step1Labels = mixedMoment B raw9864step2 raw9864step2Labels := by
      have ha : raw9864step2 = raw9864step1 := by apply Matrix.ext; unfold raw9864step2 raw9864step1; decide +kernel
      have hl : raw9864step1Labels = labelEmbedding6 ∘ raw9864step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9864step1 raw9864step1Labels raw9864step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4401 node4401Labels := by rfl

theorem canonical9866 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9866 raw9866Labels = mixedMoment B node5047 node5047Labels := by
  calc
    mixedMoment B raw9866 raw9866Labels = mixedMoment B raw9866step0 raw9866step0Labels := by
      have ha : raw9866step0 = (fun i j => raw9866 (permutation182 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9866step0 raw9866; decide +kernel
      have hl : raw9866step0Labels = raw9866Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9866 raw9866Labels permutation182 permutation3
    mixedMoment B raw9866step0 raw9866step0Labels = mixedMoment B raw9866step1 raw9866step1Labels := by
      have ha : raw9866step1 = raw9866step0 := by apply Matrix.ext; unfold raw9866step1 raw9866step0; decide +kernel
      have hl : raw9866step0Labels = labelEmbedding6 ∘ raw9866step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9866step0 raw9866step0Labels raw9866step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5047 node5047Labels := by rfl

theorem canonical9867 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9867 raw9867Labels = mixedMoment B node5000 node5000Labels := by
  calc
    mixedMoment B raw9867 raw9867Labels = mixedMoment B raw9867step0 raw9867step0Labels := by
      have hz : ∀ j, raw9867 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw9867step0 = (fun i j => raw9867 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw9867step0 raw9867; decide +kernel
      have hl : raw9867step0Labels = raw9867Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9867 raw9867Labels permutation346 hz
    mixedMoment B raw9867step0 raw9867step0Labels = mixedMoment B raw9867step1 raw9867step1Labels := by
      have ha : raw9867step1 = (fun i j => raw9867step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9867step1 raw9867step0; decide +kernel
      have hl : raw9867step1Labels = raw9867step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9867step0 raw9867step0Labels permutation38 permutation3
    mixedMoment B raw9867step1 raw9867step1Labels = mixedMoment B raw9867step2 raw9867step2Labels := by
      have ha : raw9867step2 = raw9867step1 := by apply Matrix.ext; unfold raw9867step2 raw9867step1; decide +kernel
      have hl : raw9867step1Labels = labelEmbedding6 ∘ raw9867step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9867step1 raw9867step1Labels raw9867step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5000 node5000Labels := by rfl

theorem canonical9868 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9868 raw9868Labels = mixedMoment B node5261 node5261Labels := by
  calc
    mixedMoment B raw9868 raw9868Labels = mixedMoment B raw9868step0 raw9868step0Labels := by
      have hz : ∀ j, raw9868 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw9868step0 = (fun i j => raw9868 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw9868step0 raw9868; decide +kernel
      have hl : raw9868step0Labels = raw9868Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9868 raw9868Labels permutation520 hz
    mixedMoment B raw9868step0 raw9868step0Labels = mixedMoment B raw9868step1 raw9868step1Labels := by
      have hz : ∀ j, raw9868step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw9868step1 = (fun i j => raw9868step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw9868step1 raw9868step0; decide +kernel
      have hl : raw9868step1Labels = raw9868step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9868step0 raw9868step0Labels permutation80 hz
    mixedMoment B raw9868step1 raw9868step1Labels = mixedMoment B raw9868step2 raw9868step2Labels := by
      have ha : raw9868step2 = (fun i j => raw9868step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9868step2 raw9868step1; decide +kernel
      have hl : raw9868step2Labels = raw9868step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9868step1 raw9868step1Labels permutation10 permutation3
    mixedMoment B raw9868step2 raw9868step2Labels = mixedMoment B raw9868step3 raw9868step3Labels := by
      have ha : raw9868step3 = raw9868step2 := by apply Matrix.ext; unfold raw9868step3 raw9868step2; decide +kernel
      have hl : raw9868step2Labels = labelEmbedding6 ∘ raw9868step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9868step2 raw9868step2Labels raw9868step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5261 node5261Labels := by rfl

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

theorem canonical1024 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1024 raw1024Labels = mixedMoment B node865 node865Labels := by
  calc
    mixedMoment B raw1024 raw1024Labels = mixedMoment B raw1024step0 raw1024step0Labels := by
      have ha : raw1024step0 = (fun i j => raw1024 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1024step0 raw1024; decide +kernel
      have hl : raw1024step0Labels = raw1024Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1024 raw1024Labels permutation152 permutation4
    _ = mixedMoment B node865 node865Labels := by rfl

theorem canonical1025 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1025 raw1025Labels = mixedMoment B node1553 node1553Labels := by
  calc
    mixedMoment B raw1025 raw1025Labels = mixedMoment B raw1025step0 raw1025step0Labels := by
      have ha : raw1025step0 = (fun i j => raw1025 (permutation158 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1025step0 raw1025; decide +kernel
      have hl : raw1025step0Labels = raw1025Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1025 raw1025Labels permutation158 permutation6
    mixedMoment B raw1025step0 raw1025step0Labels = mixedMoment B raw1025step1 raw1025step1Labels := by
      have ha : raw1025step1 = -raw1025step0 := by apply Matrix.ext; change ∀ i j, raw1025step1 i j = -(raw1025step0 i j); unfold raw1025step1 raw1025step0; decide +kernel
      have hl : raw1025step1Labels = raw1025step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1025step1 raw1025step1Labels = mixedMoment B raw1025step2 raw1025step2Labels := by
      have ha : raw1025step2 = raw1025step1 := by apply Matrix.ext; unfold raw1025step2 raw1025step1; decide +kernel
      have hl : raw1025step1Labels = labelEmbedding1 ∘ raw1025step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1025step1 raw1025step1Labels raw1025step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1553 node1553Labels := by rfl

theorem canonical1029 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1029 raw1029Labels = mixedMoment B node4289 node4289Labels := by
  calc
    mixedMoment B raw1029 raw1029Labels = mixedMoment B raw1029step0 raw1029step0Labels := by
      have ha : raw1029step0 = (fun i j => raw1029 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1029step0 raw1029; decide +kernel
      have hl : raw1029step0Labels = raw1029Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1029 raw1029Labels permutation32 permutation4
    mixedMoment B raw1029step0 raw1029step0Labels = mixedMoment B raw1029step1 raw1029step1Labels := by
      have ha : raw1029step1 = raw1029step0 := by apply Matrix.ext; unfold raw1029step1 raw1029step0; decide +kernel
      have hl : raw1029step0Labels = labelEmbedding7 ∘ raw1029step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1029step0 raw1029step0Labels raw1029step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4289 node4289Labels := by rfl

theorem canonical1030 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1030 raw1030Labels = mixedMoment B node867 node867Labels := by
  calc
    mixedMoment B raw1030 raw1030Labels = mixedMoment B raw1030step0 raw1030step0Labels := by
      have ha : raw1030step0 = (fun i j => raw1030 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1030step0 raw1030; decide +kernel
      have hl : raw1030step0Labels = raw1030Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1030 raw1030Labels permutation32 permutation4
    _ = mixedMoment B node867 node867Labels := by rfl

theorem canonical1031 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1031 raw1031Labels = mixedMoment B node1555 node1555Labels := by
  calc
    mixedMoment B raw1031 raw1031Labels = mixedMoment B raw1031step0 raw1031step0Labels := by
      have ha : raw1031step0 = (fun i j => raw1031 (permutation34 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1031step0 raw1031; decide +kernel
      have hl : raw1031step0Labels = raw1031Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1031 raw1031Labels permutation34 permutation6
    mixedMoment B raw1031step0 raw1031step0Labels = mixedMoment B raw1031step1 raw1031step1Labels := by
      have ha : raw1031step1 = -raw1031step0 := by apply Matrix.ext; change ∀ i j, raw1031step1 i j = -(raw1031step0 i j); unfold raw1031step1 raw1031step0; decide +kernel
      have hl : raw1031step1Labels = raw1031step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1031step1 raw1031step1Labels = mixedMoment B raw1031step2 raw1031step2Labels := by
      have ha : raw1031step2 = raw1031step1 := by apply Matrix.ext; unfold raw1031step2 raw1031step1; decide +kernel
      have hl : raw1031step1Labels = labelEmbedding1 ∘ raw1031step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1031step1 raw1031step1Labels raw1031step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1555 node1555Labels := by rfl

theorem canonical1047 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1047 raw1047Labels = mixedMoment B node4295 node4295Labels := by
  calc
    mixedMoment B raw1047 raw1047Labels = mixedMoment B raw1047step0 raw1047step0Labels := by
      have ha : raw1047step0 = (fun i j => raw1047 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1047step0 raw1047; decide +kernel
      have hl : raw1047step0Labels = raw1047Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1047 raw1047Labels permutation32 permutation4
    mixedMoment B raw1047step0 raw1047step0Labels = mixedMoment B raw1047step1 raw1047step1Labels := by
      have ha : raw1047step1 = raw1047step0 := by apply Matrix.ext; unfold raw1047step1 raw1047step0; decide +kernel
      have hl : raw1047step0Labels = labelEmbedding7 ∘ raw1047step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1047step0 raw1047step0Labels raw1047step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4295 node4295Labels := by rfl

theorem canonical1048 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1048 raw1048Labels = mixedMoment B node873 node873Labels := by
  calc
    mixedMoment B raw1048 raw1048Labels = mixedMoment B raw1048step0 raw1048step0Labels := by
      have ha : raw1048step0 = (fun i j => raw1048 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1048step0 raw1048; decide +kernel
      have hl : raw1048step0Labels = raw1048Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1048 raw1048Labels permutation32 permutation4
    _ = mixedMoment B node873 node873Labels := by rfl

theorem canonical1049 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1049 raw1049Labels = mixedMoment B node1569 node1569Labels := by
  calc
    mixedMoment B raw1049 raw1049Labels = mixedMoment B raw1049step0 raw1049step0Labels := by
      have ha : raw1049step0 = (fun i j => raw1049 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1049step0 raw1049; decide +kernel
      have hl : raw1049step0Labels = raw1049Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1049 raw1049Labels permutation32 permutation6
    mixedMoment B raw1049step0 raw1049step0Labels = mixedMoment B raw1049step1 raw1049step1Labels := by
      have ha : raw1049step1 = -raw1049step0 := by apply Matrix.ext; change ∀ i j, raw1049step1 i j = -(raw1049step0 i j); unfold raw1049step1 raw1049step0; decide +kernel
      have hl : raw1049step1Labels = raw1049step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1049step1 raw1049step1Labels = mixedMoment B raw1049step2 raw1049step2Labels := by
      have ha : raw1049step2 = raw1049step1 := by apply Matrix.ext; unfold raw1049step2 raw1049step1; decide +kernel
      have hl : raw1049step1Labels = labelEmbedding1 ∘ raw1049step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1049step1 raw1049step1Labels raw1049step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1569 node1569Labels := by rfl

theorem canonical1065 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1065 raw1065Labels = mixedMoment B node4303 node4303Labels := by
  calc
    mixedMoment B raw1065 raw1065Labels = mixedMoment B raw1065step0 raw1065step0Labels := by
      have ha : raw1065step0 = (fun i j => raw1065 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1065step0 raw1065; decide +kernel
      have hl : raw1065step0Labels = raw1065Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1065 raw1065Labels permutation32 permutation4
    mixedMoment B raw1065step0 raw1065step0Labels = mixedMoment B raw1065step1 raw1065step1Labels := by
      have ha : raw1065step1 = raw1065step0 := by apply Matrix.ext; unfold raw1065step1 raw1065step0; decide +kernel
      have hl : raw1065step0Labels = labelEmbedding7 ∘ raw1065step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1065step0 raw1065step0Labels raw1065step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4303 node4303Labels := by rfl

theorem canonical1066 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1066 raw1066Labels = mixedMoment B node881 node881Labels := by
  calc
    mixedMoment B raw1066 raw1066Labels = mixedMoment B raw1066step0 raw1066step0Labels := by
      have ha : raw1066step0 = (fun i j => raw1066 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1066step0 raw1066; decide +kernel
      have hl : raw1066step0Labels = raw1066Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1066 raw1066Labels permutation32 permutation4
    _ = mixedMoment B node881 node881Labels := by rfl

theorem canonical1067 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1067 raw1067Labels = mixedMoment B node1559 node1559Labels := by
  calc
    mixedMoment B raw1067 raw1067Labels = mixedMoment B raw1067step0 raw1067step0Labels := by
      have ha : raw1067step0 = (fun i j => raw1067 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1067step0 raw1067; decide +kernel
      have hl : raw1067step0Labels = raw1067Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1067 raw1067Labels permutation32 permutation6
    mixedMoment B raw1067step0 raw1067step0Labels = mixedMoment B raw1067step1 raw1067step1Labels := by
      have ha : raw1067step1 = -raw1067step0 := by apply Matrix.ext; change ∀ i j, raw1067step1 i j = -(raw1067step0 i j); unfold raw1067step1 raw1067step0; decide +kernel
      have hl : raw1067step1Labels = raw1067step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1067step1 raw1067step1Labels = mixedMoment B raw1067step2 raw1067step2Labels := by
      have ha : raw1067step2 = raw1067step1 := by apply Matrix.ext; unfold raw1067step2 raw1067step1; decide +kernel
      have hl : raw1067step1Labels = labelEmbedding1 ∘ raw1067step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1067step1 raw1067step1Labels raw1067step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1559 node1559Labels := by rfl

theorem canonical1101 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1101 raw1101Labels = mixedMoment B node4322 node4322Labels := by
  calc
    mixedMoment B raw1101 raw1101Labels = mixedMoment B raw1101step0 raw1101step0Labels := by
      have ha : raw1101step0 = (fun i j => raw1101 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1101step0 raw1101; decide +kernel
      have hl : raw1101step0Labels = raw1101Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1101 raw1101Labels permutation152 permutation4
    mixedMoment B raw1101step0 raw1101step0Labels = mixedMoment B raw1101step1 raw1101step1Labels := by
      have ha : raw1101step1 = raw1101step0 := by apply Matrix.ext; unfold raw1101step1 raw1101step0; decide +kernel
      have hl : raw1101step0Labels = labelEmbedding7 ∘ raw1101step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1101step0 raw1101step0Labels raw1101step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4322 node4322Labels := by rfl

theorem canonical1102 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1102 raw1102Labels = mixedMoment B node900 node900Labels := by
  calc
    mixedMoment B raw1102 raw1102Labels = mixedMoment B raw1102step0 raw1102step0Labels := by
      have ha : raw1102step0 = (fun i j => raw1102 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1102step0 raw1102; decide +kernel
      have hl : raw1102step0Labels = raw1102Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1102 raw1102Labels permutation152 permutation4
    _ = mixedMoment B node900 node900Labels := by rfl

theorem canonical1103 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1103 raw1103Labels = mixedMoment B node1588 node1588Labels := by
  calc
    mixedMoment B raw1103 raw1103Labels = mixedMoment B raw1103step0 raw1103step0Labels := by
      have ha : raw1103step0 = (fun i j => raw1103 (permutation176 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1103step0 raw1103; decide +kernel
      have hl : raw1103step0Labels = raw1103Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1103 raw1103Labels permutation176 permutation6
    mixedMoment B raw1103step0 raw1103step0Labels = mixedMoment B raw1103step1 raw1103step1Labels := by
      have ha : raw1103step1 = -raw1103step0 := by apply Matrix.ext; change ∀ i j, raw1103step1 i j = -(raw1103step0 i j); unfold raw1103step1 raw1103step0; decide +kernel
      have hl : raw1103step1Labels = raw1103step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1103step1 raw1103step1Labels = mixedMoment B raw1103step2 raw1103step2Labels := by
      have ha : raw1103step2 = raw1103step1 := by apply Matrix.ext; unfold raw1103step2 raw1103step1; decide +kernel
      have hl : raw1103step1Labels = labelEmbedding1 ∘ raw1103step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1103step1 raw1103step1Labels raw1103step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1588 node1588Labels := by rfl

theorem canonical1110 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1110 raw1110Labels = mixedMoment B node4325 node4325Labels := by
  calc
    mixedMoment B raw1110 raw1110Labels = mixedMoment B raw1110step0 raw1110step0Labels := by
      have ha : raw1110step0 = (fun i j => raw1110 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1110step0 raw1110; decide +kernel
      have hl : raw1110step0Labels = raw1110Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1110 raw1110Labels permutation32 permutation4
    mixedMoment B raw1110step0 raw1110step0Labels = mixedMoment B raw1110step1 raw1110step1Labels := by
      have ha : raw1110step1 = raw1110step0 := by apply Matrix.ext; unfold raw1110step1 raw1110step0; decide +kernel
      have hl : raw1110step0Labels = labelEmbedding7 ∘ raw1110step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1110step0 raw1110step0Labels raw1110step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4325 node4325Labels := by rfl

theorem canonical1111 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1111 raw1111Labels = mixedMoment B node903 node903Labels := by
  calc
    mixedMoment B raw1111 raw1111Labels = mixedMoment B raw1111step0 raw1111step0Labels := by
      have ha : raw1111step0 = (fun i j => raw1111 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1111step0 raw1111; decide +kernel
      have hl : raw1111step0Labels = raw1111Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1111 raw1111Labels permutation32 permutation4
    _ = mixedMoment B node903 node903Labels := by rfl

theorem canonical1112 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1112 raw1112Labels = mixedMoment B node1591 node1591Labels := by
  calc
    mixedMoment B raw1112 raw1112Labels = mixedMoment B raw1112step0 raw1112step0Labels := by
      have ha : raw1112step0 = (fun i j => raw1112 (permutation38 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1112step0 raw1112; decide +kernel
      have hl : raw1112step0Labels = raw1112Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1112 raw1112Labels permutation38 permutation6
    mixedMoment B raw1112step0 raw1112step0Labels = mixedMoment B raw1112step1 raw1112step1Labels := by
      have ha : raw1112step1 = -raw1112step0 := by apply Matrix.ext; change ∀ i j, raw1112step1 i j = -(raw1112step0 i j); unfold raw1112step1 raw1112step0; decide +kernel
      have hl : raw1112step1Labels = raw1112step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1112step1 raw1112step1Labels = mixedMoment B raw1112step2 raw1112step2Labels := by
      have ha : raw1112step2 = raw1112step1 := by apply Matrix.ext; unfold raw1112step2 raw1112step1; decide +kernel
      have hl : raw1112step1Labels = labelEmbedding1 ∘ raw1112step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1112step1 raw1112step1Labels raw1112step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1591 node1591Labels := by rfl

theorem canonical1131 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1131 raw1131Labels = mixedMoment B node4346 node4346Labels := by
  calc
    mixedMoment B raw1131 raw1131Labels = mixedMoment B raw1131step0 raw1131step0Labels := by
      have ha : raw1131step0 = (fun i j => raw1131 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1131step0 raw1131; decide +kernel
      have hl : raw1131step0Labels = raw1131Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1131 raw1131Labels permutation32 permutation4
    mixedMoment B raw1131step0 raw1131step0Labels = mixedMoment B raw1131step1 raw1131step1Labels := by
      have ha : raw1131step1 = raw1131step0 := by apply Matrix.ext; unfold raw1131step1 raw1131step0; decide +kernel
      have hl : raw1131step0Labels = labelEmbedding7 ∘ raw1131step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1131step0 raw1131step0Labels raw1131step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4346 node4346Labels := by rfl

theorem canonical1132 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1132 raw1132Labels = mixedMoment B node924 node924Labels := by
  calc
    mixedMoment B raw1132 raw1132Labels = mixedMoment B raw1132step0 raw1132step0Labels := by
      have ha : raw1132step0 = (fun i j => raw1132 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1132step0 raw1132; decide +kernel
      have hl : raw1132step0Labels = raw1132Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1132 raw1132Labels permutation32 permutation4
    _ = mixedMoment B node924 node924Labels := by rfl

theorem canonical1133 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1133 raw1133Labels = mixedMoment B node1674 node1674Labels := by
  calc
    mixedMoment B raw1133 raw1133Labels = mixedMoment B raw1133step0 raw1133step0Labels := by
      have ha : raw1133step0 = (fun i j => raw1133 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1133step0 raw1133; decide +kernel
      have hl : raw1133step0Labels = raw1133Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1133 raw1133Labels permutation32 permutation6
    mixedMoment B raw1133step0 raw1133step0Labels = mixedMoment B raw1133step1 raw1133step1Labels := by
      have ha : raw1133step1 = -raw1133step0 := by apply Matrix.ext; change ∀ i j, raw1133step1 i j = -(raw1133step0 i j); unfold raw1133step1 raw1133step0; decide +kernel
      have hl : raw1133step1Labels = raw1133step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1133step1 raw1133step1Labels = mixedMoment B raw1133step2 raw1133step2Labels := by
      have ha : raw1133step2 = raw1133step1 := by apply Matrix.ext; unfold raw1133step2 raw1133step1; decide +kernel
      have hl : raw1133step1Labels = labelEmbedding1 ∘ raw1133step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1133step1 raw1133step1Labels raw1133step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1674 node1674Labels := by rfl

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

theorem canonical1215 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1215 raw1215Labels = mixedMoment B node4401 node4401Labels := by
  calc
    mixedMoment B raw1215 raw1215Labels = mixedMoment B raw1215step0 raw1215step0Labels := by
      have ha : raw1215step0 = (fun i j => raw1215 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1215step0 raw1215; decide +kernel
      have hl : raw1215step0Labels = raw1215Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1215 raw1215Labels permutation32 permutation4
    mixedMoment B raw1215step0 raw1215step0Labels = mixedMoment B raw1215step1 raw1215step1Labels := by
      have ha : raw1215step1 = raw1215step0 := by apply Matrix.ext; unfold raw1215step1 raw1215step0; decide +kernel
      have hl : raw1215step0Labels = labelEmbedding7 ∘ raw1215step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1215step0 raw1215step0Labels raw1215step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4401 node4401Labels := by rfl

theorem canonical1216 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1216 raw1216Labels = mixedMoment B node982 node982Labels := by
  calc
    mixedMoment B raw1216 raw1216Labels = mixedMoment B raw1216step0 raw1216step0Labels := by
      have ha : raw1216step0 = (fun i j => raw1216 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1216step0 raw1216; decide +kernel
      have hl : raw1216step0Labels = raw1216Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1216 raw1216Labels permutation32 permutation4
    _ = mixedMoment B node982 node982Labels := by rfl

theorem canonical1217 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1217 raw1217Labels = mixedMoment B node1617 node1617Labels := by
  calc
    mixedMoment B raw1217 raw1217Labels = mixedMoment B raw1217step0 raw1217step0Labels := by
      have ha : raw1217step0 = (fun i j => raw1217 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1217step0 raw1217; decide +kernel
      have hl : raw1217step0Labels = raw1217Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1217 raw1217Labels permutation32 permutation6
    mixedMoment B raw1217step0 raw1217step0Labels = mixedMoment B raw1217step1 raw1217step1Labels := by
      have ha : raw1217step1 = -raw1217step0 := by apply Matrix.ext; change ∀ i j, raw1217step1 i j = -(raw1217step0 i j); unfold raw1217step1 raw1217step0; decide +kernel
      have hl : raw1217step1Labels = raw1217step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1217step1 raw1217step1Labels = mixedMoment B raw1217step2 raw1217step2Labels := by
      have ha : raw1217step2 = raw1217step1 := by apply Matrix.ext; unfold raw1217step2 raw1217step1; decide +kernel
      have hl : raw1217step1Labels = labelEmbedding1 ∘ raw1217step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1217step1 raw1217step1Labels raw1217step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1617 node1617Labels := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical20
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical666 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw666 = injectiveMoment H node168 := by
  calc
    injectiveMoment H raw666 = injectiveMoment H raw666step0 := by
      have heq : raw666step0 = (fun i j => raw666 (permutation32 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw666 permutation32 permutation8
    _ = injectiveMoment H node168 := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical26
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical841 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw841 = injectiveMoment H node10 := by
  calc
    injectiveMoment H raw841 = injectiveMoment H raw841step0 := by
      have heq : raw841step0 = raw841.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw841).symm
    injectiveMoment H raw841step0 = injectiveMoment H raw841step1 := by
      have heq : raw841step1 = (fun i j => raw841step0 (permutation4 i) (permutation1 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw841step0 permutation4 permutation1
    _ = injectiveMoment H node10 := by rfl

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

theorem canonical869 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw869 = injectiveMoment H node24 := by
  rfl

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

theorem canonical7735 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7735 = injectiveMoment H node5 := by
  calc
    injectiveMoment H raw7735 = injectiveMoment H raw7735step0 := by
      have hz : ∀ j, raw7735 (permutation7 0) j = 0 := by decide +kernel
      have heq : raw7735step0 = (fun i j => raw7735 (permutation7 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7735 permutation7 hz
    _ = injectiveMoment H node5 := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical28
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical900 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw900 = injectiveMoment H node3 := by
  calc
    injectiveMoment H raw900 = injectiveMoment H raw900step0 := by
      have hz : ∀ j, raw900 (permutation5 0) j = 0 := by decide +kernel
      have heq : raw900step0 = (fun i j => raw900 (permutation5 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw900 permutation5 hz
    _ = injectiveMoment H node3 := by rfl

theorem canonical917 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw917 = injectiveMoment H node10 := by
  rfl

theorem canonical926 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw926 = injectiveMoment H node3 := by
  rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical5
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical180 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw180 = injectiveMoment H node9 := by
  calc
    injectiveMoment H raw180 = injectiveMoment H raw180step0 := by
      have heq : raw180step0 = raw180.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw180).symm
    _ = injectiveMoment H node9 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical6
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical211 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw211 = injectiveMoment H node8 := by
  rfl

theorem canonical215 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw215 = injectiveMoment H node2 := by
  rfl

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

theorem sound2 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node2 = Sparse.eval value2 (momentVector H) := by
  have hc : momentVector H 6 = injectiveMoment H node2 := rfl
  simp [value2, Sparse.eval, hc]

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

theorem sound8 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node8 = Sparse.eval value8 (momentVector H) := by
  have heq : pivotMatrix8 = (fun u v => node8 (pivotPermutation8 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node8 = injectiveMoment H pivotMatrix8 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix8 0 = Pi.single (0 : Fin 2) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 2 < 6) hH pivotMatrix8 0 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix8 (0 : Fin 2)) =
      Sparse.eval value3 (momentVector H) := by
    have heq : mergeFirst pivotMatrix8 (0 : Fin 2) = raw926 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical926 hH).trans (sound3 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix8 (1 : Fin 2)) =
      Sparse.eval value2 (momentVector H) := by
    have heq : mergeFirst pivotMatrix8 (1 : Fin 2) = raw215 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical215 hH).trans (sound2 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (4 : ℝ) * injectiveMoment H node8 + (injectiveMoment H (mergeFirst pivotMatrix8 (0 : Fin 2)) + (injectiveMoment H (mergeFirst pivotMatrix8 (1 : Fin 2)))) = 0 at hc
  rw [hm0, hm1] at hc
  norm_num [value8, value2, value3, Sparse.eval] at hc ⊢
  linarith

theorem sound9 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node9 = Sparse.eval value9 (momentVector H) := by
  have hc : momentVector H 5 = injectiveMoment H node9 := rfl
  simp [value9, Sparse.eval, hc]

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

theorem sound24 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node24 = Sparse.eval value24 (momentVector H) := by
  have heq : pivotMatrix24 = (fun u v => node24 (pivotPermutation24 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node24 = injectiveMoment H pivotMatrix24 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix24 0 = Pi.single (1 : Fin 2) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix24 1 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix24 (0 : Fin 3)) =
      Sparse.eval value8 (momentVector H) := by
    have heq : mergeFirst pivotMatrix24 (0 : Fin 3) = raw211 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical211 hH).trans (sound8 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix24 (1 : Fin 3)) =
      Sparse.eval value3 (momentVector H) := by
    have heq : mergeFirst pivotMatrix24 (1 : Fin 3) = raw900 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical900 hH).trans (sound3 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix24 (2 : Fin 3)) =
      Sparse.eval value10 (momentVector H) := by
    have heq : mergeFirst pivotMatrix24 (2 : Fin 3) = raw917 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical917 hH).trans (sound10 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node24 + (injectiveMoment H (mergeFirst pivotMatrix24 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix24 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix24 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value24, value10, value3, value8, Sparse.eval] at hc ⊢
  linarith

theorem sound52 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node52 = Sparse.eval value52 (momentVector H) := by
  have heq : pivotMatrix52 = (fun u v => node52.transpose (pivotPermutation52 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node52 = injectiveMoment H pivotMatrix52 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix52 0 = Pi.single (2 : Fin 3) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 2 < 6) hH pivotMatrix52 2 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix52 (0 : Fin 2)) =
      Sparse.eval value9 (momentVector H) := by
    have heq : mergeFirst pivotMatrix52 (0 : Fin 2) = raw180 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical180 hH).trans (sound9 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix52 (1 : Fin 2)) =
      Sparse.eval value10 (momentVector H) := by
    have heq : mergeFirst pivotMatrix52 (1 : Fin 2) = raw841 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical841 hH).trans (sound10 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (4 : ℝ) * injectiveMoment H node52 + (injectiveMoment H (mergeFirst pivotMatrix52 (0 : Fin 2)) + (injectiveMoment H (mergeFirst pivotMatrix52 (1 : Fin 2)))) = 0 at hc
  rw [hm0, hm1] at hc
  norm_num [value52, value10, value9, Sparse.eval] at hc ⊢
  linarith

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical44
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical1420 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1420 = injectiveMoment H node52 := by
  calc
    injectiveMoment H raw1420 = injectiveMoment H raw1420step0 := by
      have heq : raw1420step0 = raw1420.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1420).symm
    injectiveMoment H raw1420step0 = injectiveMoment H raw1420step1 := by
      have heq : raw1420step1 = (fun i j => raw1420step0 (permutation7 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1420step0 permutation7 permutation6
    _ = injectiveMoment H node52 := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical86
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical2783 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2783 = injectiveMoment H node10 := by
  calc
    injectiveMoment H raw2783 = injectiveMoment H raw2783step0 := by
      have heq : raw2783step0 = raw2783.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2783).symm
    injectiveMoment H raw2783step0 = injectiveMoment H raw2783step1 := by
      have hz : ∀ i, raw2783step0 i (permutation5 0) = 0 := by decide +kernel
      have heq : raw2783step1 = (fun i j => raw2783step0 i (permutation5 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw2783step0 permutation5 hz
    injectiveMoment H raw2783step1 = injectiveMoment H raw2783step2 := by
      have heq : raw2783step2 = (fun i j => raw2783step1 (permutation8 i) (permutation2 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2783step1 permutation8 permutation2
    _ = injectiveMoment H node10 := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound2
attribute [-simp] _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_toRational _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

theorem sound168 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node168 = Sparse.eval value168 (momentVector H) := by
  have heq : pivotMatrix168 = (fun u v => node168 (pivotPermutation168 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node168 = injectiveMoment H pivotMatrix168 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix168 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix168 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix168 (0 : Fin 3)) =
      Sparse.eval value52 (momentVector H) := by
    have heq : mergeFirst pivotMatrix168 (0 : Fin 3) = raw1420 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical1420 hH).trans (sound52 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix168 (1 : Fin 3)) =
      Sparse.eval value10 (momentVector H) := by
    have heq : mergeFirst pivotMatrix168 (1 : Fin 3) = raw2783 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical2783 hH).trans (sound10 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix168 (2 : Fin 3)) =
      Sparse.eval value57 (momentVector H) := by
    have heq : mergeFirst pivotMatrix168 (2 : Fin 3) = raw2823 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical2823 hH).trans (sound57 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node168 + (injectiveMoment H (mergeFirst pivotMatrix168 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix168 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix168 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value168, value10, value52, value57, Sparse.eval] at hc ⊢
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_SingleGroup20
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singlePair338 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node338 node338Labels = Sparse.eval singlePairValue338 (familyPairVector B) := by
  have hp := single_label_three B hB node338
  have hl : node338Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node338 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node338 (EqualityPatterns.family3.label 0) = PairSemantics.raw7980 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node338 PairSemantics.raw7980; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7980 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node338 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value4 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node338 (EqualityPatterns.family3.label 1) = PairSemantics.raw5169 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node338 PairSemantics.raw5169; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5169 hH).trans (PairSemantics.sound4 hH)
  have hm2 : familyPairMoment B (groupedColumns node338 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value65 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node338 (EqualityPatterns.family3.label 2) = PairSemantics.raw7678 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node338 PairSemantics.raw7678; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7678 hH).trans (PairSemantics.sound65 hH)
  have hm3 : familyPairMoment B (groupedColumns node338 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value24 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node338 (EqualityPatterns.family3.label 3) = PairSemantics.raw869 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node338 PairSemantics.raw869; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical869 hH).trans (PairSemantics.sound24 hH)
  have hm4 : familyPairMoment B (groupedColumns node338 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value168 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node338 (EqualityPatterns.family3.label 4) = PairSemantics.raw666 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node338 PairSemantics.raw666; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical666 hH).trans (PairSemantics.sound168 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue338, PairSemantics.value0, PairSemantics.value4, PairSemantics.value24, PairSemantics.value65, PairSemantics.value168, Sparse.eval] at hp ⊢
  linarith only [hp]

end MUB6.Certificate.MixedSemantics

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons40
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singleton2598 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node2598 node2598Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node338 node338Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw238 singletonSmall2598
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall2598) = raw238Labels := by decide +kernel
  rw [hl, canonical238 B hB] at h
  have hc0 : mixedMoment B raw238 (Fin.cases (0 : Fin 1) singletonSmall2598) =
      mixedMoment B node338 node338Labels := by
    have ha : raw238 = raw239 := by apply Matrix.ext; unfold raw238 raw239; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall2598 = raw239Labels := by decide +kernel
    rw [ha, hj, canonical239 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

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

theorem singleton4287 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4287 node4287Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node865 node865Labels + mixedMoment B node1553 node1553Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1023 singletonSmall4287
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4287) = raw1023Labels := by decide +kernel
  rw [hl, canonical1023 B hB] at h
  have hc0 : mixedMoment B raw1023 (Fin.cases (0 : Fin 2) singletonSmall4287) =
      mixedMoment B node865 node865Labels := by
    have ha : raw1023 = raw1024 := by apply Matrix.ext; unfold raw1023 raw1024; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4287 = raw1024Labels := by decide +kernel
    rw [ha, hj, canonical1024 B hB]
  have hc1 : mixedMoment B raw1023 (Fin.cases (1 : Fin 2) singletonSmall4287) =
      mixedMoment B node1553 node1553Labels := by
    have ha : raw1023 = raw1025 := by apply Matrix.ext; unfold raw1023 raw1025; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4287 = raw1025Labels := by decide +kernel
    rw [ha, hj, canonical1025 B hB]
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

theorem singleton4289 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4289 node4289Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node867 node867Labels + mixedMoment B node1555 node1555Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1029 singletonSmall4289
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4289) = raw1029Labels := by decide +kernel
  rw [hl, canonical1029 B hB] at h
  have hc0 : mixedMoment B raw1029 (Fin.cases (0 : Fin 2) singletonSmall4289) =
      mixedMoment B node867 node867Labels := by
    have ha : raw1029 = raw1030 := by apply Matrix.ext; unfold raw1029 raw1030; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4289 = raw1030Labels := by decide +kernel
    rw [ha, hj, canonical1030 B hB]
  have hc1 : mixedMoment B raw1029 (Fin.cases (1 : Fin 2) singletonSmall4289) =
      mixedMoment B node1555 node1555Labels := by
    have ha : raw1029 = raw1031 := by apply Matrix.ext; unfold raw1029 raw1031; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4289 = raw1031Labels := by decide +kernel
    rw [ha, hj, canonical1031 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4295 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4295 node4295Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node873 node873Labels + mixedMoment B node1569 node1569Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1047 singletonSmall4295
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4295) = raw1047Labels := by decide +kernel
  rw [hl, canonical1047 B hB] at h
  have hc0 : mixedMoment B raw1047 (Fin.cases (0 : Fin 2) singletonSmall4295) =
      mixedMoment B node873 node873Labels := by
    have ha : raw1047 = raw1048 := by apply Matrix.ext; unfold raw1047 raw1048; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4295 = raw1048Labels := by decide +kernel
    rw [ha, hj, canonical1048 B hB]
  have hc1 : mixedMoment B raw1047 (Fin.cases (1 : Fin 2) singletonSmall4295) =
      mixedMoment B node1569 node1569Labels := by
    have ha : raw1047 = raw1049 := by apply Matrix.ext; unfold raw1047 raw1049; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4295 = raw1049Labels := by decide +kernel
    rw [ha, hj, canonical1049 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4303 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4303 node4303Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node881 node881Labels + mixedMoment B node1559 node1559Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1065 singletonSmall4303
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4303) = raw1065Labels := by decide +kernel
  rw [hl, canonical1065 B hB] at h
  have hc0 : mixedMoment B raw1065 (Fin.cases (0 : Fin 2) singletonSmall4303) =
      mixedMoment B node881 node881Labels := by
    have ha : raw1065 = raw1066 := by apply Matrix.ext; unfold raw1065 raw1066; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4303 = raw1066Labels := by decide +kernel
    rw [ha, hj, canonical1066 B hB]
  have hc1 : mixedMoment B raw1065 (Fin.cases (1 : Fin 2) singletonSmall4303) =
      mixedMoment B node1559 node1559Labels := by
    have ha : raw1065 = raw1067 := by apply Matrix.ext; unfold raw1065 raw1067; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4303 = raw1067Labels := by decide +kernel
    rw [ha, hj, canonical1067 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4322 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4322 node4322Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node900 node900Labels + mixedMoment B node1588 node1588Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1101 singletonSmall4322
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4322) = raw1101Labels := by decide +kernel
  rw [hl, canonical1101 B hB] at h
  have hc0 : mixedMoment B raw1101 (Fin.cases (0 : Fin 2) singletonSmall4322) =
      mixedMoment B node900 node900Labels := by
    have ha : raw1101 = raw1102 := by apply Matrix.ext; unfold raw1101 raw1102; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4322 = raw1102Labels := by decide +kernel
    rw [ha, hj, canonical1102 B hB]
  have hc1 : mixedMoment B raw1101 (Fin.cases (1 : Fin 2) singletonSmall4322) =
      mixedMoment B node1588 node1588Labels := by
    have ha : raw1101 = raw1103 := by apply Matrix.ext; unfold raw1101 raw1103; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4322 = raw1103Labels := by decide +kernel
    rw [ha, hj, canonical1103 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4325 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4325 node4325Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node903 node903Labels + mixedMoment B node1591 node1591Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1110 singletonSmall4325
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4325) = raw1110Labels := by decide +kernel
  rw [hl, canonical1110 B hB] at h
  have hc0 : mixedMoment B raw1110 (Fin.cases (0 : Fin 2) singletonSmall4325) =
      mixedMoment B node903 node903Labels := by
    have ha : raw1110 = raw1111 := by apply Matrix.ext; unfold raw1110 raw1111; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4325 = raw1111Labels := by decide +kernel
    rw [ha, hj, canonical1111 B hB]
  have hc1 : mixedMoment B raw1110 (Fin.cases (1 : Fin 2) singletonSmall4325) =
      mixedMoment B node1591 node1591Labels := by
    have ha : raw1110 = raw1112 := by apply Matrix.ext; unfold raw1110 raw1112; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4325 = raw1112Labels := by decide +kernel
    rw [ha, hj, canonical1112 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4346 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4346 node4346Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node924 node924Labels + mixedMoment B node1674 node1674Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1131 singletonSmall4346
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4346) = raw1131Labels := by decide +kernel
  rw [hl, canonical1131 B hB] at h
  have hc0 : mixedMoment B raw1131 (Fin.cases (0 : Fin 2) singletonSmall4346) =
      mixedMoment B node924 node924Labels := by
    have ha : raw1131 = raw1132 := by apply Matrix.ext; unfold raw1131 raw1132; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4346 = raw1132Labels := by decide +kernel
    rw [ha, hj, canonical1132 B hB]
  have hc1 : mixedMoment B raw1131 (Fin.cases (1 : Fin 2) singletonSmall4346) =
      mixedMoment B node1674 node1674Labels := by
    have ha : raw1131 = raw1133 := by apply Matrix.ext; unfold raw1131 raw1133; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4346 = raw1133Labels := by decide +kernel
    rw [ha, hj, canonical1133 B hB]
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

theorem singleton4401 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4401 node4401Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node982 node982Labels + mixedMoment B node1617 node1617Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1215 singletonSmall4401
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4401) = raw1215Labels := by decide +kernel
  rw [hl, canonical1215 B hB] at h
  have hc0 : mixedMoment B raw1215 (Fin.cases (0 : Fin 2) singletonSmall4401) =
      mixedMoment B node982 node982Labels := by
    have ha : raw1215 = raw1216 := by apply Matrix.ext; unfold raw1215 raw1216; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4401 = raw1216Labels := by decide +kernel
    rw [ha, hj, canonical1216 B hB]
  have hc1 : mixedMoment B raw1215 (Fin.cases (1 : Fin 2) singletonSmall4401) =
      mixedMoment B node1617 node1617Labels := by
    have ha : raw1215 = raw1217 := by apply Matrix.ext; unfold raw1215 raw1217; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4401 = raw1217Labels := by decide +kernel
    rw [ha, hj, canonical1217 B hB]
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons76
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singleton4902 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4902 node4902Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2295 node2295Labels + mixedMoment B node3315 node3315Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1833 singletonSmall4902
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4902) = raw1833Labels := by decide +kernel
  rw [hl, canonical1833 B hB] at h
  have hc0 : mixedMoment B raw1833 (Fin.cases (0 : Fin 2) singletonSmall4902) =
      mixedMoment B node2295 node2295Labels := by
    have ha : raw1833 = raw1834 := by apply Matrix.ext; unfold raw1833 raw1834; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4902 = raw1834Labels := by decide +kernel
    rw [ha, hj, canonical1834 B hB]
  have hc1 : mixedMoment B raw1833 (Fin.cases (1 : Fin 2) singletonSmall4902) =
      mixedMoment B node3315 node3315Labels := by
    have ha : raw1833 = raw1835 := by apply Matrix.ext; unfold raw1833 raw1835; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4902 = raw1835Labels := by decide +kernel
    rw [ha, hj, canonical1835 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4907 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4907 node4907Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2300 node2300Labels + mixedMoment B node3325 node3325Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1848 singletonSmall4907
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4907) = raw1848Labels := by decide +kernel
  rw [hl, canonical1848 B hB] at h
  have hc0 : mixedMoment B raw1848 (Fin.cases (0 : Fin 2) singletonSmall4907) =
      mixedMoment B node2300 node2300Labels := by
    have ha : raw1848 = raw1849 := by apply Matrix.ext; unfold raw1848 raw1849; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4907 = raw1849Labels := by decide +kernel
    rw [ha, hj, canonical1849 B hB]
  have hc1 : mixedMoment B raw1848 (Fin.cases (1 : Fin 2) singletonSmall4907) =
      mixedMoment B node3325 node3325Labels := by
    have ha : raw1848 = raw1850 := by apply Matrix.ext; unfold raw1848 raw1850; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4907 = raw1850Labels := by decide +kernel
    rw [ha, hj, canonical1850 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4913 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4913 node4913Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2306 node2306Labels + mixedMoment B node3318 node3318Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1863 singletonSmall4913
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4913) = raw1863Labels := by decide +kernel
  rw [hl, canonical1863 B hB] at h
  have hc0 : mixedMoment B raw1863 (Fin.cases (0 : Fin 2) singletonSmall4913) =
      mixedMoment B node2306 node2306Labels := by
    have ha : raw1863 = raw1864 := by apply Matrix.ext; unfold raw1863 raw1864; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4913 = raw1864Labels := by decide +kernel
    rw [ha, hj, canonical1864 B hB]
  have hc1 : mixedMoment B raw1863 (Fin.cases (1 : Fin 2) singletonSmall4913) =
      mixedMoment B node3318 node3318Labels := by
    have ha : raw1863 = raw1865 := by apply Matrix.ext; unfold raw1863 raw1865; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4913 = raw1865Labels := by decide +kernel
    rw [ha, hj, canonical1865 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4927 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4927 node4927Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2317 node2317Labels + mixedMoment B node3399 node3399Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1890 singletonSmall4927
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4927) = raw1890Labels := by decide +kernel
  rw [hl, canonical1890 B hB] at h
  have hc0 : mixedMoment B raw1890 (Fin.cases (0 : Fin 2) singletonSmall4927) =
      mixedMoment B node2317 node2317Labels := by
    have ha : raw1890 = raw1891 := by apply Matrix.ext; unfold raw1890 raw1891; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4927 = raw1891Labels := by decide +kernel
    rw [ha, hj, canonical1891 B hB]
  have hc1 : mixedMoment B raw1890 (Fin.cases (1 : Fin 2) singletonSmall4927) =
      mixedMoment B node3399 node3399Labels := by
    have ha : raw1890 = raw1892 := by apply Matrix.ext; unfold raw1890 raw1892; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4927 = raw1892Labels := by decide +kernel
    rw [ha, hj, canonical1892 B hB]
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

theorem singleton4943 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4943 node4943Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2334 node2334Labels + mixedMoment B node3411 node3411Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1908 singletonSmall4943
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4943) = raw1908Labels := by decide +kernel
  rw [hl, canonical1908 B hB] at h
  have hc0 : mixedMoment B raw1908 (Fin.cases (0 : Fin 2) singletonSmall4943) =
      mixedMoment B node2334 node2334Labels := by
    have ha : raw1908 = raw1909 := by apply Matrix.ext; unfold raw1908 raw1909; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4943 = raw1909Labels := by decide +kernel
    rw [ha, hj, canonical1909 B hB]
  have hc1 : mixedMoment B raw1908 (Fin.cases (1 : Fin 2) singletonSmall4943) =
      mixedMoment B node3411 node3411Labels := by
    have ha : raw1908 = raw1910 := by apply Matrix.ext; unfold raw1908 raw1910; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4943 = raw1910Labels := by decide +kernel
    rw [ha, hj, canonical1910 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4986 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4986 node4986Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2371 node2371Labels + mixedMoment B node3335 node3335Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1992 singletonSmall4986
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4986) = raw1992Labels := by decide +kernel
  rw [hl, canonical1992 B hB] at h
  have hc0 : mixedMoment B raw1992 (Fin.cases (0 : Fin 2) singletonSmall4986) =
      mixedMoment B node2371 node2371Labels := by
    have ha : raw1992 = raw1993 := by apply Matrix.ext; unfold raw1992 raw1993; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4986 = raw1993Labels := by decide +kernel
    rw [ha, hj, canonical1993 B hB]
  have hc1 : mixedMoment B raw1992 (Fin.cases (1 : Fin 2) singletonSmall4986) =
      mixedMoment B node3335 node3335Labels := by
    have ha : raw1992 = raw1994 := by apply Matrix.ext; unfold raw1992 raw1994; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4986 = raw1994Labels := by decide +kernel
    rw [ha, hj, canonical1994 B hB]
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

theorem singleton5033 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5033 node5033Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2425 node2425Labels + mixedMoment B node3449 node3449Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2052 singletonSmall5033
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5033) = raw2052Labels := by decide +kernel
  rw [hl, canonical2052 B hB] at h
  have hc0 : mixedMoment B raw2052 (Fin.cases (0 : Fin 2) singletonSmall5033) =
      mixedMoment B node2425 node2425Labels := by
    have ha : raw2052 = raw2053 := by apply Matrix.ext; unfold raw2052 raw2053; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5033 = raw2053Labels := by decide +kernel
    rw [ha, hj, canonical2053 B hB]
  have hc1 : mixedMoment B raw2052 (Fin.cases (1 : Fin 2) singletonSmall5033) =
      mixedMoment B node3449 node3449Labels := by
    have ha : raw2052 = raw2054 := by apply Matrix.ext; unfold raw2052 raw2054; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5033 = raw2054Labels := by decide +kernel
    rw [ha, hj, canonical2054 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton5047 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5047 node5047Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2449 node2449Labels + mixedMoment B node3432 node3432Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2073 singletonSmall5047
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5047) = raw2073Labels := by decide +kernel
  rw [hl, canonical2073 B hB] at h
  have hc0 : mixedMoment B raw2073 (Fin.cases (0 : Fin 2) singletonSmall5047) =
      mixedMoment B node2449 node2449Labels := by
    have ha : raw2073 = raw2074 := by apply Matrix.ext; unfold raw2073 raw2074; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5047 = raw2074Labels := by decide +kernel
    rw [ha, hj, canonical2074 B hB]
  have hc1 : mixedMoment B raw2073 (Fin.cases (1 : Fin 2) singletonSmall5047) =
      mixedMoment B node3432 node3432Labels := by
    have ha : raw2073 = raw2075 := by apply Matrix.ext; unfold raw2073 raw2075; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5047 = raw2075Labels := by decide +kernel
    rw [ha, hj, canonical2075 B hB]
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

theorem singleton5081 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5081 node5081Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2489 node2489Labels + mixedMoment B node3482 node3482Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2109 singletonSmall5081
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5081) = raw2109Labels := by decide +kernel
  rw [hl, canonical2109 B hB] at h
  have hc0 : mixedMoment B raw2109 (Fin.cases (0 : Fin 2) singletonSmall5081) =
      mixedMoment B node2489 node2489Labels := by
    have ha : raw2109 = raw2110 := by apply Matrix.ext; unfold raw2109 raw2110; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5081 = raw2110Labels := by decide +kernel
    rw [ha, hj, canonical2110 B hB]
  have hc1 : mixedMoment B raw2109 (Fin.cases (1 : Fin 2) singletonSmall5081) =
      mixedMoment B node3482 node3482Labels := by
    have ha : raw2109 = raw2111 := by apply Matrix.ext; unfold raw2109 raw2111; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5081 = raw2111Labels := by decide +kernel
    rw [ha, hj, canonical2111 B hB]
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons80
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singleton5137 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5137 node5137Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2556 node2556Labels + mixedMoment B node3521 node3521Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2166 singletonSmall5137
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5137) = raw2166Labels := by decide +kernel
  rw [hl, canonical2166 B hB] at h
  have hc0 : mixedMoment B raw2166 (Fin.cases (0 : Fin 2) singletonSmall5137) =
      mixedMoment B node2556 node2556Labels := by
    have ha : raw2166 = raw2167 := by apply Matrix.ext; unfold raw2166 raw2167; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5137 = raw2167Labels := by decide +kernel
    rw [ha, hj, canonical2167 B hB]
  have hc1 : mixedMoment B raw2166 (Fin.cases (1 : Fin 2) singletonSmall5137) =
      mixedMoment B node3521 node3521Labels := by
    have ha : raw2166 = raw2168 := by apply Matrix.ext; unfold raw2166 raw2168; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5137 = raw2168Labels := by decide +kernel
    rw [ha, hj, canonical2168 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton5141 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5141 node5141Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2561 node2561Labels + mixedMoment B node3522 node3522Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2169 singletonSmall5141
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5141) = raw2169Labels := by decide +kernel
  rw [hl, canonical2169 B hB] at h
  have hc0 : mixedMoment B raw2169 (Fin.cases (0 : Fin 2) singletonSmall5141) =
      mixedMoment B node2561 node2561Labels := by
    have ha : raw2169 = raw2170 := by apply Matrix.ext; unfold raw2169 raw2170; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5141 = raw2170Labels := by decide +kernel
    rw [ha, hj, canonical2170 B hB]
  have hc1 : mixedMoment B raw2169 (Fin.cases (1 : Fin 2) singletonSmall5141) =
      mixedMoment B node3522 node3522Labels := by
    have ha : raw2169 = raw2171 := by apply Matrix.ext; unfold raw2169 raw2171; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5141 = raw2171Labels := by decide +kernel
    rw [ha, hj, canonical2171 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton5171 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5171 node5171Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2598 node2598Labels + mixedMoment B node3608 node3608Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2205 singletonSmall5171
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5171) = raw2205Labels := by decide +kernel
  rw [hl, canonical2205 B hB] at h
  have hc0 : mixedMoment B raw2205 (Fin.cases (0 : Fin 2) singletonSmall5171) =
      mixedMoment B node2598 node2598Labels := by
    have ha : raw2205 = raw2206 := by apply Matrix.ext; unfold raw2205 raw2206; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5171 = raw2206Labels := by decide +kernel
    rw [ha, hj, canonical2206 B hB]
  have hc1 : mixedMoment B raw2205 (Fin.cases (1 : Fin 2) singletonSmall5171) =
      mixedMoment B node3608 node3608Labels := by
    have ha : raw2205 = raw2207 := by apply Matrix.ext; unfold raw2205 raw2207; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5171 = raw2207Labels := by decide +kernel
    rw [ha, hj, canonical2207 B hB]
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

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound13
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound865 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node865 node865Labels = Sparse.eval nodeValue865 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 865) = mixedMoment B node865 node865Labels := rfl
  simpa [nodeValue865, Sparse.eval] using hc.symm

theorem sound867 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node867 node867Labels = Sparse.eval nodeValue867 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 867) = mixedMoment B node867 node867Labels := rfl
  simpa [nodeValue867, Sparse.eval] using hc.symm

theorem sound873 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node873 node873Labels = Sparse.eval nodeValue873 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 873) = mixedMoment B node873 node873Labels := rfl
  simpa [nodeValue873, Sparse.eval] using hc.symm

theorem sound881 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node881 node881Labels = Sparse.eval nodeValue881 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 881) = mixedMoment B node881 node881Labels := rfl
  simpa [nodeValue881, Sparse.eval] using hc.symm

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

theorem sound900 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node900 node900Labels = Sparse.eval nodeValue900 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 900) = mixedMoment B node900 node900Labels := rfl
  simpa [nodeValue900, Sparse.eval] using hc.symm

theorem sound903 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node903 node903Labels = Sparse.eval nodeValue903 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 903) = mixedMoment B node903 node903Labels := rfl
  simpa [nodeValue903, Sparse.eval] using hc.symm

theorem sound924 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node924 node924Labels = Sparse.eval nodeValue924 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 924) = mixedMoment B node924 node924Labels := rfl
  simpa [nodeValue924, Sparse.eval] using hc.symm

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

theorem sound982 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node982 node982Labels = Sparse.eval nodeValue982 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 982) = mixedMoment B node982 node982Labels := rfl
  simpa [nodeValue982, Sparse.eval] using hc.symm

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound24
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound1553 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1553 node1553Labels = Sparse.eval nodeValue1553 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1553) = mixedMoment B node1553 node1553Labels := rfl
  simpa [nodeValue1553, Sparse.eval] using hc.symm

theorem sound1555 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1555 node1555Labels = Sparse.eval nodeValue1555 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1555) = mixedMoment B node1555 node1555Labels := rfl
  simpa [nodeValue1555, Sparse.eval] using hc.symm

theorem sound1559 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1559 node1559Labels = Sparse.eval nodeValue1559 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1559) = mixedMoment B node1559 node1559Labels := rfl
  simpa [nodeValue1559, Sparse.eval] using hc.symm

theorem sound1569 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1569 node1569Labels = Sparse.eval nodeValue1569 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1569) = mixedMoment B node1569 node1569Labels := rfl
  simpa [nodeValue1569, Sparse.eval] using hc.symm

theorem sound1588 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1588 node1588Labels = Sparse.eval nodeValue1588 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1588) = mixedMoment B node1588 node1588Labels := rfl
  simpa [nodeValue1588, Sparse.eval] using hc.symm

theorem sound1591 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1591 node1591Labels = Sparse.eval nodeValue1591 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1591) = mixedMoment B node1591 node1591Labels := rfl
  simpa [nodeValue1591, Sparse.eval] using hc.symm

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

theorem sound1617 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1617 node1617Labels = Sparse.eval nodeValue1617 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1617) = mixedMoment B node1617 node1617Labels := rfl
  simpa [nodeValue1617, Sparse.eval] using hc.symm

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

theorem sound1674 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1674 node1674Labels = Sparse.eval nodeValue1674 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1674) = mixedMoment B node1674 node1674Labels := rfl
  simpa [nodeValue1674, Sparse.eval] using hc.symm

theorem sound1725 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1725 node1725Labels = Sparse.eval nodeValue1725 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1725) = mixedMoment B node1725 node1725Labels := rfl
  simpa [nodeValue1725, Sparse.eval] using hc.symm

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

theorem sound2295 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2295 node2295Labels = Sparse.eval nodeValue2295 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2295) = mixedMoment B node2295 node2295Labels := rfl
  simpa [nodeValue2295, Sparse.eval] using hc.symm

theorem sound2300 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2300 node2300Labels = Sparse.eval nodeValue2300 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2300) = mixedMoment B node2300 node2300Labels := rfl
  simpa [nodeValue2300, Sparse.eval] using hc.symm

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

theorem sound2306 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2306 node2306Labels = Sparse.eval nodeValue2306 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2306) = mixedMoment B node2306 node2306Labels := rfl
  simpa [nodeValue2306, Sparse.eval] using hc.symm

theorem sound2317 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2317 node2317Labels = Sparse.eval nodeValue2317 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2317) = mixedMoment B node2317 node2317Labels := rfl
  simpa [nodeValue2317, Sparse.eval] using hc.symm

theorem sound2334 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2334 node2334Labels = Sparse.eval nodeValue2334 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2334) = mixedMoment B node2334 node2334Labels := rfl
  simpa [nodeValue2334, Sparse.eval] using hc.symm

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

theorem sound2371 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2371 node2371Labels = Sparse.eval nodeValue2371 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2371) = mixedMoment B node2371 node2371Labels := rfl
  simpa [nodeValue2371, Sparse.eval] using hc.symm

theorem sound2385 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2385 node2385Labels = Sparse.eval nodeValue2385 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2385) = mixedMoment B node2385 node2385Labels := rfl
  simpa [nodeValue2385, Sparse.eval] using hc.symm

theorem sound2425 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2425 node2425Labels = Sparse.eval nodeValue2425 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2425) = mixedMoment B node2425 node2425Labels := rfl
  simpa [nodeValue2425, Sparse.eval] using hc.symm

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

theorem sound2449 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2449 node2449Labels = Sparse.eval nodeValue2449 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2449) = mixedMoment B node2449 node2449Labels := rfl
  simpa [nodeValue2449, Sparse.eval] using hc.symm

theorem sound2480 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2480 node2480Labels = Sparse.eval nodeValue2480 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2480) = mixedMoment B node2480 node2480Labels := rfl
  simpa [nodeValue2480, Sparse.eval] using hc.symm

theorem sound2482 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2482 node2482Labels = Sparse.eval nodeValue2482 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2482) = mixedMoment B node2482 node2482Labels := rfl
  simpa [nodeValue2482, Sparse.eval] using hc.symm

theorem sound2489 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2489 node2489Labels = Sparse.eval nodeValue2489 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2489) = mixedMoment B node2489 node2489Labels := rfl
  simpa [nodeValue2489, Sparse.eval] using hc.symm

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

theorem sound2556 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2556 node2556Labels = Sparse.eval nodeValue2556 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2556) = mixedMoment B node2556 node2556Labels := rfl
  simpa [nodeValue2556, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound5
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound338 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node338 node338Labels = Sparse.eval nodeValue338 (mixedVector B) := by
  calc
    _ = Sparse.eval singlePairValue338 (familyPairVector B) := singlePair338 B _hB
    _ = _ := by norm_num [singlePairValue338, nodeValue338, Sparse.eval, mixedVector] <;> ring

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound40
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound2561 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2561 node2561Labels = Sparse.eval nodeValue2561 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2561) = mixedMoment B node2561 node2561Labels := rfl
  simpa [nodeValue2561, Sparse.eval] using hc.symm

theorem sound2598 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2598 node2598Labels = Sparse.eval nodeValue2598 (mixedVector B) := by
  have h := singleton2598 B _hB
  rw [sound338 B _hB _hF] at h
  norm_num [nodeValue2598, nodeValue338, Sparse.eval] at h ⊢
  linarith only [h]

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

theorem sound3315 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3315 node3315Labels = Sparse.eval nodeValue3315 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3315) = mixedMoment B node3315 node3315Labels := rfl
  simpa [nodeValue3315, Sparse.eval] using hc.symm

theorem sound3318 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3318 node3318Labels = Sparse.eval nodeValue3318 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3318) = mixedMoment B node3318 node3318Labels := rfl
  simpa [nodeValue3318, Sparse.eval] using hc.symm

theorem sound3325 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3325 node3325Labels = Sparse.eval nodeValue3325 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3325) = mixedMoment B node3325 node3325Labels := rfl
  simpa [nodeValue3325, Sparse.eval] using hc.symm

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

theorem sound3335 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3335 node3335Labels = Sparse.eval nodeValue3335 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3335) = mixedMoment B node3335 node3335Labels := rfl
  simpa [nodeValue3335, Sparse.eval] using hc.symm

theorem sound3353 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3353 node3353Labels = Sparse.eval nodeValue3353 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3353) = mixedMoment B node3353 node3353Labels := rfl
  simpa [nodeValue3353, Sparse.eval] using hc.symm

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

theorem sound3399 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3399 node3399Labels = Sparse.eval nodeValue3399 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3399) = mixedMoment B node3399 node3399Labels := rfl
  simpa [nodeValue3399, Sparse.eval] using hc.symm

theorem sound3411 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3411 node3411Labels = Sparse.eval nodeValue3411 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3411) = mixedMoment B node3411 node3411Labels := rfl
  simpa [nodeValue3411, Sparse.eval] using hc.symm

theorem sound3432 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3432 node3432Labels = Sparse.eval nodeValue3432 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3432) = mixedMoment B node3432 node3432Labels := rfl
  simpa [nodeValue3432, Sparse.eval] using hc.symm

theorem sound3449 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3449 node3449Labels = Sparse.eval nodeValue3449 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3449) = mixedMoment B node3449 node3449Labels := rfl
  simpa [nodeValue3449, Sparse.eval] using hc.symm

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

theorem sound3467 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3467 node3467Labels = Sparse.eval nodeValue3467 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3467) = mixedMoment B node3467 node3467Labels := rfl
  simpa [nodeValue3467, Sparse.eval] using hc.symm

theorem sound3468 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3468 node3468Labels = Sparse.eval nodeValue3468 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3468) = mixedMoment B node3468 node3468Labels := rfl
  simpa [nodeValue3468, Sparse.eval] using hc.symm

theorem sound3471 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3471 node3471Labels = Sparse.eval nodeValue3471 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3471) = mixedMoment B node3471 node3471Labels := rfl
  simpa [nodeValue3471, Sparse.eval] using hc.symm

theorem sound3482 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3482 node3482Labels = Sparse.eval nodeValue3482 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3482) = mixedMoment B node3482 node3482Labels := rfl
  simpa [nodeValue3482, Sparse.eval] using hc.symm

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

theorem sound3521 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3521 node3521Labels = Sparse.eval nodeValue3521 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3521) = mixedMoment B node3521 node3521Labels := rfl
  simpa [nodeValue3521, Sparse.eval] using hc.symm

theorem sound3522 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3522 node3522Labels = Sparse.eval nodeValue3522 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3522) = mixedMoment B node3522 node3522Labels := rfl
  simpa [nodeValue3522, Sparse.eval] using hc.symm

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

theorem sound3608 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3608 node3608Labels = Sparse.eval nodeValue3608 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3608) = mixedMoment B node3608 node3608Labels := rfl
  simpa [nodeValue3608, Sparse.eval] using hc.symm

theorem sound3627 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3627 node3627Labels = Sparse.eval nodeValue3627 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3627) = mixedMoment B node3627 node3627Labels := rfl
  simpa [nodeValue3627, Sparse.eval] using hc.symm

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

theorem sound4287 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4287 node4287Labels = Sparse.eval nodeValue4287 (mixedVector B) := by
  have h := singleton4287 B _hB
  rw [sound865 B _hB _hF, sound1553 B _hB _hF] at h
  norm_num [nodeValue4287, nodeValue865, nodeValue1553, Sparse.eval] at h ⊢
  linarith only [h]

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

theorem sound4289 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4289 node4289Labels = Sparse.eval nodeValue4289 (mixedVector B) := by
  have h := singleton4289 B _hB
  rw [sound867 B _hB _hF, sound1555 B _hB _hF] at h
  norm_num [nodeValue4289, nodeValue867, nodeValue1555, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4295 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4295 node4295Labels = Sparse.eval nodeValue4295 (mixedVector B) := by
  have h := singleton4295 B _hB
  rw [sound873 B _hB _hF, sound1569 B _hB _hF] at h
  norm_num [nodeValue4295, nodeValue873, nodeValue1569, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4303 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4303 node4303Labels = Sparse.eval nodeValue4303 (mixedVector B) := by
  have h := singleton4303 B _hB
  rw [sound881 B _hB _hF, sound1559 B _hB _hF] at h
  norm_num [nodeValue4303, nodeValue881, nodeValue1559, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4322 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4322 node4322Labels = Sparse.eval nodeValue4322 (mixedVector B) := by
  have h := singleton4322 B _hB
  rw [sound900 B _hB _hF, sound1588 B _hB _hF] at h
  norm_num [nodeValue4322, nodeValue900, nodeValue1588, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4325 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4325 node4325Labels = Sparse.eval nodeValue4325 (mixedVector B) := by
  have h := singleton4325 B _hB
  rw [sound903 B _hB _hF, sound1591 B _hB _hF] at h
  norm_num [nodeValue4325, nodeValue903, nodeValue1591, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4346 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4346 node4346Labels = Sparse.eval nodeValue4346 (mixedVector B) := by
  have h := singleton4346 B _hB
  rw [sound924 B _hB _hF, sound1674 B _hB _hF] at h
  norm_num [nodeValue4346, nodeValue924, nodeValue1674, Sparse.eval] at h ⊢
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

theorem sound4401 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4401 node4401Labels = Sparse.eval nodeValue4401 (mixedVector B) := by
  have h := singleton4401 B _hB
  rw [sound982 B _hB _hF, sound1617 B _hB _hF] at h
  norm_num [nodeValue4401, nodeValue982, nodeValue1617, Sparse.eval] at h ⊢
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound76
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound4902 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4902 node4902Labels = Sparse.eval nodeValue4902 (mixedVector B) := by
  have h := singleton4902 B _hB
  rw [sound2295 B _hB _hF, sound3315 B _hB _hF] at h
  norm_num [nodeValue4902, nodeValue2295, nodeValue3315, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4907 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4907 node4907Labels = Sparse.eval nodeValue4907 (mixedVector B) := by
  have h := singleton4907 B _hB
  rw [sound2300 B _hB _hF, sound3325 B _hB _hF] at h
  norm_num [nodeValue4907, nodeValue2300, nodeValue3325, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4913 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4913 node4913Labels = Sparse.eval nodeValue4913 (mixedVector B) := by
  have h := singleton4913 B _hB
  rw [sound2306 B _hB _hF, sound3318 B _hB _hF] at h
  norm_num [nodeValue4913, nodeValue2306, nodeValue3318, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4927 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4927 node4927Labels = Sparse.eval nodeValue4927 (mixedVector B) := by
  have h := singleton4927 B _hB
  rw [sound2317 B _hB _hF, sound3399 B _hB _hF] at h
  norm_num [nodeValue4927, nodeValue2317, nodeValue3399, Sparse.eval] at h ⊢
  linarith only [h]

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

theorem sound4943 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4943 node4943Labels = Sparse.eval nodeValue4943 (mixedVector B) := by
  have h := singleton4943 B _hB
  rw [sound2334 B _hB _hF, sound3411 B _hB _hF] at h
  norm_num [nodeValue4943, nodeValue2334, nodeValue3411, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4986 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4986 node4986Labels = Sparse.eval nodeValue4986 (mixedVector B) := by
  have h := singleton4986 B _hB
  rw [sound2371 B _hB _hF, sound3335 B _hB _hF] at h
  norm_num [nodeValue4986, nodeValue2371, nodeValue3335, Sparse.eval] at h ⊢
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

theorem sound5033 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5033 node5033Labels = Sparse.eval nodeValue5033 (mixedVector B) := by
  have h := singleton5033 B _hB
  rw [sound2425 B _hB _hF, sound3449 B _hB _hF] at h
  norm_num [nodeValue5033, nodeValue2425, nodeValue3449, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5047 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5047 node5047Labels = Sparse.eval nodeValue5047 (mixedVector B) := by
  have h := singleton5047 B _hB
  rw [sound2449 B _hB _hF, sound3432 B _hB _hF] at h
  norm_num [nodeValue5047, nodeValue2449, nodeValue3432, Sparse.eval] at h ⊢
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

theorem sound5073 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5073 node5073Labels = Sparse.eval nodeValue5073 (mixedVector B) := by
  have h := singleton5073 B _hB
  rw [sound2480 B _hB _hF, sound3467 B _hB _hF] at h
  norm_num [nodeValue5073, nodeValue2480, nodeValue3467, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5075 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5075 node5075Labels = Sparse.eval nodeValue5075 (mixedVector B) := by
  have h := singleton5075 B _hB
  rw [sound2482 B _hB _hF, sound3468 B _hB _hF] at h
  norm_num [nodeValue5075, nodeValue2482, nodeValue3468, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5081 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5081 node5081Labels = Sparse.eval nodeValue5081 (mixedVector B) := by
  have h := singleton5081 B _hB
  rw [sound2489 B _hB _hF, sound3482 B _hB _hF] at h
  norm_num [nodeValue5081, nodeValue2489, nodeValue3482, Sparse.eval] at h ⊢
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound80
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound5137 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5137 node5137Labels = Sparse.eval nodeValue5137 (mixedVector B) := by
  have h := singleton5137 B _hB
  rw [sound2556 B _hB _hF, sound3521 B _hB _hF] at h
  norm_num [nodeValue5137, nodeValue2556, nodeValue3521, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5141 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5141 node5141Labels = Sparse.eval nodeValue5141 (mixedVector B) := by
  have h := singleton5141 B _hB
  rw [sound2561 B _hB _hF, sound3522 B _hB _hF] at h
  norm_num [nodeValue5141, nodeValue2561, nodeValue3522, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5171 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5171 node5171Labels = Sparse.eval nodeValue5171 (mixedVector B) := by
  have h := singleton5171 B _hB
  rw [sound2598 B _hB _hF, sound3608 B _hB _hF] at h
  norm_num [nodeValue5171, nodeValue2598, nodeValue3608, Sparse.eval] at h ⊢
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

theorem sound5293 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5293 node5293Labels = Sparse.eval nodeValue5293 (mixedVector B) := by
  have h := singleton5293 B _hB
  rw [sound2767 B _hB _hF, sound3627 B _hB _hF] at h
  norm_num [nodeValue5293, nodeValue2767, nodeValue3627, Sparse.eval] at h ⊢
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

theorem sourceEq2036 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2036 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2036 + difference 0 1) (sourceB2036 + difference 1 0) sourceC2036) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5081) := by
    have ha : (tripleCharges (sourceA2036 + difference 0 1) (sourceB2036 + difference 1 0) sourceC2036) = raw17099 := by
      apply Matrix.ext; unfold tripleCharges sourceA2036 sourceB2036 sourceC2036 difference raw17099; decide +kernel
    rw [ha]
    exact (canonical17099 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2036 + difference 0 2) (sourceB2036 + difference 2 0) sourceC2036) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5073) := by
    have ha : (tripleCharges (sourceA2036 + difference 0 2) (sourceB2036 + difference 2 0) sourceC2036) = raw17100 := by
      apply Matrix.ext; unfold tripleCharges sourceA2036 sourceB2036 sourceC2036 difference raw17100; decide +kernel
    rw [ha]
    exact (canonical17100 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2036 + difference 0 3) (sourceB2036 + difference 3 0) sourceC2036) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5102) := by
    have ha : (tripleCharges (sourceA2036 + difference 0 3) (sourceB2036 + difference 3 0) sourceC2036) = raw17101 := by
      apply Matrix.ext; unfold tripleCharges sourceA2036 sourceB2036 sourceC2036 difference raw17101; decide +kernel
    rw [ha]
    exact (canonical17101 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2036 + difference 0 4) (sourceB2036 + difference 4 0) sourceC2036) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5293) := by
    have ha : (tripleCharges (sourceA2036 + difference 0 4) (sourceB2036 + difference 4 0) sourceC2036) = raw17102 := by
      apply Matrix.ext; unfold tripleCharges sourceA2036 sourceB2036 sourceC2036 difference raw17102; decide +kernel
    rw [ha]
    exact (canonical17102 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2036 + difference 0 5) (sourceB2036 + difference 5 0) sourceC2036) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5483) := by
    have ha : (tripleCharges (sourceA2036 + difference 0 5) (sourceB2036 + difference 5 0) sourceC2036) = raw3145 := by
      apply Matrix.ext; unfold tripleCharges sourceA2036 sourceB2036 sourceC2036 difference raw3145; decide +kernel
    rw [ha]
    exact (canonical3145 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2036 + difference 1 0) (sourceB2036 + difference 0 1) sourceC2036) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4401) := by
    have ha : (tripleCharges (sourceA2036 + difference 1 0) (sourceB2036 + difference 0 1) sourceC2036) = raw9864 := by
      apply Matrix.ext; unfold tripleCharges sourceA2036 sourceB2036 sourceC2036 difference raw9864; decide +kernel
    rw [ha]
    exact (canonical9864 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2036 + difference 1 2) (sourceB2036 + difference 2 1) sourceC2036) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5047) := by
    have ha : (tripleCharges (sourceA2036 + difference 1 2) (sourceB2036 + difference 2 1) sourceC2036) = raw9866 := by
      apply Matrix.ext; unfold tripleCharges sourceA2036 sourceB2036 sourceC2036 difference raw9866; decide +kernel
    rw [ha]
    exact (canonical9866 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2036 + difference 1 3) (sourceB2036 + difference 3 1) sourceC2036) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5000) := by
    have ha : (tripleCharges (sourceA2036 + difference 1 3) (sourceB2036 + difference 3 1) sourceC2036) = raw9867 := by
      apply Matrix.ext; unfold tripleCharges sourceA2036 sourceB2036 sourceC2036 difference raw9867; decide +kernel
    rw [ha]
    exact (canonical9867 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2036 + difference 1 4) (sourceB2036 + difference 4 1) sourceC2036) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5261) := by
    have ha : (tripleCharges (sourceA2036 + difference 1 4) (sourceB2036 + difference 4 1) sourceC2036) = raw9868 := by
      apply Matrix.ext; unfold tripleCharges sourceA2036 sourceB2036 sourceC2036 difference raw9868; decide +kernel
    rw [ha]
    exact (canonical9868 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2036 + difference 1 5) (sourceB2036 + difference 5 1) sourceC2036) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5259) := by
    have ha : (tripleCharges (sourceA2036 + difference 1 5) (sourceB2036 + difference 5 1) sourceC2036) = raw3144 := by
      apply Matrix.ext; unfold tripleCharges sourceA2036 sourceB2036 sourceC2036 difference raw3144; decide +kernel
    rw [ha]
    exact (canonical3144 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2036 + difference 2 0) (sourceB2036 + difference 0 2) sourceC2036) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4322) := by
    have ha : (tripleCharges (sourceA2036 + difference 2 0) (sourceB2036 + difference 0 2) sourceC2036) = raw28764 := by
      apply Matrix.ext; unfold tripleCharges sourceA2036 sourceB2036 sourceC2036 difference raw28764; decide +kernel
    rw [ha]
    exact (canonical28764 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2036 + difference 2 1) (sourceB2036 + difference 1 2) sourceC2036) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4927) := by
    have ha : (tripleCharges (sourceA2036 + difference 2 1) (sourceB2036 + difference 1 2) sourceC2036) = raw28765 := by
      apply Matrix.ext; unfold tripleCharges sourceA2036 sourceB2036 sourceC2036 difference raw28765; decide +kernel
    rw [ha]
    exact (canonical28765 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2036 + difference 2 3) (sourceB2036 + difference 3 2) sourceC2036) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4986) := by
    have ha : (tripleCharges (sourceA2036 + difference 2 3) (sourceB2036 + difference 3 2) sourceC2036) = raw28766 := by
      apply Matrix.ext; unfold tripleCharges sourceA2036 sourceB2036 sourceC2036 difference raw28766; decide +kernel
    rw [ha]
    exact (canonical28766 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2036 + difference 2 4) (sourceB2036 + difference 4 2) sourceC2036) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5075) := by
    have ha : (tripleCharges (sourceA2036 + difference 2 4) (sourceB2036 + difference 4 2) sourceC2036) = raw28767 := by
      apply Matrix.ext; unfold tripleCharges sourceA2036 sourceB2036 sourceC2036 difference raw28767; decide +kernel
    rw [ha]
    exact (canonical28767 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2036 + difference 2 5) (sourceB2036 + difference 5 2) sourceC2036) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5137) := by
    have ha : (tripleCharges (sourceA2036 + difference 2 5) (sourceB2036 + difference 5 2) sourceC2036) = raw9853 := by
      apply Matrix.ext; unfold tripleCharges sourceA2036 sourceB2036 sourceC2036 difference raw9853; decide +kernel
    rw [ha]
    exact (canonical9853 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2036 + difference 3 0) (sourceB2036 + difference 0 3) sourceC2036) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4346) := by
    have ha : (tripleCharges (sourceA2036 + difference 3 0) (sourceB2036 + difference 0 3) sourceC2036) = raw28768 := by
      apply Matrix.ext; unfold tripleCharges sourceA2036 sourceB2036 sourceC2036 difference raw28768; decide +kernel
    rw [ha]
    exact (canonical28768 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2036 + difference 3 1) (sourceB2036 + difference 1 3) sourceC2036) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4943) := by
    have ha : (tripleCharges (sourceA2036 + difference 3 1) (sourceB2036 + difference 1 3) sourceC2036) = raw28769 := by
      apply Matrix.ext; unfold tripleCharges sourceA2036 sourceB2036 sourceC2036 difference raw28769; decide +kernel
    rw [ha]
    exact (canonical28769 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2036 + difference 3 2) (sourceB2036 + difference 2 3) sourceC2036) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5033) := by
    have ha : (tripleCharges (sourceA2036 + difference 3 2) (sourceB2036 + difference 2 3) sourceC2036) = raw28770 := by
      apply Matrix.ext; unfold tripleCharges sourceA2036 sourceB2036 sourceC2036 difference raw28770; decide +kernel
    rw [ha]
    exact (canonical28770 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2036 + difference 3 4) (sourceB2036 + difference 4 3) sourceC2036) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5171) := by
    have ha : (tripleCharges (sourceA2036 + difference 3 4) (sourceB2036 + difference 4 3) sourceC2036) = raw28771 := by
      apply Matrix.ext; unfold tripleCharges sourceA2036 sourceB2036 sourceC2036 difference raw28771; decide +kernel
    rw [ha]
    exact (canonical28771 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2036 + difference 3 5) (sourceB2036 + difference 5 3) sourceC2036) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5169) := by
    have ha : (tripleCharges (sourceA2036 + difference 3 5) (sourceB2036 + difference 5 3) sourceC2036) = raw9857 := by
      apply Matrix.ext; unfold tripleCharges sourceA2036 sourceB2036 sourceC2036 difference raw9857; decide +kernel
    rw [ha]
    exact (canonical9857 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2036 + difference 4 0) (sourceB2036 + difference 0 4) sourceC2036) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4325) := by
    have ha : (tripleCharges (sourceA2036 + difference 4 0) (sourceB2036 + difference 0 4) sourceC2036) = raw28772 := by
      apply Matrix.ext; unfold tripleCharges sourceA2036 sourceB2036 sourceC2036 difference raw28772; decide +kernel
    rw [ha]
    exact (canonical28772 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2036 + difference 4 1) (sourceB2036 + difference 1 4) sourceC2036) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4907) := by
    have ha : (tripleCharges (sourceA2036 + difference 4 1) (sourceB2036 + difference 1 4) sourceC2036) = raw28773 := by
      apply Matrix.ext; unfold tripleCharges sourceA2036 sourceB2036 sourceC2036 difference raw28773; decide +kernel
    rw [ha]
    exact (canonical28773 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2036 + difference 4 2) (sourceB2036 + difference 2 4) sourceC2036) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4902) := by
    have ha : (tripleCharges (sourceA2036 + difference 4 2) (sourceB2036 + difference 2 4) sourceC2036) = raw28774 := by
      apply Matrix.ext; unfold tripleCharges sourceA2036 sourceB2036 sourceC2036 difference raw28774; decide +kernel
    rw [ha]
    exact (canonical28774 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2036 + difference 4 3) (sourceB2036 + difference 3 4) sourceC2036) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4913) := by
    have ha : (tripleCharges (sourceA2036 + difference 4 3) (sourceB2036 + difference 3 4) sourceC2036) = raw28775 := by
      apply Matrix.ext; unfold tripleCharges sourceA2036 sourceB2036 sourceC2036 difference raw28775; decide +kernel
    rw [ha]
    exact (canonical28775 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2036 + difference 4 5) (sourceB2036 + difference 5 4) sourceC2036) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5141) := by
    have ha : (tripleCharges (sourceA2036 + difference 4 5) (sourceB2036 + difference 5 4) sourceC2036) = raw9861 := by
      apply Matrix.ext; unfold tripleCharges sourceA2036 sourceB2036 sourceC2036 difference raw9861; decide +kernel
    rw [ha]
    exact (canonical9861 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2036 + difference 5 0) (sourceB2036 + difference 0 5) sourceC2036) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4289) := by
    have ha : (tripleCharges (sourceA2036 + difference 5 0) (sourceB2036 + difference 0 5) sourceC2036) = raw28776 := by
      apply Matrix.ext; unfold tripleCharges sourceA2036 sourceB2036 sourceC2036 difference raw28776; decide +kernel
    rw [ha]
    exact (canonical28776 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2036 + difference 5 1) (sourceB2036 + difference 1 5) sourceC2036) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4295) := by
    have ha : (tripleCharges (sourceA2036 + difference 5 1) (sourceB2036 + difference 1 5) sourceC2036) = raw28777 := by
      apply Matrix.ext; unfold tripleCharges sourceA2036 sourceB2036 sourceC2036 difference raw28777; decide +kernel
    rw [ha]
    exact (canonical28777 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2036 + difference 5 2) (sourceB2036 + difference 2 5) sourceC2036) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4287) := by
    have ha : (tripleCharges (sourceA2036 + difference 5 2) (sourceB2036 + difference 2 5) sourceC2036) = raw28778 := by
      apply Matrix.ext; unfold tripleCharges sourceA2036 sourceB2036 sourceC2036 difference raw28778; decide +kernel
    rw [ha]
    exact (canonical28778 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2036 + difference 5 3) (sourceB2036 + difference 3 5) sourceC2036) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4303) := by
    have ha : (tripleCharges (sourceA2036 + difference 5 3) (sourceB2036 + difference 3 5) sourceC2036) = raw28779 := by
      apply Matrix.ext; unfold tripleCharges sourceA2036 sourceB2036 sourceC2036 difference raw28779; decide +kernel
    rw [ha]
    exact (canonical28779 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2036 + difference 5 4) (sourceB2036 + difference 4 5) sourceC2036) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4460) := by
    have ha : (tripleCharges (sourceA2036 + difference 5 4) (sourceB2036 + difference 4 5) sourceC2036) = raw28780 := by
      apply Matrix.ext; unfold tripleCharges sourceA2036 sourceB2036 sourceC2036 difference raw28780; decide +kernel
    rw [ha]
    exact (canonical28780 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2036 sourceB2036 sourceC2036
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2036, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic107
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reindexCheck1715 : Integer.Sparse.reindex keyMap MixedData.row1715 = numericRow1715 := by decide +kernel

theorem numericCheck1715 (x : Master → ℝ) : Integer.Sparse.eval numericRow1715 x =
    (17280 : ℝ) * reducedSource1715 x := by
  norm_num [numericRow1715, reducedSource1715, Integer.Sparse.eval, Sparse.eval, nodeValue4287, nodeValue4289, nodeValue4295, nodeValue4303, nodeValue4322, nodeValue4325, nodeValue4346, nodeValue4401, nodeValue4460, nodeValue4902, nodeValue4907, nodeValue4913, nodeValue4927, nodeValue4943, nodeValue4986, nodeValue5000, nodeValue5033, nodeValue5047, nodeValue5073, nodeValue5075, nodeValue5081, nodeValue5102, nodeValue5137, nodeValue5141, nodeValue5169, nodeValue5171, nodeValue5259, nodeValue5261, nodeValue5293, nodeValue5483] <;> ring

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Rows107
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero1715 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1715 (mixedVector B) = 0 := by
  have h4287 : mixedVector B (Sum.inr 4287) = Sparse.eval nodeValue4287 (mixedVector B) := by
    change mixedMoment B node4287 node4287Labels = _
    exact sound4287 B hB hF
  have h4289 : mixedVector B (Sum.inr 4289) = Sparse.eval nodeValue4289 (mixedVector B) := by
    change mixedMoment B node4289 node4289Labels = _
    exact sound4289 B hB hF
  have h4295 : mixedVector B (Sum.inr 4295) = Sparse.eval nodeValue4295 (mixedVector B) := by
    change mixedMoment B node4295 node4295Labels = _
    exact sound4295 B hB hF
  have h4303 : mixedVector B (Sum.inr 4303) = Sparse.eval nodeValue4303 (mixedVector B) := by
    change mixedMoment B node4303 node4303Labels = _
    exact sound4303 B hB hF
  have h4322 : mixedVector B (Sum.inr 4322) = Sparse.eval nodeValue4322 (mixedVector B) := by
    change mixedMoment B node4322 node4322Labels = _
    exact sound4322 B hB hF
  have h4325 : mixedVector B (Sum.inr 4325) = Sparse.eval nodeValue4325 (mixedVector B) := by
    change mixedMoment B node4325 node4325Labels = _
    exact sound4325 B hB hF
  have h4346 : mixedVector B (Sum.inr 4346) = Sparse.eval nodeValue4346 (mixedVector B) := by
    change mixedMoment B node4346 node4346Labels = _
    exact sound4346 B hB hF
  have h4401 : mixedVector B (Sum.inr 4401) = Sparse.eval nodeValue4401 (mixedVector B) := by
    change mixedMoment B node4401 node4401Labels = _
    exact sound4401 B hB hF
  have h4460 : mixedVector B (Sum.inr 4460) = Sparse.eval nodeValue4460 (mixedVector B) := by
    change mixedMoment B node4460 node4460Labels = _
    exact sound4460 B hB hF
  have h4902 : mixedVector B (Sum.inr 4902) = Sparse.eval nodeValue4902 (mixedVector B) := by
    change mixedMoment B node4902 node4902Labels = _
    exact sound4902 B hB hF
  have h4907 : mixedVector B (Sum.inr 4907) = Sparse.eval nodeValue4907 (mixedVector B) := by
    change mixedMoment B node4907 node4907Labels = _
    exact sound4907 B hB hF
  have h4913 : mixedVector B (Sum.inr 4913) = Sparse.eval nodeValue4913 (mixedVector B) := by
    change mixedMoment B node4913 node4913Labels = _
    exact sound4913 B hB hF
  have h4927 : mixedVector B (Sum.inr 4927) = Sparse.eval nodeValue4927 (mixedVector B) := by
    change mixedMoment B node4927 node4927Labels = _
    exact sound4927 B hB hF
  have h4943 : mixedVector B (Sum.inr 4943) = Sparse.eval nodeValue4943 (mixedVector B) := by
    change mixedMoment B node4943 node4943Labels = _
    exact sound4943 B hB hF
  have h4986 : mixedVector B (Sum.inr 4986) = Sparse.eval nodeValue4986 (mixedVector B) := by
    change mixedMoment B node4986 node4986Labels = _
    exact sound4986 B hB hF
  have h5000 : mixedVector B (Sum.inr 5000) = Sparse.eval nodeValue5000 (mixedVector B) := by
    change mixedMoment B node5000 node5000Labels = _
    exact sound5000 B hB hF
  have h5033 : mixedVector B (Sum.inr 5033) = Sparse.eval nodeValue5033 (mixedVector B) := by
    change mixedMoment B node5033 node5033Labels = _
    exact sound5033 B hB hF
  have h5047 : mixedVector B (Sum.inr 5047) = Sparse.eval nodeValue5047 (mixedVector B) := by
    change mixedMoment B node5047 node5047Labels = _
    exact sound5047 B hB hF
  have h5073 : mixedVector B (Sum.inr 5073) = Sparse.eval nodeValue5073 (mixedVector B) := by
    change mixedMoment B node5073 node5073Labels = _
    exact sound5073 B hB hF
  have h5075 : mixedVector B (Sum.inr 5075) = Sparse.eval nodeValue5075 (mixedVector B) := by
    change mixedMoment B node5075 node5075Labels = _
    exact sound5075 B hB hF
  have h5081 : mixedVector B (Sum.inr 5081) = Sparse.eval nodeValue5081 (mixedVector B) := by
    change mixedMoment B node5081 node5081Labels = _
    exact sound5081 B hB hF
  have h5102 : mixedVector B (Sum.inr 5102) = Sparse.eval nodeValue5102 (mixedVector B) := by
    change mixedMoment B node5102 node5102Labels = _
    exact sound5102 B hB hF
  have h5137 : mixedVector B (Sum.inr 5137) = Sparse.eval nodeValue5137 (mixedVector B) := by
    change mixedMoment B node5137 node5137Labels = _
    exact sound5137 B hB hF
  have h5141 : mixedVector B (Sum.inr 5141) = Sparse.eval nodeValue5141 (mixedVector B) := by
    change mixedMoment B node5141 node5141Labels = _
    exact sound5141 B hB hF
  have h5169 : mixedVector B (Sum.inr 5169) = Sparse.eval nodeValue5169 (mixedVector B) := by
    change mixedMoment B node5169 node5169Labels = _
    exact sound5169_e B hB hF
  have h5171 : mixedVector B (Sum.inr 5171) = Sparse.eval nodeValue5171 (mixedVector B) := by
    change mixedMoment B node5171 node5171Labels = _
    exact sound5171 B hB hF
  have h5259 : mixedVector B (Sum.inr 5259) = Sparse.eval nodeValue5259 (mixedVector B) := by
    change mixedMoment B node5259 node5259Labels = _
    exact sound5259 B hB hF
  have h5261 : mixedVector B (Sum.inr 5261) = Sparse.eval nodeValue5261 (mixedVector B) := by
    change mixedMoment B node5261 node5261Labels = _
    exact sound5261 B hB hF
  have h5293 : mixedVector B (Sum.inr 5293) = Sparse.eval nodeValue5293 (mixedVector B) := by
    change mixedMoment B node5293 node5293Labels = _
    exact sound5293 B hB hF
  have h5483 : mixedVector B (Sum.inr 5483) = Sparse.eval nodeValue5483 (mixedVector B) := by
    change mixedMoment B node5483 node5483Labels = _
    exact sound5483_e B hB hF
  simpa only [sourceForm2036, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4287, h4289, h4295, h4303, h4322, h4325, h4346, h4401, h4460, h4902, h4907, h4913, h4927, h4943, h4986, h5000, h5033, h5047, h5073, h5075, h5081, h5102, h5137, h5141, h5169, h5171, h5259, h5261, h5293, h5483, reducedSource1715] using sourceEq2036 B hB

theorem rowSound1715_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1715 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1715, numericCheck1715, reducedZero1715 B hB hF, mul_zero]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedSourceBridge.rowSound1715_e_oai := @OAI.MUB6.Certificate.MixedSourceBridge.rowSound1715_e_oai
