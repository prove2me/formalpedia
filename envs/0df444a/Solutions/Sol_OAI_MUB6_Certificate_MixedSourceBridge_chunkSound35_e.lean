-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedSourceBridge.chunkSound35_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T04:27:10.298369+00:00
-- url     : https://prove2.me/submissions/5c9f19db-b4b2-498c-8417-2591dcabaea9

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E077
import Definitions.Def_OAIQ106E086
import Definitions.Def_OAIQ106E087
import Definitions.Def_OAIQ106E088
import Definitions.Def_OAIQ106E103
import Definitions.Def_OAIQ106E115
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
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound2766_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound564_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound565_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound566_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound567_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound568_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound570_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound571_e

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Moments_Orthogonality
attribute [-simp] _root_.OAI.MUB6.embedCharge_apply _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero _root_.OAI.MUB6.offDiagSum_zero _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators ComplexConjugate

namespace MUB6

/-- The finite orthogonality contraction underlying equation (same-matrix). -/
theorem weighted_contraction {H : CMatrix} (hH : IsHadamard H)
    (u v : Coord → ℂ) (i : Coord) :
    (∑ j, (∑ k, u k * H i k * conj (H j k)) *
      (∑ l, v l * conj (H i l) * H j l)) =
      6 * ∑ k, u k * v k := by
  have hexpand :
      (∑ j, (∑ k, u k * H i k * conj (H j k)) *
        (∑ l, v l * conj (H i l) * H j l)) =
      ∑ l, ∑ k, (u k * v l * H i k * conj (H i l)) *
        (∑ j, conj (H j k) * H j l) := by
    simp only [Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro l _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro k _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hexpand]
  simp_rw [hH.column_orthogonal]
  have hunit (k : Coord) : H i k * conj (H i k) = 1 := by
    rw [Complex.mul_conj, hH.1]
    norm_num
  simp only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true, if_true]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  calc
    u k * v k * H i k * conj (H i k) * 6 =
      6 * (u k * v k) * (H i k * conj (H i k)) := by ring
    _ = _ := by rw [hunit, mul_one]

theorem g_add_difference {H : CMatrix} (hH : IsHadamard H)
    (a : Charge) (i j : Coord) :
    g H (a + difference i j) = (6 : ℂ)⁻¹ *
      ∑ k, character (fun r => H r k) a * H i k * conj (H j k) := by
  simp only [g]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  rw [character_add _ (fun r => unit_ne_zero (hH.1 r k)),
    character_difference _ (fun r => hH.1 r k)]
  ring

/-- Source Lemma (basic), equation (same-matrix), for arbitrary integral charges. -/
theorem same_matrix_identity {H : CMatrix} (hH : IsHadamard H)
    (a b : Charge) (i : Coord) :
    ∑ j, g H (a + difference i j) * g H (b + difference j i) = g H (a + b) := by
  simp_rw [g_add_difference hH]
  have hexpand :
      (∑ j, ((6 : ℂ)⁻¹ * ∑ k, character (fun r => H r k) a * H i k * conj (H j k)) *
        ((6 : ℂ)⁻¹ * ∑ l, character (fun r => H r l) b * H j l * conj (H i l))) =
      (6 : ℂ)⁻¹ * (6 : ℂ)⁻¹ *
        (∑ j, (∑ k, character (fun r => H r k) a * H i k * conj (H j k)) *
          (∑ l, character (fun r => H r l) b * conj (H i l) * H j l)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    have he : (∑ l, character (fun r => H r l) b * H j l * conj (H i l)) =
        ∑ l, character (fun r => H r l) b * conj (H i l) * H j l := by
      apply Finset.sum_congr rfl
      intro l _
      ring
    rw [he]
    ring
  rw [hexpand, weighted_contraction hH]
  unfold g
  have hs : (∑ k, character (fun r => H r k) a * character (fun r => H r k) b) =
      ∑ k, character (fun r => H r k) (a + b) := by
    apply Finset.sum_congr rfl
    intro k _
    exact (character_add _ (fun r => unit_ne_zero (hH.1 r k)) a b).symm
  rw [hs]
  ring

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

theorem mixedIntegrand_two {l : ℕ} (B : Fin 7 → Basis) (a b : Charge)
    (s t : Fin l) (r : Fin 7) (ρ : Coord ↪ Coord) (τ : Fin l ↪ Coord) :
    mixedIntegrand B (doubleCharges a b) ![s, t] r ρ τ =
      g (sampledMatrix B r ρ (τ s)) a * g (sampledMatrix B r ρ (τ t)) b := by
  simp [mixedIntegrand, doubleCharges, Fin.prod_univ_succ, rowFourier, g, character, sampledMatrix]

theorem mixedMoment_same {l : ℕ} (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (a b c : Charge) (s u : Fin l) (i : Coord) :
    (∑ j, mixedMoment B (tripleCharges (a + difference i j) (b + difference j i) c) ![s, s, u]) =
      mixedMoment B (doubleCharges (a + b) c) ![s, u] := by
  simp only [mixedMoment, ← average_sum]
  apply average_congr
  intro r
  apply average_congr
  intro ρ
  apply average_congr
  intro τ
  simp only [mixedIntegrand_three, mixedIntegrand_two, ← Complex.re_sum, ← Finset.sum_mul]
  rw [same_matrix_identity (sampledMatrix_isHadamard B hB r ρ _) a b i]

theorem mixedMoment_same_reversed {l : ℕ} (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (a b c : Charge) (s u : Fin l) (i : Coord) :
    (∑ j, mixedMoment B (tripleCharges (a + difference j i) (b + difference i j) c) ![s, s, u]) =
      mixedMoment B (doubleCharges (a + b) c) ![s, u] := by
  simp only [mixedMoment, ← average_sum]
  apply average_congr
  intro r
  apply average_congr
  intro ρ
  apply average_congr
  intro τ
  simp only [mixedIntegrand_three, mixedIntegrand_two, ← Complex.re_sum, ← Finset.sum_mul]
  have h := same_matrix_identity (sampledMatrix_isHadamard B hB r ρ (τ s)) b a i
  simpa only [mul_comm, add_comm] using congrArg
    (fun z => (z * g (sampledMatrix B r ρ (τ u)) c).re) h

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical44
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical5754 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5754 raw5754Labels = mixedMoment B node4084 node4084Labels := by
  calc
    mixedMoment B raw5754 raw5754Labels = mixedMoment B raw5754step0 raw5754step0Labels := by
      have hz : ∀ j, raw5754 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5754step0 = (fun i j => raw5754 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5754step0 raw5754; decide +kernel
      have hl : raw5754step0Labels = raw5754Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5754 raw5754Labels permutation434 hz
    mixedMoment B raw5754step0 raw5754step0Labels = mixedMoment B raw5754step1 raw5754step1Labels := by
      have hz : ∀ j, raw5754step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5754step1 = (fun i j => raw5754step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5754step1 raw5754step0; decide +kernel
      have hl : raw5754step1Labels = raw5754step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5754step0 raw5754step0Labels permutation80 hz
    mixedMoment B raw5754step1 raw5754step1Labels = mixedMoment B raw5754step2 raw5754step2Labels := by
      have hz : ∀ j, raw5754step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw5754step2 = (fun i j => raw5754step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw5754step2 raw5754step1; decide +kernel
      have hl : raw5754step2Labels = raw5754step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5754step1 raw5754step1Labels permutation14 hz
    mixedMoment B raw5754step2 raw5754step2Labels = mixedMoment B raw5754step3 raw5754step3Labels := by
      have ha : raw5754step3 = -raw5754step2 := by apply Matrix.ext; change ∀ i j, raw5754step3 i j = -(raw5754step2 i j); unfold raw5754step3 raw5754step2; decide +kernel
      have hl : raw5754step3Labels = raw5754step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4084 node4084Labels := by rfl

theorem canonical5758 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5758 raw5758Labels = mixedMoment B node1056 node1056Labels := by
  calc
    mixedMoment B raw5758 raw5758Labels = mixedMoment B raw5758step0 raw5758step0Labels := by
      have ha : raw5758step0 = (fun i j => raw5758 (permutation246 i) (permutation4 j)) := by apply Matrix.ext; unfold raw5758step0 raw5758; decide +kernel
      have hl : raw5758step0Labels = raw5758Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5758 raw5758Labels permutation246 permutation4
    mixedMoment B raw5758step0 raw5758step0Labels = mixedMoment B raw5758step1 raw5758step1Labels := by
      have ha : raw5758step1 = -raw5758step0 := by apply Matrix.ext; change ∀ i j, raw5758step1 i j = -(raw5758step0 i j); unfold raw5758step1 raw5758step0; decide +kernel
      have hl : raw5758step1Labels = raw5758step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1056 node1056Labels := by rfl

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

theorem canonical5762 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5762 raw5762Labels = mixedMoment B node2277 node2277Labels := by
  calc
    mixedMoment B raw5762 raw5762Labels = mixedMoment B raw5762step0 raw5762step0Labels := by
      have hz : ∀ j, raw5762 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5762step0 = (fun i j => raw5762 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5762step0 raw5762; decide +kernel
      have hl : raw5762step0Labels = raw5762Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5762 raw5762Labels permutation434 hz
    mixedMoment B raw5762step0 raw5762step0Labels = mixedMoment B raw5762step1 raw5762step1Labels := by
      have ha : raw5762step1 = (fun i j => raw5762step0 (permutation50 i) (permutation4 j)) := by apply Matrix.ext; unfold raw5762step1 raw5762step0; decide +kernel
      have hl : raw5762step1Labels = raw5762step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5762step0 raw5762step0Labels permutation50 permutation4
    mixedMoment B raw5762step1 raw5762step1Labels = mixedMoment B raw5762step2 raw5762step2Labels := by
      have ha : raw5762step2 = -raw5762step1 := by apply Matrix.ext; change ∀ i j, raw5762step2 i j = -(raw5762step1 i j); unfold raw5762step2 raw5762step1; decide +kernel
      have hl : raw5762step2Labels = raw5762step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2277 node2277Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical86
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical11080 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11080 raw11080Labels = mixedMoment B node2245 node2245Labels := by
  calc
    mixedMoment B raw11080 raw11080Labels = mixedMoment B raw11080step0 raw11080step0Labels := by
      have hz : ∀ j, raw11080 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11080step0 = (fun i j => raw11080 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11080step0 raw11080; decide +kernel
      have hl : raw11080step0Labels = raw11080Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11080 raw11080Labels permutation434 hz
    _ = mixedMoment B node2245 node2245Labels := by rfl

theorem canonical11081 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11081 raw11081Labels = mixedMoment B node3573 node3573Labels := by
  calc
    mixedMoment B raw11081 raw11081Labels = mixedMoment B raw11081step0 raw11081step0Labels := by
      have hz : ∀ j, raw11081 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11081step0 = (fun i j => raw11081 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11081step0 raw11081; decide +kernel
      have hl : raw11081step0Labels = raw11081Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11081 raw11081Labels permutation434 hz
    _ = mixedMoment B node3573 node3573Labels := by rfl

theorem canonical11083 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11083 raw11083Labels = mixedMoment B node3526 node3526Labels := by
  calc
    mixedMoment B raw11083 raw11083Labels = mixedMoment B raw11083step0 raw11083step0Labels := by
      have ha : raw11083step0 = (fun i j => raw11083 (permutation200 i) (permutation2 j)) := by apply Matrix.ext; unfold raw11083step0 raw11083; decide +kernel
      have hl : raw11083step0Labels = raw11083Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11083 raw11083Labels permutation200 permutation2
    _ = mixedMoment B node3526 node3526Labels := by rfl

theorem canonical11086 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11086 raw11086Labels = mixedMoment B node4083 node4083Labels := by
  calc
    mixedMoment B raw11086 raw11086Labels = mixedMoment B raw11086step0 raw11086step0Labels := by
      have hz : ∀ j, raw11086 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw11086step0 = (fun i j => raw11086 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw11086step0 raw11086; decide +kernel
      have hl : raw11086step0Labels = raw11086Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11086 raw11086Labels permutation590 hz
    mixedMoment B raw11086step0 raw11086step0Labels = mixedMoment B raw11086step1 raw11086step1Labels := by
      have hz : ∀ j, raw11086step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw11086step1 = (fun i j => raw11086step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw11086step1 raw11086step0; decide +kernel
      have hl : raw11086step1Labels = raw11086step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11086step0 raw11086step0Labels permutation104 hz
    _ = mixedMoment B node4083 node4083Labels := by rfl

theorem canonical11087 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11087 raw11087Labels = mixedMoment B node1044 node1044Labels := by
  calc
    mixedMoment B raw11087 raw11087Labels = mixedMoment B raw11087step0 raw11087step0Labels := by
      have hz : ∀ j, raw11087 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11087step0 = (fun i j => raw11087 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11087step0 raw11087; decide +kernel
      have hl : raw11087step0Labels = raw11087Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11087 raw11087Labels permutation434 hz
    mixedMoment B raw11087step0 raw11087step0Labels = mixedMoment B raw11087step1 raw11087step1Labels := by
      have ha : raw11087step1 = (fun i j => raw11087step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw11087step1 raw11087step0; decide +kernel
      have hl : raw11087step1Labels = raw11087step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11087step0 raw11087step0Labels permutation38 permutation2
    _ = mixedMoment B node1044 node1044Labels := by rfl

theorem canonical11088 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11088 raw11088Labels = mixedMoment B node2110 node2110Labels := by
  calc
    mixedMoment B raw11088 raw11088Labels = mixedMoment B raw11088step0 raw11088step0Labels := by
      have hz : ∀ j, raw11088 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11088step0 = (fun i j => raw11088 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11088step0 raw11088; decide +kernel
      have hl : raw11088step0Labels = raw11088Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11088 raw11088Labels permutation434 hz
    mixedMoment B raw11088step0 raw11088step0Labels = mixedMoment B raw11088step1 raw11088step1Labels := by
      have ha : raw11088step1 = (fun i j => raw11088step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw11088step1 raw11088step0; decide +kernel
      have hl : raw11088step1Labels = raw11088step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11088step0 raw11088step0Labels permutation38 permutation2
    _ = mixedMoment B node2110 node2110Labels := by rfl

theorem canonical11089 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11089 raw11089Labels = mixedMoment B node2023 node2023Labels := by
  calc
    mixedMoment B raw11089 raw11089Labels = mixedMoment B raw11089step0 raw11089step0Labels := by
      have ha : raw11089step0 = (fun i j => raw11089 (permutation206 i) (permutation2 j)) := by apply Matrix.ext; unfold raw11089step0 raw11089; decide +kernel
      have hl : raw11089step0Labels = raw11089Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11089 raw11089Labels permutation206 permutation2
    _ = mixedMoment B node2023 node2023Labels := by rfl

theorem canonical11090 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11090 raw11090Labels = mixedMoment B node2245 node2245Labels := by
  calc
    mixedMoment B raw11090 raw11090Labels = mixedMoment B raw11090step0 raw11090step0Labels := by
      have hz : ∀ j, raw11090 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11090step0 = (fun i j => raw11090 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11090step0 raw11090; decide +kernel
      have hl : raw11090step0Labels = raw11090Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11090 raw11090Labels permutation434 hz
    mixedMoment B raw11090step0 raw11090step0Labels = mixedMoment B raw11090step1 raw11090step1Labels := by
      have ha : raw11090step1 = (fun i j => raw11090step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw11090step1 raw11090step0; decide +kernel
      have hl : raw11090step1Labels = raw11090step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11090step0 raw11090step0Labels permutation40 permutation2
    _ = mixedMoment B node2245 node2245Labels := by rfl

theorem canonical11091 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11091 raw11091Labels = mixedMoment B node2263 node2263Labels := by
  calc
    mixedMoment B raw11091 raw11091Labels = mixedMoment B raw11091step0 raw11091step0Labels := by
      have hz : ∀ j, raw11091 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11091step0 = (fun i j => raw11091 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11091step0 raw11091; decide +kernel
      have hl : raw11091step0Labels = raw11091Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11091 raw11091Labels permutation434 hz
    mixedMoment B raw11091step0 raw11091step0Labels = mixedMoment B raw11091step1 raw11091step1Labels := by
      have ha : raw11091step1 = (fun i j => raw11091step0 (permutation42 i) (permutation2 j)) := by apply Matrix.ext; unfold raw11091step1 raw11091step0; decide +kernel
      have hl : raw11091step1Labels = raw11091step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11091step0 raw11091step0Labels permutation42 permutation2
    _ = mixedMoment B node2263 node2263Labels := by rfl

theorem canonical11092 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11092 raw11092Labels = mixedMoment B node2110 node2110Labels := by
  calc
    mixedMoment B raw11092 raw11092Labels = mixedMoment B raw11092step0 raw11092step0Labels := by
      have hz : ∀ j, raw11092 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11092step0 = (fun i j => raw11092 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11092step0 raw11092; decide +kernel
      have hl : raw11092step0Labels = raw11092Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11092 raw11092Labels permutation434 hz
    _ = mixedMoment B node2110 node2110Labels := by rfl

theorem canonical11093 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11093 raw11093Labels = mixedMoment B node2089 node2089Labels := by
  calc
    _ = mixedMoment B node2089 node2089Labels := by rfl

theorem canonical11094 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11094 raw11094Labels = mixedMoment B node2094 node2094Labels := by
  calc
    mixedMoment B raw11094 raw11094Labels = mixedMoment B raw11094step0 raw11094step0Labels := by
      have hz : ∀ j, raw11094 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11094step0 = (fun i j => raw11094 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11094step0 raw11094; decide +kernel
      have hl : raw11094step0Labels = raw11094Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11094 raw11094Labels permutation434 hz
    mixedMoment B raw11094step0 raw11094step0Labels = mixedMoment B raw11094step1 raw11094step1Labels := by
      have ha : raw11094step1 = (fun i j => raw11094step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw11094step1 raw11094step0; decide +kernel
      have hl : raw11094step1Labels = raw11094step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11094step0 raw11094step0Labels permutation33 permutation2
    _ = mixedMoment B node2094 node2094Labels := by rfl

theorem canonical11095 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11095 raw11095Labels = mixedMoment B node2092 node2092Labels := by
  calc
    mixedMoment B raw11095 raw11095Labels = mixedMoment B raw11095step0 raw11095step0Labels := by
      have hz : ∀ j, raw11095 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11095step0 = (fun i j => raw11095 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11095step0 raw11095; decide +kernel
      have hl : raw11095step0Labels = raw11095Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11095 raw11095Labels permutation434 hz
    _ = mixedMoment B node2092 node2092Labels := by rfl

theorem canonical11096 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11096 raw11096Labels = mixedMoment B node2023 node2023Labels := by
  calc
    mixedMoment B raw11096 raw11096Labels = mixedMoment B raw11096step0 raw11096step0Labels := by
      have ha : raw11096step0 = (fun i j => raw11096 (permutation200 i) (permutation2 j)) := by apply Matrix.ext; unfold raw11096step0 raw11096; decide +kernel
      have hl : raw11096step0Labels = raw11096Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11096 raw11096Labels permutation200 permutation2
    _ = mixedMoment B node2023 node2023Labels := by rfl

theorem canonical11097 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11097 raw11097Labels = mixedMoment B node2012 node2012Labels := by
  calc
    mixedMoment B raw11097 raw11097Labels = mixedMoment B raw11097step0 raw11097step0Labels := by
      have ha : raw11097step0 = (fun i j => raw11097 (permutation201 i) (permutation2 j)) := by apply Matrix.ext; unfold raw11097step0 raw11097; decide +kernel
      have hl : raw11097step0Labels = raw11097Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11097 raw11097Labels permutation201 permutation2
    _ = mixedMoment B node2012 node2012Labels := by rfl

theorem canonical11098 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11098 raw11098Labels = mixedMoment B node2010 node2010Labels := by
  calc
    mixedMoment B raw11098 raw11098Labels = mixedMoment B raw11098step0 raw11098step0Labels := by
      have ha : raw11098step0 = (fun i j => raw11098 (permutation200 i) (permutation2 j)) := by apply Matrix.ext; unfold raw11098step0 raw11098; decide +kernel
      have hl : raw11098step0Labels = raw11098Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11098 raw11098Labels permutation200 permutation2
    _ = mixedMoment B node2010 node2010Labels := by rfl

theorem canonical11099 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11099 raw11099Labels = mixedMoment B node1026 node1026Labels := by
  calc
    mixedMoment B raw11099 raw11099Labels = mixedMoment B raw11099step0 raw11099step0Labels := by
      have hz : ∀ j, raw11099 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11099step0 = (fun i j => raw11099 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11099step0 raw11099; decide +kernel
      have hl : raw11099step0Labels = raw11099Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11099 raw11099Labels permutation434 hz
    mixedMoment B raw11099step0 raw11099step0Labels = mixedMoment B raw11099step1 raw11099step1Labels := by
      have ha : raw11099step1 = (fun i j => raw11099step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw11099step1 raw11099step0; decide +kernel
      have hl : raw11099step1Labels = raw11099step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11099step0 raw11099step0Labels permutation33 permutation2
    _ = mixedMoment B node1026 node1026Labels := by rfl

theorem canonical11100 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11100 raw11100Labels = mixedMoment B node2094 node2094Labels := by
  calc
    mixedMoment B raw11100 raw11100Labels = mixedMoment B raw11100step0 raw11100step0Labels := by
      have hz : ∀ j, raw11100 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11100step0 = (fun i j => raw11100 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11100step0 raw11100; decide +kernel
      have hl : raw11100step0Labels = raw11100Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11100 raw11100Labels permutation434 hz
    mixedMoment B raw11100step0 raw11100step0Labels = mixedMoment B raw11100step1 raw11100step1Labels := by
      have ha : raw11100step1 = (fun i j => raw11100step0 (permutation39 i) (permutation2 j)) := by apply Matrix.ext; unfold raw11100step1 raw11100step0; decide +kernel
      have hl : raw11100step1Labels = raw11100step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11100step0 raw11100step0Labels permutation39 permutation2
    _ = mixedMoment B node2094 node2094Labels := by rfl

theorem canonical11101 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11101 raw11101Labels = mixedMoment B node2244 node2244Labels := by
  calc
    mixedMoment B raw11101 raw11101Labels = mixedMoment B raw11101step0 raw11101step0Labels := by
      have hz : ∀ j, raw11101 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11101step0 = (fun i j => raw11101 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11101step0 raw11101; decide +kernel
      have hl : raw11101step0Labels = raw11101Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11101 raw11101Labels permutation434 hz
    mixedMoment B raw11101step0 raw11101step0Labels = mixedMoment B raw11101step1 raw11101step1Labels := by
      have ha : raw11101step1 = (fun i j => raw11101step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw11101step1 raw11101step0; decide +kernel
      have hl : raw11101step1Labels = raw11101step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11101step0 raw11101step0Labels permutation33 permutation2
    _ = mixedMoment B node2244 node2244Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical87
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical11198 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11198 raw11198Labels = mixedMoment B node1058 node1058Labels := by
  calc
    mixedMoment B raw11198 raw11198Labels = mixedMoment B raw11198step0 raw11198step0Labels := by
      have hz : ∀ j, raw11198 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11198step0 = (fun i j => raw11198 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11198step0 raw11198; decide +kernel
      have hl : raw11198step0Labels = raw11198Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11198 raw11198Labels permutation434 hz
    mixedMoment B raw11198step0 raw11198step0Labels = mixedMoment B raw11198step1 raw11198step1Labels := by
      have ha : raw11198step1 = (fun i j => raw11198step0 (permutation53 i) (permutation4 j)) := by apply Matrix.ext; unfold raw11198step1 raw11198step0; decide +kernel
      have hl : raw11198step1Labels = raw11198step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11198step0 raw11198step0Labels permutation53 permutation4
    mixedMoment B raw11198step1 raw11198step1Labels = mixedMoment B raw11198step2 raw11198step2Labels := by
      have ha : raw11198step2 = -raw11198step1 := by apply Matrix.ext; change ∀ i j, raw11198step2 i j = -(raw11198step1 i j); unfold raw11198step2 raw11198step1; decide +kernel
      have hl : raw11198step2Labels = raw11198step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1058 node1058Labels := by rfl

theorem canonical11199 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11199 raw11199Labels = mixedMoment B node1058 node1058Labels := by
  calc
    mixedMoment B raw11199 raw11199Labels = mixedMoment B raw11199step0 raw11199step0Labels := by
      have hz : ∀ j, raw11199 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11199step0 = (fun i j => raw11199 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11199step0 raw11199; decide +kernel
      have hl : raw11199step0Labels = raw11199Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11199 raw11199Labels permutation434 hz
    mixedMoment B raw11199step0 raw11199step0Labels = mixedMoment B raw11199step1 raw11199step1Labels := by
      have ha : raw11199step1 = (fun i j => raw11199step0 (permutation51 i) (permutation4 j)) := by apply Matrix.ext; unfold raw11199step1 raw11199step0; decide +kernel
      have hl : raw11199step1Labels = raw11199step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11199step0 raw11199step0Labels permutation51 permutation4
    mixedMoment B raw11199step1 raw11199step1Labels = mixedMoment B raw11199step2 raw11199step2Labels := by
      have ha : raw11199step2 = -raw11199step1 := by apply Matrix.ext; change ∀ i j, raw11199step2 i j = -(raw11199step1 i j); unfold raw11199step2 raw11199step1; decide +kernel
      have hl : raw11199step2Labels = raw11199step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1058 node1058Labels := by rfl

theorem canonical11200 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11200 raw11200Labels = mixedMoment B node1057 node1057Labels := by
  calc
    mixedMoment B raw11200 raw11200Labels = mixedMoment B raw11200step0 raw11200step0Labels := by
      have hz : ∀ j, raw11200 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11200step0 = (fun i j => raw11200 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11200step0 raw11200; decide +kernel
      have hl : raw11200step0Labels = raw11200Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11200 raw11200Labels permutation434 hz
    mixedMoment B raw11200step0 raw11200step0Labels = mixedMoment B raw11200step1 raw11200step1Labels := by
      have ha : raw11200step1 = (fun i j => raw11200step0 (permutation50 i) (permutation4 j)) := by apply Matrix.ext; unfold raw11200step1 raw11200step0; decide +kernel
      have hl : raw11200step1Labels = raw11200step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11200step0 raw11200step0Labels permutation50 permutation4
    mixedMoment B raw11200step1 raw11200step1Labels = mixedMoment B raw11200step2 raw11200step2Labels := by
      have ha : raw11200step2 = -raw11200step1 := by apply Matrix.ext; change ∀ i j, raw11200step2 i j = -(raw11200step1 i j); unfold raw11200step2 raw11200step1; decide +kernel
      have hl : raw11200step2Labels = raw11200step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1057 node1057Labels := by rfl

theorem canonical11201 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11201 raw11201Labels = mixedMoment B node1079 node1079Labels := by
  calc
    mixedMoment B raw11201 raw11201Labels = mixedMoment B raw11201step0 raw11201step0Labels := by
      have hz : ∀ j, raw11201 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11201step0 = (fun i j => raw11201 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11201step0 raw11201; decide +kernel
      have hl : raw11201step0Labels = raw11201Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11201 raw11201Labels permutation434 hz
    mixedMoment B raw11201step0 raw11201step0Labels = mixedMoment B raw11201step1 raw11201step1Labels := by
      have ha : raw11201step1 = (fun i j => raw11201step0 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw11201step1 raw11201step0; decide +kernel
      have hl : raw11201step1Labels = raw11201step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11201step0 raw11201step0Labels permutation32 permutation4
    mixedMoment B raw11201step1 raw11201step1Labels = mixedMoment B raw11201step2 raw11201step2Labels := by
      have ha : raw11201step2 = -raw11201step1 := by apply Matrix.ext; change ∀ i j, raw11201step2 i j = -(raw11201step1 i j); unfold raw11201step2 raw11201step1; decide +kernel
      have hl : raw11201step2Labels = raw11201step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1079 node1079Labels := by rfl

theorem canonical11262 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11262 raw11262Labels = mixedMoment B node2763 node2763Labels := by
  calc
    mixedMoment B raw11262 raw11262Labels = mixedMoment B raw11262step0 raw11262step0Labels := by
      have hz : ∀ j, raw11262 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11262step0 = (fun i j => raw11262 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11262step0 raw11262; decide +kernel
      have hl : raw11262step0Labels = raw11262Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11262 raw11262Labels permutation434 hz
    mixedMoment B raw11262step0 raw11262step0Labels = mixedMoment B raw11262step1 raw11262step1Labels := by
      have ha : raw11262step1 = (fun i j => raw11262step0 (permutation44 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11262step1 raw11262step0; decide +kernel
      have hl : raw11262step1Labels = raw11262step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11262step0 raw11262step0Labels permutation44 permutation7
    mixedMoment B raw11262step1 raw11262step1Labels = mixedMoment B raw11262step2 raw11262step2Labels := by
      have ha : raw11262step2 = -raw11262step1 := by apply Matrix.ext; change ∀ i j, raw11262step2 i j = -(raw11262step1 i j); unfold raw11262step2 raw11262step1; decide +kernel
      have hl : raw11262step2Labels = raw11262step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11262step2 raw11262step2Labels = mixedMoment B raw11262step3 raw11262step3Labels := by
      have ha : raw11262step3 = raw11262step2 := by apply Matrix.ext; unfold raw11262step3 raw11262step2; decide +kernel
      have hl : raw11262step2Labels = labelEmbedding1 ∘ raw11262step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11262step2 raw11262step2Labels raw11262step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2763 node2763Labels := by rfl

theorem canonical11263 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11263 raw11263Labels = mixedMoment B node2763 node2763Labels := by
  calc
    mixedMoment B raw11263 raw11263Labels = mixedMoment B raw11263step0 raw11263step0Labels := by
      have hz : ∀ j, raw11263 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11263step0 = (fun i j => raw11263 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11263step0 raw11263; decide +kernel
      have hl : raw11263step0Labels = raw11263Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11263 raw11263Labels permutation434 hz
    mixedMoment B raw11263step0 raw11263step0Labels = mixedMoment B raw11263step1 raw11263step1Labels := by
      have ha : raw11263step1 = (fun i j => raw11263step0 (permutation46 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11263step1 raw11263step0; decide +kernel
      have hl : raw11263step1Labels = raw11263step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11263step0 raw11263step0Labels permutation46 permutation7
    mixedMoment B raw11263step1 raw11263step1Labels = mixedMoment B raw11263step2 raw11263step2Labels := by
      have ha : raw11263step2 = -raw11263step1 := by apply Matrix.ext; change ∀ i j, raw11263step2 i j = -(raw11263step1 i j); unfold raw11263step2 raw11263step1; decide +kernel
      have hl : raw11263step2Labels = raw11263step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11263step2 raw11263step2Labels = mixedMoment B raw11263step3 raw11263step3Labels := by
      have ha : raw11263step3 = raw11263step2 := by apply Matrix.ext; unfold raw11263step3 raw11263step2; decide +kernel
      have hl : raw11263step2Labels = labelEmbedding1 ∘ raw11263step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11263step2 raw11263step2Labels raw11263step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2763 node2763Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical88
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical11264 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11264 raw11264Labels = mixedMoment B node2720 node2720Labels := by
  calc
    mixedMoment B raw11264 raw11264Labels = mixedMoment B raw11264step0 raw11264step0Labels := by
      have ha : raw11264step0 = (fun i j => raw11264 (permutation212 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11264step0 raw11264; decide +kernel
      have hl : raw11264step0Labels = raw11264Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11264 raw11264Labels permutation212 permutation7
    mixedMoment B raw11264step0 raw11264step0Labels = mixedMoment B raw11264step1 raw11264step1Labels := by
      have ha : raw11264step1 = -raw11264step0 := by apply Matrix.ext; change ∀ i j, raw11264step1 i j = -(raw11264step0 i j); unfold raw11264step1 raw11264step0; decide +kernel
      have hl : raw11264step1Labels = raw11264step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11264step1 raw11264step1Labels = mixedMoment B raw11264step2 raw11264step2Labels := by
      have ha : raw11264step2 = raw11264step1 := by apply Matrix.ext; unfold raw11264step2 raw11264step1; decide +kernel
      have hl : raw11264step1Labels = labelEmbedding1 ∘ raw11264step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11264step1 raw11264step1Labels raw11264step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2720 node2720Labels := by rfl

theorem canonical11265 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11265 raw11265Labels = mixedMoment B node2784 node2784Labels := by
  calc
    mixedMoment B raw11265 raw11265Labels = mixedMoment B raw11265step0 raw11265step0Labels := by
      have hz : ∀ j, raw11265 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw11265step0 = (fun i j => raw11265 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw11265step0 raw11265; decide +kernel
      have hl : raw11265step0Labels = raw11265Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11265 raw11265Labels permutation520 hz
    mixedMoment B raw11265step0 raw11265step0Labels = mixedMoment B raw11265step1 raw11265step1Labels := by
      have hz : ∀ j, raw11265step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw11265step1 = (fun i j => raw11265step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw11265step1 raw11265step0; decide +kernel
      have hl : raw11265step1Labels = raw11265step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11265step0 raw11265step0Labels permutation104 hz
    mixedMoment B raw11265step1 raw11265step1Labels = mixedMoment B raw11265step2 raw11265step2Labels := by
      have ha : raw11265step2 = (fun i j => raw11265step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11265step2 raw11265step1; decide +kernel
      have hl : raw11265step2Labels = raw11265step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11265step1 raw11265step1Labels permutation8 permutation7
    mixedMoment B raw11265step2 raw11265step2Labels = mixedMoment B raw11265step3 raw11265step3Labels := by
      have ha : raw11265step3 = -raw11265step2 := by apply Matrix.ext; change ∀ i j, raw11265step3 i j = -(raw11265step2 i j); unfold raw11265step3 raw11265step2; decide +kernel
      have hl : raw11265step3Labels = raw11265step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11265step3 raw11265step3Labels = mixedMoment B raw11265step4 raw11265step4Labels := by
      have ha : raw11265step4 = raw11265step3 := by apply Matrix.ext; unfold raw11265step4 raw11265step3; decide +kernel
      have hl : raw11265step3Labels = labelEmbedding1 ∘ raw11265step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11265step3 raw11265step3Labels raw11265step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2784 node2784Labels := by rfl

theorem canonical11266 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11266 raw11266Labels = mixedMoment B node2766 node2766Labels := by
  calc
    mixedMoment B raw11266 raw11266Labels = mixedMoment B raw11266step0 raw11266step0Labels := by
      have hz : ∀ j, raw11266 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11266step0 = (fun i j => raw11266 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11266step0 raw11266; decide +kernel
      have hl : raw11266step0Labels = raw11266Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11266 raw11266Labels permutation434 hz
    mixedMoment B raw11266step0 raw11266step0Labels = mixedMoment B raw11266step1 raw11266step1Labels := by
      have ha : raw11266step1 = (fun i j => raw11266step0 (permutation44 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11266step1 raw11266step0; decide +kernel
      have hl : raw11266step1Labels = raw11266step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11266step0 raw11266step0Labels permutation44 permutation7
    mixedMoment B raw11266step1 raw11266step1Labels = mixedMoment B raw11266step2 raw11266step2Labels := by
      have ha : raw11266step2 = -raw11266step1 := by apply Matrix.ext; change ∀ i j, raw11266step2 i j = -(raw11266step1 i j); unfold raw11266step2 raw11266step1; decide +kernel
      have hl : raw11266step2Labels = raw11266step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11266step2 raw11266step2Labels = mixedMoment B raw11266step3 raw11266step3Labels := by
      have ha : raw11266step3 = raw11266step2 := by apply Matrix.ext; unfold raw11266step3 raw11266step2; decide +kernel
      have hl : raw11266step2Labels = labelEmbedding1 ∘ raw11266step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11266step2 raw11266step2Labels raw11266step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2766 node2766Labels := by rfl

theorem canonical11267 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11267 raw11267Labels = mixedMoment B node1724 node1724Labels := by
  calc
    mixedMoment B raw11267 raw11267Labels = mixedMoment B raw11267step0 raw11267step0Labels := by
      have hz : ∀ j, raw11267 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11267step0 = (fun i j => raw11267 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11267step0 raw11267; decide +kernel
      have hl : raw11267step0Labels = raw11267Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11267 raw11267Labels permutation434 hz
    mixedMoment B raw11267step0 raw11267step0Labels = mixedMoment B raw11267step1 raw11267step1Labels := by
      have ha : raw11267step1 = (fun i j => raw11267step0 (permutation46 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11267step1 raw11267step0; decide +kernel
      have hl : raw11267step1Labels = raw11267step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11267step0 raw11267step0Labels permutation46 permutation7
    mixedMoment B raw11267step1 raw11267step1Labels = mixedMoment B raw11267step2 raw11267step2Labels := by
      have ha : raw11267step2 = -raw11267step1 := by apply Matrix.ext; change ∀ i j, raw11267step2 i j = -(raw11267step1 i j); unfold raw11267step2 raw11267step1; decide +kernel
      have hl : raw11267step2Labels = raw11267step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11267step2 raw11267step2Labels = mixedMoment B raw11267step3 raw11267step3Labels := by
      have ha : raw11267step3 = raw11267step2 := by apply Matrix.ext; unfold raw11267step3 raw11267step2; decide +kernel
      have hl : raw11267step2Labels = labelEmbedding1 ∘ raw11267step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11267step2 raw11267step2Labels raw11267step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1724 node1724Labels := by rfl

theorem canonical11268 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11268 raw11268Labels = mixedMoment B node2260 node2260Labels := by
  calc
    mixedMoment B raw11268 raw11268Labels = mixedMoment B raw11268step0 raw11268step0Labels := by
      have hz : ∀ j, raw11268 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11268step0 = (fun i j => raw11268 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11268step0 raw11268; decide +kernel
      have hl : raw11268step0Labels = raw11268Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11268 raw11268Labels permutation434 hz
    mixedMoment B raw11268step0 raw11268step0Labels = mixedMoment B raw11268step1 raw11268step1Labels := by
      have ha : raw11268step1 = (fun i j => raw11268step0 (permutation46 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11268step1 raw11268step0; decide +kernel
      have hl : raw11268step1Labels = raw11268step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11268step0 raw11268step0Labels permutation46 permutation7
    mixedMoment B raw11268step1 raw11268step1Labels = mixedMoment B raw11268step2 raw11268step2Labels := by
      have ha : raw11268step2 = -raw11268step1 := by apply Matrix.ext; change ∀ i j, raw11268step2 i j = -(raw11268step1 i j); unfold raw11268step2 raw11268step1; decide +kernel
      have hl : raw11268step2Labels = raw11268step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11268step2 raw11268step2Labels = mixedMoment B raw11268step3 raw11268step3Labels := by
      have ha : raw11268step3 = raw11268step2 := by apply Matrix.ext; unfold raw11268step3 raw11268step2; decide +kernel
      have hl : raw11268step2Labels = labelEmbedding1 ∘ raw11268step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11268step2 raw11268step2Labels raw11268step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2260 node2260Labels := by rfl

theorem canonical11269 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11269 raw11269Labels = mixedMoment B node2202 node2202Labels := by
  calc
    mixedMoment B raw11269 raw11269Labels = mixedMoment B raw11269step0 raw11269step0Labels := by
      have ha : raw11269step0 = (fun i j => raw11269 (permutation214 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11269step0 raw11269; decide +kernel
      have hl : raw11269step0Labels = raw11269Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11269 raw11269Labels permutation214 permutation7
    mixedMoment B raw11269step0 raw11269step0Labels = mixedMoment B raw11269step1 raw11269step1Labels := by
      have ha : raw11269step1 = -raw11269step0 := by apply Matrix.ext; change ∀ i j, raw11269step1 i j = -(raw11269step0 i j); unfold raw11269step1 raw11269step0; decide +kernel
      have hl : raw11269step1Labels = raw11269step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11269step1 raw11269step1Labels = mixedMoment B raw11269step2 raw11269step2Labels := by
      have ha : raw11269step2 = raw11269step1 := by apply Matrix.ext; unfold raw11269step2 raw11269step1; decide +kernel
      have hl : raw11269step1Labels = labelEmbedding1 ∘ raw11269step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11269step1 raw11269step1Labels raw11269step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2202 node2202Labels := by rfl

theorem canonical11270 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11270 raw11270Labels = mixedMoment B node2291 node2291Labels := by
  calc
    mixedMoment B raw11270 raw11270Labels = mixedMoment B raw11270step0 raw11270step0Labels := by
      have hz : ∀ j, raw11270 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw11270step0 = (fun i j => raw11270 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw11270step0 raw11270; decide +kernel
      have hl : raw11270step0Labels = raw11270Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11270 raw11270Labels permutation520 hz
    mixedMoment B raw11270step0 raw11270step0Labels = mixedMoment B raw11270step1 raw11270step1Labels := by
      have hz : ∀ j, raw11270step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw11270step1 = (fun i j => raw11270step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw11270step1 raw11270step0; decide +kernel
      have hl : raw11270step1Labels = raw11270step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11270step0 raw11270step0Labels permutation104 hz
    mixedMoment B raw11270step1 raw11270step1Labels = mixedMoment B raw11270step2 raw11270step2Labels := by
      have ha : raw11270step2 = (fun i j => raw11270step1 (permutation10 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11270step2 raw11270step1; decide +kernel
      have hl : raw11270step2Labels = raw11270step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11270step1 raw11270step1Labels permutation10 permutation7
    mixedMoment B raw11270step2 raw11270step2Labels = mixedMoment B raw11270step3 raw11270step3Labels := by
      have ha : raw11270step3 = -raw11270step2 := by apply Matrix.ext; change ∀ i j, raw11270step3 i j = -(raw11270step2 i j); unfold raw11270step3 raw11270step2; decide +kernel
      have hl : raw11270step3Labels = raw11270step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11270step3 raw11270step3Labels = mixedMoment B raw11270step4 raw11270step4Labels := by
      have ha : raw11270step4 = raw11270step3 := by apply Matrix.ext; unfold raw11270step4 raw11270step3; decide +kernel
      have hl : raw11270step3Labels = labelEmbedding1 ∘ raw11270step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11270step3 raw11270step3Labels raw11270step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2291 node2291Labels := by rfl

theorem canonical11271 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11271 raw11271Labels = mixedMoment B node2263 node2263Labels := by
  calc
    mixedMoment B raw11271 raw11271Labels = mixedMoment B raw11271step0 raw11271step0Labels := by
      have hz : ∀ j, raw11271 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11271step0 = (fun i j => raw11271 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11271step0 raw11271; decide +kernel
      have hl : raw11271step0Labels = raw11271Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11271 raw11271Labels permutation434 hz
    mixedMoment B raw11271step0 raw11271step0Labels = mixedMoment B raw11271step1 raw11271step1Labels := by
      have ha : raw11271step1 = (fun i j => raw11271step0 (permutation46 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11271step1 raw11271step0; decide +kernel
      have hl : raw11271step1Labels = raw11271step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11271step0 raw11271step0Labels permutation46 permutation7
    mixedMoment B raw11271step1 raw11271step1Labels = mixedMoment B raw11271step2 raw11271step2Labels := by
      have ha : raw11271step2 = -raw11271step1 := by apply Matrix.ext; change ∀ i j, raw11271step2 i j = -(raw11271step1 i j); unfold raw11271step2 raw11271step1; decide +kernel
      have hl : raw11271step2Labels = raw11271step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11271step2 raw11271step2Labels = mixedMoment B raw11271step3 raw11271step3Labels := by
      have ha : raw11271step3 = raw11271step2 := by apply Matrix.ext; unfold raw11271step3 raw11271step2; decide +kernel
      have hl : raw11271step2Labels = labelEmbedding1 ∘ raw11271step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11271step2 raw11271step2Labels raw11271step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2263 node2263Labels := by rfl

theorem canonical11272 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11272 raw11272Labels = mixedMoment B node1724 node1724Labels := by
  calc
    mixedMoment B raw11272 raw11272Labels = mixedMoment B raw11272step0 raw11272step0Labels := by
      have hz : ∀ j, raw11272 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11272step0 = (fun i j => raw11272 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11272step0 raw11272; decide +kernel
      have hl : raw11272step0Labels = raw11272Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11272 raw11272Labels permutation434 hz
    mixedMoment B raw11272step0 raw11272step0Labels = mixedMoment B raw11272step1 raw11272step1Labels := by
      have ha : raw11272step1 = (fun i j => raw11272step0 (permutation44 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11272step1 raw11272step0; decide +kernel
      have hl : raw11272step1Labels = raw11272step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11272step0 raw11272step0Labels permutation44 permutation7
    mixedMoment B raw11272step1 raw11272step1Labels = mixedMoment B raw11272step2 raw11272step2Labels := by
      have ha : raw11272step2 = -raw11272step1 := by apply Matrix.ext; change ∀ i j, raw11272step2 i j = -(raw11272step1 i j); unfold raw11272step2 raw11272step1; decide +kernel
      have hl : raw11272step2Labels = raw11272step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11272step2 raw11272step2Labels = mixedMoment B raw11272step3 raw11272step3Labels := by
      have ha : raw11272step3 = raw11272step2 := by apply Matrix.ext; unfold raw11272step3 raw11272step2; decide +kernel
      have hl : raw11272step2Labels = labelEmbedding1 ∘ raw11272step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11272step2 raw11272step2Labels raw11272step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1724 node1724Labels := by rfl

theorem canonical11273 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11273 raw11273Labels = mixedMoment B node2260 node2260Labels := by
  calc
    mixedMoment B raw11273 raw11273Labels = mixedMoment B raw11273step0 raw11273step0Labels := by
      have hz : ∀ j, raw11273 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11273step0 = (fun i j => raw11273 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11273step0 raw11273; decide +kernel
      have hl : raw11273step0Labels = raw11273Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11273 raw11273Labels permutation434 hz
    mixedMoment B raw11273step0 raw11273step0Labels = mixedMoment B raw11273step1 raw11273step1Labels := by
      have ha : raw11273step1 = (fun i j => raw11273step0 (permutation44 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11273step1 raw11273step0; decide +kernel
      have hl : raw11273step1Labels = raw11273step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11273step0 raw11273step0Labels permutation44 permutation7
    mixedMoment B raw11273step1 raw11273step1Labels = mixedMoment B raw11273step2 raw11273step2Labels := by
      have ha : raw11273step2 = -raw11273step1 := by apply Matrix.ext; change ∀ i j, raw11273step2 i j = -(raw11273step1 i j); unfold raw11273step2 raw11273step1; decide +kernel
      have hl : raw11273step2Labels = raw11273step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11273step2 raw11273step2Labels = mixedMoment B raw11273step3 raw11273step3Labels := by
      have ha : raw11273step3 = raw11273step2 := by apply Matrix.ext; unfold raw11273step3 raw11273step2; decide +kernel
      have hl : raw11273step2Labels = labelEmbedding1 ∘ raw11273step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11273step2 raw11273step2Labels raw11273step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2260 node2260Labels := by rfl

theorem canonical11274 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11274 raw11274Labels = mixedMoment B node2202 node2202Labels := by
  calc
    mixedMoment B raw11274 raw11274Labels = mixedMoment B raw11274step0 raw11274step0Labels := by
      have ha : raw11274step0 = (fun i j => raw11274 (permutation212 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11274step0 raw11274; decide +kernel
      have hl : raw11274step0Labels = raw11274Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11274 raw11274Labels permutation212 permutation7
    mixedMoment B raw11274step0 raw11274step0Labels = mixedMoment B raw11274step1 raw11274step1Labels := by
      have ha : raw11274step1 = -raw11274step0 := by apply Matrix.ext; change ∀ i j, raw11274step1 i j = -(raw11274step0 i j); unfold raw11274step1 raw11274step0; decide +kernel
      have hl : raw11274step1Labels = raw11274step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11274step1 raw11274step1Labels = mixedMoment B raw11274step2 raw11274step2Labels := by
      have ha : raw11274step2 = raw11274step1 := by apply Matrix.ext; unfold raw11274step2 raw11274step1; decide +kernel
      have hl : raw11274step1Labels = labelEmbedding1 ∘ raw11274step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11274step1 raw11274step1Labels raw11274step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2202 node2202Labels := by rfl

theorem canonical11275 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11275 raw11275Labels = mixedMoment B node2291 node2291Labels := by
  calc
    mixedMoment B raw11275 raw11275Labels = mixedMoment B raw11275step0 raw11275step0Labels := by
      have hz : ∀ j, raw11275 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw11275step0 = (fun i j => raw11275 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw11275step0 raw11275; decide +kernel
      have hl : raw11275step0Labels = raw11275Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11275 raw11275Labels permutation520 hz
    mixedMoment B raw11275step0 raw11275step0Labels = mixedMoment B raw11275step1 raw11275step1Labels := by
      have hz : ∀ j, raw11275step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw11275step1 = (fun i j => raw11275step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw11275step1 raw11275step0; decide +kernel
      have hl : raw11275step1Labels = raw11275step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11275step0 raw11275step0Labels permutation104 hz
    mixedMoment B raw11275step1 raw11275step1Labels = mixedMoment B raw11275step2 raw11275step2Labels := by
      have ha : raw11275step2 = (fun i j => raw11275step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11275step2 raw11275step1; decide +kernel
      have hl : raw11275step2Labels = raw11275step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11275step1 raw11275step1Labels permutation8 permutation7
    mixedMoment B raw11275step2 raw11275step2Labels = mixedMoment B raw11275step3 raw11275step3Labels := by
      have ha : raw11275step3 = -raw11275step2 := by apply Matrix.ext; change ∀ i j, raw11275step3 i j = -(raw11275step2 i j); unfold raw11275step3 raw11275step2; decide +kernel
      have hl : raw11275step3Labels = raw11275step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11275step3 raw11275step3Labels = mixedMoment B raw11275step4 raw11275step4Labels := by
      have ha : raw11275step4 = raw11275step3 := by apply Matrix.ext; unfold raw11275step4 raw11275step3; decide +kernel
      have hl : raw11275step3Labels = labelEmbedding1 ∘ raw11275step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11275step3 raw11275step3Labels raw11275step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2291 node2291Labels := by rfl

theorem canonical11276 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11276 raw11276Labels = mixedMoment B node2263 node2263Labels := by
  calc
    mixedMoment B raw11276 raw11276Labels = mixedMoment B raw11276step0 raw11276step0Labels := by
      have hz : ∀ j, raw11276 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11276step0 = (fun i j => raw11276 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11276step0 raw11276; decide +kernel
      have hl : raw11276step0Labels = raw11276Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11276 raw11276Labels permutation434 hz
    mixedMoment B raw11276step0 raw11276step0Labels = mixedMoment B raw11276step1 raw11276step1Labels := by
      have ha : raw11276step1 = (fun i j => raw11276step0 (permutation44 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11276step1 raw11276step0; decide +kernel
      have hl : raw11276step1Labels = raw11276step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11276step0 raw11276step0Labels permutation44 permutation7
    mixedMoment B raw11276step1 raw11276step1Labels = mixedMoment B raw11276step2 raw11276step2Labels := by
      have ha : raw11276step2 = -raw11276step1 := by apply Matrix.ext; change ∀ i j, raw11276step2 i j = -(raw11276step1 i j); unfold raw11276step2 raw11276step1; decide +kernel
      have hl : raw11276step2Labels = raw11276step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11276step2 raw11276step2Labels = mixedMoment B raw11276step3 raw11276step3Labels := by
      have ha : raw11276step3 = raw11276step2 := by apply Matrix.ext; unfold raw11276step3 raw11276step2; decide +kernel
      have hl : raw11276step2Labels = labelEmbedding1 ∘ raw11276step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11276step2 raw11276step2Labels raw11276step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2263 node2263Labels := by rfl

theorem canonical11277 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11277 raw11277Labels = mixedMoment B node1705 node1705Labels := by
  calc
    mixedMoment B raw11277 raw11277Labels = mixedMoment B raw11277step0 raw11277step0Labels := by
      have ha : raw11277step0 = (fun i j => raw11277 (permutation212 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11277step0 raw11277; decide +kernel
      have hl : raw11277step0Labels = raw11277Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11277 raw11277Labels permutation212 permutation7
    mixedMoment B raw11277step0 raw11277step0Labels = mixedMoment B raw11277step1 raw11277step1Labels := by
      have ha : raw11277step1 = -raw11277step0 := by apply Matrix.ext; change ∀ i j, raw11277step1 i j = -(raw11277step0 i j); unfold raw11277step1 raw11277step0; decide +kernel
      have hl : raw11277step1Labels = raw11277step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11277step1 raw11277step1Labels = mixedMoment B raw11277step2 raw11277step2Labels := by
      have ha : raw11277step2 = raw11277step1 := by apply Matrix.ext; unfold raw11277step2 raw11277step1; decide +kernel
      have hl : raw11277step1Labels = labelEmbedding1 ∘ raw11277step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11277step1 raw11277step1Labels raw11277step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1705 node1705Labels := by rfl

theorem canonical11278 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11278 raw11278Labels = mixedMoment B node2240 node2240Labels := by
  calc
    mixedMoment B raw11278 raw11278Labels = mixedMoment B raw11278step0 raw11278step0Labels := by
      have ha : raw11278step0 = (fun i j => raw11278 (permutation212 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11278step0 raw11278; decide +kernel
      have hl : raw11278step0Labels = raw11278Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11278 raw11278Labels permutation212 permutation7
    mixedMoment B raw11278step0 raw11278step0Labels = mixedMoment B raw11278step1 raw11278step1Labels := by
      have ha : raw11278step1 = -raw11278step0 := by apply Matrix.ext; change ∀ i j, raw11278step1 i j = -(raw11278step0 i j); unfold raw11278step1 raw11278step0; decide +kernel
      have hl : raw11278step1Labels = raw11278step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11278step1 raw11278step1Labels = mixedMoment B raw11278step2 raw11278step2Labels := by
      have ha : raw11278step2 = raw11278step1 := by apply Matrix.ext; unfold raw11278step2 raw11278step1; decide +kernel
      have hl : raw11278step1Labels = labelEmbedding1 ∘ raw11278step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11278step1 raw11278step1Labels raw11278step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2240 node2240Labels := by rfl

theorem canonical11279 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11279 raw11279Labels = mixedMoment B node2240 node2240Labels := by
  calc
    mixedMoment B raw11279 raw11279Labels = mixedMoment B raw11279step0 raw11279step0Labels := by
      have ha : raw11279step0 = (fun i j => raw11279 (permutation214 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11279step0 raw11279; decide +kernel
      have hl : raw11279step0Labels = raw11279Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11279 raw11279Labels permutation214 permutation7
    mixedMoment B raw11279step0 raw11279step0Labels = mixedMoment B raw11279step1 raw11279step1Labels := by
      have ha : raw11279step1 = -raw11279step0 := by apply Matrix.ext; change ∀ i j, raw11279step1 i j = -(raw11279step0 i j); unfold raw11279step1 raw11279step0; decide +kernel
      have hl : raw11279step1Labels = raw11279step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11279step1 raw11279step1Labels = mixedMoment B raw11279step2 raw11279step2Labels := by
      have ha : raw11279step2 = raw11279step1 := by apply Matrix.ext; unfold raw11279step2 raw11279step1; decide +kernel
      have hl : raw11279step1Labels = labelEmbedding1 ∘ raw11279step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11279step1 raw11279step1Labels raw11279step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2240 node2240Labels := by rfl

theorem canonical11280 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11280 raw11280Labels = mixedMoment B node2262 node2262Labels := by
  calc
    mixedMoment B raw11280 raw11280Labels = mixedMoment B raw11280step0 raw11280step0Labels := by
      have hz : ∀ j, raw11280 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw11280step0 = (fun i j => raw11280 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw11280step0 raw11280; decide +kernel
      have hl : raw11280step0Labels = raw11280Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11280 raw11280Labels permutation520 hz
    mixedMoment B raw11280step0 raw11280step0Labels = mixedMoment B raw11280step1 raw11280step1Labels := by
      have ha : raw11280step1 = (fun i j => raw11280step0 (permutation44 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11280step1 raw11280step0; decide +kernel
      have hl : raw11280step1Labels = raw11280step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11280step0 raw11280step0Labels permutation44 permutation7
    mixedMoment B raw11280step1 raw11280step1Labels = mixedMoment B raw11280step2 raw11280step2Labels := by
      have ha : raw11280step2 = -raw11280step1 := by apply Matrix.ext; change ∀ i j, raw11280step2 i j = -(raw11280step1 i j); unfold raw11280step2 raw11280step1; decide +kernel
      have hl : raw11280step2Labels = raw11280step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11280step2 raw11280step2Labels = mixedMoment B raw11280step3 raw11280step3Labels := by
      have ha : raw11280step3 = raw11280step2 := by apply Matrix.ext; unfold raw11280step3 raw11280step2; decide +kernel
      have hl : raw11280step2Labels = labelEmbedding1 ∘ raw11280step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11280step2 raw11280step2Labels raw11280step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2262 node2262Labels := by rfl

theorem canonical11281 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11281 raw11281Labels = mixedMoment B node2243 node2243Labels := by
  calc
    mixedMoment B raw11281 raw11281Labels = mixedMoment B raw11281step0 raw11281step0Labels := by
      have ha : raw11281step0 = (fun i j => raw11281 (permutation212 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11281step0 raw11281; decide +kernel
      have hl : raw11281step0Labels = raw11281Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11281 raw11281Labels permutation212 permutation7
    mixedMoment B raw11281step0 raw11281step0Labels = mixedMoment B raw11281step1 raw11281step1Labels := by
      have ha : raw11281step1 = -raw11281step0 := by apply Matrix.ext; change ∀ i j, raw11281step1 i j = -(raw11281step0 i j); unfold raw11281step1 raw11281step0; decide +kernel
      have hl : raw11281step1Labels = raw11281step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11281step1 raw11281step1Labels = mixedMoment B raw11281step2 raw11281step2Labels := by
      have ha : raw11281step2 = raw11281step1 := by apply Matrix.ext; unfold raw11281step2 raw11281step1; decide +kernel
      have hl : raw11281step1Labels = labelEmbedding1 ∘ raw11281step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11281step1 raw11281step1Labels raw11281step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2243 node2243Labels := by rfl

theorem canonical11282 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11282 raw11282Labels = mixedMoment B node1736 node1736Labels := by
  calc
    mixedMoment B raw11282 raw11282Labels = mixedMoment B raw11282step0 raw11282step0Labels := by
      have hz : ∀ j, raw11282 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11282step0 = (fun i j => raw11282 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11282step0 raw11282; decide +kernel
      have hl : raw11282step0Labels = raw11282Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11282 raw11282Labels permutation434 hz
    mixedMoment B raw11282step0 raw11282step0Labels = mixedMoment B raw11282step1 raw11282step1Labels := by
      have ha : raw11282step1 = (fun i j => raw11282step0 (permutation44 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11282step1 raw11282step0; decide +kernel
      have hl : raw11282step1Labels = raw11282step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11282step0 raw11282step0Labels permutation44 permutation7
    mixedMoment B raw11282step1 raw11282step1Labels = mixedMoment B raw11282step2 raw11282step2Labels := by
      have ha : raw11282step2 = -raw11282step1 := by apply Matrix.ext; change ∀ i j, raw11282step2 i j = -(raw11282step1 i j); unfold raw11282step2 raw11282step1; decide +kernel
      have hl : raw11282step2Labels = raw11282step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11282step2 raw11282step2Labels = mixedMoment B raw11282step3 raw11282step3Labels := by
      have ha : raw11282step3 = raw11282step2 := by apply Matrix.ext; unfold raw11282step3 raw11282step2; decide +kernel
      have hl : raw11282step2Labels = labelEmbedding1 ∘ raw11282step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11282step2 raw11282step2Labels raw11282step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1736 node1736Labels := by rfl

theorem canonical11283 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11283 raw11283Labels = mixedMoment B node2274 node2274Labels := by
  calc
    mixedMoment B raw11283 raw11283Labels = mixedMoment B raw11283step0 raw11283step0Labels := by
      have hz : ∀ j, raw11283 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11283step0 = (fun i j => raw11283 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11283step0 raw11283; decide +kernel
      have hl : raw11283step0Labels = raw11283Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11283 raw11283Labels permutation434 hz
    mixedMoment B raw11283step0 raw11283step0Labels = mixedMoment B raw11283step1 raw11283step1Labels := by
      have ha : raw11283step1 = (fun i j => raw11283step0 (permutation44 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11283step1 raw11283step0; decide +kernel
      have hl : raw11283step1Labels = raw11283step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11283step0 raw11283step0Labels permutation44 permutation7
    mixedMoment B raw11283step1 raw11283step1Labels = mixedMoment B raw11283step2 raw11283step2Labels := by
      have ha : raw11283step2 = -raw11283step1 := by apply Matrix.ext; change ∀ i j, raw11283step2 i j = -(raw11283step1 i j); unfold raw11283step2 raw11283step1; decide +kernel
      have hl : raw11283step2Labels = raw11283step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11283step2 raw11283step2Labels = mixedMoment B raw11283step3 raw11283step3Labels := by
      have ha : raw11283step3 = raw11283step2 := by apply Matrix.ext; unfold raw11283step3 raw11283step2; decide +kernel
      have hl : raw11283step2Labels = labelEmbedding1 ∘ raw11283step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11283step2 raw11283step2Labels raw11283step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2274 node2274Labels := by rfl

theorem canonical11284 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11284 raw11284Labels = mixedMoment B node2274 node2274Labels := by
  calc
    mixedMoment B raw11284 raw11284Labels = mixedMoment B raw11284step0 raw11284step0Labels := by
      have hz : ∀ j, raw11284 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11284step0 = (fun i j => raw11284 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11284step0 raw11284; decide +kernel
      have hl : raw11284step0Labels = raw11284Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11284 raw11284Labels permutation434 hz
    mixedMoment B raw11284step0 raw11284step0Labels = mixedMoment B raw11284step1 raw11284step1Labels := by
      have ha : raw11284step1 = (fun i j => raw11284step0 (permutation46 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11284step1 raw11284step0; decide +kernel
      have hl : raw11284step1Labels = raw11284step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11284step0 raw11284step0Labels permutation46 permutation7
    mixedMoment B raw11284step1 raw11284step1Labels = mixedMoment B raw11284step2 raw11284step2Labels := by
      have ha : raw11284step2 = -raw11284step1 := by apply Matrix.ext; change ∀ i j, raw11284step2 i j = -(raw11284step1 i j); unfold raw11284step2 raw11284step1; decide +kernel
      have hl : raw11284step2Labels = raw11284step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11284step2 raw11284step2Labels = mixedMoment B raw11284step3 raw11284step3Labels := by
      have ha : raw11284step3 = raw11284step2 := by apply Matrix.ext; unfold raw11284step3 raw11284step2; decide +kernel
      have hl : raw11284step2Labels = labelEmbedding1 ∘ raw11284step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11284step2 raw11284step2Labels raw11284step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2274 node2274Labels := by rfl

theorem canonical11285 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11285 raw11285Labels = mixedMoment B node2213 node2213Labels := by
  calc
    mixedMoment B raw11285 raw11285Labels = mixedMoment B raw11285step0 raw11285step0Labels := by
      have ha : raw11285step0 = (fun i j => raw11285 (permutation212 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11285step0 raw11285; decide +kernel
      have hl : raw11285step0Labels = raw11285Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11285 raw11285Labels permutation212 permutation7
    mixedMoment B raw11285step0 raw11285step0Labels = mixedMoment B raw11285step1 raw11285step1Labels := by
      have ha : raw11285step1 = -raw11285step0 := by apply Matrix.ext; change ∀ i j, raw11285step1 i j = -(raw11285step0 i j); unfold raw11285step1 raw11285step0; decide +kernel
      have hl : raw11285step1Labels = raw11285step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11285step1 raw11285step1Labels = mixedMoment B raw11285step2 raw11285step2Labels := by
      have ha : raw11285step2 = raw11285step1 := by apply Matrix.ext; unfold raw11285step2 raw11285step1; decide +kernel
      have hl : raw11285step1Labels = labelEmbedding1 ∘ raw11285step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11285step1 raw11285step1Labels raw11285step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2213 node2213Labels := by rfl

theorem canonical11286 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11286 raw11286Labels = mixedMoment B node2277 node2277Labels := by
  calc
    mixedMoment B raw11286 raw11286Labels = mixedMoment B raw11286step0 raw11286step0Labels := by
      have hz : ∀ j, raw11286 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11286step0 = (fun i j => raw11286 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11286step0 raw11286; decide +kernel
      have hl : raw11286step0Labels = raw11286Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11286 raw11286Labels permutation434 hz
    mixedMoment B raw11286step0 raw11286step0Labels = mixedMoment B raw11286step1 raw11286step1Labels := by
      have ha : raw11286step1 = (fun i j => raw11286step0 (permutation44 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11286step1 raw11286step0; decide +kernel
      have hl : raw11286step1Labels = raw11286step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11286step0 raw11286step0Labels permutation44 permutation7
    mixedMoment B raw11286step1 raw11286step1Labels = mixedMoment B raw11286step2 raw11286step2Labels := by
      have ha : raw11286step2 = -raw11286step1 := by apply Matrix.ext; change ∀ i j, raw11286step2 i j = -(raw11286step1 i j); unfold raw11286step2 raw11286step1; decide +kernel
      have hl : raw11286step2Labels = raw11286step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11286step2 raw11286step2Labels = mixedMoment B raw11286step3 raw11286step3Labels := by
      have ha : raw11286step3 = raw11286step2 := by apply Matrix.ext; unfold raw11286step3 raw11286step2; decide +kernel
      have hl : raw11286step2Labels = labelEmbedding1 ∘ raw11286step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11286step2 raw11286step2Labels raw11286step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2277 node2277Labels := by rfl

theorem canonical11287 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11287 raw11287Labels = mixedMoment B node1723 node1723Labels := by
  calc
    mixedMoment B raw11287 raw11287Labels = mixedMoment B raw11287step0 raw11287step0Labels := by
      have hz : ∀ j, raw11287 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11287step0 = (fun i j => raw11287 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11287step0 raw11287; decide +kernel
      have hl : raw11287step0Labels = raw11287Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11287 raw11287Labels permutation434 hz
    mixedMoment B raw11287step0 raw11287step0Labels = mixedMoment B raw11287step1 raw11287step1Labels := by
      have ha : raw11287step1 = (fun i j => raw11287step0 (permutation44 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11287step1 raw11287step0; decide +kernel
      have hl : raw11287step1Labels = raw11287step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11287step0 raw11287step0Labels permutation44 permutation7
    mixedMoment B raw11287step1 raw11287step1Labels = mixedMoment B raw11287step2 raw11287step2Labels := by
      have ha : raw11287step2 = -raw11287step1 := by apply Matrix.ext; change ∀ i j, raw11287step2 i j = -(raw11287step1 i j); unfold raw11287step2 raw11287step1; decide +kernel
      have hl : raw11287step2Labels = raw11287step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11287step2 raw11287step2Labels = mixedMoment B raw11287step3 raw11287step3Labels := by
      have ha : raw11287step3 = raw11287step2 := by apply Matrix.ext; unfold raw11287step3 raw11287step2; decide +kernel
      have hl : raw11287step2Labels = labelEmbedding1 ∘ raw11287step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11287step2 raw11287step2Labels raw11287step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1723 node1723Labels := by rfl

theorem canonical11288 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11288 raw11288Labels = mixedMoment B node2259 node2259Labels := by
  calc
    mixedMoment B raw11288 raw11288Labels = mixedMoment B raw11288step0 raw11288step0Labels := by
      have hz : ∀ j, raw11288 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11288step0 = (fun i j => raw11288 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11288step0 raw11288; decide +kernel
      have hl : raw11288step0Labels = raw11288Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11288 raw11288Labels permutation434 hz
    mixedMoment B raw11288step0 raw11288step0Labels = mixedMoment B raw11288step1 raw11288step1Labels := by
      have ha : raw11288step1 = (fun i j => raw11288step0 (permutation44 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11288step1 raw11288step0; decide +kernel
      have hl : raw11288step1Labels = raw11288step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11288step0 raw11288step0Labels permutation44 permutation7
    mixedMoment B raw11288step1 raw11288step1Labels = mixedMoment B raw11288step2 raw11288step2Labels := by
      have ha : raw11288step2 = -raw11288step1 := by apply Matrix.ext; change ∀ i j, raw11288step2 i j = -(raw11288step1 i j); unfold raw11288step2 raw11288step1; decide +kernel
      have hl : raw11288step2Labels = raw11288step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11288step2 raw11288step2Labels = mixedMoment B raw11288step3 raw11288step3Labels := by
      have ha : raw11288step3 = raw11288step2 := by apply Matrix.ext; unfold raw11288step3 raw11288step2; decide +kernel
      have hl : raw11288step2Labels = labelEmbedding1 ∘ raw11288step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11288step2 raw11288step2Labels raw11288step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2259 node2259Labels := by rfl

theorem canonical11289 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11289 raw11289Labels = mixedMoment B node2259 node2259Labels := by
  calc
    mixedMoment B raw11289 raw11289Labels = mixedMoment B raw11289step0 raw11289step0Labels := by
      have hz : ∀ j, raw11289 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11289step0 = (fun i j => raw11289 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11289step0 raw11289; decide +kernel
      have hl : raw11289step0Labels = raw11289Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11289 raw11289Labels permutation434 hz
    mixedMoment B raw11289step0 raw11289step0Labels = mixedMoment B raw11289step1 raw11289step1Labels := by
      have ha : raw11289step1 = (fun i j => raw11289step0 (permutation46 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11289step1 raw11289step0; decide +kernel
      have hl : raw11289step1Labels = raw11289step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11289step0 raw11289step0Labels permutation46 permutation7
    mixedMoment B raw11289step1 raw11289step1Labels = mixedMoment B raw11289step2 raw11289step2Labels := by
      have ha : raw11289step2 = -raw11289step1 := by apply Matrix.ext; change ∀ i j, raw11289step2 i j = -(raw11289step1 i j); unfold raw11289step2 raw11289step1; decide +kernel
      have hl : raw11289step2Labels = raw11289step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11289step2 raw11289step2Labels = mixedMoment B raw11289step3 raw11289step3Labels := by
      have ha : raw11289step3 = raw11289step2 := by apply Matrix.ext; unfold raw11289step3 raw11289step2; decide +kernel
      have hl : raw11289step2Labels = labelEmbedding1 ∘ raw11289step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11289step2 raw11289step2Labels raw11289step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2259 node2259Labels := by rfl

theorem canonical11290 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11290 raw11290Labels = mixedMoment B node2201 node2201Labels := by
  calc
    mixedMoment B raw11290 raw11290Labels = mixedMoment B raw11290step0 raw11290step0Labels := by
      have ha : raw11290step0 = (fun i j => raw11290 (permutation212 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11290step0 raw11290; decide +kernel
      have hl : raw11290step0Labels = raw11290Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11290 raw11290Labels permutation212 permutation7
    mixedMoment B raw11290step0 raw11290step0Labels = mixedMoment B raw11290step1 raw11290step1Labels := by
      have ha : raw11290step1 = -raw11290step0 := by apply Matrix.ext; change ∀ i j, raw11290step1 i j = -(raw11290step0 i j); unfold raw11290step1 raw11290step0; decide +kernel
      have hl : raw11290step1Labels = raw11290step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11290step1 raw11290step1Labels = mixedMoment B raw11290step2 raw11290step2Labels := by
      have ha : raw11290step2 = raw11290step1 := by apply Matrix.ext; unfold raw11290step2 raw11290step1; decide +kernel
      have hl : raw11290step1Labels = labelEmbedding1 ∘ raw11290step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11290step1 raw11290step1Labels raw11290step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2201 node2201Labels := by rfl

theorem canonical11291 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11291 raw11291Labels = mixedMoment B node2290 node2290Labels := by
  calc
    mixedMoment B raw11291 raw11291Labels = mixedMoment B raw11291step0 raw11291step0Labels := by
      have hz : ∀ j, raw11291 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw11291step0 = (fun i j => raw11291 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw11291step0 raw11291; decide +kernel
      have hl : raw11291step0Labels = raw11291Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11291 raw11291Labels permutation520 hz
    mixedMoment B raw11291step0 raw11291step0Labels = mixedMoment B raw11291step1 raw11291step1Labels := by
      have hz : ∀ j, raw11291step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw11291step1 = (fun i j => raw11291step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw11291step1 raw11291step0; decide +kernel
      have hl : raw11291step1Labels = raw11291step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11291step0 raw11291step0Labels permutation104 hz
    mixedMoment B raw11291step1 raw11291step1Labels = mixedMoment B raw11291step2 raw11291step2Labels := by
      have ha : raw11291step2 = (fun i j => raw11291step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11291step2 raw11291step1; decide +kernel
      have hl : raw11291step2Labels = raw11291step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11291step1 raw11291step1Labels permutation8 permutation7
    mixedMoment B raw11291step2 raw11291step2Labels = mixedMoment B raw11291step3 raw11291step3Labels := by
      have ha : raw11291step3 = -raw11291step2 := by apply Matrix.ext; change ∀ i j, raw11291step3 i j = -(raw11291step2 i j); unfold raw11291step3 raw11291step2; decide +kernel
      have hl : raw11291step3Labels = raw11291step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11291step3 raw11291step3Labels = mixedMoment B raw11291step4 raw11291step4Labels := by
      have ha : raw11291step4 = raw11291step3 := by apply Matrix.ext; unfold raw11291step4 raw11291step3; decide +kernel
      have hl : raw11291step3Labels = labelEmbedding1 ∘ raw11291step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11291step3 raw11291step3Labels raw11291step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2290 node2290Labels := by rfl

theorem canonical11292 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11292 raw11292Labels = mixedMoment B node2244 node2244Labels := by
  calc
    mixedMoment B raw11292 raw11292Labels = mixedMoment B raw11292step0 raw11292step0Labels := by
      have hz : ∀ j, raw11292 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11292step0 = (fun i j => raw11292 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11292step0 raw11292; decide +kernel
      have hl : raw11292step0Labels = raw11292Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11292 raw11292Labels permutation434 hz
    _ = mixedMoment B node2244 node2244Labels := by rfl

theorem canonical11293 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11293 raw11293Labels = mixedMoment B node3572 node3572Labels := by
  calc
    mixedMoment B raw11293 raw11293Labels = mixedMoment B raw11293step0 raw11293step0Labels := by
      have hz : ∀ j, raw11293 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11293step0 = (fun i j => raw11293 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11293step0 raw11293; decide +kernel
      have hl : raw11293step0Labels = raw11293Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11293 raw11293Labels permutation434 hz
    _ = mixedMoment B node3572 node3572Labels := by rfl

theorem canonical11294 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11294 raw11294Labels = mixedMoment B node3572 node3572Labels := by
  calc
    mixedMoment B raw11294 raw11294Labels = mixedMoment B raw11294step0 raw11294step0Labels := by
      have hz : ∀ j, raw11294 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11294step0 = (fun i j => raw11294 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11294step0 raw11294; decide +kernel
      have hl : raw11294step0Labels = raw11294Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11294 raw11294Labels permutation434 hz
    mixedMoment B raw11294step0 raw11294step0Labels = mixedMoment B raw11294step1 raw11294step1Labels := by
      have ha : raw11294step1 = (fun i j => raw11294step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw11294step1 raw11294step0; decide +kernel
      have hl : raw11294step1Labels = raw11294step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11294step0 raw11294step0Labels permutation38 permutation2
    _ = mixedMoment B node3572 node3572Labels := by rfl

theorem canonical11295 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11295 raw11295Labels = mixedMoment B node3525 node3525Labels := by
  calc
    mixedMoment B raw11295 raw11295Labels = mixedMoment B raw11295step0 raw11295step0Labels := by
      have ha : raw11295step0 = (fun i j => raw11295 (permutation200 i) (permutation2 j)) := by apply Matrix.ext; unfold raw11295step0 raw11295; decide +kernel
      have hl : raw11295step0Labels = raw11295Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11295 raw11295Labels permutation200 permutation2
    _ = mixedMoment B node3525 node3525Labels := by rfl

theorem canonical11296 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11296 raw11296Labels = mixedMoment B node3623 node3623Labels := by
  calc
    mixedMoment B raw11296 raw11296Labels = mixedMoment B raw11296step0 raw11296step0Labels := by
      have hz : ∀ j, raw11296 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw11296step0 = (fun i j => raw11296 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw11296step0 raw11296; decide +kernel
      have hl : raw11296step0Labels = raw11296Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11296 raw11296Labels permutation520 hz
    mixedMoment B raw11296step0 raw11296step0Labels = mixedMoment B raw11296step1 raw11296step1Labels := by
      have hz : ∀ j, raw11296step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw11296step1 = (fun i j => raw11296step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw11296step1 raw11296step0; decide +kernel
      have hl : raw11296step1Labels = raw11296step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11296step0 raw11296step0Labels permutation104 hz
    _ = mixedMoment B node3623 node3623Labels := by rfl

theorem canonical11297 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11297 raw11297Labels = mixedMoment B node3622 node3622Labels := by
  calc
    mixedMoment B raw11297 raw11297Labels = mixedMoment B raw11297step0 raw11297step0Labels := by
      have hz : ∀ j, raw11297 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11297step0 = (fun i j => raw11297 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11297step0 raw11297; decide +kernel
      have hl : raw11297step0Labels = raw11297Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11297 raw11297Labels permutation434 hz
    _ = mixedMoment B node3622 node3622Labels := by rfl

theorem canonical11298 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11298 raw11298Labels = mixedMoment B node4083 node4083Labels := by
  calc
    mixedMoment B raw11298 raw11298Labels = mixedMoment B raw11298step0 raw11298step0Labels := by
      have hz : ∀ j, raw11298 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw11298step0 = (fun i j => raw11298 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw11298step0 raw11298; decide +kernel
      have hl : raw11298step0Labels = raw11298Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11298 raw11298Labels permutation520 hz
    mixedMoment B raw11298step0 raw11298step0Labels = mixedMoment B raw11298step1 raw11298step1Labels := by
      have hz : ∀ j, raw11298step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw11298step1 = (fun i j => raw11298step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw11298step1 raw11298step0; decide +kernel
      have hl : raw11298step1Labels = raw11298step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11298step0 raw11298step0Labels permutation104 hz
    _ = mixedMoment B node4083 node4083Labels := by rfl

theorem canonical11299 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11299 raw11299Labels = mixedMoment B node1041 node1041Labels := by
  calc
    mixedMoment B raw11299 raw11299Labels = mixedMoment B raw11299step0 raw11299step0Labels := by
      have hz : ∀ j, raw11299 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11299step0 = (fun i j => raw11299 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11299step0 raw11299; decide +kernel
      have hl : raw11299step0Labels = raw11299Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11299 raw11299Labels permutation434 hz
    mixedMoment B raw11299step0 raw11299step0Labels = mixedMoment B raw11299step1 raw11299step1Labels := by
      have ha : raw11299step1 = (fun i j => raw11299step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw11299step1 raw11299step0; decide +kernel
      have hl : raw11299step1Labels = raw11299step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11299step0 raw11299step0Labels permutation40 permutation2
    _ = mixedMoment B node1041 node1041Labels := by rfl

theorem canonical11300 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11300 raw11300Labels = mixedMoment B node1041 node1041Labels := by
  calc
    mixedMoment B raw11300 raw11300Labels = mixedMoment B raw11300step0 raw11300step0Labels := by
      have hz : ∀ j, raw11300 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11300step0 = (fun i j => raw11300 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11300step0 raw11300; decide +kernel
      have hl : raw11300step0Labels = raw11300Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11300 raw11300Labels permutation434 hz
    mixedMoment B raw11300step0 raw11300step0Labels = mixedMoment B raw11300step1 raw11300step1Labels := by
      have ha : raw11300step1 = (fun i j => raw11300step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw11300step1 raw11300step0; decide +kernel
      have hl : raw11300step1Labels = raw11300step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11300step0 raw11300step0Labels permutation34 permutation2
    _ = mixedMoment B node1041 node1041Labels := by rfl

theorem canonical11301 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11301 raw11301Labels = mixedMoment B node1020 node1020Labels := by
  calc
    _ = mixedMoment B node1020 node1020Labels := by rfl

theorem canonical11302 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11302 raw11302Labels = mixedMoment B node1026 node1026Labels := by
  calc
    mixedMoment B raw11302 raw11302Labels = mixedMoment B raw11302step0 raw11302step0Labels := by
      have hz : ∀ j, raw11302 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11302step0 = (fun i j => raw11302 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11302step0 raw11302; decide +kernel
      have hl : raw11302step0Labels = raw11302Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11302 raw11302Labels permutation434 hz
    _ = mixedMoment B node1026 node1026Labels := by rfl

theorem canonical11303 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11303 raw11303Labels = mixedMoment B node1022 node1022Labels := by
  calc
    mixedMoment B raw11303 raw11303Labels = mixedMoment B raw11303step0 raw11303step0Labels := by
      have hz : ∀ j, raw11303 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11303step0 = (fun i j => raw11303 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11303step0 raw11303; decide +kernel
      have hl : raw11303step0Labels = raw11303Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11303 raw11303Labels permutation434 hz
    _ = mixedMoment B node1022 node1022Labels := by rfl

theorem canonical11304 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11304 raw11304Labels = mixedMoment B node2107 node2107Labels := by
  calc
    mixedMoment B raw11304 raw11304Labels = mixedMoment B raw11304step0 raw11304step0Labels := by
      have hz : ∀ j, raw11304 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11304step0 = (fun i j => raw11304 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11304step0 raw11304; decide +kernel
      have hl : raw11304step0Labels = raw11304Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11304 raw11304Labels permutation434 hz
    mixedMoment B raw11304step0 raw11304step0Labels = mixedMoment B raw11304step1 raw11304step1Labels := by
      have ha : raw11304step1 = (fun i j => raw11304step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw11304step1 raw11304step0; decide +kernel
      have hl : raw11304step1Labels = raw11304step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11304step0 raw11304step0Labels permutation40 permutation2
    _ = mixedMoment B node2107 node2107Labels := by rfl

theorem canonical11305 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11305 raw11305Labels = mixedMoment B node2020 node2020Labels := by
  calc
    mixedMoment B raw11305 raw11305Labels = mixedMoment B raw11305step0 raw11305step0Labels := by
      have ha : raw11305step0 = (fun i j => raw11305 (permutation208 i) (permutation2 j)) := by apply Matrix.ext; unfold raw11305step0 raw11305; decide +kernel
      have hl : raw11305step0Labels = raw11305Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11305 raw11305Labels permutation208 permutation2
    _ = mixedMoment B node2020 node2020Labels := by rfl

theorem canonical11306 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11306 raw11306Labels = mixedMoment B node2265 node2265Labels := by
  calc
    mixedMoment B raw11306 raw11306Labels = mixedMoment B raw11306step0 raw11306step0Labels := by
      have hz : ∀ j, raw11306 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw11306step0 = (fun i j => raw11306 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw11306step0 raw11306; decide +kernel
      have hl : raw11306step0Labels = raw11306Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11306 raw11306Labels permutation520 hz
    mixedMoment B raw11306step0 raw11306step0Labels = mixedMoment B raw11306step1 raw11306step1Labels := by
      have hz : ∀ j, raw11306step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw11306step1 = (fun i j => raw11306step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw11306step1 raw11306step0; decide +kernel
      have hl : raw11306step1Labels = raw11306step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11306step0 raw11306step0Labels permutation104 hz
    mixedMoment B raw11306step1 raw11306step1Labels = mixedMoment B raw11306step2 raw11306step2Labels := by
      have ha : raw11306step2 = (fun i j => raw11306step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw11306step2 raw11306step1; decide +kernel
      have hl : raw11306step2Labels = raw11306step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11306step1 raw11306step1Labels permutation10 permutation2
    _ = mixedMoment B node2265 node2265Labels := by rfl

theorem canonical11307 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11307 raw11307Labels = mixedMoment B node2263 node2263Labels := by
  calc
    mixedMoment B raw11307 raw11307Labels = mixedMoment B raw11307step0 raw11307step0Labels := by
      have hz : ∀ j, raw11307 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11307step0 = (fun i j => raw11307 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11307step0 raw11307; decide +kernel
      have hl : raw11307step0Labels = raw11307Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11307 raw11307Labels permutation434 hz
    mixedMoment B raw11307step0 raw11307step0Labels = mixedMoment B raw11307step1 raw11307step1Labels := by
      have ha : raw11307step1 = (fun i j => raw11307step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw11307step1 raw11307step0; decide +kernel
      have hl : raw11307step1Labels = raw11307step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11307step0 raw11307step0Labels permutation40 permutation2
    _ = mixedMoment B node2263 node2263Labels := by rfl

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

theorem sum_fin_six {R : Type*} [AddCommMonoid R] (f : Fin 6 → R) :
    ∑ i, f i = f 0 + f 1 + f 2 + f 3 + f 4 + f 5 := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change f 0 + (f 1 + (f 2 + (f 3 + (f 4 + f 5)))) = _
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical162
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical249
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

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

end MUB6.Certificate.PairSemantics

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons43
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros15
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero1020 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node1020 node1020Labels = 0 := by
  exact mixedMoment_alpha B hF node1020 node1020Labels 1 permutation152
    (by decide +kernel)

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

theorem sound1020 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1020 node1020Labels = Sparse.eval nodeValue1020 (mixedVector B) := by
  simpa only [nodeValue1020, Sparse.eval_nil] using zero1020 B _hB _hF

theorem sound1022 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1022 node1022Labels = Sparse.eval nodeValue1022 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1022) = mixedMoment B node1022 node1022Labels := rfl
  simpa [nodeValue1022, Sparse.eval] using hc.symm

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

theorem sound1026 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1026 node1026Labels = Sparse.eval nodeValue1026 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1026) = mixedMoment B node1026 node1026Labels := rfl
  simpa [nodeValue1026, Sparse.eval] using hc.symm

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

theorem sound1056 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1056 node1056Labels = Sparse.eval nodeValue1056 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1056) = mixedMoment B node1056 node1056Labels := rfl
  simpa [nodeValue1056, Sparse.eval] using hc.symm

theorem sound1057 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1057 node1057Labels = Sparse.eval nodeValue1057 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1057) = mixedMoment B node1057 node1057Labels := rfl
  simpa [nodeValue1057, Sparse.eval] using hc.symm

theorem sound1058 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1058 node1058Labels = Sparse.eval nodeValue1058 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1058) = mixedMoment B node1058 node1058Labels := rfl
  simpa [nodeValue1058, Sparse.eval] using hc.symm

theorem sound1079 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1079 node1079Labels = Sparse.eval nodeValue1079 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1079) = mixedMoment B node1079 node1079Labels := rfl
  simpa [nodeValue1079, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros26
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero1705 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node1705 node1705Labels = 0 := by
  exact mixedMoment_alpha B hF node1705 node1705Labels 1 permutation437
    (by decide +kernel)

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

theorem sound1705 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1705 node1705Labels = Sparse.eval nodeValue1705 (mixedVector B) := by
  simpa only [nodeValue1705, Sparse.eval_nil] using zero1705 B _hB _hF

theorem sound1723 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1723 node1723Labels = Sparse.eval nodeValue1723 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1723) = mixedMoment B node1723 node1723Labels := rfl
  simpa [nodeValue1723, Sparse.eval] using hc.symm

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

theorem sound1736 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1736 node1736Labels = Sparse.eval nodeValue1736 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1736) = mixedMoment B node1736 node1736Labels := rfl
  simpa [nodeValue1736, Sparse.eval] using hc.symm

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

theorem sound2010 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2010 node2010Labels = Sparse.eval nodeValue2010 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2010) = mixedMoment B node2010 node2010Labels := rfl
  simpa [nodeValue2010, Sparse.eval] using hc.symm

theorem sound2012 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2012 node2012Labels = Sparse.eval nodeValue2012 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2012) = mixedMoment B node2012 node2012Labels := rfl
  simpa [nodeValue2012, Sparse.eval] using hc.symm

theorem sound2020 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2020 node2020Labels = Sparse.eval nodeValue2020 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2020) = mixedMoment B node2020 node2020Labels := rfl
  simpa [nodeValue2020, Sparse.eval] using hc.symm

theorem sound2023 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2023 node2023Labels = Sparse.eval nodeValue2023 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2023) = mixedMoment B node2023 node2023Labels := rfl
  simpa [nodeValue2023, Sparse.eval] using hc.symm

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

theorem sound2089 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2089 node2089Labels = Sparse.eval nodeValue2089 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2089) = mixedMoment B node2089 node2089Labels := rfl
  simpa [nodeValue2089, Sparse.eval] using hc.symm

theorem sound2092 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2092 node2092Labels = Sparse.eval nodeValue2092 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2092) = mixedMoment B node2092 node2092Labels := rfl
  simpa [nodeValue2092, Sparse.eval] using hc.symm

theorem sound2094 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2094 node2094Labels = Sparse.eval nodeValue2094 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2094) = mixedMoment B node2094 node2094Labels := rfl
  simpa [nodeValue2094, Sparse.eval] using hc.symm

theorem sound2107 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2107 node2107Labels = Sparse.eval nodeValue2107 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2107) = mixedMoment B node2107 node2107Labels := rfl
  simpa [nodeValue2107, Sparse.eval] using hc.symm

theorem sound2110 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2110 node2110Labels = Sparse.eval nodeValue2110 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2110) = mixedMoment B node2110 node2110Labels := rfl
  simpa [nodeValue2110, Sparse.eval] using hc.symm

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

theorem sound2201 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2201 node2201Labels = Sparse.eval nodeValue2201 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2201) = mixedMoment B node2201 node2201Labels := rfl
  simpa [nodeValue2201, Sparse.eval] using hc.symm

theorem sound2202 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2202 node2202Labels = Sparse.eval nodeValue2202 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2202) = mixedMoment B node2202 node2202Labels := rfl
  simpa [nodeValue2202, Sparse.eval] using hc.symm

theorem sound2213 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2213 node2213Labels = Sparse.eval nodeValue2213 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2213) = mixedMoment B node2213 node2213Labels := rfl
  simpa [nodeValue2213, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros35
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero2263 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2263 node2263Labels = 0 := by
  exact mixedMoment_order_one B hB node2263 node2263Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero2265 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2265 node2265Labels = 0 := by
  exact mixedMoment_order_one B hB node2265 node2265Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero2291 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2291 node2291Labels = 0 := by
  exact mixedMoment_order_one B hB node2291 node2291Labels 1
    (by decide +kernel) (by decide +kernel)

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

theorem sound2240 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2240 node2240Labels = Sparse.eval nodeValue2240 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2240) = mixedMoment B node2240 node2240Labels := rfl
  simpa [nodeValue2240, Sparse.eval] using hc.symm

theorem sound2243 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2243 node2243Labels = Sparse.eval nodeValue2243 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2243) = mixedMoment B node2243 node2243Labels := rfl
  simpa [nodeValue2243, Sparse.eval] using hc.symm

theorem sound2244 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2244 node2244Labels = Sparse.eval nodeValue2244 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2244) = mixedMoment B node2244 node2244Labels := rfl
  simpa [nodeValue2244, Sparse.eval] using hc.symm

theorem sound2245 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2245 node2245Labels = Sparse.eval nodeValue2245 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2245) = mixedMoment B node2245 node2245Labels := rfl
  simpa [nodeValue2245, Sparse.eval] using hc.symm

theorem sound2259 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2259 node2259Labels = Sparse.eval nodeValue2259 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2259) = mixedMoment B node2259 node2259Labels := rfl
  simpa [nodeValue2259, Sparse.eval] using hc.symm

theorem sound2260 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2260 node2260Labels = Sparse.eval nodeValue2260 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2260) = mixedMoment B node2260 node2260Labels := rfl
  simpa [nodeValue2260, Sparse.eval] using hc.symm

theorem sound2262 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2262 node2262Labels = Sparse.eval nodeValue2262 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2262) = mixedMoment B node2262 node2262Labels := rfl
  simpa [nodeValue2262, Sparse.eval] using hc.symm

theorem sound2263 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2263 node2263Labels = Sparse.eval nodeValue2263 (mixedVector B) := by
  simpa only [nodeValue2263, Sparse.eval_nil] using zero2263 B _hB _hF

theorem sound2265 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2265 node2265Labels = Sparse.eval nodeValue2265 (mixedVector B) := by
  simpa only [nodeValue2265, Sparse.eval_nil] using zero2265 B _hB _hF

theorem sound2274 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2274 node2274Labels = Sparse.eval nodeValue2274 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2274) = mixedMoment B node2274 node2274Labels := rfl
  simpa [nodeValue2274, Sparse.eval] using hc.symm

theorem sound2277 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2277 node2277Labels = Sparse.eval nodeValue2277 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2277) = mixedMoment B node2277 node2277Labels := rfl
  simpa [nodeValue2277, Sparse.eval] using hc.symm

theorem sound2290 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2290 node2290Labels = Sparse.eval nodeValue2290 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2290) = mixedMoment B node2290 node2290Labels := rfl
  simpa [nodeValue2290, Sparse.eval] using hc.symm

theorem sound2291 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2291 node2291Labels = Sparse.eval nodeValue2291 (mixedVector B) := by
  simpa only [nodeValue2291, Sparse.eval_nil] using zero2291 B _hB _hF

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros42
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero2720 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node2720 node2720Labels = 0 := by
  exact mixedMoment_alpha B hF node2720 node2720Labels 1 permutation203
    (by decide +kernel)

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

theorem sound2720 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2720 node2720Labels = Sparse.eval nodeValue2720 (mixedVector B) := by
  simpa only [nodeValue2720, Sparse.eval_nil] using zero2720 B _hB _hF

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

theorem sound2763 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2763 node2763Labels = Sparse.eval nodeValue2763 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2763) = mixedMoment B node2763 node2763Labels := rfl
  simpa [nodeValue2763, Sparse.eval] using hc.symm

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros55
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero3525 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node3525 node3525Labels = 0 := by
  exact mixedMoment_alpha B hF node3525 node3525Labels 1 permutation434
    (by decide +kernel)

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

theorem sound3525 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3525 node3525Labels = Sparse.eval nodeValue3525 (mixedVector B) := by
  simpa only [nodeValue3525, Sparse.eval_nil] using zero3525 B _hB _hF

theorem sound3526 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3526 node3526Labels = Sparse.eval nodeValue3526 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3526) = mixedMoment B node3526 node3526Labels := rfl
  simpa [nodeValue3526, Sparse.eval] using hc.symm

theorem sound3572 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3572 node3572Labels = Sparse.eval nodeValue3572 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3572) = mixedMoment B node3572 node3572Labels := rfl
  simpa [nodeValue3572, Sparse.eval] using hc.symm

theorem sound3573 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3573 node3573Labels = Sparse.eval nodeValue3573 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3573) = mixedMoment B node3573 node3573Labels := rfl
  simpa [nodeValue3573, Sparse.eval] using hc.symm

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

theorem sound3622 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3622 node3622Labels = Sparse.eval nodeValue3622 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3622) = mixedMoment B node3622 node3622Labels := rfl
  simpa [nodeValue3622, Sparse.eval] using hc.symm

theorem sound3623 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3623 node3623Labels = Sparse.eval nodeValue3623 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3623) = mixedMoment B node3623 node3623Labels := rfl
  simpa [nodeValue3623, Sparse.eval] using hc.symm

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

theorem sound4083 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4083 node4083Labels = Sparse.eval nodeValue4083 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4083) = mixedMoment B node4083 node4083Labels := rfl
  simpa [nodeValue4083, Sparse.eval] using hc.symm

theorem sound4084 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4084 node4084Labels = Sparse.eval nodeValue4084 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4084) = mixedMoment B node4084 node4084Labels := rfl
  simpa [nodeValue4084, Sparse.eval] using hc.symm

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources20
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sourceEq651 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm651 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA651 + difference 1 0) (sourceB651 + difference 0 1) sourceC651) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1044) := by
    have ha : (tripleCharges (sourceA651 + difference 1 0) (sourceB651 + difference 0 1) sourceC651) = raw11087 := by
      apply Matrix.ext; unfold tripleCharges sourceA651 sourceB651 sourceC651 difference raw11087; decide +kernel
    rw [ha]
    exact (canonical11087 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA651 + difference 1 1) (sourceB651 + difference 1 1) sourceC651) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2245) := by
    have ha : (tripleCharges (sourceA651 + difference 1 1) (sourceB651 + difference 1 1) sourceC651) = raw11080 := by
      apply Matrix.ext; unfold tripleCharges sourceA651 sourceB651 sourceC651 difference raw11080; decide +kernel
    rw [ha]
    exact (canonical11080 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA651 + difference 1 2) (sourceB651 + difference 2 1) sourceC651) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2110) := by
    have ha : (tripleCharges (sourceA651 + difference 1 2) (sourceB651 + difference 2 1) sourceC651) = raw11088 := by
      apply Matrix.ext; unfold tripleCharges sourceA651 sourceB651 sourceC651 difference raw11088; decide +kernel
    rw [ha]
    exact (canonical11088 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA651 + difference 1 3) (sourceB651 + difference 3 1) sourceC651) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2023) := by
    have ha : (tripleCharges (sourceA651 + difference 1 3) (sourceB651 + difference 3 1) sourceC651) = raw11089 := by
      apply Matrix.ext; unfold tripleCharges sourceA651 sourceB651 sourceC651 difference raw11089; decide +kernel
    rw [ha]
    exact (canonical11089 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA651 + difference 1 4) (sourceB651 + difference 4 1) sourceC651) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2245) := by
    have ha : (tripleCharges (sourceA651 + difference 1 4) (sourceB651 + difference 4 1) sourceC651) = raw11090 := by
      apply Matrix.ext; unfold tripleCharges sourceA651 sourceB651 sourceC651 difference raw11090; decide +kernel
    rw [ha]
    exact (canonical11090 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA651 + difference 1 5) (sourceB651 + difference 5 1) sourceC651) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2263) := by
    have ha : (tripleCharges (sourceA651 + difference 1 5) (sourceB651 + difference 5 1) sourceC651) = raw11091 := by
      apply Matrix.ext; unfold tripleCharges sourceA651 sourceB651 sourceC651 difference raw11091; decide +kernel
    rw [ha]
    exact (canonical11091 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA651 + sourceB651) sourceC651) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4083) := by
    have ha : (doubleCharges (sourceA651 + sourceB651) sourceC651) = raw11086 := by
      apply Matrix.ext; unfold doubleCharges sourceA651 sourceB651 sourceC651 raw11086; decide +kernel
    rw [ha]
    exact (canonical11086 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA651 sourceB651 sourceC651
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm651, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq652 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm652 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA652 + difference 0 1) (sourceB652 + difference 1 0) sourceC652) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3573) := by
    have ha : (tripleCharges (sourceA652 + difference 0 1) (sourceB652 + difference 1 0) sourceC652) = raw11081 := by
      apply Matrix.ext; unfold tripleCharges sourceA652 sourceB652 sourceC652 difference raw11081; decide +kernel
    rw [ha]
    exact (canonical11081 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA652 + difference 1 1) (sourceB652 + difference 1 1) sourceC652) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2245) := by
    have ha : (tripleCharges (sourceA652 + difference 1 1) (sourceB652 + difference 1 1) sourceC652) = raw11080 := by
      apply Matrix.ext; unfold tripleCharges sourceA652 sourceB652 sourceC652 difference raw11080; decide +kernel
    rw [ha]
    exact (canonical11080 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA652 + difference 2 1) (sourceB652 + difference 1 2) sourceC652) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2110) := by
    have ha : (tripleCharges (sourceA652 + difference 2 1) (sourceB652 + difference 1 2) sourceC652) = raw11092 := by
      apply Matrix.ext; unfold tripleCharges sourceA652 sourceB652 sourceC652 difference raw11092; decide +kernel
    rw [ha]
    exact (canonical11092 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA652 + difference 3 1) (sourceB652 + difference 1 3) sourceC652) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2089) := by
    have ha : (tripleCharges (sourceA652 + difference 3 1) (sourceB652 + difference 1 3) sourceC652) = raw11093 := by
      apply Matrix.ext; unfold tripleCharges sourceA652 sourceB652 sourceC652 difference raw11093; decide +kernel
    rw [ha]
    exact (canonical11093 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA652 + difference 4 1) (sourceB652 + difference 1 4) sourceC652) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2094) := by
    have ha : (tripleCharges (sourceA652 + difference 4 1) (sourceB652 + difference 1 4) sourceC652) = raw11094 := by
      apply Matrix.ext; unfold tripleCharges sourceA652 sourceB652 sourceC652 difference raw11094; decide +kernel
    rw [ha]
    exact (canonical11094 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA652 + difference 5 1) (sourceB652 + difference 1 5) sourceC652) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2092) := by
    have ha : (tripleCharges (sourceA652 + difference 5 1) (sourceB652 + difference 1 5) sourceC652) = raw11095 := by
      apply Matrix.ext; unfold tripleCharges sourceA652 sourceB652 sourceC652 difference raw11095; decide +kernel
    rw [ha]
    exact (canonical11095 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA652 + sourceB652) sourceC652) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4083) := by
    have ha : (doubleCharges (sourceA652 + sourceB652) sourceC652) = raw11086 := by
      apply Matrix.ext; unfold doubleCharges sourceA652 sourceB652 sourceC652 raw11086; decide +kernel
    rw [ha]
    exact (canonical11086 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA652 sourceB652 sourceC652
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm652, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq653 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm653 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA653 + difference 0 3) (sourceB653 + difference 3 0) sourceC653) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3526) := by
    have ha : (tripleCharges (sourceA653 + difference 0 3) (sourceB653 + difference 3 0) sourceC653) = raw11083 := by
      apply Matrix.ext; unfold tripleCharges sourceA653 sourceB653 sourceC653 difference raw11083; decide +kernel
    rw [ha]
    exact (canonical11083 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA653 + difference 1 3) (sourceB653 + difference 3 1) sourceC653) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2023) := by
    have ha : (tripleCharges (sourceA653 + difference 1 3) (sourceB653 + difference 3 1) sourceC653) = raw11089 := by
      apply Matrix.ext; unfold tripleCharges sourceA653 sourceB653 sourceC653 difference raw11089; decide +kernel
    rw [ha]
    exact (canonical11089 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA653 + difference 2 3) (sourceB653 + difference 3 2) sourceC653) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2023) := by
    have ha : (tripleCharges (sourceA653 + difference 2 3) (sourceB653 + difference 3 2) sourceC653) = raw11096 := by
      apply Matrix.ext; unfold tripleCharges sourceA653 sourceB653 sourceC653 difference raw11096; decide +kernel
    rw [ha]
    exact (canonical11096 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA653 + difference 3 3) (sourceB653 + difference 3 3) sourceC653) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2245) := by
    have ha : (tripleCharges (sourceA653 + difference 3 3) (sourceB653 + difference 3 3) sourceC653) = raw11080 := by
      apply Matrix.ext; unfold tripleCharges sourceA653 sourceB653 sourceC653 difference raw11080; decide +kernel
    rw [ha]
    exact (canonical11080 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA653 + difference 4 3) (sourceB653 + difference 3 4) sourceC653) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2012) := by
    have ha : (tripleCharges (sourceA653 + difference 4 3) (sourceB653 + difference 3 4) sourceC653) = raw11097 := by
      apply Matrix.ext; unfold tripleCharges sourceA653 sourceB653 sourceC653 difference raw11097; decide +kernel
    rw [ha]
    exact (canonical11097 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA653 + difference 5 3) (sourceB653 + difference 3 5) sourceC653) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2010) := by
    have ha : (tripleCharges (sourceA653 + difference 5 3) (sourceB653 + difference 3 5) sourceC653) = raw11098 := by
      apply Matrix.ext; unfold tripleCharges sourceA653 sourceB653 sourceC653 difference raw11098; decide +kernel
    rw [ha]
    exact (canonical11098 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA653 + sourceB653) sourceC653) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4083) := by
    have ha : (doubleCharges (sourceA653 + sourceB653) sourceC653) = raw11086 := by
      apply Matrix.ext; unfold doubleCharges sourceA653 sourceB653 sourceC653 raw11086; decide +kernel
    rw [ha]
    exact (canonical11086 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA653 sourceB653 sourceC653
    (0 : Fin 2) 1 (3 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm653, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq654 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm654 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA654 + difference 4 0) (sourceB654 + difference 0 4) sourceC654) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1026) := by
    have ha : (tripleCharges (sourceA654 + difference 4 0) (sourceB654 + difference 0 4) sourceC654) = raw11099 := by
      apply Matrix.ext; unfold tripleCharges sourceA654 sourceB654 sourceC654 difference raw11099; decide +kernel
    rw [ha]
    exact (canonical11099 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA654 + difference 4 1) (sourceB654 + difference 1 4) sourceC654) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2094) := by
    have ha : (tripleCharges (sourceA654 + difference 4 1) (sourceB654 + difference 1 4) sourceC654) = raw11094 := by
      apply Matrix.ext; unfold tripleCharges sourceA654 sourceB654 sourceC654 difference raw11094; decide +kernel
    rw [ha]
    exact (canonical11094 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA654 + difference 4 2) (sourceB654 + difference 2 4) sourceC654) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2094) := by
    have ha : (tripleCharges (sourceA654 + difference 4 2) (sourceB654 + difference 2 4) sourceC654) = raw11100 := by
      apply Matrix.ext; unfold tripleCharges sourceA654 sourceB654 sourceC654 difference raw11100; decide +kernel
    rw [ha]
    exact (canonical11100 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA654 + difference 4 3) (sourceB654 + difference 3 4) sourceC654) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2012) := by
    have ha : (tripleCharges (sourceA654 + difference 4 3) (sourceB654 + difference 3 4) sourceC654) = raw11097 := by
      apply Matrix.ext; unfold tripleCharges sourceA654 sourceB654 sourceC654 difference raw11097; decide +kernel
    rw [ha]
    exact (canonical11097 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA654 + difference 4 4) (sourceB654 + difference 4 4) sourceC654) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2245) := by
    have ha : (tripleCharges (sourceA654 + difference 4 4) (sourceB654 + difference 4 4) sourceC654) = raw11080 := by
      apply Matrix.ext; unfold tripleCharges sourceA654 sourceB654 sourceC654 difference raw11080; decide +kernel
    rw [ha]
    exact (canonical11080 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA654 + difference 4 5) (sourceB654 + difference 5 4) sourceC654) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2244) := by
    have ha : (tripleCharges (sourceA654 + difference 4 5) (sourceB654 + difference 5 4) sourceC654) = raw11101 := by
      apply Matrix.ext; unfold tripleCharges sourceA654 sourceB654 sourceC654 difference raw11101; decide +kernel
    rw [ha]
    exact (canonical11101 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA654 + sourceB654) sourceC654) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4083) := by
    have ha : (doubleCharges (sourceA654 + sourceB654) sourceC654) = raw11086 := by
      apply Matrix.ext; unfold doubleCharges sourceA654 sourceB654 sourceC654 raw11086; decide +kernel
    rw [ha]
    exact (canonical11086 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA654 sourceB654 sourceC654
    (0 : Fin 2) 1 (4 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm654, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq660 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm660 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA660 + difference 0 0) (sourceB660 + difference 0 0) sourceC660) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2277) := by
    have ha : (tripleCharges (sourceA660 + difference 0 0) (sourceB660 + difference 0 0) sourceC660) = raw5762 := by
      apply Matrix.ext; unfold tripleCharges sourceA660 sourceB660 sourceC660 difference raw5762; decide +kernel
    rw [ha]
    exact (canonical5762 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA660 + difference 1 0) (sourceB660 + difference 0 1) sourceC660) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1058) := by
    have ha : (tripleCharges (sourceA660 + difference 1 0) (sourceB660 + difference 0 1) sourceC660) = raw11198 := by
      apply Matrix.ext; unfold tripleCharges sourceA660 sourceB660 sourceC660 difference raw11198; decide +kernel
    rw [ha]
    exact (canonical11198 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA660 + difference 2 0) (sourceB660 + difference 0 2) sourceC660) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1058) := by
    have ha : (tripleCharges (sourceA660 + difference 2 0) (sourceB660 + difference 0 2) sourceC660) = raw11199 := by
      apply Matrix.ext; unfold tripleCharges sourceA660 sourceB660 sourceC660 difference raw11199; decide +kernel
    rw [ha]
    exact (canonical11199 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA660 + difference 3 0) (sourceB660 + difference 0 3) sourceC660) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1056) := by
    have ha : (tripleCharges (sourceA660 + difference 3 0) (sourceB660 + difference 0 3) sourceC660) = raw5758 := by
      apply Matrix.ext; unfold tripleCharges sourceA660 sourceB660 sourceC660 difference raw5758; decide +kernel
    rw [ha]
    exact (canonical5758 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA660 + difference 4 0) (sourceB660 + difference 0 4) sourceC660) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1057) := by
    have ha : (tripleCharges (sourceA660 + difference 4 0) (sourceB660 + difference 0 4) sourceC660) = raw11200 := by
      apply Matrix.ext; unfold tripleCharges sourceA660 sourceB660 sourceC660 difference raw11200; decide +kernel
    rw [ha]
    exact (canonical11200 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA660 + difference 5 0) (sourceB660 + difference 0 5) sourceC660) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1079) := by
    have ha : (tripleCharges (sourceA660 + difference 5 0) (sourceB660 + difference 0 5) sourceC660) = raw11201 := by
      apply Matrix.ext; unfold tripleCharges sourceA660 sourceB660 sourceC660 difference raw11201; decide +kernel
    rw [ha]
    exact (canonical11201 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA660 + sourceB660) sourceC660) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA660 + sourceB660) sourceC660) = raw5754 := by
      apply Matrix.ext; unfold doubleCharges sourceA660 sourceB660 sourceC660 raw5754; decide +kernel
    rw [ha]
    exact (canonical5754 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA660 sourceB660 sourceC660
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm660, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq663 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm663 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA663 + difference 0 1) (sourceB663 + difference 1 0) sourceC663) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2763) := by
    have ha : (tripleCharges (sourceA663 + difference 0 1) (sourceB663 + difference 1 0) sourceC663) = raw11262 := by
      apply Matrix.ext; unfold tripleCharges sourceA663 sourceB663 sourceC663 difference raw11262; decide +kernel
    rw [ha]
    exact (canonical11262 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA663 + difference 0 2) (sourceB663 + difference 2 0) sourceC663) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2763) := by
    have ha : (tripleCharges (sourceA663 + difference 0 2) (sourceB663 + difference 2 0) sourceC663) = raw11263 := by
      apply Matrix.ext; unfold tripleCharges sourceA663 sourceB663 sourceC663 difference raw11263; decide +kernel
    rw [ha]
    exact (canonical11263 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA663 + difference 0 3) (sourceB663 + difference 3 0) sourceC663) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2720) := by
    have ha : (tripleCharges (sourceA663 + difference 0 3) (sourceB663 + difference 3 0) sourceC663) = raw11264 := by
      apply Matrix.ext; unfold tripleCharges sourceA663 sourceB663 sourceC663 difference raw11264; decide +kernel
    rw [ha]
    exact (canonical11264 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA663 + difference 0 4) (sourceB663 + difference 4 0) sourceC663) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2784) := by
    have ha : (tripleCharges (sourceA663 + difference 0 4) (sourceB663 + difference 4 0) sourceC663) = raw11265 := by
      apply Matrix.ext; unfold tripleCharges sourceA663 sourceB663 sourceC663 difference raw11265; decide +kernel
    rw [ha]
    exact (canonical11265 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA663 + difference 0 5) (sourceB663 + difference 5 0) sourceC663) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2766) := by
    have ha : (tripleCharges (sourceA663 + difference 0 5) (sourceB663 + difference 5 0) sourceC663) = raw11266 := by
      apply Matrix.ext; unfold tripleCharges sourceA663 sourceB663 sourceC663 difference raw11266; decide +kernel
    rw [ha]
    exact (canonical11266 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA663 + difference 1 0) (sourceB663 + difference 0 1) sourceC663) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1724) := by
    have ha : (tripleCharges (sourceA663 + difference 1 0) (sourceB663 + difference 0 1) sourceC663) = raw11267 := by
      apply Matrix.ext; unfold tripleCharges sourceA663 sourceB663 sourceC663 difference raw11267; decide +kernel
    rw [ha]
    exact (canonical11267 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA663 + difference 1 2) (sourceB663 + difference 2 1) sourceC663) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2260) := by
    have ha : (tripleCharges (sourceA663 + difference 1 2) (sourceB663 + difference 2 1) sourceC663) = raw11268 := by
      apply Matrix.ext; unfold tripleCharges sourceA663 sourceB663 sourceC663 difference raw11268; decide +kernel
    rw [ha]
    exact (canonical11268 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA663 + difference 1 3) (sourceB663 + difference 3 1) sourceC663) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2202) := by
    have ha : (tripleCharges (sourceA663 + difference 1 3) (sourceB663 + difference 3 1) sourceC663) = raw11269 := by
      apply Matrix.ext; unfold tripleCharges sourceA663 sourceB663 sourceC663 difference raw11269; decide +kernel
    rw [ha]
    exact (canonical11269 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA663 + difference 1 4) (sourceB663 + difference 4 1) sourceC663) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2291) := by
    have ha : (tripleCharges (sourceA663 + difference 1 4) (sourceB663 + difference 4 1) sourceC663) = raw11270 := by
      apply Matrix.ext; unfold tripleCharges sourceA663 sourceB663 sourceC663 difference raw11270; decide +kernel
    rw [ha]
    exact (canonical11270 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA663 + difference 1 5) (sourceB663 + difference 5 1) sourceC663) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2263) := by
    have ha : (tripleCharges (sourceA663 + difference 1 5) (sourceB663 + difference 5 1) sourceC663) = raw11271 := by
      apply Matrix.ext; unfold tripleCharges sourceA663 sourceB663 sourceC663 difference raw11271; decide +kernel
    rw [ha]
    exact (canonical11271 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA663 + difference 2 0) (sourceB663 + difference 0 2) sourceC663) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1724) := by
    have ha : (tripleCharges (sourceA663 + difference 2 0) (sourceB663 + difference 0 2) sourceC663) = raw11272 := by
      apply Matrix.ext; unfold tripleCharges sourceA663 sourceB663 sourceC663 difference raw11272; decide +kernel
    rw [ha]
    exact (canonical11272 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA663 + difference 2 1) (sourceB663 + difference 1 2) sourceC663) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2260) := by
    have ha : (tripleCharges (sourceA663 + difference 2 1) (sourceB663 + difference 1 2) sourceC663) = raw11273 := by
      apply Matrix.ext; unfold tripleCharges sourceA663 sourceB663 sourceC663 difference raw11273; decide +kernel
    rw [ha]
    exact (canonical11273 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA663 + difference 2 3) (sourceB663 + difference 3 2) sourceC663) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2202) := by
    have ha : (tripleCharges (sourceA663 + difference 2 3) (sourceB663 + difference 3 2) sourceC663) = raw11274 := by
      apply Matrix.ext; unfold tripleCharges sourceA663 sourceB663 sourceC663 difference raw11274; decide +kernel
    rw [ha]
    exact (canonical11274 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA663 + difference 2 4) (sourceB663 + difference 4 2) sourceC663) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2291) := by
    have ha : (tripleCharges (sourceA663 + difference 2 4) (sourceB663 + difference 4 2) sourceC663) = raw11275 := by
      apply Matrix.ext; unfold tripleCharges sourceA663 sourceB663 sourceC663 difference raw11275; decide +kernel
    rw [ha]
    exact (canonical11275 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA663 + difference 2 5) (sourceB663 + difference 5 2) sourceC663) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2263) := by
    have ha : (tripleCharges (sourceA663 + difference 2 5) (sourceB663 + difference 5 2) sourceC663) = raw11276 := by
      apply Matrix.ext; unfold tripleCharges sourceA663 sourceB663 sourceC663 difference raw11276; decide +kernel
    rw [ha]
    exact (canonical11276 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA663 + difference 3 0) (sourceB663 + difference 0 3) sourceC663) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1705) := by
    have ha : (tripleCharges (sourceA663 + difference 3 0) (sourceB663 + difference 0 3) sourceC663) = raw11277 := by
      apply Matrix.ext; unfold tripleCharges sourceA663 sourceB663 sourceC663 difference raw11277; decide +kernel
    rw [ha]
    exact (canonical11277 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA663 + difference 3 1) (sourceB663 + difference 1 3) sourceC663) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2240) := by
    have ha : (tripleCharges (sourceA663 + difference 3 1) (sourceB663 + difference 1 3) sourceC663) = raw11278 := by
      apply Matrix.ext; unfold tripleCharges sourceA663 sourceB663 sourceC663 difference raw11278; decide +kernel
    rw [ha]
    exact (canonical11278 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA663 + difference 3 2) (sourceB663 + difference 2 3) sourceC663) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2240) := by
    have ha : (tripleCharges (sourceA663 + difference 3 2) (sourceB663 + difference 2 3) sourceC663) = raw11279 := by
      apply Matrix.ext; unfold tripleCharges sourceA663 sourceB663 sourceC663 difference raw11279; decide +kernel
    rw [ha]
    exact (canonical11279 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA663 + difference 3 4) (sourceB663 + difference 4 3) sourceC663) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2262) := by
    have ha : (tripleCharges (sourceA663 + difference 3 4) (sourceB663 + difference 4 3) sourceC663) = raw11280 := by
      apply Matrix.ext; unfold tripleCharges sourceA663 sourceB663 sourceC663 difference raw11280; decide +kernel
    rw [ha]
    exact (canonical11280 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA663 + difference 3 5) (sourceB663 + difference 5 3) sourceC663) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2243) := by
    have ha : (tripleCharges (sourceA663 + difference 3 5) (sourceB663 + difference 5 3) sourceC663) = raw11281 := by
      apply Matrix.ext; unfold tripleCharges sourceA663 sourceB663 sourceC663 difference raw11281; decide +kernel
    rw [ha]
    exact (canonical11281 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA663 + difference 4 0) (sourceB663 + difference 0 4) sourceC663) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1736) := by
    have ha : (tripleCharges (sourceA663 + difference 4 0) (sourceB663 + difference 0 4) sourceC663) = raw11282 := by
      apply Matrix.ext; unfold tripleCharges sourceA663 sourceB663 sourceC663 difference raw11282; decide +kernel
    rw [ha]
    exact (canonical11282 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA663 + difference 4 1) (sourceB663 + difference 1 4) sourceC663) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2274) := by
    have ha : (tripleCharges (sourceA663 + difference 4 1) (sourceB663 + difference 1 4) sourceC663) = raw11283 := by
      apply Matrix.ext; unfold tripleCharges sourceA663 sourceB663 sourceC663 difference raw11283; decide +kernel
    rw [ha]
    exact (canonical11283 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA663 + difference 4 2) (sourceB663 + difference 2 4) sourceC663) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2274) := by
    have ha : (tripleCharges (sourceA663 + difference 4 2) (sourceB663 + difference 2 4) sourceC663) = raw11284 := by
      apply Matrix.ext; unfold tripleCharges sourceA663 sourceB663 sourceC663 difference raw11284; decide +kernel
    rw [ha]
    exact (canonical11284 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA663 + difference 4 3) (sourceB663 + difference 3 4) sourceC663) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2213) := by
    have ha : (tripleCharges (sourceA663 + difference 4 3) (sourceB663 + difference 3 4) sourceC663) = raw11285 := by
      apply Matrix.ext; unfold tripleCharges sourceA663 sourceB663 sourceC663 difference raw11285; decide +kernel
    rw [ha]
    exact (canonical11285 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA663 + difference 4 5) (sourceB663 + difference 5 4) sourceC663) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2277) := by
    have ha : (tripleCharges (sourceA663 + difference 4 5) (sourceB663 + difference 5 4) sourceC663) = raw11286 := by
      apply Matrix.ext; unfold tripleCharges sourceA663 sourceB663 sourceC663 difference raw11286; decide +kernel
    rw [ha]
    exact (canonical11286 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA663 + difference 5 0) (sourceB663 + difference 0 5) sourceC663) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1723) := by
    have ha : (tripleCharges (sourceA663 + difference 5 0) (sourceB663 + difference 0 5) sourceC663) = raw11287 := by
      apply Matrix.ext; unfold tripleCharges sourceA663 sourceB663 sourceC663 difference raw11287; decide +kernel
    rw [ha]
    exact (canonical11287 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA663 + difference 5 1) (sourceB663 + difference 1 5) sourceC663) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2259) := by
    have ha : (tripleCharges (sourceA663 + difference 5 1) (sourceB663 + difference 1 5) sourceC663) = raw11288 := by
      apply Matrix.ext; unfold tripleCharges sourceA663 sourceB663 sourceC663 difference raw11288; decide +kernel
    rw [ha]
    exact (canonical11288 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA663 + difference 5 2) (sourceB663 + difference 2 5) sourceC663) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2259) := by
    have ha : (tripleCharges (sourceA663 + difference 5 2) (sourceB663 + difference 2 5) sourceC663) = raw11289 := by
      apply Matrix.ext; unfold tripleCharges sourceA663 sourceB663 sourceC663 difference raw11289; decide +kernel
    rw [ha]
    exact (canonical11289 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA663 + difference 5 3) (sourceB663 + difference 3 5) sourceC663) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2201) := by
    have ha : (tripleCharges (sourceA663 + difference 5 3) (sourceB663 + difference 3 5) sourceC663) = raw11290 := by
      apply Matrix.ext; unfold tripleCharges sourceA663 sourceB663 sourceC663 difference raw11290; decide +kernel
    rw [ha]
    exact (canonical11290 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA663 + difference 5 4) (sourceB663 + difference 4 5) sourceC663) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2290) := by
    have ha : (tripleCharges (sourceA663 + difference 5 4) (sourceB663 + difference 4 5) sourceC663) = raw11291 := by
      apply Matrix.ext; unfold tripleCharges sourceA663 sourceB663 sourceC663 difference raw11291; decide +kernel
    rw [ha]
    exact (canonical11291 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA663 sourceB663 sourceC663
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm663, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq664 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm664 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA664 + difference 0 0) (sourceB664 + difference 0 0) sourceC664) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2244) := by
    have ha : (tripleCharges (sourceA664 + difference 0 0) (sourceB664 + difference 0 0) sourceC664) = raw11292 := by
      apply Matrix.ext; unfold tripleCharges sourceA664 sourceB664 sourceC664 difference raw11292; decide +kernel
    rw [ha]
    exact (canonical11292 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA664 + difference 0 1) (sourceB664 + difference 1 0) sourceC664) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3572) := by
    have ha : (tripleCharges (sourceA664 + difference 0 1) (sourceB664 + difference 1 0) sourceC664) = raw11293 := by
      apply Matrix.ext; unfold tripleCharges sourceA664 sourceB664 sourceC664 difference raw11293; decide +kernel
    rw [ha]
    exact (canonical11293 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA664 + difference 0 2) (sourceB664 + difference 2 0) sourceC664) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3572) := by
    have ha : (tripleCharges (sourceA664 + difference 0 2) (sourceB664 + difference 2 0) sourceC664) = raw11294 := by
      apply Matrix.ext; unfold tripleCharges sourceA664 sourceB664 sourceC664 difference raw11294; decide +kernel
    rw [ha]
    exact (canonical11294 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA664 + difference 0 3) (sourceB664 + difference 3 0) sourceC664) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3525) := by
    have ha : (tripleCharges (sourceA664 + difference 0 3) (sourceB664 + difference 3 0) sourceC664) = raw11295 := by
      apply Matrix.ext; unfold tripleCharges sourceA664 sourceB664 sourceC664 difference raw11295; decide +kernel
    rw [ha]
    exact (canonical11295 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA664 + difference 0 4) (sourceB664 + difference 4 0) sourceC664) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3623) := by
    have ha : (tripleCharges (sourceA664 + difference 0 4) (sourceB664 + difference 4 0) sourceC664) = raw11296 := by
      apply Matrix.ext; unfold tripleCharges sourceA664 sourceB664 sourceC664 difference raw11296; decide +kernel
    rw [ha]
    exact (canonical11296 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA664 + difference 0 5) (sourceB664 + difference 5 0) sourceC664) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3622) := by
    have ha : (tripleCharges (sourceA664 + difference 0 5) (sourceB664 + difference 5 0) sourceC664) = raw11297 := by
      apply Matrix.ext; unfold tripleCharges sourceA664 sourceB664 sourceC664 difference raw11297; decide +kernel
    rw [ha]
    exact (canonical11297 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA664 + sourceB664) sourceC664) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4083) := by
    have ha : (doubleCharges (sourceA664 + sourceB664) sourceC664) = raw11298 := by
      apply Matrix.ext; unfold doubleCharges sourceA664 sourceB664 sourceC664 raw11298; decide +kernel
    rw [ha]
    exact (canonical11298 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA664 sourceB664 sourceC664
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm664, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq665 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm665 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA665 + difference 0 0) (sourceB665 + difference 0 0) sourceC665) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2244) := by
    have ha : (tripleCharges (sourceA665 + difference 0 0) (sourceB665 + difference 0 0) sourceC665) = raw11292 := by
      apply Matrix.ext; unfold tripleCharges sourceA665 sourceB665 sourceC665 difference raw11292; decide +kernel
    rw [ha]
    exact (canonical11292 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA665 + difference 1 0) (sourceB665 + difference 0 1) sourceC665) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1041) := by
    have ha : (tripleCharges (sourceA665 + difference 1 0) (sourceB665 + difference 0 1) sourceC665) = raw11299 := by
      apply Matrix.ext; unfold tripleCharges sourceA665 sourceB665 sourceC665 difference raw11299; decide +kernel
    rw [ha]
    exact (canonical11299 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA665 + difference 2 0) (sourceB665 + difference 0 2) sourceC665) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1041) := by
    have ha : (tripleCharges (sourceA665 + difference 2 0) (sourceB665 + difference 0 2) sourceC665) = raw11300 := by
      apply Matrix.ext; unfold tripleCharges sourceA665 sourceB665 sourceC665 difference raw11300; decide +kernel
    rw [ha]
    exact (canonical11300 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA665 + difference 3 0) (sourceB665 + difference 0 3) sourceC665) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1020) := by
    have ha : (tripleCharges (sourceA665 + difference 3 0) (sourceB665 + difference 0 3) sourceC665) = raw11301 := by
      apply Matrix.ext; unfold tripleCharges sourceA665 sourceB665 sourceC665 difference raw11301; decide +kernel
    rw [ha]
    exact (canonical11301 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA665 + difference 4 0) (sourceB665 + difference 0 4) sourceC665) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1026) := by
    have ha : (tripleCharges (sourceA665 + difference 4 0) (sourceB665 + difference 0 4) sourceC665) = raw11302 := by
      apply Matrix.ext; unfold tripleCharges sourceA665 sourceB665 sourceC665 difference raw11302; decide +kernel
    rw [ha]
    exact (canonical11302 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA665 + difference 5 0) (sourceB665 + difference 0 5) sourceC665) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1022) := by
    have ha : (tripleCharges (sourceA665 + difference 5 0) (sourceB665 + difference 0 5) sourceC665) = raw11303 := by
      apply Matrix.ext; unfold tripleCharges sourceA665 sourceB665 sourceC665 difference raw11303; decide +kernel
    rw [ha]
    exact (canonical11303 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA665 + sourceB665) sourceC665) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4083) := by
    have ha : (doubleCharges (sourceA665 + sourceB665) sourceC665) = raw11298 := by
      apply Matrix.ext; unfold doubleCharges sourceA665 sourceB665 sourceC665 raw11298; decide +kernel
    rw [ha]
    exact (canonical11298 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA665 sourceB665 sourceC665
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm665, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq666 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm666 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA666 + difference 1 0) (sourceB666 + difference 0 1) sourceC666) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1041) := by
    have ha : (tripleCharges (sourceA666 + difference 1 0) (sourceB666 + difference 0 1) sourceC666) = raw11299 := by
      apply Matrix.ext; unfold tripleCharges sourceA666 sourceB666 sourceC666 difference raw11299; decide +kernel
    rw [ha]
    exact (canonical11299 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA666 + difference 1 1) (sourceB666 + difference 1 1) sourceC666) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2244) := by
    have ha : (tripleCharges (sourceA666 + difference 1 1) (sourceB666 + difference 1 1) sourceC666) = raw11292 := by
      apply Matrix.ext; unfold tripleCharges sourceA666 sourceB666 sourceC666 difference raw11292; decide +kernel
    rw [ha]
    exact (canonical11292 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA666 + difference 1 2) (sourceB666 + difference 2 1) sourceC666) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2107) := by
    have ha : (tripleCharges (sourceA666 + difference 1 2) (sourceB666 + difference 2 1) sourceC666) = raw11304 := by
      apply Matrix.ext; unfold tripleCharges sourceA666 sourceB666 sourceC666 difference raw11304; decide +kernel
    rw [ha]
    exact (canonical11304 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA666 + difference 1 3) (sourceB666 + difference 3 1) sourceC666) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2020) := by
    have ha : (tripleCharges (sourceA666 + difference 1 3) (sourceB666 + difference 3 1) sourceC666) = raw11305 := by
      apply Matrix.ext; unfold tripleCharges sourceA666 sourceB666 sourceC666 difference raw11305; decide +kernel
    rw [ha]
    exact (canonical11305 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA666 + difference 1 4) (sourceB666 + difference 4 1) sourceC666) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2265) := by
    have ha : (tripleCharges (sourceA666 + difference 1 4) (sourceB666 + difference 4 1) sourceC666) = raw11306 := by
      apply Matrix.ext; unfold tripleCharges sourceA666 sourceB666 sourceC666 difference raw11306; decide +kernel
    rw [ha]
    exact (canonical11306 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA666 + difference 1 5) (sourceB666 + difference 5 1) sourceC666) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2263) := by
    have ha : (tripleCharges (sourceA666 + difference 1 5) (sourceB666 + difference 5 1) sourceC666) = raw11307 := by
      apply Matrix.ext; unfold tripleCharges sourceA666 sourceB666 sourceC666 difference raw11307; decide +kernel
    rw [ha]
    exact (canonical11307 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA666 + sourceB666) sourceC666) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4083) := by
    have ha : (doubleCharges (sourceA666 + sourceB666) sourceC666) = raw11298 := by
      apply Matrix.ext; unfold doubleCharges sourceA666 sourceB666 sourceC666 raw11298; decide +kernel
    rw [ha]
    exact (canonical11298 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA666 sourceB666 sourceC666
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm666, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic35
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reindexCheck560 : Integer.Sparse.reindex keyMap MixedData.row560 = numericRow560 := by decide +kernel

theorem numericCheck560 (x : Master → ℝ) : Integer.Sparse.eval numericRow560 x =
    (1 : ℝ) * reducedSource560 x := by
  norm_num [numericRow560, reducedSource560, Integer.Sparse.eval, Sparse.eval, nodeValue1044, nodeValue2023, nodeValue2110, nodeValue2245, nodeValue2263, nodeValue4083]

theorem reindexCheck561 : Integer.Sparse.reindex keyMap MixedData.row561 = numericRow561 := by decide +kernel

theorem numericCheck561 (x : Master → ℝ) : Integer.Sparse.eval numericRow561 x =
    (1 : ℝ) * reducedSource561 x := by
  norm_num [numericRow561, reducedSource561, Integer.Sparse.eval, Sparse.eval, nodeValue2089, nodeValue2092, nodeValue2094, nodeValue2110, nodeValue2245, nodeValue3573, nodeValue4083]

theorem reindexCheck562 : Integer.Sparse.reindex keyMap MixedData.row562 = numericRow562 := by decide +kernel

theorem numericCheck562 (x : Master → ℝ) : Integer.Sparse.eval numericRow562 x =
    (1 : ℝ) * reducedSource562 x := by
  norm_num [numericRow562, reducedSource562, Integer.Sparse.eval, Sparse.eval, nodeValue2010, nodeValue2012, nodeValue2023, nodeValue2245, nodeValue3526, nodeValue4083]

theorem reindexCheck563 : Integer.Sparse.reindex keyMap MixedData.row563 = numericRow563 := by decide +kernel

theorem numericCheck563 (x : Master → ℝ) : Integer.Sparse.eval numericRow563 x =
    (1 : ℝ) * reducedSource563 x := by
  norm_num [numericRow563, reducedSource563, Integer.Sparse.eval, Sparse.eval, nodeValue1026, nodeValue2012, nodeValue2094, nodeValue2244, nodeValue2245, nodeValue4083]

theorem reindexCheck569 : Integer.Sparse.reindex keyMap MixedData.row569 = numericRow569 := by decide +kernel

theorem numericCheck569 (x : Master → ℝ) : Integer.Sparse.eval numericRow569 x =
    (1 : ℝ) * reducedSource569 x := by
  norm_num [numericRow569, reducedSource569, Integer.Sparse.eval, Sparse.eval, nodeValue1056, nodeValue1057, nodeValue1058, nodeValue1079, nodeValue2277, nodeValue4084]

theorem reindexCheck572 : Integer.Sparse.reindex keyMap MixedData.row572 = numericRow572 := by decide +kernel

theorem numericCheck572 (x : Master → ℝ) : Integer.Sparse.eval numericRow572 x =
    (864 : ℝ) * reducedSource572 x := by
  norm_num [numericRow572, reducedSource572, Integer.Sparse.eval, Sparse.eval, nodeValue1705, nodeValue1723, nodeValue1724, nodeValue1736, nodeValue2201, nodeValue2202, nodeValue2213, nodeValue2240, nodeValue2243, nodeValue2259, nodeValue2260, nodeValue2262, nodeValue2263, nodeValue2274, nodeValue2277, nodeValue2290, nodeValue2291, nodeValue2720, nodeValue2763, nodeValue2766, nodeValue2784]
  ring

theorem reindexCheck573 : Integer.Sparse.reindex keyMap MixedData.row573 = numericRow573 := by decide +kernel

theorem numericCheck573 (x : Master → ℝ) : Integer.Sparse.eval numericRow573 x =
    (1 : ℝ) * reducedSource573 x := by
  norm_num [numericRow573, reducedSource573, Integer.Sparse.eval, Sparse.eval, nodeValue2244, nodeValue3525, nodeValue3572, nodeValue3622, nodeValue3623, nodeValue4083]

theorem reindexCheck574 : Integer.Sparse.reindex keyMap MixedData.row574 = numericRow574 := by decide +kernel

theorem numericCheck574 (x : Master → ℝ) : Integer.Sparse.eval numericRow574 x =
    (1 : ℝ) * reducedSource574 x := by
  norm_num [numericRow574, reducedSource574, Integer.Sparse.eval, Sparse.eval, nodeValue1020, nodeValue1022, nodeValue1026, nodeValue1041, nodeValue2244, nodeValue4083]

theorem reindexCheck575 : Integer.Sparse.reindex keyMap MixedData.row575 = numericRow575 := by decide +kernel

theorem numericCheck575 (x : Master → ℝ) : Integer.Sparse.eval numericRow575 x =
    (1 : ℝ) * reducedSource575 x := by
  norm_num [numericRow575, reducedSource575, Integer.Sparse.eval, Sparse.eval, nodeValue1041, nodeValue2020, nodeValue2107, nodeValue2244, nodeValue2263, nodeValue2265, nodeValue4083]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Rows35
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero560 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource560 (mixedVector B) = 0 := by
  have h1044 : mixedVector B (Sum.inr 1044) = Sparse.eval nodeValue1044 (mixedVector B) := by
    change mixedMoment B node1044 node1044Labels = _
    exact sound1044 B hB hF
  have h2023 : mixedVector B (Sum.inr 2023) = Sparse.eval nodeValue2023 (mixedVector B) := by
    change mixedMoment B node2023 node2023Labels = _
    exact sound2023 B hB hF
  have h2110 : mixedVector B (Sum.inr 2110) = Sparse.eval nodeValue2110 (mixedVector B) := by
    change mixedMoment B node2110 node2110Labels = _
    exact sound2110 B hB hF
  have h2245 : mixedVector B (Sum.inr 2245) = Sparse.eval nodeValue2245 (mixedVector B) := by
    change mixedMoment B node2245 node2245Labels = _
    exact sound2245 B hB hF
  have h2263 : mixedVector B (Sum.inr 2263) = Sparse.eval nodeValue2263 (mixedVector B) := by
    change mixedMoment B node2263 node2263Labels = _
    exact sound2263 B hB hF
  have h4083 : mixedVector B (Sum.inr 4083) = Sparse.eval nodeValue4083 (mixedVector B) := by
    change mixedMoment B node4083 node4083Labels = _
    exact sound4083 B hB hF
  simpa only [sourceForm651, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1044, h2023, h2110, h2245, h2263, h4083, reducedSource560] using sourceEq651 B hB

theorem rowSound560 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row560 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck560, numericCheck560, reducedZero560 B hB hF, mul_zero]

theorem reducedZero561 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource561 (mixedVector B) = 0 := by
  have h2089 : mixedVector B (Sum.inr 2089) = Sparse.eval nodeValue2089 (mixedVector B) := by
    change mixedMoment B node2089 node2089Labels = _
    exact sound2089 B hB hF
  have h2092 : mixedVector B (Sum.inr 2092) = Sparse.eval nodeValue2092 (mixedVector B) := by
    change mixedMoment B node2092 node2092Labels = _
    exact sound2092 B hB hF
  have h2094 : mixedVector B (Sum.inr 2094) = Sparse.eval nodeValue2094 (mixedVector B) := by
    change mixedMoment B node2094 node2094Labels = _
    exact sound2094 B hB hF
  have h2110 : mixedVector B (Sum.inr 2110) = Sparse.eval nodeValue2110 (mixedVector B) := by
    change mixedMoment B node2110 node2110Labels = _
    exact sound2110 B hB hF
  have h2245 : mixedVector B (Sum.inr 2245) = Sparse.eval nodeValue2245 (mixedVector B) := by
    change mixedMoment B node2245 node2245Labels = _
    exact sound2245 B hB hF
  have h3573 : mixedVector B (Sum.inr 3573) = Sparse.eval nodeValue3573 (mixedVector B) := by
    change mixedMoment B node3573 node3573Labels = _
    exact sound3573 B hB hF
  have h4083 : mixedVector B (Sum.inr 4083) = Sparse.eval nodeValue4083 (mixedVector B) := by
    change mixedMoment B node4083 node4083Labels = _
    exact sound4083 B hB hF
  simpa only [sourceForm652, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2089, h2092, h2094, h2110, h2245, h3573, h4083, reducedSource561] using sourceEq652 B hB

theorem rowSound561 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row561 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck561, numericCheck561, reducedZero561 B hB hF, mul_zero]

theorem reducedZero562 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource562 (mixedVector B) = 0 := by
  have h2010 : mixedVector B (Sum.inr 2010) = Sparse.eval nodeValue2010 (mixedVector B) := by
    change mixedMoment B node2010 node2010Labels = _
    exact sound2010 B hB hF
  have h2012 : mixedVector B (Sum.inr 2012) = Sparse.eval nodeValue2012 (mixedVector B) := by
    change mixedMoment B node2012 node2012Labels = _
    exact sound2012 B hB hF
  have h2023 : mixedVector B (Sum.inr 2023) = Sparse.eval nodeValue2023 (mixedVector B) := by
    change mixedMoment B node2023 node2023Labels = _
    exact sound2023 B hB hF
  have h2245 : mixedVector B (Sum.inr 2245) = Sparse.eval nodeValue2245 (mixedVector B) := by
    change mixedMoment B node2245 node2245Labels = _
    exact sound2245 B hB hF
  have h3526 : mixedVector B (Sum.inr 3526) = Sparse.eval nodeValue3526 (mixedVector B) := by
    change mixedMoment B node3526 node3526Labels = _
    exact sound3526 B hB hF
  have h4083 : mixedVector B (Sum.inr 4083) = Sparse.eval nodeValue4083 (mixedVector B) := by
    change mixedMoment B node4083 node4083Labels = _
    exact sound4083 B hB hF
  simpa only [sourceForm653, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2010, h2012, h2023, h2245, h3526, h4083, reducedSource562] using sourceEq653 B hB

theorem rowSound562 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row562 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck562, numericCheck562, reducedZero562 B hB hF, mul_zero]

theorem reducedZero563 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource563 (mixedVector B) = 0 := by
  have h1026 : mixedVector B (Sum.inr 1026) = Sparse.eval nodeValue1026 (mixedVector B) := by
    change mixedMoment B node1026 node1026Labels = _
    exact sound1026 B hB hF
  have h2012 : mixedVector B (Sum.inr 2012) = Sparse.eval nodeValue2012 (mixedVector B) := by
    change mixedMoment B node2012 node2012Labels = _
    exact sound2012 B hB hF
  have h2094 : mixedVector B (Sum.inr 2094) = Sparse.eval nodeValue2094 (mixedVector B) := by
    change mixedMoment B node2094 node2094Labels = _
    exact sound2094 B hB hF
  have h2244 : mixedVector B (Sum.inr 2244) = Sparse.eval nodeValue2244 (mixedVector B) := by
    change mixedMoment B node2244 node2244Labels = _
    exact sound2244 B hB hF
  have h2245 : mixedVector B (Sum.inr 2245) = Sparse.eval nodeValue2245 (mixedVector B) := by
    change mixedMoment B node2245 node2245Labels = _
    exact sound2245 B hB hF
  have h4083 : mixedVector B (Sum.inr 4083) = Sparse.eval nodeValue4083 (mixedVector B) := by
    change mixedMoment B node4083 node4083Labels = _
    exact sound4083 B hB hF
  simpa only [sourceForm654, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1026, h2012, h2094, h2244, h2245, h4083, reducedSource563] using sourceEq654 B hB

theorem rowSound563 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row563 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck563, numericCheck563, reducedZero563 B hB hF, mul_zero]

theorem reducedZero569 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource569 (mixedVector B) = 0 := by
  have h1056 : mixedVector B (Sum.inr 1056) = Sparse.eval nodeValue1056 (mixedVector B) := by
    change mixedMoment B node1056 node1056Labels = _
    exact sound1056 B hB hF
  have h1057 : mixedVector B (Sum.inr 1057) = Sparse.eval nodeValue1057 (mixedVector B) := by
    change mixedMoment B node1057 node1057Labels = _
    exact sound1057 B hB hF
  have h1058 : mixedVector B (Sum.inr 1058) = Sparse.eval nodeValue1058 (mixedVector B) := by
    change mixedMoment B node1058 node1058Labels = _
    exact sound1058 B hB hF
  have h1079 : mixedVector B (Sum.inr 1079) = Sparse.eval nodeValue1079 (mixedVector B) := by
    change mixedMoment B node1079 node1079Labels = _
    exact sound1079 B hB hF
  have h2277 : mixedVector B (Sum.inr 2277) = Sparse.eval nodeValue2277 (mixedVector B) := by
    change mixedMoment B node2277 node2277Labels = _
    exact sound2277 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm660, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1056, h1057, h1058, h1079, h2277, h4084, reducedSource569] using sourceEq660 B hB

theorem rowSound569 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row569 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck569, numericCheck569, reducedZero569 B hB hF, mul_zero]

theorem reducedZero572 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource572 (mixedVector B) = 0 := by
  have h1705 : mixedVector B (Sum.inr 1705) = Sparse.eval nodeValue1705 (mixedVector B) := by
    change mixedMoment B node1705 node1705Labels = _
    exact sound1705 B hB hF
  have h1723 : mixedVector B (Sum.inr 1723) = Sparse.eval nodeValue1723 (mixedVector B) := by
    change mixedMoment B node1723 node1723Labels = _
    exact sound1723 B hB hF
  have h1724 : mixedVector B (Sum.inr 1724) = Sparse.eval nodeValue1724 (mixedVector B) := by
    change mixedMoment B node1724 node1724Labels = _
    exact sound1724 B hB hF
  have h1736 : mixedVector B (Sum.inr 1736) = Sparse.eval nodeValue1736 (mixedVector B) := by
    change mixedMoment B node1736 node1736Labels = _
    exact sound1736 B hB hF
  have h2201 : mixedVector B (Sum.inr 2201) = Sparse.eval nodeValue2201 (mixedVector B) := by
    change mixedMoment B node2201 node2201Labels = _
    exact sound2201 B hB hF
  have h2202 : mixedVector B (Sum.inr 2202) = Sparse.eval nodeValue2202 (mixedVector B) := by
    change mixedMoment B node2202 node2202Labels = _
    exact sound2202 B hB hF
  have h2213 : mixedVector B (Sum.inr 2213) = Sparse.eval nodeValue2213 (mixedVector B) := by
    change mixedMoment B node2213 node2213Labels = _
    exact sound2213 B hB hF
  have h2240 : mixedVector B (Sum.inr 2240) = Sparse.eval nodeValue2240 (mixedVector B) := by
    change mixedMoment B node2240 node2240Labels = _
    exact sound2240 B hB hF
  have h2243 : mixedVector B (Sum.inr 2243) = Sparse.eval nodeValue2243 (mixedVector B) := by
    change mixedMoment B node2243 node2243Labels = _
    exact sound2243 B hB hF
  have h2259 : mixedVector B (Sum.inr 2259) = Sparse.eval nodeValue2259 (mixedVector B) := by
    change mixedMoment B node2259 node2259Labels = _
    exact sound2259 B hB hF
  have h2260 : mixedVector B (Sum.inr 2260) = Sparse.eval nodeValue2260 (mixedVector B) := by
    change mixedMoment B node2260 node2260Labels = _
    exact sound2260 B hB hF
  have h2262 : mixedVector B (Sum.inr 2262) = Sparse.eval nodeValue2262 (mixedVector B) := by
    change mixedMoment B node2262 node2262Labels = _
    exact sound2262 B hB hF
  have h2263 : mixedVector B (Sum.inr 2263) = Sparse.eval nodeValue2263 (mixedVector B) := by
    change mixedMoment B node2263 node2263Labels = _
    exact sound2263 B hB hF
  have h2274 : mixedVector B (Sum.inr 2274) = Sparse.eval nodeValue2274 (mixedVector B) := by
    change mixedMoment B node2274 node2274Labels = _
    exact sound2274 B hB hF
  have h2277 : mixedVector B (Sum.inr 2277) = Sparse.eval nodeValue2277 (mixedVector B) := by
    change mixedMoment B node2277 node2277Labels = _
    exact sound2277 B hB hF
  have h2290 : mixedVector B (Sum.inr 2290) = Sparse.eval nodeValue2290 (mixedVector B) := by
    change mixedMoment B node2290 node2290Labels = _
    exact sound2290 B hB hF
  have h2291 : mixedVector B (Sum.inr 2291) = Sparse.eval nodeValue2291 (mixedVector B) := by
    change mixedMoment B node2291 node2291Labels = _
    exact sound2291 B hB hF
  have h2720 : mixedVector B (Sum.inr 2720) = Sparse.eval nodeValue2720 (mixedVector B) := by
    change mixedMoment B node2720 node2720Labels = _
    exact sound2720 B hB hF
  have h2763 : mixedVector B (Sum.inr 2763) = Sparse.eval nodeValue2763 (mixedVector B) := by
    change mixedMoment B node2763 node2763Labels = _
    exact sound2763 B hB hF
  have h2766 : mixedVector B (Sum.inr 2766) = Sparse.eval nodeValue2766 (mixedVector B) := by
    change mixedMoment B node2766 node2766Labels = _
    exact sound2766_e B hB hF
  have h2784 : mixedVector B (Sum.inr 2784) = Sparse.eval nodeValue2784 (mixedVector B) := by
    change mixedMoment B node2784 node2784Labels = _
    exact sound2784 B hB hF
  simpa only [sourceForm663, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1705, h1723, h1724, h1736, h2201, h2202, h2213, h2240, h2243, h2259, h2260, h2262, h2263, h2274, h2277, h2290, h2291, h2720, h2763, h2766, h2784, reducedSource572] using sourceEq663 B hB

theorem rowSound572 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row572 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck572, numericCheck572, reducedZero572 B hB hF, mul_zero]

theorem reducedZero573 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource573 (mixedVector B) = 0 := by
  have h2244 : mixedVector B (Sum.inr 2244) = Sparse.eval nodeValue2244 (mixedVector B) := by
    change mixedMoment B node2244 node2244Labels = _
    exact sound2244 B hB hF
  have h3525 : mixedVector B (Sum.inr 3525) = Sparse.eval nodeValue3525 (mixedVector B) := by
    change mixedMoment B node3525 node3525Labels = _
    exact sound3525 B hB hF
  have h3572 : mixedVector B (Sum.inr 3572) = Sparse.eval nodeValue3572 (mixedVector B) := by
    change mixedMoment B node3572 node3572Labels = _
    exact sound3572 B hB hF
  have h3622 : mixedVector B (Sum.inr 3622) = Sparse.eval nodeValue3622 (mixedVector B) := by
    change mixedMoment B node3622 node3622Labels = _
    exact sound3622 B hB hF
  have h3623 : mixedVector B (Sum.inr 3623) = Sparse.eval nodeValue3623 (mixedVector B) := by
    change mixedMoment B node3623 node3623Labels = _
    exact sound3623 B hB hF
  have h4083 : mixedVector B (Sum.inr 4083) = Sparse.eval nodeValue4083 (mixedVector B) := by
    change mixedMoment B node4083 node4083Labels = _
    exact sound4083 B hB hF
  simpa only [sourceForm664, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2244, h3525, h3572, h3622, h3623, h4083, reducedSource573] using sourceEq664 B hB

theorem rowSound573 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row573 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck573, numericCheck573, reducedZero573 B hB hF, mul_zero]

theorem reducedZero574 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource574 (mixedVector B) = 0 := by
  have h1020 : mixedVector B (Sum.inr 1020) = Sparse.eval nodeValue1020 (mixedVector B) := by
    change mixedMoment B node1020 node1020Labels = _
    exact sound1020 B hB hF
  have h1022 : mixedVector B (Sum.inr 1022) = Sparse.eval nodeValue1022 (mixedVector B) := by
    change mixedMoment B node1022 node1022Labels = _
    exact sound1022 B hB hF
  have h1026 : mixedVector B (Sum.inr 1026) = Sparse.eval nodeValue1026 (mixedVector B) := by
    change mixedMoment B node1026 node1026Labels = _
    exact sound1026 B hB hF
  have h1041 : mixedVector B (Sum.inr 1041) = Sparse.eval nodeValue1041 (mixedVector B) := by
    change mixedMoment B node1041 node1041Labels = _
    exact sound1041 B hB hF
  have h2244 : mixedVector B (Sum.inr 2244) = Sparse.eval nodeValue2244 (mixedVector B) := by
    change mixedMoment B node2244 node2244Labels = _
    exact sound2244 B hB hF
  have h4083 : mixedVector B (Sum.inr 4083) = Sparse.eval nodeValue4083 (mixedVector B) := by
    change mixedMoment B node4083 node4083Labels = _
    exact sound4083 B hB hF
  simpa only [sourceForm665, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1020, h1022, h1026, h1041, h2244, h4083, reducedSource574] using sourceEq665 B hB

theorem rowSound574 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row574 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck574, numericCheck574, reducedZero574 B hB hF, mul_zero]

theorem reducedZero575 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource575 (mixedVector B) = 0 := by
  have h1041 : mixedVector B (Sum.inr 1041) = Sparse.eval nodeValue1041 (mixedVector B) := by
    change mixedMoment B node1041 node1041Labels = _
    exact sound1041 B hB hF
  have h2020 : mixedVector B (Sum.inr 2020) = Sparse.eval nodeValue2020 (mixedVector B) := by
    change mixedMoment B node2020 node2020Labels = _
    exact sound2020 B hB hF
  have h2107 : mixedVector B (Sum.inr 2107) = Sparse.eval nodeValue2107 (mixedVector B) := by
    change mixedMoment B node2107 node2107Labels = _
    exact sound2107 B hB hF
  have h2244 : mixedVector B (Sum.inr 2244) = Sparse.eval nodeValue2244 (mixedVector B) := by
    change mixedMoment B node2244 node2244Labels = _
    exact sound2244 B hB hF
  have h2263 : mixedVector B (Sum.inr 2263) = Sparse.eval nodeValue2263 (mixedVector B) := by
    change mixedMoment B node2263 node2263Labels = _
    exact sound2263 B hB hF
  have h2265 : mixedVector B (Sum.inr 2265) = Sparse.eval nodeValue2265 (mixedVector B) := by
    change mixedMoment B node2265 node2265Labels = _
    exact sound2265 B hB hF
  have h4083 : mixedVector B (Sum.inr 4083) = Sparse.eval nodeValue4083 (mixedVector B) := by
    change mixedMoment B node4083 node4083Labels = _
    exact sound4083 B hB hF
  simpa only [sourceForm666, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1041, h2020, h2107, h2244, h2263, h2265, h4083, reducedSource575] using sourceEq666 B hB

theorem rowSound575 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row575 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck575, numericCheck575, reducedZero575 B hB hF, mul_zero]

theorem sourceRowsAt560 : MixedData.sourceRows (560 : Fin 2425) =
    MixedData.row560 := by decide +kernel

theorem sourceRowsAt561 : MixedData.sourceRows (561 : Fin 2425) =
    MixedData.row561 := by decide +kernel

theorem sourceRowsAt562 : MixedData.sourceRows (562 : Fin 2425) =
    MixedData.row562 := by decide +kernel

theorem sourceRowsAt563 : MixedData.sourceRows (563 : Fin 2425) =
    MixedData.row563 := by decide +kernel

theorem sourceRowsAt564 : MixedData.sourceRows (564 : Fin 2425) =
    MixedData.row564 := by decide +kernel

theorem sourceRowsAt565 : MixedData.sourceRows (565 : Fin 2425) =
    MixedData.row565 := by decide +kernel

theorem sourceRowsAt566 : MixedData.sourceRows (566 : Fin 2425) =
    MixedData.row566 := by decide +kernel

theorem sourceRowsAt567 : MixedData.sourceRows (567 : Fin 2425) =
    MixedData.row567 := by decide +kernel

theorem sourceRowsAt568 : MixedData.sourceRows (568 : Fin 2425) =
    MixedData.row568 := by decide +kernel

theorem sourceRowsAt569 : MixedData.sourceRows (569 : Fin 2425) =
    MixedData.row569 := by decide +kernel

theorem sourceRowsAt570 : MixedData.sourceRows (570 : Fin 2425) =
    MixedData.row570 := by decide +kernel

theorem sourceRowsAt571 : MixedData.sourceRows (571 : Fin 2425) =
    MixedData.row571 := by decide +kernel

theorem sourceRowsAt572 : MixedData.sourceRows (572 : Fin 2425) =
    MixedData.row572 := by decide +kernel

theorem sourceRowsAt573 : MixedData.sourceRows (573 : Fin 2425) =
    MixedData.row573 := by decide +kernel

theorem sourceRowsAt574 : MixedData.sourceRows (574 : Fin 2425) =
    MixedData.row574 := by decide +kernel

theorem sourceRowsAt575 : MixedData.sourceRows (575 : Fin 2425) =
    MixedData.row575 := by decide +kernel

theorem chunkSound35_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) (k : Fin 2425)
    (hk : k.val / 16 = 35) :
    Integer.Sparse.eval (MixedData.sourceRows k) (numericVector B) = 0 := by
  have heq : k.val = 560 ∨ k.val = 561 ∨ k.val = 562 ∨ k.val = 563 ∨ k.val = 564 ∨ k.val = 565 ∨ k.val = 566 ∨ k.val = 567 ∨ k.val = 568 ∨ k.val = 569 ∨ k.val = 570 ∨ k.val = 571 ∨ k.val = 572 ∨ k.val = 573 ∨ k.val = 574 ∨ k.val = 575 := by omega
  rcases heq with h560 | h561 | h562 | h563 | h564 | h565 | h566 | h567 | h568 | h569 | h570 | h571 | h572 | h573 | h574 | h575
  · have he : k = (560 : Fin 2425) := Fin.ext h560
    subst k
    rw [sourceRowsAt560]
    exact rowSound560 B hB hF
  · have he : k = (561 : Fin 2425) := Fin.ext h561
    subst k
    rw [sourceRowsAt561]
    exact rowSound561 B hB hF
  · have he : k = (562 : Fin 2425) := Fin.ext h562
    subst k
    rw [sourceRowsAt562]
    exact rowSound562 B hB hF
  · have he : k = (563 : Fin 2425) := Fin.ext h563
    subst k
    rw [sourceRowsAt563]
    exact rowSound563 B hB hF
  · have he : k = (564 : Fin 2425) := Fin.ext h564
    subst k
    rw [sourceRowsAt564]
    exact rowSound564_e B hB hF
  · have he : k = (565 : Fin 2425) := Fin.ext h565
    subst k
    rw [sourceRowsAt565]
    exact rowSound565_e B hB hF
  · have he : k = (566 : Fin 2425) := Fin.ext h566
    subst k
    rw [sourceRowsAt566]
    exact rowSound566_e B hB hF
  · have he : k = (567 : Fin 2425) := Fin.ext h567
    subst k
    rw [sourceRowsAt567]
    exact rowSound567_e B hB hF
  · have he : k = (568 : Fin 2425) := Fin.ext h568
    subst k
    rw [sourceRowsAt568]
    exact rowSound568_e B hB hF
  · have he : k = (569 : Fin 2425) := Fin.ext h569
    subst k
    rw [sourceRowsAt569]
    exact rowSound569 B hB hF
  · have he : k = (570 : Fin 2425) := Fin.ext h570
    subst k
    rw [sourceRowsAt570]
    exact rowSound570_e B hB hF
  · have he : k = (571 : Fin 2425) := Fin.ext h571
    subst k
    rw [sourceRowsAt571]
    exact rowSound571_e B hB hF
  · have he : k = (572 : Fin 2425) := Fin.ext h572
    subst k
    rw [sourceRowsAt572]
    exact rowSound572 B hB hF
  · have he : k = (573 : Fin 2425) := Fin.ext h573
    subst k
    rw [sourceRowsAt573]
    exact rowSound573 B hB hF
  · have he : k = (574 : Fin 2425) := Fin.ext h574
    subst k
    rw [sourceRowsAt574]
    exact rowSound574 B hB hF
  · have he : k = (575 : Fin 2425) := Fin.ext h575
    subst k
    rw [sourceRowsAt575]
    exact rowSound575 B hB hF

end MUB6.Certificate.MixedSourceBridge

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedSourceBridge.chunkSound35_e_oai := @OAI.MUB6.Certificate.MixedSourceBridge.chunkSound35_e_oai
