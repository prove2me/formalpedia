-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedSourceBridge.chunkSound47_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T04:19:43.083541+00:00
-- url     : https://prove2.me/submissions/a4263793-aa82-4037-b916-e7e24999bd44

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E077
import Definitions.Def_OAIQ106E086
import Definitions.Def_OAIQ106E090
import Definitions.Def_OAIQ106E100
import Definitions.Def_OAIQ106E194
import Definitions.Def_OAIQ106E119
import Definitions.Def_OAIQ106E123
import Definitions.Def_OAIQ106E128
import Definitions.Def_OAIQ106E140
import Definitions.Def_OAIQ106E147
import Definitions.Def_OAIQ106E170
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound5434_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound758_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound759_e

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical112
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical14437 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14437 raw14437Labels = mixedMoment B node3803 node3803Labels := by
  calc
    _ = mixedMoment B node3803 node3803Labels := by rfl

theorem canonical14438 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14438 raw14438Labels = mixedMoment B node3788 node3788Labels := by
  calc
    mixedMoment B raw14438 raw14438Labels = mixedMoment B raw14438step0 raw14438step0Labels := by
      have ha : raw14438step0 = (fun i j => raw14438 (permutation472 i) (permutation4 j)) := by apply Matrix.ext; unfold raw14438step0 raw14438; decide +kernel
      have hl : raw14438step0Labels = raw14438Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14438 raw14438Labels permutation472 permutation4
    mixedMoment B raw14438step0 raw14438step0Labels = mixedMoment B raw14438step1 raw14438step1Labels := by
      have ha : raw14438step1 = -raw14438step0 := by apply Matrix.ext; change ∀ i j, raw14438step1 i j = -(raw14438step0 i j); unfold raw14438step1 raw14438step0; decide +kernel
      have hl : raw14438step1Labels = raw14438step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3788 node3788Labels := by rfl

theorem canonical14439 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14439 raw14439Labels = mixedMoment B node3691 node3691Labels := by
  calc
    mixedMoment B raw14439 raw14439Labels = mixedMoment B raw14439step0 raw14439step0Labels := by
      have ha : raw14439step0 = (fun i j => raw14439 (permutation472 i) (permutation4 j)) := by apply Matrix.ext; unfold raw14439step0 raw14439; decide +kernel
      have hl : raw14439step0Labels = raw14439Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14439 raw14439Labels permutation472 permutation4
    mixedMoment B raw14439step0 raw14439step0Labels = mixedMoment B raw14439step1 raw14439step1Labels := by
      have ha : raw14439step1 = -raw14439step0 := by apply Matrix.ext; change ∀ i j, raw14439step1 i j = -(raw14439step0 i j); unfold raw14439step1 raw14439step0; decide +kernel
      have hl : raw14439step1Labels = raw14439step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3691 node3691Labels := by rfl

theorem canonical14440 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14440 raw14440Labels = mixedMoment B node2481 node2481Labels := by
  calc
    mixedMoment B raw14440 raw14440Labels = mixedMoment B raw14440step0 raw14440step0Labels := by
      have ha : raw14440step0 = (fun i j => raw14440 (permutation472 i) (permutation4 j)) := by apply Matrix.ext; unfold raw14440step0 raw14440; decide +kernel
      have hl : raw14440step0Labels = raw14440Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14440 raw14440Labels permutation472 permutation4
    mixedMoment B raw14440step0 raw14440step0Labels = mixedMoment B raw14440step1 raw14440step1Labels := by
      have ha : raw14440step1 = -raw14440step0 := by apply Matrix.ext; change ∀ i j, raw14440step1 i j = -(raw14440step0 i j); unfold raw14440step1 raw14440step0; decide +kernel
      have hl : raw14440step1Labels = raw14440step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2481 node2481Labels := by rfl

theorem canonical14441 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14441 raw14441Labels = mixedMoment B node3809 node3809Labels := by
  calc
    mixedMoment B raw14441 raw14441Labels = mixedMoment B raw14441step0 raw14441step0Labels := by
      have hz : ∀ j, raw14441 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw14441step0 = (fun i j => raw14441 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw14441step0 raw14441; decide +kernel
      have hl : raw14441step0Labels = raw14441Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14441 raw14441Labels permutation520 hz
    mixedMoment B raw14441step0 raw14441step0Labels = mixedMoment B raw14441step1 raw14441step1Labels := by
      have ha : raw14441step1 = (fun i j => raw14441step0 (permutation118 i) (permutation4 j)) := by apply Matrix.ext; unfold raw14441step1 raw14441step0; decide +kernel
      have hl : raw14441step1Labels = raw14441step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14441step0 raw14441step0Labels permutation118 permutation4
    mixedMoment B raw14441step1 raw14441step1Labels = mixedMoment B raw14441step2 raw14441step2Labels := by
      have ha : raw14441step2 = -raw14441step1 := by apply Matrix.ext; change ∀ i j, raw14441step2 i j = -(raw14441step1 i j); unfold raw14441step2 raw14441step1; decide +kernel
      have hl : raw14441step2Labels = raw14441step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3809 node3809Labels := by rfl

theorem canonical14442 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14442 raw14442Labels = mixedMoment B node3805 node3805Labels := by
  calc
    mixedMoment B raw14442 raw14442Labels = mixedMoment B raw14442step0 raw14442step0Labels := by
      have ha : raw14442step0 = (fun i j => raw14442 (permutation473 i) (permutation4 j)) := by apply Matrix.ext; unfold raw14442step0 raw14442; decide +kernel
      have hl : raw14442step0Labels = raw14442Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14442 raw14442Labels permutation473 permutation4
    mixedMoment B raw14442step0 raw14442step0Labels = mixedMoment B raw14442step1 raw14442step1Labels := by
      have ha : raw14442step1 = -raw14442step0 := by apply Matrix.ext; change ∀ i j, raw14442step1 i j = -(raw14442step0 i j); unfold raw14442step1 raw14442step0; decide +kernel
      have hl : raw14442step1Labels = raw14442step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3805 node3805Labels := by rfl

theorem canonical14443 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14443 raw14443Labels = mixedMoment B node4092 node4092Labels := by
  calc
    mixedMoment B raw14443 raw14443Labels = mixedMoment B raw14443step0 raw14443step0Labels := by
      have hz : ∀ j, raw14443 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw14443step0 = (fun i j => raw14443 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw14443step0 raw14443; decide +kernel
      have hl : raw14443step0Labels = raw14443Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14443 raw14443Labels permutation590 hz
    mixedMoment B raw14443step0 raw14443step0Labels = mixedMoment B raw14443step1 raw14443step1Labels := by
      have hz : ∀ j, raw14443step0 (permutation128 0) j = 0 := by decide +kernel
      have ha : raw14443step1 = (fun i j => raw14443step0 (permutation128 i.succ) j) := by apply Matrix.ext; unfold raw14443step1 raw14443step0; decide +kernel
      have hl : raw14443step1Labels = raw14443step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14443step0 raw14443step0Labels permutation128 hz
    _ = mixedMoment B node4092 node4092Labels := by rfl

theorem canonical14444 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14444 raw14444Labels = mixedMoment B node2714 node2714Labels := by
  calc
    _ = mixedMoment B node2714 node2714Labels := by rfl

theorem canonical14445 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14445 raw14445Labels = mixedMoment B node2494 node2494Labels := by
  calc
    mixedMoment B raw14445 raw14445Labels = mixedMoment B raw14445step0 raw14445step0Labels := by
      have ha : raw14445step0 = (fun i j => raw14445 (permutation160 i) (permutation2 j)) := by apply Matrix.ext; unfold raw14445step0 raw14445; decide +kernel
      have hl : raw14445step0Labels = raw14445Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14445 raw14445Labels permutation160 permutation2
    _ = mixedMoment B node2494 node2494Labels := by rfl

theorem canonical14446 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14446 raw14446Labels = mixedMoment B node2481 node2481Labels := by
  calc
    mixedMoment B raw14446 raw14446Labels = mixedMoment B raw14446step0 raw14446step0Labels := by
      have ha : raw14446step0 = (fun i j => raw14446 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw14446step0 raw14446; decide +kernel
      have hl : raw14446step0Labels = raw14446Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14446 raw14446Labels permutation154 permutation2
    _ = mixedMoment B node2481 node2481Labels := by rfl

theorem canonical14447 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14447 raw14447Labels = mixedMoment B node2475 node2475Labels := by
  calc
    _ = mixedMoment B node2475 node2475Labels := by rfl

theorem canonical14448 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14448 raw14448Labels = mixedMoment B node2474 node2474Labels := by
  calc
    _ = mixedMoment B node2474 node2474Labels := by rfl

theorem canonical14449 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14449 raw14449Labels = mixedMoment B node3698 node3698Labels := by
  calc
    mixedMoment B raw14449 raw14449Labels = mixedMoment B raw14449step0 raw14449step0Labels := by
      have ha : raw14449step0 = (fun i j => raw14449 (permutation467 i) (permutation4 j)) := by apply Matrix.ext; unfold raw14449step0 raw14449; decide +kernel
      have hl : raw14449step0Labels = raw14449Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14449 raw14449Labels permutation467 permutation4
    mixedMoment B raw14449step0 raw14449step0Labels = mixedMoment B raw14449step1 raw14449step1Labels := by
      have ha : raw14449step1 = -raw14449step0 := by apply Matrix.ext; change ∀ i j, raw14449step1 i j = -(raw14449step0 i j); unfold raw14449step1 raw14449step0; decide +kernel
      have hl : raw14449step1Labels = raw14449step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3698 node3698Labels := by rfl

theorem canonical14450 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14450 raw14450Labels = mixedMoment B node2494 node2494Labels := by
  calc
    mixedMoment B raw14450 raw14450Labels = mixedMoment B raw14450step0 raw14450step0Labels := by
      have ha : raw14450step0 = (fun i j => raw14450 (permutation467 i) (permutation4 j)) := by apply Matrix.ext; unfold raw14450step0 raw14450; decide +kernel
      have hl : raw14450step0Labels = raw14450Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14450 raw14450Labels permutation467 permutation4
    mixedMoment B raw14450step0 raw14450step0Labels = mixedMoment B raw14450step1 raw14450step1Labels := by
      have ha : raw14450step1 = -raw14450step0 := by apply Matrix.ext; change ∀ i j, raw14450step1 i j = -(raw14450step0 i j); unfold raw14450step1 raw14450step0; decide +kernel
      have hl : raw14450step1Labels = raw14450step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2494 node2494Labels := by rfl

theorem canonical14451 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14451 raw14451Labels = mixedMoment B node3814 node3814Labels := by
  calc
    mixedMoment B raw14451 raw14451Labels = mixedMoment B raw14451step0 raw14451step0Labels := by
      have hz : ∀ j, raw14451 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw14451step0 = (fun i j => raw14451 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw14451step0 raw14451; decide +kernel
      have hl : raw14451step0Labels = raw14451Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14451 raw14451Labels permutation520 hz
    mixedMoment B raw14451step0 raw14451step0Labels = mixedMoment B raw14451step1 raw14451step1Labels := by
      have ha : raw14451step1 = (fun i j => raw14451step0 (permutation116 i) (permutation4 j)) := by apply Matrix.ext; unfold raw14451step1 raw14451step0; decide +kernel
      have hl : raw14451step1Labels = raw14451step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14451step0 raw14451step0Labels permutation116 permutation4
    mixedMoment B raw14451step1 raw14451step1Labels = mixedMoment B raw14451step2 raw14451step2Labels := by
      have ha : raw14451step2 = -raw14451step1 := by apply Matrix.ext; change ∀ i j, raw14451step2 i j = -(raw14451step1 i j); unfold raw14451step2 raw14451step1; decide +kernel
      have hl : raw14451step2Labels = raw14451step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3814 node3814Labels := by rfl

theorem canonical14452 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14452 raw14452Labels = mixedMoment B node3812 node3812Labels := by
  calc
    mixedMoment B raw14452 raw14452Labels = mixedMoment B raw14452step0 raw14452step0Labels := by
      have ha : raw14452step0 = (fun i j => raw14452 (permutation468 i) (permutation4 j)) := by apply Matrix.ext; unfold raw14452step0 raw14452; decide +kernel
      have hl : raw14452step0Labels = raw14452Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14452 raw14452Labels permutation468 permutation4
    mixedMoment B raw14452step0 raw14452step0Labels = mixedMoment B raw14452step1 raw14452step1Labels := by
      have ha : raw14452step1 = -raw14452step0 := by apply Matrix.ext; change ∀ i j, raw14452step1 i j = -(raw14452step0 i j); unfold raw14452step1 raw14452step0; decide +kernel
      have hl : raw14452step1Labels = raw14452step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3812 node3812Labels := by rfl

theorem canonical14453 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14453 raw14453Labels = mixedMoment B node3698 node3698Labels := by
  calc
    mixedMoment B raw14453 raw14453Labels = mixedMoment B raw14453step0 raw14453step0Labels := by
      have ha : raw14453step0 = (fun i j => raw14453 (permutation160 i) (permutation2 j)) := by apply Matrix.ext; unfold raw14453step0 raw14453; decide +kernel
      have hl : raw14453step0Labels = raw14453Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14453 raw14453Labels permutation160 permutation2
    _ = mixedMoment B node3698 node3698Labels := by rfl

theorem canonical14454 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14454 raw14454Labels = mixedMoment B node3691 node3691Labels := by
  calc
    mixedMoment B raw14454 raw14454Labels = mixedMoment B raw14454step0 raw14454step0Labels := by
      have ha : raw14454step0 = (fun i j => raw14454 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw14454step0 raw14454; decide +kernel
      have hl : raw14454step0Labels = raw14454Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14454 raw14454Labels permutation154 permutation2
    _ = mixedMoment B node3691 node3691Labels := by rfl

theorem canonical14455 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14455 raw14455Labels = mixedMoment B node3686 node3686Labels := by
  calc
    _ = mixedMoment B node3686 node3686Labels := by rfl

theorem canonical14456 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14456 raw14456Labels = mixedMoment B node3217 node3217Labels := by
  calc
    mixedMoment B raw14456 raw14456Labels = mixedMoment B raw14456step0 raw14456step0Labels := by
      have ha : raw14456step0 = (fun i j => raw14456 (permutation688 i) (permutation2 j)) := by apply Matrix.ext; unfold raw14456step0 raw14456; decide +kernel
      have hl : raw14456step0Labels = raw14456Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14456 raw14456Labels permutation688 permutation2
    mixedMoment B raw14456step0 raw14456step0Labels = mixedMoment B raw14456step1 raw14456step1Labels := by
      have ha : raw14456step1 = -raw14456step0 := by apply Matrix.ext; change ∀ i j, raw14456step1 i j = -(raw14456step0 i j); unfold raw14456step1 raw14456step0; decide +kernel
      have hl : raw14456step1Labels = raw14456step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3217 node3217Labels := by rfl

theorem canonical14457 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14457 raw14457Labels = mixedMoment B node3686 node3686Labels := by
  calc
    mixedMoment B raw14457 raw14457Labels = mixedMoment B raw14457step0 raw14457step0Labels := by
      have ha : raw14457step0 = (fun i j => raw14457 (permutation470 i) (permutation4 j)) := by apply Matrix.ext; unfold raw14457step0 raw14457; decide +kernel
      have hl : raw14457step0Labels = raw14457Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14457 raw14457Labels permutation470 permutation4
    mixedMoment B raw14457step0 raw14457step0Labels = mixedMoment B raw14457step1 raw14457step1Labels := by
      have ha : raw14457step1 = -raw14457step0 := by apply Matrix.ext; change ∀ i j, raw14457step1 i j = -(raw14457step0 i j); unfold raw14457step1 raw14457step0; decide +kernel
      have hl : raw14457step1Labels = raw14457step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3686 node3686Labels := by rfl

theorem canonical14458 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14458 raw14458Labels = mixedMoment B node2475 node2475Labels := by
  calc
    mixedMoment B raw14458 raw14458Labels = mixedMoment B raw14458step0 raw14458step0Labels := by
      have ha : raw14458step0 = (fun i j => raw14458 (permutation470 i) (permutation4 j)) := by apply Matrix.ext; unfold raw14458step0 raw14458; decide +kernel
      have hl : raw14458step0Labels = raw14458Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14458 raw14458Labels permutation470 permutation4
    mixedMoment B raw14458step0 raw14458step0Labels = mixedMoment B raw14458step1 raw14458step1Labels := by
      have ha : raw14458step1 = -raw14458step0 := by apply Matrix.ext; change ∀ i j, raw14458step1 i j = -(raw14458step0 i j); unfold raw14458step1 raw14458step0; decide +kernel
      have hl : raw14458step1Labels = raw14458step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2475 node2475Labels := by rfl

theorem canonical14459 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14459 raw14459Labels = mixedMoment B node3803 node3803Labels := by
  calc
    mixedMoment B raw14459 raw14459Labels = mixedMoment B raw14459step0 raw14459step0Labels := by
      have ha : raw14459step0 = (fun i j => raw14459 (permutation153 i) (permutation2 j)) := by apply Matrix.ext; unfold raw14459step0 raw14459; decide +kernel
      have hl : raw14459step0Labels = raw14459Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14459 raw14459Labels permutation153 permutation2
    _ = mixedMoment B node3803 node3803Labels := by rfl

theorem canonical14460 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14460 raw14460Labels = mixedMoment B node5420 node5420Labels := by
  calc
    mixedMoment B raw14460 raw14460Labels = mixedMoment B raw14460step0 raw14460step0Labels := by
      have ha : raw14460step0 = (fun i j => raw14460 (permutation628 i) (permutation5 j)) := by apply Matrix.ext; unfold raw14460step0 raw14460; decide +kernel
      have hl : raw14460step0Labels = raw14460Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14460 raw14460Labels permutation628 permutation5
    mixedMoment B raw14460step0 raw14460step0Labels = mixedMoment B raw14460step1 raw14460step1Labels := by
      have ha : raw14460step1 = raw14460step0 := by apply Matrix.ext; unfold raw14460step1 raw14460step0; decide +kernel
      have hl : raw14460step0Labels = labelEmbedding8 ∘ raw14460step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14460step0 raw14460step0Labels raw14460step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5420 node5420Labels := by rfl

theorem canonical14461 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14461 raw14461Labels = mixedMoment B node5445 node5445Labels := by
  calc
    mixedMoment B raw14461 raw14461Labels = mixedMoment B raw14461step0 raw14461step0Labels := by
      have ha : raw14461step0 = (fun i j => raw14461 (permutation684 i) (permutation3 j)) := by apply Matrix.ext; unfold raw14461step0 raw14461; decide +kernel
      have hl : raw14461step0Labels = raw14461Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14461 raw14461Labels permutation684 permutation3
    mixedMoment B raw14461step0 raw14461step0Labels = mixedMoment B raw14461step1 raw14461step1Labels := by
      have ha : raw14461step1 = -raw14461step0 := by apply Matrix.ext; change ∀ i j, raw14461step1 i j = -(raw14461step0 i j); unfold raw14461step1 raw14461step0; decide +kernel
      have hl : raw14461step1Labels = raw14461step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw14461step1 raw14461step1Labels = mixedMoment B raw14461step2 raw14461step2Labels := by
      have ha : raw14461step2 = raw14461step1 := by apply Matrix.ext; unfold raw14461step2 raw14461step1; decide +kernel
      have hl : raw14461step1Labels = labelEmbedding6 ∘ raw14461step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14461step1 raw14461step1Labels raw14461step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5445 node5445Labels := by rfl

theorem canonical14462 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14462 raw14462Labels = mixedMoment B node5421 node5421Labels := by
  calc
    mixedMoment B raw14462 raw14462Labels = mixedMoment B raw14462step0 raw14462step0Labels := by
      have ha : raw14462step0 = (fun i j => raw14462 (permutation627 i) (permutation5 j)) := by apply Matrix.ext; unfold raw14462step0 raw14462; decide +kernel
      have hl : raw14462step0Labels = raw14462Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14462 raw14462Labels permutation627 permutation5
    mixedMoment B raw14462step0 raw14462step0Labels = mixedMoment B raw14462step1 raw14462step1Labels := by
      have ha : raw14462step1 = raw14462step0 := by apply Matrix.ext; unfold raw14462step1 raw14462step0; decide +kernel
      have hl : raw14462step0Labels = labelEmbedding8 ∘ raw14462step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14462step0 raw14462step0Labels raw14462step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5421 node5421Labels := by rfl

theorem canonical14463 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14463 raw14463Labels = mixedMoment B node5397 node5397Labels := by
  calc
    mixedMoment B raw14463 raw14463Labels = mixedMoment B raw14463step0 raw14463step0Labels := by
      have ha : raw14463step0 = (fun i j => raw14463 (permutation556 i) (permutation4 j)) := by apply Matrix.ext; unfold raw14463step0 raw14463; decide +kernel
      have hl : raw14463step0Labels = raw14463Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14463 raw14463Labels permutation556 permutation4
    mixedMoment B raw14463step0 raw14463step0Labels = mixedMoment B raw14463step1 raw14463step1Labels := by
      have ha : raw14463step1 = -raw14463step0 := by apply Matrix.ext; change ∀ i j, raw14463step1 i j = -(raw14463step0 i j); unfold raw14463step1 raw14463step0; decide +kernel
      have hl : raw14463step1Labels = raw14463step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw14463step1 raw14463step1Labels = mixedMoment B raw14463step2 raw14463step2Labels := by
      have ha : raw14463step2 = raw14463step1 := by apply Matrix.ext; unfold raw14463step2 raw14463step1; decide +kernel
      have hl : raw14463step1Labels = labelEmbedding7 ∘ raw14463step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14463step1 raw14463step1Labels raw14463step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5397 node5397Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical113
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical14464 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14464 raw14464Labels = mixedMoment B node5477 node5477Labels := by
  calc
    mixedMoment B raw14464 raw14464Labels = mixedMoment B raw14464step0 raw14464step0Labels := by
      have ha : raw14464step0 = (fun i j => raw14464 (permutation559 i) (permutation6 j)) := by apply Matrix.ext; unfold raw14464step0 raw14464; decide +kernel
      have hl : raw14464step0Labels = raw14464Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14464 raw14464Labels permutation559 permutation6
    mixedMoment B raw14464step0 raw14464step0Labels = mixedMoment B raw14464step1 raw14464step1Labels := by
      have ha : raw14464step1 = raw14464step0 := by apply Matrix.ext; unfold raw14464step1 raw14464step0; decide +kernel
      have hl : raw14464step0Labels = labelEmbedding9 ∘ raw14464step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14464step0 raw14464step0Labels raw14464step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5477 node5477Labels := by rfl

theorem canonical14465 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14465 raw14465Labels = mixedMoment B node5260 node5260Labels := by
  calc
    mixedMoment B raw14465 raw14465Labels = mixedMoment B raw14465step0 raw14465step0Labels := by
      have hz : ∀ j, raw14465 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw14465step0 = (fun i j => raw14465 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw14465step0 raw14465; decide +kernel
      have hl : raw14465step0Labels = raw14465Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14465 raw14465Labels permutation265 hz
    _ = mixedMoment B node5260 node5260Labels := by rfl

theorem canonical14466 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14466 raw14466Labels = mixedMoment B node5411 node5411Labels := by
  calc
    mixedMoment B raw14466 raw14466Labels = mixedMoment B raw14466step0 raw14466step0Labels := by
      have hz : ∀ j, raw14466 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw14466step0 = (fun i j => raw14466 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw14466step0 raw14466; decide +kernel
      have hl : raw14466step0Labels = raw14466Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14466 raw14466Labels permutation265 hz
    _ = mixedMoment B node5411 node5411Labels := by rfl

theorem canonical14467 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14467 raw14467Labels = mixedMoment B node5436 node5436Labels := by
  calc
    mixedMoment B raw14467 raw14467Labels = mixedMoment B raw14467step0 raw14467step0Labels := by
      have hz : ∀ j, raw14467 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw14467step0 = (fun i j => raw14467 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw14467step0 raw14467; decide +kernel
      have hl : raw14467step0Labels = raw14467Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14467 raw14467Labels permutation265 hz
    mixedMoment B raw14467step0 raw14467step0Labels = mixedMoment B raw14467step1 raw14467step1Labels := by
      have ha : raw14467step1 = (fun i j => raw14467step0 (permutation135 i) (permutation5 j)) := by apply Matrix.ext; unfold raw14467step1 raw14467step0; decide +kernel
      have hl : raw14467step1Labels = raw14467step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14467step0 raw14467step0Labels permutation135 permutation5
    mixedMoment B raw14467step1 raw14467step1Labels = mixedMoment B raw14467step2 raw14467step2Labels := by
      have ha : raw14467step2 = raw14467step1 := by apply Matrix.ext; unfold raw14467step2 raw14467step1; decide +kernel
      have hl : raw14467step1Labels = labelEmbedding8 ∘ raw14467step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14467step1 raw14467step1Labels raw14467step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5436 node5436Labels := by rfl

theorem canonical14468 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14468 raw14468Labels = mixedMoment B node5412 node5412Labels := by
  calc
    mixedMoment B raw14468 raw14468Labels = mixedMoment B raw14468step0 raw14468step0Labels := by
      have hz : ∀ j, raw14468 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw14468step0 = (fun i j => raw14468 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw14468step0 raw14468; decide +kernel
      have hl : raw14468step0Labels = raw14468Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14468 raw14468Labels permutation265 hz
    mixedMoment B raw14468step0 raw14468step0Labels = mixedMoment B raw14468step1 raw14468step1Labels := by
      have ha : raw14468step1 = (fun i j => raw14468step0 (permutation116 i) (permutation4 j)) := by apply Matrix.ext; unfold raw14468step1 raw14468step0; decide +kernel
      have hl : raw14468step1Labels = raw14468step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14468step0 raw14468step0Labels permutation116 permutation4
    mixedMoment B raw14468step1 raw14468step1Labels = mixedMoment B raw14468step2 raw14468step2Labels := by
      have ha : raw14468step2 = -raw14468step1 := by apply Matrix.ext; change ∀ i j, raw14468step2 i j = -(raw14468step1 i j); unfold raw14468step2 raw14468step1; decide +kernel
      have hl : raw14468step2Labels = raw14468step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw14468step2 raw14468step2Labels = mixedMoment B raw14468step3 raw14468step3Labels := by
      have ha : raw14468step3 = raw14468step2 := by apply Matrix.ext; unfold raw14468step3 raw14468step2; decide +kernel
      have hl : raw14468step2Labels = labelEmbedding7 ∘ raw14468step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14468step2 raw14468step2Labels raw14468step3Labels labelEmbedding7 hl
    _ = mixedMoment B node5412 node5412Labels := by rfl

theorem canonical14469 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14469 raw14469Labels = mixedMoment B node5434 node5434Labels := by
  calc
    mixedMoment B raw14469 raw14469Labels = mixedMoment B raw14469step0 raw14469step0Labels := by
      have hz : ∀ j, raw14469 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw14469step0 = (fun i j => raw14469 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw14469step0 raw14469; decide +kernel
      have hl : raw14469step0Labels = raw14469Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14469 raw14469Labels permutation265 hz
    mixedMoment B raw14469step0 raw14469step0Labels = mixedMoment B raw14469step1 raw14469step1Labels := by
      have ha : raw14469step1 = (fun i j => raw14469step0 (permutation36 i) (permutation7 j)) := by apply Matrix.ext; unfold raw14469step1 raw14469step0; decide +kernel
      have hl : raw14469step1Labels = raw14469step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14469step0 raw14469step0Labels permutation36 permutation7
    mixedMoment B raw14469step1 raw14469step1Labels = mixedMoment B raw14469step2 raw14469step2Labels := by
      have ha : raw14469step2 = -raw14469step1 := by apply Matrix.ext; change ∀ i j, raw14469step2 i j = -(raw14469step1 i j); unfold raw14469step2 raw14469step1; decide +kernel
      have hl : raw14469step2Labels = raw14469step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw14469step2 raw14469step2Labels = mixedMoment B raw14469step3 raw14469step3Labels := by
      have ha : raw14469step3 = raw14469step2 := by apply Matrix.ext; unfold raw14469step3 raw14469step2; decide +kernel
      have hl : raw14469step2Labels = labelEmbedding10 ∘ raw14469step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14469step2 raw14469step2Labels raw14469step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5434 node5434Labels := by rfl

theorem canonical14470 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14470 raw14470Labels = mixedMoment B node5146 node5146Labels := by
  calc
    mixedMoment B raw14470 raw14470Labels = mixedMoment B raw14470step0 raw14470step0Labels := by
      have ha : raw14470step0 = (fun i j => raw14470 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw14470step0 raw14470; decide +kernel
      have hl : raw14470step0Labels = raw14470Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14470 raw14470Labels permutation158 permutation2
    _ = mixedMoment B node5146 node5146Labels := by rfl

theorem canonical14471 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14471 raw14471Labels = mixedMoment B node5357 node5357Labels := by
  calc
    mixedMoment B raw14471 raw14471Labels = mixedMoment B raw14471step0 raw14471step0Labels := by
      have ha : raw14471step0 = (fun i j => raw14471 (permutation628 i) (permutation5 j)) := by apply Matrix.ext; unfold raw14471step0 raw14471; decide +kernel
      have hl : raw14471step0Labels = raw14471Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14471 raw14471Labels permutation628 permutation5
    mixedMoment B raw14471step0 raw14471step0Labels = mixedMoment B raw14471step1 raw14471step1Labels := by
      have ha : raw14471step1 = raw14471step0 := by apply Matrix.ext; unfold raw14471step1 raw14471step0; decide +kernel
      have hl : raw14471step0Labels = labelEmbedding8 ∘ raw14471step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14471step0 raw14471step0Labels raw14471step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5357 node5357Labels := by rfl

theorem canonical14472 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14472 raw14472Labels = mixedMoment B node5358 node5358Labels := by
  calc
    mixedMoment B raw14472 raw14472Labels = mixedMoment B raw14472step0 raw14472step0Labels := by
      have ha : raw14472step0 = (fun i j => raw14472 (permutation627 i) (permutation5 j)) := by apply Matrix.ext; unfold raw14472step0 raw14472; decide +kernel
      have hl : raw14472step0Labels = raw14472Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14472 raw14472Labels permutation627 permutation5
    mixedMoment B raw14472step0 raw14472step0Labels = mixedMoment B raw14472step1 raw14472step1Labels := by
      have ha : raw14472step1 = raw14472step0 := by apply Matrix.ext; unfold raw14472step1 raw14472step0; decide +kernel
      have hl : raw14472step0Labels = labelEmbedding8 ∘ raw14472step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14472step0 raw14472step0Labels raw14472step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5358 node5358Labels := by rfl

theorem canonical14473 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14473 raw14473Labels = mixedMoment B node5360 node5360Labels := by
  calc
    mixedMoment B raw14473 raw14473Labels = mixedMoment B raw14473step0 raw14473step0Labels := by
      have ha : raw14473step0 = (fun i j => raw14473 (permutation625 i) (permutation5 j)) := by apply Matrix.ext; unfold raw14473step0 raw14473; decide +kernel
      have hl : raw14473step0Labels = raw14473Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14473 raw14473Labels permutation625 permutation5
    mixedMoment B raw14473step0 raw14473step0Labels = mixedMoment B raw14473step1 raw14473step1Labels := by
      have ha : raw14473step1 = raw14473step0 := by apply Matrix.ext; unfold raw14473step1 raw14473step0; decide +kernel
      have hl : raw14473step0Labels = labelEmbedding8 ∘ raw14473step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14473step0 raw14473step0Labels raw14473step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5360 node5360Labels := by rfl

theorem canonical14474 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14474 raw14474Labels = mixedMoment B node5430 node5430Labels := by
  calc
    mixedMoment B raw14474 raw14474Labels = mixedMoment B raw14474step0 raw14474step0Labels := by
      have ha : raw14474step0 = (fun i j => raw14474 (permutation159 i) (permutation2 j)) := by apply Matrix.ext; unfold raw14474step0 raw14474; decide +kernel
      have hl : raw14474step0Labels = raw14474Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14474 raw14474Labels permutation159 permutation2
    _ = mixedMoment B node5430 node5430Labels := by rfl

theorem canonical14475 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14475 raw14475Labels = mixedMoment B node5138 node5138Labels := by
  calc
    _ = mixedMoment B node5138 node5138Labels := by rfl

theorem canonical14476 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14476 raw14476Labels = mixedMoment B node5381 node5381Labels := by
  calc
    _ = mixedMoment B node5381 node5381Labels := by rfl

theorem canonical14477 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14477 raw14477Labels = mixedMoment B node5397 node5397Labels := by
  calc
    mixedMoment B raw14477 raw14477Labels = mixedMoment B raw14477step0 raw14477step0Labels := by
      have ha : raw14477step0 = (fun i j => raw14477 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw14477step0 raw14477; decide +kernel
      have hl : raw14477step0Labels = raw14477Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14477 raw14477Labels permutation176 permutation2
    _ = mixedMoment B node5397 node5397Labels := by rfl

theorem canonical14478 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14478 raw14478Labels = mixedMoment B node5426 node5426Labels := by
  calc
    mixedMoment B raw14478 raw14478Labels = mixedMoment B raw14478step0 raw14478step0Labels := by
      have ha : raw14478step0 = (fun i j => raw14478 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw14478step0 raw14478; decide +kernel
      have hl : raw14478step0Labels = raw14478Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14478 raw14478Labels permutation154 permutation2
    _ = mixedMoment B node5426 node5426Labels := by rfl

theorem canonical14479 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14479 raw14479Labels = mixedMoment B node5424 node5424Labels := by
  calc
    mixedMoment B raw14479 raw14479Labels = mixedMoment B raw14479step0 raw14479step0Labels := by
      have ha : raw14479step0 = (fun i j => raw14479 (permutation180 i) (permutation7 j)) := by apply Matrix.ext; unfold raw14479step0 raw14479; decide +kernel
      have hl : raw14479step0Labels = raw14479Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14479 raw14479Labels permutation180 permutation7
    mixedMoment B raw14479step0 raw14479step0Labels = mixedMoment B raw14479step1 raw14479step1Labels := by
      have ha : raw14479step1 = -raw14479step0 := by apply Matrix.ext; change ∀ i j, raw14479step1 i j = -(raw14479step0 i j); unfold raw14479step1 raw14479step0; decide +kernel
      have hl : raw14479step1Labels = raw14479step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw14479step1 raw14479step1Labels = mixedMoment B raw14479step2 raw14479step2Labels := by
      have ha : raw14479step2 = raw14479step1 := by apply Matrix.ext; unfold raw14479step2 raw14479step1; decide +kernel
      have hl : raw14479step1Labels = labelEmbedding10 ∘ raw14479step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14479step1 raw14479step1Labels raw14479step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5424 node5424Labels := by rfl

theorem canonical14480 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14480 raw14480Labels = mixedMoment B node5129 node5129Labels := by
  calc
    mixedMoment B raw14480 raw14480Labels = mixedMoment B raw14480step0 raw14480step0Labels := by
      have ha : raw14480step0 = (fun i j => raw14480 (permutation153 i) (permutation2 j)) := by apply Matrix.ext; unfold raw14480step0 raw14480; decide +kernel
      have hl : raw14480step0Labels = raw14480Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14480 raw14480Labels permutation153 permutation2
    _ = mixedMoment B node5129 node5129Labels := by rfl

theorem canonical14481 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14481 raw14481Labels = mixedMoment B node5376 node5376Labels := by
  calc
    mixedMoment B raw14481 raw14481Labels = mixedMoment B raw14481step0 raw14481step0Labels := by
      have ha : raw14481step0 = (fun i j => raw14481 (permutation153 i) (permutation2 j)) := by apply Matrix.ext; unfold raw14481step0 raw14481; decide +kernel
      have hl : raw14481step0Labels = raw14481Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14481 raw14481Labels permutation153 permutation2
    _ = mixedMoment B node5376 node5376Labels := by rfl

theorem canonical14482 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14482 raw14482Labels = mixedMoment B node5378 node5378Labels := by
  calc
    mixedMoment B raw14482 raw14482Labels = mixedMoment B raw14482step0 raw14482step0Labels := by
      have ha : raw14482step0 = (fun i j => raw14482 (permutation587 i) (permutation2 j)) := by apply Matrix.ext; unfold raw14482step0 raw14482; decide +kernel
      have hl : raw14482step0Labels = raw14482Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14482 raw14482Labels permutation587 permutation2
    mixedMoment B raw14482step0 raw14482step0Labels = mixedMoment B raw14482step1 raw14482step1Labels := by
      have ha : raw14482step1 = -raw14482step0 := by apply Matrix.ext; change ∀ i j, raw14482step1 i j = -(raw14482step0 i j); unfold raw14482step1 raw14482step0; decide +kernel
      have hl : raw14482step1Labels = raw14482step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5378 node5378Labels := by rfl

theorem canonical14483 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14483 raw14483Labels = mixedMoment B node5381 node5381Labels := by
  calc
    mixedMoment B raw14483 raw14483Labels = mixedMoment B raw14483step0 raw14483step0Labels := by
      have ha : raw14483step0 = (fun i j => raw14483 (permutation680 i) (permutation3 j)) := by apply Matrix.ext; unfold raw14483step0 raw14483; decide +kernel
      have hl : raw14483step0Labels = raw14483Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14483 raw14483Labels permutation680 permutation3
    mixedMoment B raw14483step0 raw14483step0Labels = mixedMoment B raw14483step1 raw14483step1Labels := by
      have ha : raw14483step1 = -raw14483step0 := by apply Matrix.ext; change ∀ i j, raw14483step1 i j = -(raw14483step0 i j); unfold raw14483step1 raw14483step0; decide +kernel
      have hl : raw14483step1Labels = raw14483step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw14483step1 raw14483step1Labels = mixedMoment B raw14483step2 raw14483step2Labels := by
      have ha : raw14483step2 = raw14483step1 := by apply Matrix.ext; unfold raw14483step2 raw14483step1; decide +kernel
      have hl : raw14483step1Labels = labelEmbedding6 ∘ raw14483step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14483step1 raw14483step1Labels raw14483step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5381 node5381Labels := by rfl

theorem canonical14484 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14484 raw14484Labels = mixedMoment B node5423 node5423Labels := by
  calc
    mixedMoment B raw14484 raw14484Labels = mixedMoment B raw14484step0 raw14484step0Labels := by
      have ha : raw14484step0 = (fun i j => raw14484 (permutation153 i) (permutation2 j)) := by apply Matrix.ext; unfold raw14484step0 raw14484; decide +kernel
      have hl : raw14484step0Labels = raw14484Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14484 raw14484Labels permutation153 permutation2
    _ = mixedMoment B node5423 node5423Labels := by rfl

theorem canonical14485 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14485 raw14485Labels = mixedMoment B node4824 node4824Labels := by
  calc
    mixedMoment B raw14485 raw14485Labels = mixedMoment B raw14485step0 raw14485step0Labels := by
      have ha : raw14485step0 = (fun i j => raw14485 (permutation646 i) (permutation5 j)) := by apply Matrix.ext; unfold raw14485step0 raw14485; decide +kernel
      have hl : raw14485step0Labels = raw14485Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14485 raw14485Labels permutation646 permutation5
    mixedMoment B raw14485step0 raw14485step0Labels = mixedMoment B raw14485step1 raw14485step1Labels := by
      have ha : raw14485step1 = raw14485step0 := by apply Matrix.ext; unfold raw14485step1 raw14485step0; decide +kernel
      have hl : raw14485step0Labels = labelEmbedding8 ∘ raw14485step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14485step0 raw14485step0Labels raw14485step1Labels labelEmbedding8 hl
    _ = mixedMoment B node4824 node4824Labels := by rfl

theorem canonical14486 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14486 raw14486Labels = mixedMoment B node4812 node4812Labels := by
  calc
    mixedMoment B raw14486 raw14486Labels = mixedMoment B raw14486step0 raw14486step0Labels := by
      have ha : raw14486step0 = (fun i j => raw14486 (permutation628 i) (permutation5 j)) := by apply Matrix.ext; unfold raw14486step0 raw14486; decide +kernel
      have hl : raw14486step0Labels = raw14486Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14486 raw14486Labels permutation628 permutation5
    mixedMoment B raw14486step0 raw14486step0Labels = mixedMoment B raw14486step1 raw14486step1Labels := by
      have ha : raw14486step1 = raw14486step0 := by apply Matrix.ext; unfold raw14486step1 raw14486step0; decide +kernel
      have hl : raw14486step0Labels = labelEmbedding8 ∘ raw14486step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14486step0 raw14486step0Labels raw14486step1Labels labelEmbedding8 hl
    _ = mixedMoment B node4812 node4812Labels := by rfl

theorem canonical14487 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14487 raw14487Labels = mixedMoment B node4852 node4852Labels := by
  calc
    mixedMoment B raw14487 raw14487Labels = mixedMoment B raw14487step0 raw14487step0Labels := by
      have ha : raw14487step0 = (fun i j => raw14487 (permutation688 i) (permutation3 j)) := by apply Matrix.ext; unfold raw14487step0 raw14487; decide +kernel
      have hl : raw14487step0Labels = raw14487Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14487 raw14487Labels permutation688 permutation3
    mixedMoment B raw14487step0 raw14487step0Labels = mixedMoment B raw14487step1 raw14487step1Labels := by
      have ha : raw14487step1 = -raw14487step0 := by apply Matrix.ext; change ∀ i j, raw14487step1 i j = -(raw14487step0 i j); unfold raw14487step1 raw14487step0; decide +kernel
      have hl : raw14487step1Labels = raw14487step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw14487step1 raw14487step1Labels = mixedMoment B raw14487step2 raw14487step2Labels := by
      have ha : raw14487step2 = raw14487step1 := by apply Matrix.ext; unfold raw14487step2 raw14487step1; decide +kernel
      have hl : raw14487step1Labels = labelEmbedding6 ∘ raw14487step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14487step1 raw14487step1Labels raw14487step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4852 node4852Labels := by rfl

theorem canonical14488 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14488 raw14488Labels = mixedMoment B node4813 node4813Labels := by
  calc
    mixedMoment B raw14488 raw14488Labels = mixedMoment B raw14488step0 raw14488step0Labels := by
      have ha : raw14488step0 = (fun i j => raw14488 (permutation627 i) (permutation5 j)) := by apply Matrix.ext; unfold raw14488step0 raw14488; decide +kernel
      have hl : raw14488step0Labels = raw14488Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14488 raw14488Labels permutation627 permutation5
    mixedMoment B raw14488step0 raw14488step0Labels = mixedMoment B raw14488step1 raw14488step1Labels := by
      have ha : raw14488step1 = raw14488step0 := by apply Matrix.ext; unfold raw14488step1 raw14488step0; decide +kernel
      have hl : raw14488step0Labels = labelEmbedding8 ∘ raw14488step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14488step0 raw14488step0Labels raw14488step1Labels labelEmbedding8 hl
    _ = mixedMoment B node4813 node4813Labels := by rfl

theorem canonical14489 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14489 raw14489Labels = mixedMoment B node4816 node4816Labels := by
  calc
    mixedMoment B raw14489 raw14489Labels = mixedMoment B raw14489step0 raw14489step0Labels := by
      have ha : raw14489step0 = (fun i j => raw14489 (permutation625 i) (permutation5 j)) := by apply Matrix.ext; unfold raw14489step0 raw14489; decide +kernel
      have hl : raw14489step0Labels = raw14489Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14489 raw14489Labels permutation625 permutation5
    mixedMoment B raw14489step0 raw14489step0Labels = mixedMoment B raw14489step1 raw14489step1Labels := by
      have ha : raw14489step1 = raw14489step0 := by apply Matrix.ext; unfold raw14489step1 raw14489step0; decide +kernel
      have hl : raw14489step0Labels = labelEmbedding8 ∘ raw14489step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14489step0 raw14489step0Labels raw14489step1Labels labelEmbedding8 hl
    _ = mixedMoment B node4816 node4816Labels := by rfl

theorem canonical14550 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14550 raw14550Labels = mixedMoment B node3839 node3839Labels := by
  calc
    _ = mixedMoment B node3839 node3839Labels := by rfl

theorem canonical14551 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14551 raw14551Labels = mixedMoment B node4022 node4022Labels := by
  calc
    mixedMoment B raw14551 raw14551Labels = mixedMoment B raw14551step0 raw14551step0Labels := by
      have ha : raw14551step0 = (fun i j => raw14551 (permutation595 i) (permutation4 j)) := by apply Matrix.ext; unfold raw14551step0 raw14551; decide +kernel
      have hl : raw14551step0Labels = raw14551Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14551 raw14551Labels permutation595 permutation4
    _ = mixedMoment B node4022 node4022Labels := by rfl

theorem canonical14552 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14552 raw14552Labels = mixedMoment B node4024 node4024Labels := by
  calc
    mixedMoment B raw14552 raw14552Labels = mixedMoment B raw14552step0 raw14552step0Labels := by
      have ha : raw14552step0 = (fun i j => raw14552 (permutation686 i) (permutation2 j)) := by apply Matrix.ext; unfold raw14552step0 raw14552; decide +kernel
      have hl : raw14552step0Labels = raw14552Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14552 raw14552Labels permutation686 permutation2
    mixedMoment B raw14552step0 raw14552step0Labels = mixedMoment B raw14552step1 raw14552step1Labels := by
      have ha : raw14552step1 = -raw14552step0 := by apply Matrix.ext; change ∀ i j, raw14552step1 i j = -(raw14552step0 i j); unfold raw14552step1 raw14552step0; decide +kernel
      have hl : raw14552step1Labels = raw14552step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4024 node4024Labels := by rfl

theorem canonical14553 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14553 raw14553Labels = mixedMoment B node3946 node3946Labels := by
  calc
    mixedMoment B raw14553 raw14553Labels = mixedMoment B raw14553step0 raw14553step0Labels := by
      have ha : raw14553step0 = (fun i j => raw14553 (permutation491 i) (permutation4 j)) := by apply Matrix.ext; unfold raw14553step0 raw14553; decide +kernel
      have hl : raw14553step0Labels = raw14553Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14553 raw14553Labels permutation491 permutation4
    mixedMoment B raw14553step0 raw14553step0Labels = mixedMoment B raw14553step1 raw14553step1Labels := by
      have ha : raw14553step1 = -raw14553step0 := by apply Matrix.ext; change ∀ i j, raw14553step1 i j = -(raw14553step0 i j); unfold raw14553step1 raw14553step0; decide +kernel
      have hl : raw14553step1Labels = raw14553step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3946 node3946Labels := by rfl

theorem canonical14554 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14554 raw14554Labels = mixedMoment B node3782 node3782Labels := by
  calc
    mixedMoment B raw14554 raw14554Labels = mixedMoment B raw14554step0 raw14554step0Labels := by
      have ha : raw14554step0 = (fun i j => raw14554 (permutation556 i) (permutation4 j)) := by apply Matrix.ext; unfold raw14554step0 raw14554; decide +kernel
      have hl : raw14554step0Labels = raw14554Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14554 raw14554Labels permutation556 permutation4
    mixedMoment B raw14554step0 raw14554step0Labels = mixedMoment B raw14554step1 raw14554step1Labels := by
      have ha : raw14554step1 = -raw14554step0 := by apply Matrix.ext; change ∀ i j, raw14554step1 i j = -(raw14554step0 i j); unfold raw14554step1 raw14554step0; decide +kernel
      have hl : raw14554step1Labels = raw14554step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3782 node3782Labels := by rfl

theorem canonical14555 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14555 raw14555Labels = mixedMoment B node4044 node4044Labels := by
  calc
    mixedMoment B raw14555 raw14555Labels = mixedMoment B raw14555step0 raw14555step0Labels := by
      have ha : raw14555step0 = (fun i j => raw14555 (permutation194 i) (permutation4 j)) := by apply Matrix.ext; unfold raw14555step0 raw14555; decide +kernel
      have hl : raw14555step0Labels = raw14555Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14555 raw14555Labels permutation194 permutation4
    _ = mixedMoment B node4044 node4044Labels := by rfl

theorem canonical14556 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14556 raw14556Labels = mixedMoment B node4092 node4092Labels := by
  calc
    mixedMoment B raw14556 raw14556Labels = mixedMoment B raw14556step0 raw14556step0Labels := by
      have hz : ∀ j, raw14556 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw14556step0 = (fun i j => raw14556 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw14556step0 raw14556; decide +kernel
      have hl : raw14556step0Labels = raw14556Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14556 raw14556Labels permutation590 hz
    mixedMoment B raw14556step0 raw14556step0Labels = mixedMoment B raw14556step1 raw14556step1Labels := by
      have hz : ∀ j, raw14556step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw14556step1 = (fun i j => raw14556step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw14556step1 raw14556step0; decide +kernel
      have hl : raw14556step1Labels = raw14556step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14556step0 raw14556step0Labels permutation56 hz
    _ = mixedMoment B node4092 node4092Labels := by rfl

theorem canonical14557 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14557 raw14557Labels = mixedMoment B node3725 node3725Labels := by
  calc
    mixedMoment B raw14557 raw14557Labels = mixedMoment B raw14557step0 raw14557step0Labels := by
      have ha : raw14557step0 = (fun i j => raw14557 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw14557step0 raw14557; decide +kernel
      have hl : raw14557step0Labels = raw14557Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14557 raw14557Labels permutation158 permutation2
    _ = mixedMoment B node3725 node3725Labels := by rfl

theorem canonical14558 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14558 raw14558Labels = mixedMoment B node3722 node3722Labels := by
  calc
    _ = mixedMoment B node3722 node3722Labels := by rfl

theorem canonical14559 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14559 raw14559Labels = mixedMoment B node3715 node3715Labels := by
  calc
    mixedMoment B raw14559 raw14559Labels = mixedMoment B raw14559step0 raw14559step0Labels := by
      have ha : raw14559step0 = (fun i j => raw14559 (permutation153 i) (permutation2 j)) := by apply Matrix.ext; unfold raw14559step0 raw14559; decide +kernel
      have hl : raw14559step0Labels = raw14559Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14559 raw14559Labels permutation153 permutation2
    _ = mixedMoment B node3715 node3715Labels := by rfl

theorem canonical14560 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14560 raw14560Labels = mixedMoment B node3168 node3168Labels := by
  calc
    mixedMoment B raw14560 raw14560Labels = mixedMoment B raw14560step0 raw14560step0Labels := by
      have ha : raw14560step0 = (fun i j => raw14560 (permutation688 i) (permutation2 j)) := by apply Matrix.ext; unfold raw14560step0 raw14560; decide +kernel
      have hl : raw14560step0Labels = raw14560Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14560 raw14560Labels permutation688 permutation2
    mixedMoment B raw14560step0 raw14560step0Labels = mixedMoment B raw14560step1 raw14560step1Labels := by
      have ha : raw14560step1 = -raw14560step0 := by apply Matrix.ext; change ∀ i j, raw14560step1 i j = -(raw14560step0 i j); unfold raw14560step1 raw14560step0; decide +kernel
      have hl : raw14560step1Labels = raw14560step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3168 node3168Labels := by rfl

theorem canonical14561 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14561 raw14561Labels = mixedMoment B node2568 node2568Labels := by
  calc
    mixedMoment B raw14561 raw14561Labels = mixedMoment B raw14561step0 raw14561step0Labels := by
      have ha : raw14561step0 = (fun i j => raw14561 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw14561step0 raw14561; decide +kernel
      have hl : raw14561step0Labels = raw14561Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14561 raw14561Labels permutation158 permutation2
    _ = mixedMoment B node2568 node2568Labels := by rfl

theorem canonical14562 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14562 raw14562Labels = mixedMoment B node3828 node3828Labels := by
  calc
    mixedMoment B raw14562 raw14562Labels = mixedMoment B raw14562step0 raw14562step0Labels := by
      have ha : raw14562step0 = (fun i j => raw14562 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw14562step0 raw14562; decide +kernel
      have hl : raw14562step0Labels = raw14562Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14562 raw14562Labels permutation158 permutation2
    _ = mixedMoment B node3828 node3828Labels := by rfl

theorem canonical14563 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14563 raw14563Labels = mixedMoment B node3780 node3780Labels := by
  calc
    mixedMoment B raw14563 raw14563Labels = mixedMoment B raw14563step0 raw14563step0Labels := by
      have ha : raw14563step0 = (fun i j => raw14563 (permutation555 i) (permutation4 j)) := by apply Matrix.ext; unfold raw14563step0 raw14563; decide +kernel
      have hl : raw14563step0Labels = raw14563Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14563 raw14563Labels permutation555 permutation4
    mixedMoment B raw14563step0 raw14563step0Labels = mixedMoment B raw14563step1 raw14563step1Labels := by
      have ha : raw14563step1 = -raw14563step0 := by apply Matrix.ext; change ∀ i j, raw14563step1 i j = -(raw14563step0 i j); unfold raw14563step1 raw14563step0; decide +kernel
      have hl : raw14563step1Labels = raw14563step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3780 node3780Labels := by rfl

theorem canonical14564 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14564 raw14564Labels = mixedMoment B node3848 node3848Labels := by
  calc
    mixedMoment B raw14564 raw14564Labels = mixedMoment B raw14564step0 raw14564step0Labels := by
      have ha : raw14564step0 = (fun i j => raw14564 (permutation159 i) (permutation2 j)) := by apply Matrix.ext; unfold raw14564step0 raw14564; decide +kernel
      have hl : raw14564step0Labels = raw14564Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14564 raw14564Labels permutation159 permutation2
    _ = mixedMoment B node3848 node3848Labels := by rfl

theorem canonical14565 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14565 raw14565Labels = mixedMoment B node3809 node3809Labels := by
  calc
    mixedMoment B raw14565 raw14565Labels = mixedMoment B raw14565step0 raw14565step0Labels := by
      have hz : ∀ j, raw14565 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw14565step0 = (fun i j => raw14565 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw14565step0 raw14565; decide +kernel
      have hl : raw14565step0Labels = raw14565Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14565 raw14565Labels permutation265 hz
    _ = mixedMoment B node3809 node3809Labels := by rfl

theorem canonical14566 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14566 raw14566Labels = mixedMoment B node3782 node3782Labels := by
  calc
    mixedMoment B raw14566 raw14566Labels = mixedMoment B raw14566step0 raw14566step0Labels := by
      have ha : raw14566step0 = (fun i j => raw14566 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw14566step0 raw14566; decide +kernel
      have hl : raw14566step0Labels = raw14566Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14566 raw14566Labels permutation176 permutation2
    _ = mixedMoment B node3782 node3782Labels := by rfl

theorem canonical14567 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14567 raw14567Labels = mixedMoment B node3719 node3719Labels := by
  calc
    mixedMoment B raw14567 raw14567Labels = mixedMoment B raw14567step0 raw14567step0Labels := by
      have ha : raw14567step0 = (fun i j => raw14567 (permutation587 i) (permutation2 j)) := by apply Matrix.ext; unfold raw14567step0 raw14567; decide +kernel
      have hl : raw14567step0Labels = raw14567Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14567 raw14567Labels permutation587 permutation2
    mixedMoment B raw14567step0 raw14567step0Labels = mixedMoment B raw14567step1 raw14567step1Labels := by
      have ha : raw14567step1 = -raw14567step0 := by apply Matrix.ext; change ∀ i j, raw14567step1 i j = -(raw14567step0 i j); unfold raw14567step1 raw14567step0; decide +kernel
      have hl : raw14567step1Labels = raw14567step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3719 node3719Labels := by rfl

theorem canonical14568 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14568 raw14568Labels = mixedMoment B node3170 node3170Labels := by
  calc
    mixedMoment B raw14568 raw14568Labels = mixedMoment B raw14568step0 raw14568step0Labels := by
      have ha : raw14568step0 = (fun i j => raw14568 (permutation686 i) (permutation2 j)) := by apply Matrix.ext; unfold raw14568step0 raw14568; decide +kernel
      have hl : raw14568step0Labels = raw14568Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14568 raw14568Labels permutation686 permutation2
    mixedMoment B raw14568step0 raw14568step0Labels = mixedMoment B raw14568step1 raw14568step1Labels := by
      have ha : raw14568step1 = -raw14568step0 := by apply Matrix.ext; change ∀ i j, raw14568step1 i j = -(raw14568step0 i j); unfold raw14568step1 raw14568step0; decide +kernel
      have hl : raw14568step1Labels = raw14568step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3170 node3170Labels := by rfl

theorem canonical14569 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14569 raw14569Labels = mixedMoment B node2557 node2557Labels := by
  calc
    _ = mixedMoment B node2557 node2557Labels := by rfl

theorem canonical14570 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14570 raw14570Labels = mixedMoment B node3841 node3841Labels := by
  calc
    mixedMoment B raw14570 raw14570Labels = mixedMoment B raw14570step0 raw14570step0Labels := by
      have ha : raw14570step0 = (fun i j => raw14570 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw14570step0 raw14570; decide +kernel
      have hl : raw14570step0Labels = raw14570Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14570 raw14570Labels permutation154 permutation2
    _ = mixedMoment B node3841 node3841Labels := by rfl

theorem canonical14571 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14571 raw14571Labels = mixedMoment B node3843 node3843Labels := by
  calc
    mixedMoment B raw14571 raw14571Labels = mixedMoment B raw14571step0 raw14571step0Labels := by
      have ha : raw14571step0 = (fun i j => raw14571 (permutation156 i) (permutation2 j)) := by apply Matrix.ext; unfold raw14571step0 raw14571; decide +kernel
      have hl : raw14571step0Labels = raw14571Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14571 raw14571Labels permutation156 permutation2
    _ = mixedMoment B node3843 node3843Labels := by rfl

theorem canonical14572 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14572 raw14572Labels = mixedMoment B node3877 node3877Labels := by
  calc
    mixedMoment B raw14572 raw14572Labels = mixedMoment B raw14572step0 raw14572step0Labels := by
      have hz : ∀ j, raw14572 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw14572step0 = (fun i j => raw14572 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw14572step0 raw14572; decide +kernel
      have hl : raw14572step0Labels = raw14572Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14572 raw14572Labels permutation265 hz
    mixedMoment B raw14572step0 raw14572step0Labels = mixedMoment B raw14572step1 raw14572step1Labels := by
      have ha : raw14572step1 = (fun i j => raw14572step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw14572step1 raw14572step0; decide +kernel
      have hl : raw14572step1Labels = raw14572step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14572step0 raw14572step0Labels permutation38 permutation2
    _ = mixedMoment B node3877 node3877Labels := by rfl

theorem canonical14573 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14573 raw14573Labels = mixedMoment B node3723 node3723Labels := by
  calc
    mixedMoment B raw14573 raw14573Labels = mixedMoment B raw14573step0 raw14573step0Labels := by
      have ha : raw14573step0 = (fun i j => raw14573 (permutation584 i) (permutation2 j)) := by apply Matrix.ext; unfold raw14573step0 raw14573; decide +kernel
      have hl : raw14573step0Labels = raw14573Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14573 raw14573Labels permutation584 permutation2
    mixedMoment B raw14573step0 raw14573step0Labels = mixedMoment B raw14573step1 raw14573step1Labels := by
      have ha : raw14573step1 = -raw14573step0 := by apply Matrix.ext; change ∀ i j, raw14573step1 i j = -(raw14573step0 i j); unfold raw14573step1 raw14573step0; decide +kernel
      have hl : raw14573step1Labels = raw14573step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3723 node3723Labels := by rfl

theorem canonical14574 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14574 raw14574Labels = mixedMoment B node3175 node3175Labels := by
  calc
    mixedMoment B raw14574 raw14574Labels = mixedMoment B raw14574step0 raw14574step0Labels := by
      have ha : raw14574step0 = (fun i j => raw14574 (permutation682 i) (permutation2 j)) := by apply Matrix.ext; unfold raw14574step0 raw14574; decide +kernel
      have hl : raw14574step0Labels = raw14574Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14574 raw14574Labels permutation682 permutation2
    mixedMoment B raw14574step0 raw14574step0Labels = mixedMoment B raw14574step1 raw14574step1Labels := by
      have ha : raw14574step1 = -raw14574step0 := by apply Matrix.ext; change ∀ i j, raw14574step1 i j = -(raw14574step0 i j); unfold raw14574step1 raw14574step0; decide +kernel
      have hl : raw14574step1Labels = raw14574step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3175 node3175Labels := by rfl

theorem canonical14575 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14575 raw14575Labels = mixedMoment B node2545 node2545Labels := by
  calc
    mixedMoment B raw14575 raw14575Labels = mixedMoment B raw14575step0 raw14575step0Labels := by
      have ha : raw14575step0 = (fun i j => raw14575 (permutation153 i) (permutation2 j)) := by apply Matrix.ext; unfold raw14575step0 raw14575; decide +kernel
      have hl : raw14575step0Labels = raw14575Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14575 raw14575Labels permutation153 permutation2
    _ = mixedMoment B node2545 node2545Labels := by rfl

theorem canonical14576 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14576 raw14576Labels = mixedMoment B node3837 node3837Labels := by
  calc
    mixedMoment B raw14576 raw14576Labels = mixedMoment B raw14576step0 raw14576step0Labels := by
      have ha : raw14576step0 = (fun i j => raw14576 (permutation153 i) (permutation2 j)) := by apply Matrix.ext; unfold raw14576step0 raw14576; decide +kernel
      have hl : raw14576step0Labels = raw14576Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14576 raw14576Labels permutation153 permutation2
    _ = mixedMoment B node3837 node3837Labels := by rfl

theorem canonical14577 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14577 raw14577Labels = mixedMoment B node3814 node3814Labels := by
  calc
    mixedMoment B raw14577 raw14577Labels = mixedMoment B raw14577step0 raw14577step0Labels := by
      have hz : ∀ j, raw14577 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw14577step0 = (fun i j => raw14577 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw14577step0 raw14577; decide +kernel
      have hl : raw14577step0Labels = raw14577Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14577 raw14577Labels permutation265 hz
    mixedMoment B raw14577step0 raw14577step0Labels = mixedMoment B raw14577step1 raw14577step1Labels := by
      have ha : raw14577step1 = (fun i j => raw14577step0 (permutation116 i) (permutation4 j)) := by apply Matrix.ext; unfold raw14577step1 raw14577step0; decide +kernel
      have hl : raw14577step1Labels = raw14577step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14577step0 raw14577step0Labels permutation116 permutation4
    mixedMoment B raw14577step1 raw14577step1Labels = mixedMoment B raw14577step2 raw14577step2Labels := by
      have ha : raw14577step2 = -raw14577step1 := by apply Matrix.ext; change ∀ i j, raw14577step2 i j = -(raw14577step1 i j); unfold raw14577step2 raw14577step1; decide +kernel
      have hl : raw14577step2Labels = raw14577step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3814 node3814Labels := by rfl

theorem canonical14578 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14578 raw14578Labels = mixedMoment B node3196 node3196Labels := by
  calc
    mixedMoment B raw14578 raw14578Labels = mixedMoment B raw14578step0 raw14578step0Labels := by
      have ha : raw14578step0 = (fun i j => raw14578 (permutation623 i) (permutation4 j)) := by apply Matrix.ext; unfold raw14578step0 raw14578; decide +kernel
      have hl : raw14578step0Labels = raw14578Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14578 raw14578Labels permutation623 permutation4
    _ = mixedMoment B node3196 node3196Labels := by rfl

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

theorem canonical2430 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2430 raw2430Labels = mixedMoment B node5378 node5378Labels := by
  calc
    mixedMoment B raw2430 raw2430Labels = mixedMoment B raw2430step0 raw2430step0Labels := by
      have ha : raw2430step0 = (fun i j => raw2430 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2430step0 raw2430; decide +kernel
      have hl : raw2430step0Labels = raw2430Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2430 raw2430Labels permutation152 permutation4
    mixedMoment B raw2430step0 raw2430step0Labels = mixedMoment B raw2430step1 raw2430step1Labels := by
      have ha : raw2430step1 = raw2430step0 := by apply Matrix.ext; unfold raw2430step1 raw2430step0; decide +kernel
      have hl : raw2430step0Labels = labelEmbedding7 ∘ raw2430step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2430step0 raw2430step0Labels raw2430step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5378 node5378Labels := by rfl

theorem canonical2431 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2431 raw2431Labels = mixedMoment B node3719 node3719Labels := by
  calc
    mixedMoment B raw2431 raw2431Labels = mixedMoment B raw2431step0 raw2431step0Labels := by
      have ha : raw2431step0 = (fun i j => raw2431 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2431step0 raw2431; decide +kernel
      have hl : raw2431step0Labels = raw2431Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2431 raw2431Labels permutation152 permutation4
    _ = mixedMoment B node3719 node3719Labels := by rfl

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

theorem canonical2432 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2432 raw2432Labels = mixedMoment B node3795 node3795Labels := by
  calc
    mixedMoment B raw2432 raw2432Labels = mixedMoment B raw2432step0 raw2432step0Labels := by
      have ha : raw2432step0 = (fun i j => raw2432 (permutation686 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2432step0 raw2432; decide +kernel
      have hl : raw2432step0Labels = raw2432Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2432 raw2432Labels permutation686 permutation6
    mixedMoment B raw2432step0 raw2432step0Labels = mixedMoment B raw2432step1 raw2432step1Labels := by
      have ha : raw2432step1 = raw2432step0 := by apply Matrix.ext; unfold raw2432step1 raw2432step0; decide +kernel
      have hl : raw2432step0Labels = labelEmbedding1 ∘ raw2432step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2432step0 raw2432step0Labels raw2432step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3795 node3795Labels := by rfl

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

theorem canonical2511 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2511 raw2511Labels = mixedMoment B node5423 node5423Labels := by
  calc
    mixedMoment B raw2511 raw2511Labels = mixedMoment B raw2511step0 raw2511step0Labels := by
      have ha : raw2511step0 = (fun i j => raw2511 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2511step0 raw2511; decide +kernel
      have hl : raw2511step0Labels = raw2511Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2511 raw2511Labels permutation152 permutation4
    mixedMoment B raw2511step0 raw2511step0Labels = mixedMoment B raw2511step1 raw2511step1Labels := by
      have ha : raw2511step1 = raw2511step0 := by apply Matrix.ext; unfold raw2511step1 raw2511step0; decide +kernel
      have hl : raw2511step0Labels = labelEmbedding7 ∘ raw2511step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2511step0 raw2511step0Labels raw2511step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5423 node5423Labels := by rfl

theorem canonical2512 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2512 raw2512Labels = mixedMoment B node3837 node3837Labels := by
  calc
    mixedMoment B raw2512 raw2512Labels = mixedMoment B raw2512step0 raw2512step0Labels := by
      have ha : raw2512step0 = (fun i j => raw2512 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2512step0 raw2512; decide +kernel
      have hl : raw2512step0Labels = raw2512Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2512 raw2512Labels permutation152 permutation4
    _ = mixedMoment B node3837 node3837Labels := by rfl

theorem canonical2513 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2513 raw2513Labels = mixedMoment B node3837 node3837Labels := by
  calc
    mixedMoment B raw2513 raw2513Labels = mixedMoment B raw2513step0 raw2513step0Labels := by
      have ha : raw2513step0 = (fun i j => raw2513 (permutation662 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2513step0 raw2513; decide +kernel
      have hl : raw2513step0Labels = raw2513Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2513 raw2513Labels permutation662 permutation6
    mixedMoment B raw2513step0 raw2513step0Labels = mixedMoment B raw2513step1 raw2513step1Labels := by
      have ha : raw2513step1 = raw2513step0 := by apply Matrix.ext; unfold raw2513step1 raw2513step0; decide +kernel
      have hl : raw2513step0Labels = labelEmbedding1 ∘ raw2513step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2513step0 raw2513step0Labels raw2513step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3837 node3837Labels := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_FiniteSums
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sum_fin_six {R : Type*} [AddCommMonoid R] (f : Fin 6 → R) :
    ∑ i, f i = f 0 + f 1 + f 2 + f 3 + f 4 + f 5 := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change f 0 + (f 1 + (f 2 + (f 3 + (f 4 + f 5)))) = _
  ac_rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons84
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singleton5378 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5378 node5378Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3719 node3719Labels + mixedMoment B node3795 node3795Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2430 singletonSmall5378
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5378) = raw2430Labels := by decide +kernel
  rw [hl, canonical2430 B hB] at h
  have hc0 : mixedMoment B raw2430 (Fin.cases (0 : Fin 2) singletonSmall5378) =
      mixedMoment B node3719 node3719Labels := by
    have ha : raw2430 = raw2431 := by apply Matrix.ext; unfold raw2430 raw2431; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5378 = raw2431Labels := by decide +kernel
    rw [ha, hj, canonical2431 B hB]
  have hc1 : mixedMoment B raw2430 (Fin.cases (1 : Fin 2) singletonSmall5378) =
      mixedMoment B node3795 node3795Labels := by
    have ha : raw2430 = raw2432 := by apply Matrix.ext; unfold raw2430 raw2432; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5378 = raw2432Labels := by decide +kernel
    rw [ha, hj, canonical2432 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

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

theorem singleton5423 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5423 node5423Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3837 node3837Labels + mixedMoment B node3837 node3837Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2511 singletonSmall5423
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5423) = raw2511Labels := by decide +kernel
  rw [hl, canonical2511 B hB] at h
  have hc0 : mixedMoment B raw2511 (Fin.cases (0 : Fin 2) singletonSmall5423) =
      mixedMoment B node3837 node3837Labels := by
    have ha : raw2511 = raw2512 := by apply Matrix.ext; unfold raw2511 raw2512; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5423 = raw2512Labels := by decide +kernel
    rw [ha, hj, canonical2512 B hB]
  have hc1 : mixedMoment B raw2511 (Fin.cases (1 : Fin 2) singletonSmall5423) =
      mixedMoment B node3837 node3837Labels := by
    have ha : raw2511 = raw2513 := by apply Matrix.ext; unfold raw2511 raw2513; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5423 = raw2513Labels := by decide +kernel
    rw [ha, hj, canonical2513 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

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

theorem zero5477 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node5477 node5477Labels = 0 := by
  exact mixedMoment_alpha B hF node5477 node5477Labels 2 permutation152
    (by decide +kernel)

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound38
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound2474 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2474 node2474Labels = Sparse.eval nodeValue2474 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2474) = mixedMoment B node2474 node2474Labels := rfl
  simpa [nodeValue2474, Sparse.eval] using hc.symm

theorem sound2475 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2475 node2475Labels = Sparse.eval nodeValue2475 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2475) = mixedMoment B node2475 node2475Labels := rfl
  simpa [nodeValue2475, Sparse.eval] using hc.symm

theorem sound2481 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2481 node2481Labels = Sparse.eval nodeValue2481 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2481) = mixedMoment B node2481 node2481Labels := rfl
  simpa [nodeValue2481, Sparse.eval] using hc.symm

theorem sound2494 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2494 node2494Labels = Sparse.eval nodeValue2494 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2494) = mixedMoment B node2494 node2494Labels := rfl
  simpa [nodeValue2494, Sparse.eval] using hc.symm

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

theorem sound2545 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2545 node2545Labels = Sparse.eval nodeValue2545 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2545) = mixedMoment B node2545 node2545Labels := rfl
  simpa [nodeValue2545, Sparse.eval] using hc.symm

theorem sound2557 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2557 node2557Labels = Sparse.eval nodeValue2557 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2557) = mixedMoment B node2557 node2557Labels := rfl
  simpa [nodeValue2557, Sparse.eval] using hc.symm

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

theorem sound2568 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2568 node2568Labels = Sparse.eval nodeValue2568 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2568) = mixedMoment B node2568 node2568Labels := rfl
  simpa [nodeValue2568, Sparse.eval] using hc.symm

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

theorem sound2714 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2714 node2714Labels = Sparse.eval nodeValue2714 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2714) = mixedMoment B node2714 node2714Labels := rfl
  simpa [nodeValue2714, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound49
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound3168 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3168 node3168Labels = Sparse.eval nodeValue3168 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3168) = mixedMoment B node3168 node3168Labels := rfl
  simpa [nodeValue3168, Sparse.eval] using hc.symm

theorem sound3170 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3170 node3170Labels = Sparse.eval nodeValue3170 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3170) = mixedMoment B node3170 node3170Labels := rfl
  simpa [nodeValue3170, Sparse.eval] using hc.symm

theorem sound3175 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3175 node3175Labels = Sparse.eval nodeValue3175 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3175) = mixedMoment B node3175 node3175Labels := rfl
  simpa [nodeValue3175, Sparse.eval] using hc.symm

theorem sound3196 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3196 node3196Labels = Sparse.eval nodeValue3196 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3196) = mixedMoment B node3196 node3196Labels := rfl
  simpa [nodeValue3196, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound50
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound3217 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3217 node3217Labels = Sparse.eval nodeValue3217 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3217) = mixedMoment B node3217 node3217Labels := rfl
  simpa [nodeValue3217, Sparse.eval] using hc.symm

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

theorem sound3686 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3686 node3686Labels = Sparse.eval nodeValue3686 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3686) = mixedMoment B node3686 node3686Labels := rfl
  simpa [nodeValue3686, Sparse.eval] using hc.symm

theorem sound3691 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3691 node3691Labels = Sparse.eval nodeValue3691 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3691) = mixedMoment B node3691 node3691Labels := rfl
  simpa [nodeValue3691, Sparse.eval] using hc.symm

theorem sound3698 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3698 node3698Labels = Sparse.eval nodeValue3698 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3698) = mixedMoment B node3698 node3698Labels := rfl
  simpa [nodeValue3698, Sparse.eval] using hc.symm

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

theorem sound3715 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3715 node3715Labels = Sparse.eval nodeValue3715 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3715) = mixedMoment B node3715 node3715Labels := rfl
  simpa [nodeValue3715, Sparse.eval] using hc.symm

theorem sound3719 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3719 node3719Labels = Sparse.eval nodeValue3719 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3719) = mixedMoment B node3719 node3719Labels := rfl
  simpa [nodeValue3719, Sparse.eval] using hc.symm

theorem sound3722 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3722 node3722Labels = Sparse.eval nodeValue3722 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3722) = mixedMoment B node3722 node3722Labels := rfl
  simpa [nodeValue3722, Sparse.eval] using hc.symm

theorem sound3723 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3723 node3723Labels = Sparse.eval nodeValue3723 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3723) = mixedMoment B node3723 node3723Labels := rfl
  simpa [nodeValue3723, Sparse.eval] using hc.symm

theorem sound3725 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3725 node3725Labels = Sparse.eval nodeValue3725 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3725) = mixedMoment B node3725 node3725Labels := rfl
  simpa [nodeValue3725, Sparse.eval] using hc.symm

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

theorem sound3780 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3780 node3780Labels = Sparse.eval nodeValue3780 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3780) = mixedMoment B node3780 node3780Labels := rfl
  simpa [nodeValue3780, Sparse.eval] using hc.symm

theorem sound3782 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3782 node3782Labels = Sparse.eval nodeValue3782 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3782) = mixedMoment B node3782 node3782Labels := rfl
  simpa [nodeValue3782, Sparse.eval] using hc.symm

theorem sound3788 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3788 node3788Labels = Sparse.eval nodeValue3788 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3788) = mixedMoment B node3788 node3788Labels := rfl
  simpa [nodeValue3788, Sparse.eval] using hc.symm

theorem sound3795 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3795 node3795Labels = Sparse.eval nodeValue3795 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3795) = mixedMoment B node3795 node3795Labels := rfl
  simpa [nodeValue3795, Sparse.eval] using hc.symm

theorem sound3796 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3796 node3796Labels = Sparse.eval nodeValue3796 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3796) = mixedMoment B node3796 node3796Labels := rfl
  simpa [nodeValue3796, Sparse.eval] using hc.symm

theorem sound3803 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3803 node3803Labels = Sparse.eval nodeValue3803 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3803) = mixedMoment B node3803 node3803Labels := rfl
  simpa [nodeValue3803, Sparse.eval] using hc.symm

theorem sound3805 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3805 node3805Labels = Sparse.eval nodeValue3805 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3805) = mixedMoment B node3805 node3805Labels := rfl
  simpa [nodeValue3805, Sparse.eval] using hc.symm

theorem sound3809 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3809 node3809Labels = Sparse.eval nodeValue3809 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3809) = mixedMoment B node3809 node3809Labels := rfl
  simpa [nodeValue3809, Sparse.eval] using hc.symm

theorem sound3812 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3812 node3812Labels = Sparse.eval nodeValue3812 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3812) = mixedMoment B node3812 node3812Labels := rfl
  simpa [nodeValue3812, Sparse.eval] using hc.symm

theorem sound3813 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3813 node3813Labels = Sparse.eval nodeValue3813 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3813) = mixedMoment B node3813 node3813Labels := rfl
  simpa [nodeValue3813, Sparse.eval] using hc.symm

theorem sound3828 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3828 node3828Labels = Sparse.eval nodeValue3828 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3828) = mixedMoment B node3828 node3828Labels := rfl
  simpa [nodeValue3828, Sparse.eval] using hc.symm

theorem sound3837 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3837 node3837Labels = Sparse.eval nodeValue3837 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3837) = mixedMoment B node3837 node3837Labels := rfl
  simpa [nodeValue3837, Sparse.eval] using hc.symm

theorem sound3838 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3838 node3838Labels = Sparse.eval nodeValue3838 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3838) = mixedMoment B node3838 node3838Labels := rfl
  simpa [nodeValue3838, Sparse.eval] using hc.symm

theorem sound3839 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3839 node3839Labels = Sparse.eval nodeValue3839 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3839) = mixedMoment B node3839 node3839Labels := rfl
  simpa [nodeValue3839, Sparse.eval] using hc.symm

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

theorem sound3841 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3841 node3841Labels = Sparse.eval nodeValue3841 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3841) = mixedMoment B node3841 node3841Labels := rfl
  simpa [nodeValue3841, Sparse.eval] using hc.symm

theorem sound3843 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3843 node3843Labels = Sparse.eval nodeValue3843 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3843) = mixedMoment B node3843 node3843Labels := rfl
  simpa [nodeValue3843, Sparse.eval] using hc.symm

theorem sound3848 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3848 node3848Labels = Sparse.eval nodeValue3848 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3848) = mixedMoment B node3848 node3848Labels := rfl
  simpa [nodeValue3848, Sparse.eval] using hc.symm

theorem sound3877 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3877 node3877Labels = Sparse.eval nodeValue3877 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3877) = mixedMoment B node3877 node3877Labels := rfl
  simpa [nodeValue3877, Sparse.eval] using hc.symm

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

theorem sound3946 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3946 node3946Labels = Sparse.eval nodeValue3946 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3946) = mixedMoment B node3946 node3946Labels := rfl
  simpa [nodeValue3946, Sparse.eval] using hc.symm

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

theorem sound4022 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4022 node4022Labels = Sparse.eval nodeValue4022 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4022) = mixedMoment B node4022 node4022Labels := rfl
  simpa [nodeValue4022, Sparse.eval] using hc.symm

theorem sound4024 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4024 node4024Labels = Sparse.eval nodeValue4024 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4024) = mixedMoment B node4024 node4024Labels := rfl
  simpa [nodeValue4024, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros63
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero4044 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node4044 node4044Labels = 0 := by
  exact mixedMoment_alpha B hF node4044 node4044Labels 0 permutation499
    (by decide +kernel)

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

theorem sound4044 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4044 node4044Labels = Sparse.eval nodeValue4044 (mixedVector B) := by
  simpa only [nodeValue4044, Sparse.eval_nil] using zero4044 B _hB _hF

theorem sound4092 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4092 node4092Labels = Sparse.eval nodeValue4092 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4092) = mixedMoment B node4092 node4092Labels := rfl
  simpa [nodeValue4092, Sparse.eval] using hc.symm

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

theorem sound4812 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4812 node4812Labels = Sparse.eval nodeValue4812 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4812) = mixedMoment B node4812 node4812Labels := rfl
  simpa [nodeValue4812, Sparse.eval] using hc.symm

theorem sound4813 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4813 node4813Labels = Sparse.eval nodeValue4813 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4813) = mixedMoment B node4813 node4813Labels := rfl
  simpa [nodeValue4813, Sparse.eval] using hc.symm

theorem sound4816 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4816 node4816Labels = Sparse.eval nodeValue4816 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4816) = mixedMoment B node4816 node4816Labels := rfl
  simpa [nodeValue4816, Sparse.eval] using hc.symm

theorem sound4824 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4824 node4824Labels = Sparse.eval nodeValue4824 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4824) = mixedMoment B node4824 node4824Labels := rfl
  simpa [nodeValue4824, Sparse.eval] using hc.symm

theorem sound4852 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4852 node4852Labels = Sparse.eval nodeValue4852 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4852) = mixedMoment B node4852 node4852Labels := rfl
  simpa [nodeValue4852, Sparse.eval] using hc.symm

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

theorem sound5146 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5146 node5146Labels = Sparse.eval nodeValue5146 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5146) = mixedMoment B node5146 node5146Labels := rfl
  simpa [nodeValue5146, Sparse.eval] using hc.symm

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

theorem sound5260 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5260 node5260Labels = Sparse.eval nodeValue5260 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5260) = mixedMoment B node5260 node5260Labels := rfl
  simpa [nodeValue5260, Sparse.eval] using hc.symm

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

theorem sound5357 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5357 node5357Labels = Sparse.eval nodeValue5357 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5357) = mixedMoment B node5357 node5357Labels := rfl
  simpa [nodeValue5357, Sparse.eval] using hc.symm

theorem sound5358 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5358 node5358Labels = Sparse.eval nodeValue5358 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5358) = mixedMoment B node5358 node5358Labels := rfl
  simpa [nodeValue5358, Sparse.eval] using hc.symm

theorem sound5360 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5360 node5360Labels = Sparse.eval nodeValue5360 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5360) = mixedMoment B node5360 node5360Labels := rfl
  simpa [nodeValue5360, Sparse.eval] using hc.symm

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

theorem sound5376 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5376 node5376Labels = Sparse.eval nodeValue5376 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5376) = mixedMoment B node5376 node5376Labels := rfl
  simpa [nodeValue5376, Sparse.eval] using hc.symm

theorem sound5378 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5378 node5378Labels = Sparse.eval nodeValue5378 (mixedVector B) := by
  have h := singleton5378 B _hB
  rw [sound3719 B _hB _hF, sound3795 B _hB _hF] at h
  norm_num [nodeValue5378, nodeValue3719, nodeValue3795, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5381 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5381 node5381Labels = Sparse.eval nodeValue5381 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5381) = mixedMoment B node5381 node5381Labels := rfl
  simpa [nodeValue5381, Sparse.eval] using hc.symm

theorem sound5397 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5397 node5397Labels = Sparse.eval nodeValue5397 (mixedVector B) := by
  have h := singleton5397 B _hB
  rw [sound3782 B _hB _hF, sound3796 B _hB _hF] at h
  norm_num [nodeValue5397, nodeValue3782, nodeValue3796, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5411 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5411 node5411Labels = Sparse.eval nodeValue5411 (mixedVector B) := by
  have h := singleton5411 B _hB
  rw [sound3809 B _hB _hF, sound3813 B _hB _hF] at h
  norm_num [nodeValue5411, nodeValue3809, nodeValue3813, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5420 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5420 node5420Labels = Sparse.eval nodeValue5420 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5420) = mixedMoment B node5420 node5420Labels := rfl
  simpa [nodeValue5420, Sparse.eval] using hc.symm

theorem sound5421 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5421 node5421Labels = Sparse.eval nodeValue5421 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5421) = mixedMoment B node5421 node5421Labels := rfl
  simpa [nodeValue5421, Sparse.eval] using hc.symm

theorem sound5423 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5423 node5423Labels = Sparse.eval nodeValue5423 (mixedVector B) := by
  have h := singleton5423 B _hB
  rw [sound3837 B _hB _hF] at h
  norm_num [nodeValue5423, nodeValue3837, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5424 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5424 node5424Labels = Sparse.eval nodeValue5424 (mixedVector B) := by
  have h := singleton5424 B _hB
  rw [sound3838 B _hB _hF, sound3843 B _hB _hF] at h
  norm_num [nodeValue5424, nodeValue3838, nodeValue3843, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5426 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5426 node5426Labels = Sparse.eval nodeValue5426 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5426) = mixedMoment B node5426 node5426Labels := rfl
  simpa [nodeValue5426, Sparse.eval] using hc.symm

theorem sound5430 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5430 node5430Labels = Sparse.eval nodeValue5430 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5430) = mixedMoment B node5430 node5430Labels := rfl
  simpa [nodeValue5430, Sparse.eval] using hc.symm

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

theorem sound5445 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5445 node5445Labels = Sparse.eval nodeValue5445 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5445) = mixedMoment B node5445 node5445Labels := rfl
  simpa [nodeValue5445, Sparse.eval] using hc.symm

theorem sound5477 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5477 node5477Labels = Sparse.eval nodeValue5477 (mixedVector B) := by
  simpa only [nodeValue5477, Sparse.eval_nil] using zero5477 B _hB _hF

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources26
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sourceEq863 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm863 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA863 + difference 0 0) (sourceB863 + difference 0 0) sourceC863) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3803) := by
    have ha : (tripleCharges (sourceA863 + difference 0 0) (sourceB863 + difference 0 0) sourceC863) = raw14437 := by
      apply Matrix.ext; unfold tripleCharges sourceA863 sourceB863 sourceC863 difference raw14437; decide +kernel
    rw [ha]
    exact (canonical14437 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA863 + difference 0 1) (sourceB863 + difference 1 0) sourceC863) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3788) := by
    have ha : (tripleCharges (sourceA863 + difference 0 1) (sourceB863 + difference 1 0) sourceC863) = raw14438 := by
      apply Matrix.ext; unfold tripleCharges sourceA863 sourceB863 sourceC863 difference raw14438; decide +kernel
    rw [ha]
    exact (canonical14438 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA863 + difference 0 2) (sourceB863 + difference 2 0) sourceC863) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3691) := by
    have ha : (tripleCharges (sourceA863 + difference 0 2) (sourceB863 + difference 2 0) sourceC863) = raw14439 := by
      apply Matrix.ext; unfold tripleCharges sourceA863 sourceB863 sourceC863 difference raw14439; decide +kernel
    rw [ha]
    exact (canonical14439 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA863 + difference 0 3) (sourceB863 + difference 3 0) sourceC863) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2481) := by
    have ha : (tripleCharges (sourceA863 + difference 0 3) (sourceB863 + difference 3 0) sourceC863) = raw14440 := by
      apply Matrix.ext; unfold tripleCharges sourceA863 sourceB863 sourceC863 difference raw14440; decide +kernel
    rw [ha]
    exact (canonical14440 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA863 + difference 0 4) (sourceB863 + difference 4 0) sourceC863) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3809) := by
    have ha : (tripleCharges (sourceA863 + difference 0 4) (sourceB863 + difference 4 0) sourceC863) = raw14441 := by
      apply Matrix.ext; unfold tripleCharges sourceA863 sourceB863 sourceC863 difference raw14441; decide +kernel
    rw [ha]
    exact (canonical14441 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA863 + difference 0 5) (sourceB863 + difference 5 0) sourceC863) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3805) := by
    have ha : (tripleCharges (sourceA863 + difference 0 5) (sourceB863 + difference 5 0) sourceC863) = raw14442 := by
      apply Matrix.ext; unfold tripleCharges sourceA863 sourceB863 sourceC863 difference raw14442; decide +kernel
    rw [ha]
    exact (canonical14442 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA863 + sourceB863) sourceC863) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA863 + sourceB863) sourceC863) = raw14443 := by
      apply Matrix.ext; unfold doubleCharges sourceA863 sourceB863 sourceC863 raw14443; decide +kernel
    rw [ha]
    exact (canonical14443 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA863 sourceB863 sourceC863
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm863, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources27
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sourceEq864 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm864 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA864 + difference 0 0) (sourceB864 + difference 0 0) sourceC864) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3803) := by
    have ha : (tripleCharges (sourceA864 + difference 0 0) (sourceB864 + difference 0 0) sourceC864) = raw14437 := by
      apply Matrix.ext; unfold tripleCharges sourceA864 sourceB864 sourceC864 difference raw14437; decide +kernel
    rw [ha]
    exact (canonical14437 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA864 + difference 1 0) (sourceB864 + difference 0 1) sourceC864) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2714) := by
    have ha : (tripleCharges (sourceA864 + difference 1 0) (sourceB864 + difference 0 1) sourceC864) = raw14444 := by
      apply Matrix.ext; unfold tripleCharges sourceA864 sourceB864 sourceC864 difference raw14444; decide +kernel
    rw [ha]
    exact (canonical14444 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA864 + difference 2 0) (sourceB864 + difference 0 2) sourceC864) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2494) := by
    have ha : (tripleCharges (sourceA864 + difference 2 0) (sourceB864 + difference 0 2) sourceC864) = raw14445 := by
      apply Matrix.ext; unfold tripleCharges sourceA864 sourceB864 sourceC864 difference raw14445; decide +kernel
    rw [ha]
    exact (canonical14445 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA864 + difference 3 0) (sourceB864 + difference 0 3) sourceC864) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2481) := by
    have ha : (tripleCharges (sourceA864 + difference 3 0) (sourceB864 + difference 0 3) sourceC864) = raw14446 := by
      apply Matrix.ext; unfold tripleCharges sourceA864 sourceB864 sourceC864 difference raw14446; decide +kernel
    rw [ha]
    exact (canonical14446 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA864 + difference 4 0) (sourceB864 + difference 0 4) sourceC864) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2475) := by
    have ha : (tripleCharges (sourceA864 + difference 4 0) (sourceB864 + difference 0 4) sourceC864) = raw14447 := by
      apply Matrix.ext; unfold tripleCharges sourceA864 sourceB864 sourceC864 difference raw14447; decide +kernel
    rw [ha]
    exact (canonical14447 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA864 + difference 5 0) (sourceB864 + difference 0 5) sourceC864) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2474) := by
    have ha : (tripleCharges (sourceA864 + difference 5 0) (sourceB864 + difference 0 5) sourceC864) = raw14448 := by
      apply Matrix.ext; unfold tripleCharges sourceA864 sourceB864 sourceC864 difference raw14448; decide +kernel
    rw [ha]
    exact (canonical14448 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA864 + sourceB864) sourceC864) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA864 + sourceB864) sourceC864) = raw14443 := by
      apply Matrix.ext; unfold doubleCharges sourceA864 sourceB864 sourceC864 raw14443; decide +kernel
    rw [ha]
    exact (canonical14443 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA864 sourceB864 sourceC864
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm864, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq865 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm865 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA865 + difference 1 0) (sourceB865 + difference 0 1) sourceC865) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2714) := by
    have ha : (tripleCharges (sourceA865 + difference 1 0) (sourceB865 + difference 0 1) sourceC865) = raw14444 := by
      apply Matrix.ext; unfold tripleCharges sourceA865 sourceB865 sourceC865 difference raw14444; decide +kernel
    rw [ha]
    exact (canonical14444 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA865 + difference 1 1) (sourceB865 + difference 1 1) sourceC865) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3803) := by
    have ha : (tripleCharges (sourceA865 + difference 1 1) (sourceB865 + difference 1 1) sourceC865) = raw14437 := by
      apply Matrix.ext; unfold tripleCharges sourceA865 sourceB865 sourceC865 difference raw14437; decide +kernel
    rw [ha]
    exact (canonical14437 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA865 + difference 1 2) (sourceB865 + difference 2 1) sourceC865) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3698) := by
    have ha : (tripleCharges (sourceA865 + difference 1 2) (sourceB865 + difference 2 1) sourceC865) = raw14449 := by
      apply Matrix.ext; unfold tripleCharges sourceA865 sourceB865 sourceC865 difference raw14449; decide +kernel
    rw [ha]
    exact (canonical14449 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA865 + difference 1 3) (sourceB865 + difference 3 1) sourceC865) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2494) := by
    have ha : (tripleCharges (sourceA865 + difference 1 3) (sourceB865 + difference 3 1) sourceC865) = raw14450 := by
      apply Matrix.ext; unfold tripleCharges sourceA865 sourceB865 sourceC865 difference raw14450; decide +kernel
    rw [ha]
    exact (canonical14450 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA865 + difference 1 4) (sourceB865 + difference 4 1) sourceC865) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3814) := by
    have ha : (tripleCharges (sourceA865 + difference 1 4) (sourceB865 + difference 4 1) sourceC865) = raw14451 := by
      apply Matrix.ext; unfold tripleCharges sourceA865 sourceB865 sourceC865 difference raw14451; decide +kernel
    rw [ha]
    exact (canonical14451 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA865 + difference 1 5) (sourceB865 + difference 5 1) sourceC865) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3812) := by
    have ha : (tripleCharges (sourceA865 + difference 1 5) (sourceB865 + difference 5 1) sourceC865) = raw14452 := by
      apply Matrix.ext; unfold tripleCharges sourceA865 sourceB865 sourceC865 difference raw14452; decide +kernel
    rw [ha]
    exact (canonical14452 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA865 + sourceB865) sourceC865) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA865 + sourceB865) sourceC865) = raw14443 := by
      apply Matrix.ext; unfold doubleCharges sourceA865 sourceB865 sourceC865 raw14443; decide +kernel
    rw [ha]
    exact (canonical14443 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA865 sourceB865 sourceC865
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm865, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq866 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm866 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA866 + difference 0 1) (sourceB866 + difference 1 0) sourceC866) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3788) := by
    have ha : (tripleCharges (sourceA866 + difference 0 1) (sourceB866 + difference 1 0) sourceC866) = raw14438 := by
      apply Matrix.ext; unfold tripleCharges sourceA866 sourceB866 sourceC866 difference raw14438; decide +kernel
    rw [ha]
    exact (canonical14438 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA866 + difference 1 1) (sourceB866 + difference 1 1) sourceC866) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3803) := by
    have ha : (tripleCharges (sourceA866 + difference 1 1) (sourceB866 + difference 1 1) sourceC866) = raw14437 := by
      apply Matrix.ext; unfold tripleCharges sourceA866 sourceB866 sourceC866 difference raw14437; decide +kernel
    rw [ha]
    exact (canonical14437 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA866 + difference 2 1) (sourceB866 + difference 1 2) sourceC866) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3698) := by
    have ha : (tripleCharges (sourceA866 + difference 2 1) (sourceB866 + difference 1 2) sourceC866) = raw14453 := by
      apply Matrix.ext; unfold tripleCharges sourceA866 sourceB866 sourceC866 difference raw14453; decide +kernel
    rw [ha]
    exact (canonical14453 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA866 + difference 3 1) (sourceB866 + difference 1 3) sourceC866) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3691) := by
    have ha : (tripleCharges (sourceA866 + difference 3 1) (sourceB866 + difference 1 3) sourceC866) = raw14454 := by
      apply Matrix.ext; unfold tripleCharges sourceA866 sourceB866 sourceC866 difference raw14454; decide +kernel
    rw [ha]
    exact (canonical14454 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA866 + difference 4 1) (sourceB866 + difference 1 4) sourceC866) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3686) := by
    have ha : (tripleCharges (sourceA866 + difference 4 1) (sourceB866 + difference 1 4) sourceC866) = raw14455 := by
      apply Matrix.ext; unfold tripleCharges sourceA866 sourceB866 sourceC866 difference raw14455; decide +kernel
    rw [ha]
    exact (canonical14455 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA866 + difference 5 1) (sourceB866 + difference 1 5) sourceC866) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3217) := by
    have ha : (tripleCharges (sourceA866 + difference 5 1) (sourceB866 + difference 1 5) sourceC866) = raw14456 := by
      apply Matrix.ext; unfold tripleCharges sourceA866 sourceB866 sourceC866 difference raw14456; decide +kernel
    rw [ha]
    exact (canonical14456 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA866 + sourceB866) sourceC866) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA866 + sourceB866) sourceC866) = raw14443 := by
      apply Matrix.ext; unfold doubleCharges sourceA866 sourceB866 sourceC866 raw14443; decide +kernel
    rw [ha]
    exact (canonical14443 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA866 sourceB866 sourceC866
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm866, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq867 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm867 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA867 + difference 4 0) (sourceB867 + difference 0 4) sourceC867) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2475) := by
    have ha : (tripleCharges (sourceA867 + difference 4 0) (sourceB867 + difference 0 4) sourceC867) = raw14447 := by
      apply Matrix.ext; unfold tripleCharges sourceA867 sourceB867 sourceC867 difference raw14447; decide +kernel
    rw [ha]
    exact (canonical14447 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA867 + difference 4 1) (sourceB867 + difference 1 4) sourceC867) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3686) := by
    have ha : (tripleCharges (sourceA867 + difference 4 1) (sourceB867 + difference 1 4) sourceC867) = raw14455 := by
      apply Matrix.ext; unfold tripleCharges sourceA867 sourceB867 sourceC867 difference raw14455; decide +kernel
    rw [ha]
    exact (canonical14455 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA867 + difference 4 2) (sourceB867 + difference 2 4) sourceC867) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3686) := by
    have ha : (tripleCharges (sourceA867 + difference 4 2) (sourceB867 + difference 2 4) sourceC867) = raw14457 := by
      apply Matrix.ext; unfold tripleCharges sourceA867 sourceB867 sourceC867 difference raw14457; decide +kernel
    rw [ha]
    exact (canonical14457 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA867 + difference 4 3) (sourceB867 + difference 3 4) sourceC867) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2475) := by
    have ha : (tripleCharges (sourceA867 + difference 4 3) (sourceB867 + difference 3 4) sourceC867) = raw14458 := by
      apply Matrix.ext; unfold tripleCharges sourceA867 sourceB867 sourceC867 difference raw14458; decide +kernel
    rw [ha]
    exact (canonical14458 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA867 + difference 4 4) (sourceB867 + difference 4 4) sourceC867) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3803) := by
    have ha : (tripleCharges (sourceA867 + difference 4 4) (sourceB867 + difference 4 4) sourceC867) = raw14437 := by
      apply Matrix.ext; unfold tripleCharges sourceA867 sourceB867 sourceC867 difference raw14437; decide +kernel
    rw [ha]
    exact (canonical14437 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA867 + difference 4 5) (sourceB867 + difference 5 4) sourceC867) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3803) := by
    have ha : (tripleCharges (sourceA867 + difference 4 5) (sourceB867 + difference 5 4) sourceC867) = raw14459 := by
      apply Matrix.ext; unfold tripleCharges sourceA867 sourceB867 sourceC867 difference raw14459; decide +kernel
    rw [ha]
    exact (canonical14459 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA867 + sourceB867) sourceC867) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA867 + sourceB867) sourceC867) = raw14443 := by
      apply Matrix.ext; unfold doubleCharges sourceA867 sourceB867 sourceC867 raw14443; decide +kernel
    rw [ha]
    exact (canonical14443 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA867 sourceB867 sourceC867
    (0 : Fin 2) 1 (4 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm867, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq868 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm868 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA868 + difference 0 1) (sourceB868 + difference 1 0) sourceC868) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5420) := by
    have ha : (tripleCharges (sourceA868 + difference 0 1) (sourceB868 + difference 1 0) sourceC868) = raw14460 := by
      apply Matrix.ext; unfold tripleCharges sourceA868 sourceB868 sourceC868 difference raw14460; decide +kernel
    rw [ha]
    exact (canonical14460 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA868 + difference 0 2) (sourceB868 + difference 2 0) sourceC868) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5445) := by
    have ha : (tripleCharges (sourceA868 + difference 0 2) (sourceB868 + difference 2 0) sourceC868) = raw14461 := by
      apply Matrix.ext; unfold tripleCharges sourceA868 sourceB868 sourceC868 difference raw14461; decide +kernel
    rw [ha]
    exact (canonical14461 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA868 + difference 0 3) (sourceB868 + difference 3 0) sourceC868) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5421) := by
    have ha : (tripleCharges (sourceA868 + difference 0 3) (sourceB868 + difference 3 0) sourceC868) = raw14462 := by
      apply Matrix.ext; unfold tripleCharges sourceA868 sourceB868 sourceC868 difference raw14462; decide +kernel
    rw [ha]
    exact (canonical14462 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA868 + difference 0 4) (sourceB868 + difference 4 0) sourceC868) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5397) := by
    have ha : (tripleCharges (sourceA868 + difference 0 4) (sourceB868 + difference 4 0) sourceC868) = raw14463 := by
      apply Matrix.ext; unfold tripleCharges sourceA868 sourceB868 sourceC868 difference raw14463; decide +kernel
    rw [ha]
    exact (canonical14463 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA868 + difference 0 5) (sourceB868 + difference 5 0) sourceC868) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5477) := by
    have ha : (tripleCharges (sourceA868 + difference 0 5) (sourceB868 + difference 5 0) sourceC868) = raw14464 := by
      apply Matrix.ext; unfold tripleCharges sourceA868 sourceB868 sourceC868 difference raw14464; decide +kernel
    rw [ha]
    exact (canonical14464 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA868 + difference 1 0) (sourceB868 + difference 0 1) sourceC868) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5260) := by
    have ha : (tripleCharges (sourceA868 + difference 1 0) (sourceB868 + difference 0 1) sourceC868) = raw14465 := by
      apply Matrix.ext; unfold tripleCharges sourceA868 sourceB868 sourceC868 difference raw14465; decide +kernel
    rw [ha]
    exact (canonical14465 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA868 + difference 1 2) (sourceB868 + difference 2 1) sourceC868) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5411) := by
    have ha : (tripleCharges (sourceA868 + difference 1 2) (sourceB868 + difference 2 1) sourceC868) = raw14466 := by
      apply Matrix.ext; unfold tripleCharges sourceA868 sourceB868 sourceC868 difference raw14466; decide +kernel
    rw [ha]
    exact (canonical14466 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA868 + difference 1 3) (sourceB868 + difference 3 1) sourceC868) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5436) := by
    have ha : (tripleCharges (sourceA868 + difference 1 3) (sourceB868 + difference 3 1) sourceC868) = raw14467 := by
      apply Matrix.ext; unfold tripleCharges sourceA868 sourceB868 sourceC868 difference raw14467; decide +kernel
    rw [ha]
    exact (canonical14467 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA868 + difference 1 4) (sourceB868 + difference 4 1) sourceC868) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5412) := by
    have ha : (tripleCharges (sourceA868 + difference 1 4) (sourceB868 + difference 4 1) sourceC868) = raw14468 := by
      apply Matrix.ext; unfold tripleCharges sourceA868 sourceB868 sourceC868 difference raw14468; decide +kernel
    rw [ha]
    exact (canonical14468 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA868 + difference 1 5) (sourceB868 + difference 5 1) sourceC868) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5434) := by
    have ha : (tripleCharges (sourceA868 + difference 1 5) (sourceB868 + difference 5 1) sourceC868) = raw14469 := by
      apply Matrix.ext; unfold tripleCharges sourceA868 sourceB868 sourceC868 difference raw14469; decide +kernel
    rw [ha]
    exact (canonical14469 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA868 + difference 2 0) (sourceB868 + difference 0 2) sourceC868) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5146) := by
    have ha : (tripleCharges (sourceA868 + difference 2 0) (sourceB868 + difference 0 2) sourceC868) = raw14470 := by
      apply Matrix.ext; unfold tripleCharges sourceA868 sourceB868 sourceC868 difference raw14470; decide +kernel
    rw [ha]
    exact (canonical14470 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA868 + difference 2 1) (sourceB868 + difference 1 2) sourceC868) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5357) := by
    have ha : (tripleCharges (sourceA868 + difference 2 1) (sourceB868 + difference 1 2) sourceC868) = raw14471 := by
      apply Matrix.ext; unfold tripleCharges sourceA868 sourceB868 sourceC868 difference raw14471; decide +kernel
    rw [ha]
    exact (canonical14471 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA868 + difference 2 3) (sourceB868 + difference 3 2) sourceC868) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5358) := by
    have ha : (tripleCharges (sourceA868 + difference 2 3) (sourceB868 + difference 3 2) sourceC868) = raw14472 := by
      apply Matrix.ext; unfold tripleCharges sourceA868 sourceB868 sourceC868 difference raw14472; decide +kernel
    rw [ha]
    exact (canonical14472 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA868 + difference 2 4) (sourceB868 + difference 4 2) sourceC868) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5360) := by
    have ha : (tripleCharges (sourceA868 + difference 2 4) (sourceB868 + difference 4 2) sourceC868) = raw14473 := by
      apply Matrix.ext; unfold tripleCharges sourceA868 sourceB868 sourceC868 difference raw14473; decide +kernel
    rw [ha]
    exact (canonical14473 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA868 + difference 2 5) (sourceB868 + difference 5 2) sourceC868) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5430) := by
    have ha : (tripleCharges (sourceA868 + difference 2 5) (sourceB868 + difference 5 2) sourceC868) = raw14474 := by
      apply Matrix.ext; unfold tripleCharges sourceA868 sourceB868 sourceC868 difference raw14474; decide +kernel
    rw [ha]
    exact (canonical14474 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA868 + difference 3 0) (sourceB868 + difference 0 3) sourceC868) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5138) := by
    have ha : (tripleCharges (sourceA868 + difference 3 0) (sourceB868 + difference 0 3) sourceC868) = raw14475 := by
      apply Matrix.ext; unfold tripleCharges sourceA868 sourceB868 sourceC868 difference raw14475; decide +kernel
    rw [ha]
    exact (canonical14475 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA868 + difference 3 1) (sourceB868 + difference 1 3) sourceC868) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5381) := by
    have ha : (tripleCharges (sourceA868 + difference 3 1) (sourceB868 + difference 1 3) sourceC868) = raw14476 := by
      apply Matrix.ext; unfold tripleCharges sourceA868 sourceB868 sourceC868 difference raw14476; decide +kernel
    rw [ha]
    exact (canonical14476 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA868 + difference 3 2) (sourceB868 + difference 2 3) sourceC868) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5397) := by
    have ha : (tripleCharges (sourceA868 + difference 3 2) (sourceB868 + difference 2 3) sourceC868) = raw14477 := by
      apply Matrix.ext; unfold tripleCharges sourceA868 sourceB868 sourceC868 difference raw14477; decide +kernel
    rw [ha]
    exact (canonical14477 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA868 + difference 3 4) (sourceB868 + difference 4 3) sourceC868) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5426) := by
    have ha : (tripleCharges (sourceA868 + difference 3 4) (sourceB868 + difference 4 3) sourceC868) = raw14478 := by
      apply Matrix.ext; unfold tripleCharges sourceA868 sourceB868 sourceC868 difference raw14478; decide +kernel
    rw [ha]
    exact (canonical14478 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA868 + difference 3 5) (sourceB868 + difference 5 3) sourceC868) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5424) := by
    have ha : (tripleCharges (sourceA868 + difference 3 5) (sourceB868 + difference 5 3) sourceC868) = raw14479 := by
      apply Matrix.ext; unfold tripleCharges sourceA868 sourceB868 sourceC868 difference raw14479; decide +kernel
    rw [ha]
    exact (canonical14479 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA868 + difference 4 0) (sourceB868 + difference 0 4) sourceC868) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5129) := by
    have ha : (tripleCharges (sourceA868 + difference 4 0) (sourceB868 + difference 0 4) sourceC868) = raw14480 := by
      apply Matrix.ext; unfold tripleCharges sourceA868 sourceB868 sourceC868 difference raw14480; decide +kernel
    rw [ha]
    exact (canonical14480 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA868 + difference 4 1) (sourceB868 + difference 1 4) sourceC868) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5376) := by
    have ha : (tripleCharges (sourceA868 + difference 4 1) (sourceB868 + difference 1 4) sourceC868) = raw14481 := by
      apply Matrix.ext; unfold tripleCharges sourceA868 sourceB868 sourceC868 difference raw14481; decide +kernel
    rw [ha]
    exact (canonical14481 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA868 + difference 4 2) (sourceB868 + difference 2 4) sourceC868) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5378) := by
    have ha : (tripleCharges (sourceA868 + difference 4 2) (sourceB868 + difference 2 4) sourceC868) = raw14482 := by
      apply Matrix.ext; unfold tripleCharges sourceA868 sourceB868 sourceC868 difference raw14482; decide +kernel
    rw [ha]
    exact (canonical14482 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA868 + difference 4 3) (sourceB868 + difference 3 4) sourceC868) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5381) := by
    have ha : (tripleCharges (sourceA868 + difference 4 3) (sourceB868 + difference 3 4) sourceC868) = raw14483 := by
      apply Matrix.ext; unfold tripleCharges sourceA868 sourceB868 sourceC868 difference raw14483; decide +kernel
    rw [ha]
    exact (canonical14483 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA868 + difference 4 5) (sourceB868 + difference 5 4) sourceC868) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5423) := by
    have ha : (tripleCharges (sourceA868 + difference 4 5) (sourceB868 + difference 5 4) sourceC868) = raw14484 := by
      apply Matrix.ext; unfold tripleCharges sourceA868 sourceB868 sourceC868 difference raw14484; decide +kernel
    rw [ha]
    exact (canonical14484 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA868 + difference 5 0) (sourceB868 + difference 0 5) sourceC868) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4824) := by
    have ha : (tripleCharges (sourceA868 + difference 5 0) (sourceB868 + difference 0 5) sourceC868) = raw14485 := by
      apply Matrix.ext; unfold tripleCharges sourceA868 sourceB868 sourceC868 difference raw14485; decide +kernel
    rw [ha]
    exact (canonical14485 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA868 + difference 5 1) (sourceB868 + difference 1 5) sourceC868) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4812) := by
    have ha : (tripleCharges (sourceA868 + difference 5 1) (sourceB868 + difference 1 5) sourceC868) = raw14486 := by
      apply Matrix.ext; unfold tripleCharges sourceA868 sourceB868 sourceC868 difference raw14486; decide +kernel
    rw [ha]
    exact (canonical14486 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA868 + difference 5 2) (sourceB868 + difference 2 5) sourceC868) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4852) := by
    have ha : (tripleCharges (sourceA868 + difference 5 2) (sourceB868 + difference 2 5) sourceC868) = raw14487 := by
      apply Matrix.ext; unfold tripleCharges sourceA868 sourceB868 sourceC868 difference raw14487; decide +kernel
    rw [ha]
    exact (canonical14487 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA868 + difference 5 3) (sourceB868 + difference 3 5) sourceC868) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4813) := by
    have ha : (tripleCharges (sourceA868 + difference 5 3) (sourceB868 + difference 3 5) sourceC868) = raw14488 := by
      apply Matrix.ext; unfold tripleCharges sourceA868 sourceB868 sourceC868 difference raw14488; decide +kernel
    rw [ha]
    exact (canonical14488 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA868 + difference 5 4) (sourceB868 + difference 4 5) sourceC868) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4816) := by
    have ha : (tripleCharges (sourceA868 + difference 5 4) (sourceB868 + difference 4 5) sourceC868) = raw14489 := by
      apply Matrix.ext; unfold tripleCharges sourceA868 sourceB868 sourceC868 difference raw14489; decide +kernel
    rw [ha]
    exact (canonical14489 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA868 sourceB868 sourceC868
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm868, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq871 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm871 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA871 + difference 0 0) (sourceB871 + difference 0 0) sourceC871) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3839) := by
    have ha : (tripleCharges (sourceA871 + difference 0 0) (sourceB871 + difference 0 0) sourceC871) = raw14550 := by
      apply Matrix.ext; unfold tripleCharges sourceA871 sourceB871 sourceC871 difference raw14550; decide +kernel
    rw [ha]
    exact (canonical14550 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA871 + difference 0 1) (sourceB871 + difference 1 0) sourceC871) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4022) := by
    have ha : (tripleCharges (sourceA871 + difference 0 1) (sourceB871 + difference 1 0) sourceC871) = raw14551 := by
      apply Matrix.ext; unfold tripleCharges sourceA871 sourceB871 sourceC871 difference raw14551; decide +kernel
    rw [ha]
    exact (canonical14551 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA871 + difference 0 2) (sourceB871 + difference 2 0) sourceC871) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4024) := by
    have ha : (tripleCharges (sourceA871 + difference 0 2) (sourceB871 + difference 2 0) sourceC871) = raw14552 := by
      apply Matrix.ext; unfold tripleCharges sourceA871 sourceB871 sourceC871 difference raw14552; decide +kernel
    rw [ha]
    exact (canonical14552 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA871 + difference 0 3) (sourceB871 + difference 3 0) sourceC871) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3946) := by
    have ha : (tripleCharges (sourceA871 + difference 0 3) (sourceB871 + difference 3 0) sourceC871) = raw14553 := by
      apply Matrix.ext; unfold tripleCharges sourceA871 sourceB871 sourceC871 difference raw14553; decide +kernel
    rw [ha]
    exact (canonical14553 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA871 + difference 0 4) (sourceB871 + difference 4 0) sourceC871) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3782) := by
    have ha : (tripleCharges (sourceA871 + difference 0 4) (sourceB871 + difference 4 0) sourceC871) = raw14554 := by
      apply Matrix.ext; unfold tripleCharges sourceA871 sourceB871 sourceC871 difference raw14554; decide +kernel
    rw [ha]
    exact (canonical14554 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA871 + difference 0 5) (sourceB871 + difference 5 0) sourceC871) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4044) := by
    have ha : (tripleCharges (sourceA871 + difference 0 5) (sourceB871 + difference 5 0) sourceC871) = raw14555 := by
      apply Matrix.ext; unfold tripleCharges sourceA871 sourceB871 sourceC871 difference raw14555; decide +kernel
    rw [ha]
    exact (canonical14555 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA871 + sourceB871) sourceC871) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA871 + sourceB871) sourceC871) = raw14556 := by
      apply Matrix.ext; unfold doubleCharges sourceA871 sourceB871 sourceC871 raw14556; decide +kernel
    rw [ha]
    exact (canonical14556 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA871 sourceB871 sourceC871
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm871, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq872 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm872 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA872 + difference 0 1) (sourceB872 + difference 1 0) sourceC872) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4022) := by
    have ha : (tripleCharges (sourceA872 + difference 0 1) (sourceB872 + difference 1 0) sourceC872) = raw14551 := by
      apply Matrix.ext; unfold tripleCharges sourceA872 sourceB872 sourceC872 difference raw14551; decide +kernel
    rw [ha]
    exact (canonical14551 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA872 + difference 1 1) (sourceB872 + difference 1 1) sourceC872) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3839) := by
    have ha : (tripleCharges (sourceA872 + difference 1 1) (sourceB872 + difference 1 1) sourceC872) = raw14550 := by
      apply Matrix.ext; unfold tripleCharges sourceA872 sourceB872 sourceC872 difference raw14550; decide +kernel
    rw [ha]
    exact (canonical14550 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA872 + difference 2 1) (sourceB872 + difference 1 2) sourceC872) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3725) := by
    have ha : (tripleCharges (sourceA872 + difference 2 1) (sourceB872 + difference 1 2) sourceC872) = raw14557 := by
      apply Matrix.ext; unfold tripleCharges sourceA872 sourceB872 sourceC872 difference raw14557; decide +kernel
    rw [ha]
    exact (canonical14557 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA872 + difference 3 1) (sourceB872 + difference 1 3) sourceC872) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3722) := by
    have ha : (tripleCharges (sourceA872 + difference 3 1) (sourceB872 + difference 1 3) sourceC872) = raw14558 := by
      apply Matrix.ext; unfold tripleCharges sourceA872 sourceB872 sourceC872 difference raw14558; decide +kernel
    rw [ha]
    exact (canonical14558 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA872 + difference 4 1) (sourceB872 + difference 1 4) sourceC872) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3715) := by
    have ha : (tripleCharges (sourceA872 + difference 4 1) (sourceB872 + difference 1 4) sourceC872) = raw14559 := by
      apply Matrix.ext; unfold tripleCharges sourceA872 sourceB872 sourceC872 difference raw14559; decide +kernel
    rw [ha]
    exact (canonical14559 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA872 + difference 5 1) (sourceB872 + difference 1 5) sourceC872) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3168) := by
    have ha : (tripleCharges (sourceA872 + difference 5 1) (sourceB872 + difference 1 5) sourceC872) = raw14560 := by
      apply Matrix.ext; unfold tripleCharges sourceA872 sourceB872 sourceC872 difference raw14560; decide +kernel
    rw [ha]
    exact (canonical14560 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA872 + sourceB872) sourceC872) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA872 + sourceB872) sourceC872) = raw14556 := by
      apply Matrix.ext; unfold doubleCharges sourceA872 sourceB872 sourceC872 raw14556; decide +kernel
    rw [ha]
    exact (canonical14556 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA872 sourceB872 sourceC872
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm872, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq873 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm873 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA873 + difference 2 0) (sourceB873 + difference 0 2) sourceC873) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2568) := by
    have ha : (tripleCharges (sourceA873 + difference 2 0) (sourceB873 + difference 0 2) sourceC873) = raw14561 := by
      apply Matrix.ext; unfold tripleCharges sourceA873 sourceB873 sourceC873 difference raw14561; decide +kernel
    rw [ha]
    exact (canonical14561 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA873 + difference 2 1) (sourceB873 + difference 1 2) sourceC873) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3725) := by
    have ha : (tripleCharges (sourceA873 + difference 2 1) (sourceB873 + difference 1 2) sourceC873) = raw14557 := by
      apply Matrix.ext; unfold tripleCharges sourceA873 sourceB873 sourceC873 difference raw14557; decide +kernel
    rw [ha]
    exact (canonical14557 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA873 + difference 2 2) (sourceB873 + difference 2 2) sourceC873) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3839) := by
    have ha : (tripleCharges (sourceA873 + difference 2 2) (sourceB873 + difference 2 2) sourceC873) = raw14550 := by
      apply Matrix.ext; unfold tripleCharges sourceA873 sourceB873 sourceC873 difference raw14550; decide +kernel
    rw [ha]
    exact (canonical14550 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA873 + difference 2 3) (sourceB873 + difference 3 2) sourceC873) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3828) := by
    have ha : (tripleCharges (sourceA873 + difference 2 3) (sourceB873 + difference 3 2) sourceC873) = raw14562 := by
      apply Matrix.ext; unfold tripleCharges sourceA873 sourceB873 sourceC873 difference raw14562; decide +kernel
    rw [ha]
    exact (canonical14562 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA873 + difference 2 4) (sourceB873 + difference 4 2) sourceC873) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3780) := by
    have ha : (tripleCharges (sourceA873 + difference 2 4) (sourceB873 + difference 4 2) sourceC873) = raw14563 := by
      apply Matrix.ext; unfold tripleCharges sourceA873 sourceB873 sourceC873 difference raw14563; decide +kernel
    rw [ha]
    exact (canonical14563 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA873 + difference 2 5) (sourceB873 + difference 5 2) sourceC873) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3848) := by
    have ha : (tripleCharges (sourceA873 + difference 2 5) (sourceB873 + difference 5 2) sourceC873) = raw14564 := by
      apply Matrix.ext; unfold tripleCharges sourceA873 sourceB873 sourceC873 difference raw14564; decide +kernel
    rw [ha]
    exact (canonical14564 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA873 + sourceB873) sourceC873) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA873 + sourceB873) sourceC873) = raw14556 := by
      apply Matrix.ext; unfold doubleCharges sourceA873 sourceB873 sourceC873 raw14556; decide +kernel
    rw [ha]
    exact (canonical14556 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA873 sourceB873 sourceC873
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm873, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq874 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm874 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA874 + difference 0 2) (sourceB874 + difference 2 0) sourceC874) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4024) := by
    have ha : (tripleCharges (sourceA874 + difference 0 2) (sourceB874 + difference 2 0) sourceC874) = raw14552 := by
      apply Matrix.ext; unfold tripleCharges sourceA874 sourceB874 sourceC874 difference raw14552; decide +kernel
    rw [ha]
    exact (canonical14552 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA874 + difference 1 2) (sourceB874 + difference 2 1) sourceC874) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3809) := by
    have ha : (tripleCharges (sourceA874 + difference 1 2) (sourceB874 + difference 2 1) sourceC874) = raw14565 := by
      apply Matrix.ext; unfold tripleCharges sourceA874 sourceB874 sourceC874 difference raw14565; decide +kernel
    rw [ha]
    exact (canonical14565 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA874 + difference 2 2) (sourceB874 + difference 2 2) sourceC874) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3839) := by
    have ha : (tripleCharges (sourceA874 + difference 2 2) (sourceB874 + difference 2 2) sourceC874) = raw14550 := by
      apply Matrix.ext; unfold tripleCharges sourceA874 sourceB874 sourceC874 difference raw14550; decide +kernel
    rw [ha]
    exact (canonical14550 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA874 + difference 3 2) (sourceB874 + difference 2 3) sourceC874) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3782) := by
    have ha : (tripleCharges (sourceA874 + difference 3 2) (sourceB874 + difference 2 3) sourceC874) = raw14566 := by
      apply Matrix.ext; unfold tripleCharges sourceA874 sourceB874 sourceC874 difference raw14566; decide +kernel
    rw [ha]
    exact (canonical14566 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA874 + difference 4 2) (sourceB874 + difference 2 4) sourceC874) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3719) := by
    have ha : (tripleCharges (sourceA874 + difference 4 2) (sourceB874 + difference 2 4) sourceC874) = raw14567 := by
      apply Matrix.ext; unfold tripleCharges sourceA874 sourceB874 sourceC874 difference raw14567; decide +kernel
    rw [ha]
    exact (canonical14567 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA874 + difference 5 2) (sourceB874 + difference 2 5) sourceC874) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3170) := by
    have ha : (tripleCharges (sourceA874 + difference 5 2) (sourceB874 + difference 2 5) sourceC874) = raw14568 := by
      apply Matrix.ext; unfold tripleCharges sourceA874 sourceB874 sourceC874 difference raw14568; decide +kernel
    rw [ha]
    exact (canonical14568 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA874 + sourceB874) sourceC874) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA874 + sourceB874) sourceC874) = raw14556 := by
      apply Matrix.ext; unfold doubleCharges sourceA874 sourceB874 sourceC874 raw14556; decide +kernel
    rw [ha]
    exact (canonical14556 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA874 sourceB874 sourceC874
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm874, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq875 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm875 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA875 + difference 3 0) (sourceB875 + difference 0 3) sourceC875) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2557) := by
    have ha : (tripleCharges (sourceA875 + difference 3 0) (sourceB875 + difference 0 3) sourceC875) = raw14569 := by
      apply Matrix.ext; unfold tripleCharges sourceA875 sourceB875 sourceC875 difference raw14569; decide +kernel
    rw [ha]
    exact (canonical14569 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA875 + difference 3 1) (sourceB875 + difference 1 3) sourceC875) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3722) := by
    have ha : (tripleCharges (sourceA875 + difference 3 1) (sourceB875 + difference 1 3) sourceC875) = raw14558 := by
      apply Matrix.ext; unfold tripleCharges sourceA875 sourceB875 sourceC875 difference raw14558; decide +kernel
    rw [ha]
    exact (canonical14558 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA875 + difference 3 2) (sourceB875 + difference 2 3) sourceC875) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3782) := by
    have ha : (tripleCharges (sourceA875 + difference 3 2) (sourceB875 + difference 2 3) sourceC875) = raw14566 := by
      apply Matrix.ext; unfold tripleCharges sourceA875 sourceB875 sourceC875 difference raw14566; decide +kernel
    rw [ha]
    exact (canonical14566 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA875 + difference 3 3) (sourceB875 + difference 3 3) sourceC875) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3839) := by
    have ha : (tripleCharges (sourceA875 + difference 3 3) (sourceB875 + difference 3 3) sourceC875) = raw14550 := by
      apply Matrix.ext; unfold tripleCharges sourceA875 sourceB875 sourceC875 difference raw14550; decide +kernel
    rw [ha]
    exact (canonical14550 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA875 + difference 3 4) (sourceB875 + difference 4 3) sourceC875) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3841) := by
    have ha : (tripleCharges (sourceA875 + difference 3 4) (sourceB875 + difference 4 3) sourceC875) = raw14570 := by
      apply Matrix.ext; unfold tripleCharges sourceA875 sourceB875 sourceC875 difference raw14570; decide +kernel
    rw [ha]
    exact (canonical14570 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA875 + difference 3 5) (sourceB875 + difference 5 3) sourceC875) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3843) := by
    have ha : (tripleCharges (sourceA875 + difference 3 5) (sourceB875 + difference 5 3) sourceC875) = raw14571 := by
      apply Matrix.ext; unfold tripleCharges sourceA875 sourceB875 sourceC875 difference raw14571; decide +kernel
    rw [ha]
    exact (canonical14571 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA875 + sourceB875) sourceC875) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA875 + sourceB875) sourceC875) = raw14556 := by
      apply Matrix.ext; unfold doubleCharges sourceA875 sourceB875 sourceC875 raw14556; decide +kernel
    rw [ha]
    exact (canonical14556 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA875 sourceB875 sourceC875
    (0 : Fin 2) 1 (3 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm875, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq876 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm876 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA876 + difference 0 3) (sourceB876 + difference 3 0) sourceC876) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3946) := by
    have ha : (tripleCharges (sourceA876 + difference 0 3) (sourceB876 + difference 3 0) sourceC876) = raw14553 := by
      apply Matrix.ext; unfold tripleCharges sourceA876 sourceB876 sourceC876 difference raw14553; decide +kernel
    rw [ha]
    exact (canonical14553 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA876 + difference 1 3) (sourceB876 + difference 3 1) sourceC876) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3877) := by
    have ha : (tripleCharges (sourceA876 + difference 1 3) (sourceB876 + difference 3 1) sourceC876) = raw14572 := by
      apply Matrix.ext; unfold tripleCharges sourceA876 sourceB876 sourceC876 difference raw14572; decide +kernel
    rw [ha]
    exact (canonical14572 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA876 + difference 2 3) (sourceB876 + difference 3 2) sourceC876) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3828) := by
    have ha : (tripleCharges (sourceA876 + difference 2 3) (sourceB876 + difference 3 2) sourceC876) = raw14562 := by
      apply Matrix.ext; unfold tripleCharges sourceA876 sourceB876 sourceC876 difference raw14562; decide +kernel
    rw [ha]
    exact (canonical14562 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA876 + difference 3 3) (sourceB876 + difference 3 3) sourceC876) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3839) := by
    have ha : (tripleCharges (sourceA876 + difference 3 3) (sourceB876 + difference 3 3) sourceC876) = raw14550 := by
      apply Matrix.ext; unfold tripleCharges sourceA876 sourceB876 sourceC876 difference raw14550; decide +kernel
    rw [ha]
    exact (canonical14550 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA876 + difference 4 3) (sourceB876 + difference 3 4) sourceC876) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3723) := by
    have ha : (tripleCharges (sourceA876 + difference 4 3) (sourceB876 + difference 3 4) sourceC876) = raw14573 := by
      apply Matrix.ext; unfold tripleCharges sourceA876 sourceB876 sourceC876 difference raw14573; decide +kernel
    rw [ha]
    exact (canonical14573 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA876 + difference 5 3) (sourceB876 + difference 3 5) sourceC876) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3175) := by
    have ha : (tripleCharges (sourceA876 + difference 5 3) (sourceB876 + difference 3 5) sourceC876) = raw14574 := by
      apply Matrix.ext; unfold tripleCharges sourceA876 sourceB876 sourceC876 difference raw14574; decide +kernel
    rw [ha]
    exact (canonical14574 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA876 + sourceB876) sourceC876) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA876 + sourceB876) sourceC876) = raw14556 := by
      apply Matrix.ext; unfold doubleCharges sourceA876 sourceB876 sourceC876 raw14556; decide +kernel
    rw [ha]
    exact (canonical14556 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA876 sourceB876 sourceC876
    (0 : Fin 2) 1 (3 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm876, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq877 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm877 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA877 + difference 4 0) (sourceB877 + difference 0 4) sourceC877) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2545) := by
    have ha : (tripleCharges (sourceA877 + difference 4 0) (sourceB877 + difference 0 4) sourceC877) = raw14575 := by
      apply Matrix.ext; unfold tripleCharges sourceA877 sourceB877 sourceC877 difference raw14575; decide +kernel
    rw [ha]
    exact (canonical14575 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA877 + difference 4 1) (sourceB877 + difference 1 4) sourceC877) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3715) := by
    have ha : (tripleCharges (sourceA877 + difference 4 1) (sourceB877 + difference 1 4) sourceC877) = raw14559 := by
      apply Matrix.ext; unfold tripleCharges sourceA877 sourceB877 sourceC877 difference raw14559; decide +kernel
    rw [ha]
    exact (canonical14559 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA877 + difference 4 2) (sourceB877 + difference 2 4) sourceC877) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3719) := by
    have ha : (tripleCharges (sourceA877 + difference 4 2) (sourceB877 + difference 2 4) sourceC877) = raw14567 := by
      apply Matrix.ext; unfold tripleCharges sourceA877 sourceB877 sourceC877 difference raw14567; decide +kernel
    rw [ha]
    exact (canonical14567 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA877 + difference 4 3) (sourceB877 + difference 3 4) sourceC877) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3723) := by
    have ha : (tripleCharges (sourceA877 + difference 4 3) (sourceB877 + difference 3 4) sourceC877) = raw14573 := by
      apply Matrix.ext; unfold tripleCharges sourceA877 sourceB877 sourceC877 difference raw14573; decide +kernel
    rw [ha]
    exact (canonical14573 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA877 + difference 4 4) (sourceB877 + difference 4 4) sourceC877) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3839) := by
    have ha : (tripleCharges (sourceA877 + difference 4 4) (sourceB877 + difference 4 4) sourceC877) = raw14550 := by
      apply Matrix.ext; unfold tripleCharges sourceA877 sourceB877 sourceC877 difference raw14550; decide +kernel
    rw [ha]
    exact (canonical14550 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA877 + difference 4 5) (sourceB877 + difference 5 4) sourceC877) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3837) := by
    have ha : (tripleCharges (sourceA877 + difference 4 5) (sourceB877 + difference 5 4) sourceC877) = raw14576 := by
      apply Matrix.ext; unfold tripleCharges sourceA877 sourceB877 sourceC877 difference raw14576; decide +kernel
    rw [ha]
    exact (canonical14576 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA877 + sourceB877) sourceC877) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA877 + sourceB877) sourceC877) = raw14556 := by
      apply Matrix.ext; unfold doubleCharges sourceA877 sourceB877 sourceC877 raw14556; decide +kernel
    rw [ha]
    exact (canonical14556 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA877 sourceB877 sourceC877
    (0 : Fin 2) 1 (4 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm877, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq878 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm878 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA878 + difference 0 4) (sourceB878 + difference 4 0) sourceC878) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3782) := by
    have ha : (tripleCharges (sourceA878 + difference 0 4) (sourceB878 + difference 4 0) sourceC878) = raw14554 := by
      apply Matrix.ext; unfold tripleCharges sourceA878 sourceB878 sourceC878 difference raw14554; decide +kernel
    rw [ha]
    exact (canonical14554 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA878 + difference 1 4) (sourceB878 + difference 4 1) sourceC878) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3814) := by
    have ha : (tripleCharges (sourceA878 + difference 1 4) (sourceB878 + difference 4 1) sourceC878) = raw14577 := by
      apply Matrix.ext; unfold tripleCharges sourceA878 sourceB878 sourceC878 difference raw14577; decide +kernel
    rw [ha]
    exact (canonical14577 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA878 + difference 2 4) (sourceB878 + difference 4 2) sourceC878) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3780) := by
    have ha : (tripleCharges (sourceA878 + difference 2 4) (sourceB878 + difference 4 2) sourceC878) = raw14563 := by
      apply Matrix.ext; unfold tripleCharges sourceA878 sourceB878 sourceC878 difference raw14563; decide +kernel
    rw [ha]
    exact (canonical14563 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA878 + difference 3 4) (sourceB878 + difference 4 3) sourceC878) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3841) := by
    have ha : (tripleCharges (sourceA878 + difference 3 4) (sourceB878 + difference 4 3) sourceC878) = raw14570 := by
      apply Matrix.ext; unfold tripleCharges sourceA878 sourceB878 sourceC878 difference raw14570; decide +kernel
    rw [ha]
    exact (canonical14570 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA878 + difference 4 4) (sourceB878 + difference 4 4) sourceC878) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3839) := by
    have ha : (tripleCharges (sourceA878 + difference 4 4) (sourceB878 + difference 4 4) sourceC878) = raw14550 := by
      apply Matrix.ext; unfold tripleCharges sourceA878 sourceB878 sourceC878 difference raw14550; decide +kernel
    rw [ha]
    exact (canonical14550 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA878 + difference 5 4) (sourceB878 + difference 4 5) sourceC878) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3196) := by
    have ha : (tripleCharges (sourceA878 + difference 5 4) (sourceB878 + difference 4 5) sourceC878) = raw14578 := by
      apply Matrix.ext; unfold tripleCharges sourceA878 sourceB878 sourceC878 difference raw14578; decide +kernel
    rw [ha]
    exact (canonical14578 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA878 + sourceB878) sourceC878) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA878 + sourceB878) sourceC878) = raw14556 := by
      apply Matrix.ext; unfold doubleCharges sourceA878 sourceB878 sourceC878 raw14556; decide +kernel
    rw [ha]
    exact (canonical14556 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA878 sourceB878 sourceC878
    (0 : Fin 2) 1 (4 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm878, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic47
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reindexCheck752 : Integer.Sparse.reindex keyMap MixedData.row752 = numericRow752 := by decide +kernel

theorem numericCheck752 (x : Master → ℝ) : Integer.Sparse.eval numericRow752 x =
    (1 : ℝ) * reducedSource752 x := by
  norm_num [numericRow752, reducedSource752, Integer.Sparse.eval, Sparse.eval, nodeValue2481, nodeValue3691, nodeValue3788, nodeValue3803, nodeValue3805, nodeValue3809, nodeValue4092]

theorem reindexCheck753 : Integer.Sparse.reindex keyMap MixedData.row753 = numericRow753 := by decide +kernel

theorem numericCheck753 (x : Master → ℝ) : Integer.Sparse.eval numericRow753 x =
    (1 : ℝ) * reducedSource753 x := by
  norm_num [numericRow753, reducedSource753, Integer.Sparse.eval, Sparse.eval, nodeValue2474, nodeValue2475, nodeValue2481, nodeValue2494, nodeValue2714, nodeValue3803, nodeValue4092]

theorem reindexCheck754 : Integer.Sparse.reindex keyMap MixedData.row754 = numericRow754 := by decide +kernel

theorem numericCheck754 (x : Master → ℝ) : Integer.Sparse.eval numericRow754 x =
    (1 : ℝ) * reducedSource754 x := by
  norm_num [numericRow754, reducedSource754, Integer.Sparse.eval, Sparse.eval, nodeValue2494, nodeValue2714, nodeValue3698, nodeValue3803, nodeValue3812, nodeValue3814, nodeValue4092]

theorem reindexCheck755 : Integer.Sparse.reindex keyMap MixedData.row755 = numericRow755 := by decide +kernel

theorem numericCheck755 (x : Master → ℝ) : Integer.Sparse.eval numericRow755 x =
    (1 : ℝ) * reducedSource755 x := by
  norm_num [numericRow755, reducedSource755, Integer.Sparse.eval, Sparse.eval, nodeValue3217, nodeValue3686, nodeValue3691, nodeValue3698, nodeValue3788, nodeValue3803, nodeValue4092]

theorem reindexCheck756 : Integer.Sparse.reindex keyMap MixedData.row756 = numericRow756 := by decide +kernel

theorem numericCheck756 (x : Master → ℝ) : Integer.Sparse.eval numericRow756 x =
    (1 : ℝ) * reducedSource756 x := by
  norm_num [numericRow756, reducedSource756, Integer.Sparse.eval, Sparse.eval, nodeValue2475, nodeValue3686, nodeValue3803, nodeValue4092]

theorem reindexCheck757 : Integer.Sparse.reindex keyMap MixedData.row757 = numericRow757 := by decide +kernel

theorem numericCheck757 (x : Master → ℝ) : Integer.Sparse.eval numericRow757 x =
    (17280 : ℝ) * reducedSource757 x := by
  norm_num [numericRow757, reducedSource757, Integer.Sparse.eval, Sparse.eval, nodeValue4812, nodeValue4813, nodeValue4816, nodeValue4824, nodeValue4852, nodeValue5129, nodeValue5138, nodeValue5146, nodeValue5260, nodeValue5357, nodeValue5358, nodeValue5360, nodeValue5376, nodeValue5378, nodeValue5381, nodeValue5397, nodeValue5411, nodeValue5412, nodeValue5420, nodeValue5421, nodeValue5423, nodeValue5424, nodeValue5426, nodeValue5430, nodeValue5434, nodeValue5436, nodeValue5445, nodeValue5477]
  ring

theorem reindexCheck760 : Integer.Sparse.reindex keyMap MixedData.row760 = numericRow760 := by decide +kernel

theorem numericCheck760 (x : Master → ℝ) : Integer.Sparse.eval numericRow760 x =
    (1 : ℝ) * reducedSource760 x := by
  norm_num [numericRow760, reducedSource760, Integer.Sparse.eval, Sparse.eval, nodeValue3782, nodeValue3839, nodeValue3946, nodeValue4022, nodeValue4024, nodeValue4044, nodeValue4092]

theorem reindexCheck761 : Integer.Sparse.reindex keyMap MixedData.row761 = numericRow761 := by decide +kernel

theorem numericCheck761 (x : Master → ℝ) : Integer.Sparse.eval numericRow761 x =
    (1 : ℝ) * reducedSource761 x := by
  norm_num [numericRow761, reducedSource761, Integer.Sparse.eval, Sparse.eval, nodeValue3168, nodeValue3715, nodeValue3722, nodeValue3725, nodeValue3839, nodeValue4022, nodeValue4092]

theorem reindexCheck762 : Integer.Sparse.reindex keyMap MixedData.row762 = numericRow762 := by decide +kernel

theorem numericCheck762 (x : Master → ℝ) : Integer.Sparse.eval numericRow762 x =
    (1 : ℝ) * reducedSource762 x := by
  norm_num [numericRow762, reducedSource762, Integer.Sparse.eval, Sparse.eval, nodeValue2568, nodeValue3725, nodeValue3780, nodeValue3828, nodeValue3839, nodeValue3848, nodeValue4092]

theorem reindexCheck763 : Integer.Sparse.reindex keyMap MixedData.row763 = numericRow763 := by decide +kernel

theorem numericCheck763 (x : Master → ℝ) : Integer.Sparse.eval numericRow763 x =
    (1 : ℝ) * reducedSource763 x := by
  norm_num [numericRow763, reducedSource763, Integer.Sparse.eval, Sparse.eval, nodeValue3170, nodeValue3719, nodeValue3782, nodeValue3809, nodeValue3839, nodeValue4024, nodeValue4092]

theorem reindexCheck764 : Integer.Sparse.reindex keyMap MixedData.row764 = numericRow764 := by decide +kernel

theorem numericCheck764 (x : Master → ℝ) : Integer.Sparse.eval numericRow764 x =
    (1 : ℝ) * reducedSource764 x := by
  norm_num [numericRow764, reducedSource764, Integer.Sparse.eval, Sparse.eval, nodeValue2557, nodeValue3722, nodeValue3782, nodeValue3839, nodeValue3841, nodeValue3843, nodeValue4092]

theorem reindexCheck765 : Integer.Sparse.reindex keyMap MixedData.row765 = numericRow765 := by decide +kernel

theorem numericCheck765 (x : Master → ℝ) : Integer.Sparse.eval numericRow765 x =
    (1 : ℝ) * reducedSource765 x := by
  norm_num [numericRow765, reducedSource765, Integer.Sparse.eval, Sparse.eval, nodeValue3175, nodeValue3723, nodeValue3828, nodeValue3839, nodeValue3877, nodeValue3946, nodeValue4092]

theorem reindexCheck766 : Integer.Sparse.reindex keyMap MixedData.row766 = numericRow766 := by decide +kernel

theorem numericCheck766 (x : Master → ℝ) : Integer.Sparse.eval numericRow766 x =
    (1 : ℝ) * reducedSource766 x := by
  norm_num [numericRow766, reducedSource766, Integer.Sparse.eval, Sparse.eval, nodeValue2545, nodeValue3715, nodeValue3719, nodeValue3723, nodeValue3837, nodeValue3839, nodeValue4092]

theorem reindexCheck767 : Integer.Sparse.reindex keyMap MixedData.row767 = numericRow767 := by decide +kernel

theorem numericCheck767 (x : Master → ℝ) : Integer.Sparse.eval numericRow767 x =
    (1 : ℝ) * reducedSource767 x := by
  norm_num [numericRow767, reducedSource767, Integer.Sparse.eval, Sparse.eval, nodeValue3196, nodeValue3780, nodeValue3782, nodeValue3814, nodeValue3839, nodeValue3841, nodeValue4092]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Rows47
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero752 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource752 (mixedVector B) = 0 := by
  have h2481 : mixedVector B (Sum.inr 2481) = Sparse.eval nodeValue2481 (mixedVector B) := by
    change mixedMoment B node2481 node2481Labels = _
    exact sound2481 B hB hF
  have h3691 : mixedVector B (Sum.inr 3691) = Sparse.eval nodeValue3691 (mixedVector B) := by
    change mixedMoment B node3691 node3691Labels = _
    exact sound3691 B hB hF
  have h3788 : mixedVector B (Sum.inr 3788) = Sparse.eval nodeValue3788 (mixedVector B) := by
    change mixedMoment B node3788 node3788Labels = _
    exact sound3788 B hB hF
  have h3803 : mixedVector B (Sum.inr 3803) = Sparse.eval nodeValue3803 (mixedVector B) := by
    change mixedMoment B node3803 node3803Labels = _
    exact sound3803 B hB hF
  have h3805 : mixedVector B (Sum.inr 3805) = Sparse.eval nodeValue3805 (mixedVector B) := by
    change mixedMoment B node3805 node3805Labels = _
    exact sound3805 B hB hF
  have h3809 : mixedVector B (Sum.inr 3809) = Sparse.eval nodeValue3809 (mixedVector B) := by
    change mixedMoment B node3809 node3809Labels = _
    exact sound3809 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm863, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2481, h3691, h3788, h3803, h3805, h3809, h4092, reducedSource752] using sourceEq863 B hB

theorem rowSound752 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row752 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck752, numericCheck752, reducedZero752 B hB hF, mul_zero]

theorem reducedZero753 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource753 (mixedVector B) = 0 := by
  have h2474 : mixedVector B (Sum.inr 2474) = Sparse.eval nodeValue2474 (mixedVector B) := by
    change mixedMoment B node2474 node2474Labels = _
    exact sound2474 B hB hF
  have h2475 : mixedVector B (Sum.inr 2475) = Sparse.eval nodeValue2475 (mixedVector B) := by
    change mixedMoment B node2475 node2475Labels = _
    exact sound2475 B hB hF
  have h2481 : mixedVector B (Sum.inr 2481) = Sparse.eval nodeValue2481 (mixedVector B) := by
    change mixedMoment B node2481 node2481Labels = _
    exact sound2481 B hB hF
  have h2494 : mixedVector B (Sum.inr 2494) = Sparse.eval nodeValue2494 (mixedVector B) := by
    change mixedMoment B node2494 node2494Labels = _
    exact sound2494 B hB hF
  have h2714 : mixedVector B (Sum.inr 2714) = Sparse.eval nodeValue2714 (mixedVector B) := by
    change mixedMoment B node2714 node2714Labels = _
    exact sound2714 B hB hF
  have h3803 : mixedVector B (Sum.inr 3803) = Sparse.eval nodeValue3803 (mixedVector B) := by
    change mixedMoment B node3803 node3803Labels = _
    exact sound3803 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm864, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2474, h2475, h2481, h2494, h2714, h3803, h4092, reducedSource753] using sourceEq864 B hB

theorem rowSound753 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row753 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck753, numericCheck753, reducedZero753 B hB hF, mul_zero]

theorem reducedZero754 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource754 (mixedVector B) = 0 := by
  have h2494 : mixedVector B (Sum.inr 2494) = Sparse.eval nodeValue2494 (mixedVector B) := by
    change mixedMoment B node2494 node2494Labels = _
    exact sound2494 B hB hF
  have h2714 : mixedVector B (Sum.inr 2714) = Sparse.eval nodeValue2714 (mixedVector B) := by
    change mixedMoment B node2714 node2714Labels = _
    exact sound2714 B hB hF
  have h3698 : mixedVector B (Sum.inr 3698) = Sparse.eval nodeValue3698 (mixedVector B) := by
    change mixedMoment B node3698 node3698Labels = _
    exact sound3698 B hB hF
  have h3803 : mixedVector B (Sum.inr 3803) = Sparse.eval nodeValue3803 (mixedVector B) := by
    change mixedMoment B node3803 node3803Labels = _
    exact sound3803 B hB hF
  have h3812 : mixedVector B (Sum.inr 3812) = Sparse.eval nodeValue3812 (mixedVector B) := by
    change mixedMoment B node3812 node3812Labels = _
    exact sound3812 B hB hF
  have h3814 : mixedVector B (Sum.inr 3814) = Sparse.eval nodeValue3814 (mixedVector B) := by
    change mixedMoment B node3814 node3814Labels = _
    exact sound3814 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm865, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2494, h2714, h3698, h3803, h3812, h3814, h4092, reducedSource754] using sourceEq865 B hB

theorem rowSound754 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row754 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck754, numericCheck754, reducedZero754 B hB hF, mul_zero]

theorem reducedZero755 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource755 (mixedVector B) = 0 := by
  have h3217 : mixedVector B (Sum.inr 3217) = Sparse.eval nodeValue3217 (mixedVector B) := by
    change mixedMoment B node3217 node3217Labels = _
    exact sound3217 B hB hF
  have h3686 : mixedVector B (Sum.inr 3686) = Sparse.eval nodeValue3686 (mixedVector B) := by
    change mixedMoment B node3686 node3686Labels = _
    exact sound3686 B hB hF
  have h3691 : mixedVector B (Sum.inr 3691) = Sparse.eval nodeValue3691 (mixedVector B) := by
    change mixedMoment B node3691 node3691Labels = _
    exact sound3691 B hB hF
  have h3698 : mixedVector B (Sum.inr 3698) = Sparse.eval nodeValue3698 (mixedVector B) := by
    change mixedMoment B node3698 node3698Labels = _
    exact sound3698 B hB hF
  have h3788 : mixedVector B (Sum.inr 3788) = Sparse.eval nodeValue3788 (mixedVector B) := by
    change mixedMoment B node3788 node3788Labels = _
    exact sound3788 B hB hF
  have h3803 : mixedVector B (Sum.inr 3803) = Sparse.eval nodeValue3803 (mixedVector B) := by
    change mixedMoment B node3803 node3803Labels = _
    exact sound3803 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm866, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h3217, h3686, h3691, h3698, h3788, h3803, h4092, reducedSource755] using sourceEq866 B hB

theorem rowSound755 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row755 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck755, numericCheck755, reducedZero755 B hB hF, mul_zero]

theorem reducedZero756 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource756 (mixedVector B) = 0 := by
  have h2475 : mixedVector B (Sum.inr 2475) = Sparse.eval nodeValue2475 (mixedVector B) := by
    change mixedMoment B node2475 node2475Labels = _
    exact sound2475 B hB hF
  have h3686 : mixedVector B (Sum.inr 3686) = Sparse.eval nodeValue3686 (mixedVector B) := by
    change mixedMoment B node3686 node3686Labels = _
    exact sound3686 B hB hF
  have h3803 : mixedVector B (Sum.inr 3803) = Sparse.eval nodeValue3803 (mixedVector B) := by
    change mixedMoment B node3803 node3803Labels = _
    exact sound3803 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm867, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2475, h3686, h3803, h4092, reducedSource756] using sourceEq867 B hB

theorem rowSound756 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row756 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck756, numericCheck756, reducedZero756 B hB hF, mul_zero]

theorem reducedZero757 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource757 (mixedVector B) = 0 := by
  have h4812 : mixedVector B (Sum.inr 4812) = Sparse.eval nodeValue4812 (mixedVector B) := by
    change mixedMoment B node4812 node4812Labels = _
    exact sound4812 B hB hF
  have h4813 : mixedVector B (Sum.inr 4813) = Sparse.eval nodeValue4813 (mixedVector B) := by
    change mixedMoment B node4813 node4813Labels = _
    exact sound4813 B hB hF
  have h4816 : mixedVector B (Sum.inr 4816) = Sparse.eval nodeValue4816 (mixedVector B) := by
    change mixedMoment B node4816 node4816Labels = _
    exact sound4816 B hB hF
  have h4824 : mixedVector B (Sum.inr 4824) = Sparse.eval nodeValue4824 (mixedVector B) := by
    change mixedMoment B node4824 node4824Labels = _
    exact sound4824 B hB hF
  have h4852 : mixedVector B (Sum.inr 4852) = Sparse.eval nodeValue4852 (mixedVector B) := by
    change mixedMoment B node4852 node4852Labels = _
    exact sound4852 B hB hF
  have h5129 : mixedVector B (Sum.inr 5129) = Sparse.eval nodeValue5129 (mixedVector B) := by
    change mixedMoment B node5129 node5129Labels = _
    exact sound5129 B hB hF
  have h5138 : mixedVector B (Sum.inr 5138) = Sparse.eval nodeValue5138 (mixedVector B) := by
    change mixedMoment B node5138 node5138Labels = _
    exact sound5138 B hB hF
  have h5146 : mixedVector B (Sum.inr 5146) = Sparse.eval nodeValue5146 (mixedVector B) := by
    change mixedMoment B node5146 node5146Labels = _
    exact sound5146 B hB hF
  have h5260 : mixedVector B (Sum.inr 5260) = Sparse.eval nodeValue5260 (mixedVector B) := by
    change mixedMoment B node5260 node5260Labels = _
    exact sound5260 B hB hF
  have h5357 : mixedVector B (Sum.inr 5357) = Sparse.eval nodeValue5357 (mixedVector B) := by
    change mixedMoment B node5357 node5357Labels = _
    exact sound5357 B hB hF
  have h5358 : mixedVector B (Sum.inr 5358) = Sparse.eval nodeValue5358 (mixedVector B) := by
    change mixedMoment B node5358 node5358Labels = _
    exact sound5358 B hB hF
  have h5360 : mixedVector B (Sum.inr 5360) = Sparse.eval nodeValue5360 (mixedVector B) := by
    change mixedMoment B node5360 node5360Labels = _
    exact sound5360 B hB hF
  have h5376 : mixedVector B (Sum.inr 5376) = Sparse.eval nodeValue5376 (mixedVector B) := by
    change mixedMoment B node5376 node5376Labels = _
    exact sound5376 B hB hF
  have h5378 : mixedVector B (Sum.inr 5378) = Sparse.eval nodeValue5378 (mixedVector B) := by
    change mixedMoment B node5378 node5378Labels = _
    exact sound5378 B hB hF
  have h5381 : mixedVector B (Sum.inr 5381) = Sparse.eval nodeValue5381 (mixedVector B) := by
    change mixedMoment B node5381 node5381Labels = _
    exact sound5381 B hB hF
  have h5397 : mixedVector B (Sum.inr 5397) = Sparse.eval nodeValue5397 (mixedVector B) := by
    change mixedMoment B node5397 node5397Labels = _
    exact sound5397 B hB hF
  have h5411 : mixedVector B (Sum.inr 5411) = Sparse.eval nodeValue5411 (mixedVector B) := by
    change mixedMoment B node5411 node5411Labels = _
    exact sound5411 B hB hF
  have h5412 : mixedVector B (Sum.inr 5412) = Sparse.eval nodeValue5412 (mixedVector B) := by
    change mixedMoment B node5412 node5412Labels = _
    exact sound5412 B hB hF
  have h5420 : mixedVector B (Sum.inr 5420) = Sparse.eval nodeValue5420 (mixedVector B) := by
    change mixedMoment B node5420 node5420Labels = _
    exact sound5420 B hB hF
  have h5421 : mixedVector B (Sum.inr 5421) = Sparse.eval nodeValue5421 (mixedVector B) := by
    change mixedMoment B node5421 node5421Labels = _
    exact sound5421 B hB hF
  have h5423 : mixedVector B (Sum.inr 5423) = Sparse.eval nodeValue5423 (mixedVector B) := by
    change mixedMoment B node5423 node5423Labels = _
    exact sound5423 B hB hF
  have h5424 : mixedVector B (Sum.inr 5424) = Sparse.eval nodeValue5424 (mixedVector B) := by
    change mixedMoment B node5424 node5424Labels = _
    exact sound5424 B hB hF
  have h5426 : mixedVector B (Sum.inr 5426) = Sparse.eval nodeValue5426 (mixedVector B) := by
    change mixedMoment B node5426 node5426Labels = _
    exact sound5426 B hB hF
  have h5430 : mixedVector B (Sum.inr 5430) = Sparse.eval nodeValue5430 (mixedVector B) := by
    change mixedMoment B node5430 node5430Labels = _
    exact sound5430 B hB hF
  have h5434 : mixedVector B (Sum.inr 5434) = Sparse.eval nodeValue5434 (mixedVector B) := by
    change mixedMoment B node5434 node5434Labels = _
    exact sound5434_e B hB hF
  have h5436 : mixedVector B (Sum.inr 5436) = Sparse.eval nodeValue5436 (mixedVector B) := by
    change mixedMoment B node5436 node5436Labels = _
    exact sound5436 B hB hF
  have h5445 : mixedVector B (Sum.inr 5445) = Sparse.eval nodeValue5445 (mixedVector B) := by
    change mixedMoment B node5445 node5445Labels = _
    exact sound5445 B hB hF
  have h5477 : mixedVector B (Sum.inr 5477) = Sparse.eval nodeValue5477 (mixedVector B) := by
    change mixedMoment B node5477 node5477Labels = _
    exact sound5477 B hB hF
  simpa only [sourceForm868, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4812, h4813, h4816, h4824, h4852, h5129, h5138, h5146, h5260, h5357, h5358, h5360, h5376, h5378, h5381, h5397, h5411, h5412, h5420, h5421, h5423, h5424, h5426, h5430, h5434, h5436, h5445, h5477, reducedSource757] using sourceEq868 B hB

theorem rowSound757 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row757 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck757, numericCheck757, reducedZero757 B hB hF, mul_zero]

theorem reducedZero760 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource760 (mixedVector B) = 0 := by
  have h3782 : mixedVector B (Sum.inr 3782) = Sparse.eval nodeValue3782 (mixedVector B) := by
    change mixedMoment B node3782 node3782Labels = _
    exact sound3782 B hB hF
  have h3839 : mixedVector B (Sum.inr 3839) = Sparse.eval nodeValue3839 (mixedVector B) := by
    change mixedMoment B node3839 node3839Labels = _
    exact sound3839 B hB hF
  have h3946 : mixedVector B (Sum.inr 3946) = Sparse.eval nodeValue3946 (mixedVector B) := by
    change mixedMoment B node3946 node3946Labels = _
    exact sound3946 B hB hF
  have h4022 : mixedVector B (Sum.inr 4022) = Sparse.eval nodeValue4022 (mixedVector B) := by
    change mixedMoment B node4022 node4022Labels = _
    exact sound4022 B hB hF
  have h4024 : mixedVector B (Sum.inr 4024) = Sparse.eval nodeValue4024 (mixedVector B) := by
    change mixedMoment B node4024 node4024Labels = _
    exact sound4024 B hB hF
  have h4044 : mixedVector B (Sum.inr 4044) = Sparse.eval nodeValue4044 (mixedVector B) := by
    change mixedMoment B node4044 node4044Labels = _
    exact sound4044 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm871, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h3782, h3839, h3946, h4022, h4024, h4044, h4092, reducedSource760] using sourceEq871 B hB

theorem rowSound760 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row760 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck760, numericCheck760, reducedZero760 B hB hF, mul_zero]

theorem reducedZero761 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource761 (mixedVector B) = 0 := by
  have h3168 : mixedVector B (Sum.inr 3168) = Sparse.eval nodeValue3168 (mixedVector B) := by
    change mixedMoment B node3168 node3168Labels = _
    exact sound3168 B hB hF
  have h3715 : mixedVector B (Sum.inr 3715) = Sparse.eval nodeValue3715 (mixedVector B) := by
    change mixedMoment B node3715 node3715Labels = _
    exact sound3715 B hB hF
  have h3722 : mixedVector B (Sum.inr 3722) = Sparse.eval nodeValue3722 (mixedVector B) := by
    change mixedMoment B node3722 node3722Labels = _
    exact sound3722 B hB hF
  have h3725 : mixedVector B (Sum.inr 3725) = Sparse.eval nodeValue3725 (mixedVector B) := by
    change mixedMoment B node3725 node3725Labels = _
    exact sound3725 B hB hF
  have h3839 : mixedVector B (Sum.inr 3839) = Sparse.eval nodeValue3839 (mixedVector B) := by
    change mixedMoment B node3839 node3839Labels = _
    exact sound3839 B hB hF
  have h4022 : mixedVector B (Sum.inr 4022) = Sparse.eval nodeValue4022 (mixedVector B) := by
    change mixedMoment B node4022 node4022Labels = _
    exact sound4022 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm872, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h3168, h3715, h3722, h3725, h3839, h4022, h4092, reducedSource761] using sourceEq872 B hB

theorem rowSound761 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row761 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck761, numericCheck761, reducedZero761 B hB hF, mul_zero]

theorem reducedZero762 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource762 (mixedVector B) = 0 := by
  have h2568 : mixedVector B (Sum.inr 2568) = Sparse.eval nodeValue2568 (mixedVector B) := by
    change mixedMoment B node2568 node2568Labels = _
    exact sound2568 B hB hF
  have h3725 : mixedVector B (Sum.inr 3725) = Sparse.eval nodeValue3725 (mixedVector B) := by
    change mixedMoment B node3725 node3725Labels = _
    exact sound3725 B hB hF
  have h3780 : mixedVector B (Sum.inr 3780) = Sparse.eval nodeValue3780 (mixedVector B) := by
    change mixedMoment B node3780 node3780Labels = _
    exact sound3780 B hB hF
  have h3828 : mixedVector B (Sum.inr 3828) = Sparse.eval nodeValue3828 (mixedVector B) := by
    change mixedMoment B node3828 node3828Labels = _
    exact sound3828 B hB hF
  have h3839 : mixedVector B (Sum.inr 3839) = Sparse.eval nodeValue3839 (mixedVector B) := by
    change mixedMoment B node3839 node3839Labels = _
    exact sound3839 B hB hF
  have h3848 : mixedVector B (Sum.inr 3848) = Sparse.eval nodeValue3848 (mixedVector B) := by
    change mixedMoment B node3848 node3848Labels = _
    exact sound3848 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm873, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2568, h3725, h3780, h3828, h3839, h3848, h4092, reducedSource762] using sourceEq873 B hB

theorem rowSound762 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row762 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck762, numericCheck762, reducedZero762 B hB hF, mul_zero]

theorem reducedZero763 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource763 (mixedVector B) = 0 := by
  have h3170 : mixedVector B (Sum.inr 3170) = Sparse.eval nodeValue3170 (mixedVector B) := by
    change mixedMoment B node3170 node3170Labels = _
    exact sound3170 B hB hF
  have h3719 : mixedVector B (Sum.inr 3719) = Sparse.eval nodeValue3719 (mixedVector B) := by
    change mixedMoment B node3719 node3719Labels = _
    exact sound3719 B hB hF
  have h3782 : mixedVector B (Sum.inr 3782) = Sparse.eval nodeValue3782 (mixedVector B) := by
    change mixedMoment B node3782 node3782Labels = _
    exact sound3782 B hB hF
  have h3809 : mixedVector B (Sum.inr 3809) = Sparse.eval nodeValue3809 (mixedVector B) := by
    change mixedMoment B node3809 node3809Labels = _
    exact sound3809 B hB hF
  have h3839 : mixedVector B (Sum.inr 3839) = Sparse.eval nodeValue3839 (mixedVector B) := by
    change mixedMoment B node3839 node3839Labels = _
    exact sound3839 B hB hF
  have h4024 : mixedVector B (Sum.inr 4024) = Sparse.eval nodeValue4024 (mixedVector B) := by
    change mixedMoment B node4024 node4024Labels = _
    exact sound4024 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm874, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h3170, h3719, h3782, h3809, h3839, h4024, h4092, reducedSource763] using sourceEq874 B hB

theorem rowSound763 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row763 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck763, numericCheck763, reducedZero763 B hB hF, mul_zero]

theorem reducedZero764 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource764 (mixedVector B) = 0 := by
  have h2557 : mixedVector B (Sum.inr 2557) = Sparse.eval nodeValue2557 (mixedVector B) := by
    change mixedMoment B node2557 node2557Labels = _
    exact sound2557 B hB hF
  have h3722 : mixedVector B (Sum.inr 3722) = Sparse.eval nodeValue3722 (mixedVector B) := by
    change mixedMoment B node3722 node3722Labels = _
    exact sound3722 B hB hF
  have h3782 : mixedVector B (Sum.inr 3782) = Sparse.eval nodeValue3782 (mixedVector B) := by
    change mixedMoment B node3782 node3782Labels = _
    exact sound3782 B hB hF
  have h3839 : mixedVector B (Sum.inr 3839) = Sparse.eval nodeValue3839 (mixedVector B) := by
    change mixedMoment B node3839 node3839Labels = _
    exact sound3839 B hB hF
  have h3841 : mixedVector B (Sum.inr 3841) = Sparse.eval nodeValue3841 (mixedVector B) := by
    change mixedMoment B node3841 node3841Labels = _
    exact sound3841 B hB hF
  have h3843 : mixedVector B (Sum.inr 3843) = Sparse.eval nodeValue3843 (mixedVector B) := by
    change mixedMoment B node3843 node3843Labels = _
    exact sound3843 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm875, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2557, h3722, h3782, h3839, h3841, h3843, h4092, reducedSource764] using sourceEq875 B hB

theorem rowSound764 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row764 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck764, numericCheck764, reducedZero764 B hB hF, mul_zero]

theorem reducedZero765 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource765 (mixedVector B) = 0 := by
  have h3175 : mixedVector B (Sum.inr 3175) = Sparse.eval nodeValue3175 (mixedVector B) := by
    change mixedMoment B node3175 node3175Labels = _
    exact sound3175 B hB hF
  have h3723 : mixedVector B (Sum.inr 3723) = Sparse.eval nodeValue3723 (mixedVector B) := by
    change mixedMoment B node3723 node3723Labels = _
    exact sound3723 B hB hF
  have h3828 : mixedVector B (Sum.inr 3828) = Sparse.eval nodeValue3828 (mixedVector B) := by
    change mixedMoment B node3828 node3828Labels = _
    exact sound3828 B hB hF
  have h3839 : mixedVector B (Sum.inr 3839) = Sparse.eval nodeValue3839 (mixedVector B) := by
    change mixedMoment B node3839 node3839Labels = _
    exact sound3839 B hB hF
  have h3877 : mixedVector B (Sum.inr 3877) = Sparse.eval nodeValue3877 (mixedVector B) := by
    change mixedMoment B node3877 node3877Labels = _
    exact sound3877 B hB hF
  have h3946 : mixedVector B (Sum.inr 3946) = Sparse.eval nodeValue3946 (mixedVector B) := by
    change mixedMoment B node3946 node3946Labels = _
    exact sound3946 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm876, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h3175, h3723, h3828, h3839, h3877, h3946, h4092, reducedSource765] using sourceEq876 B hB

theorem rowSound765 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row765 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck765, numericCheck765, reducedZero765 B hB hF, mul_zero]

theorem reducedZero766 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource766 (mixedVector B) = 0 := by
  have h2545 : mixedVector B (Sum.inr 2545) = Sparse.eval nodeValue2545 (mixedVector B) := by
    change mixedMoment B node2545 node2545Labels = _
    exact sound2545 B hB hF
  have h3715 : mixedVector B (Sum.inr 3715) = Sparse.eval nodeValue3715 (mixedVector B) := by
    change mixedMoment B node3715 node3715Labels = _
    exact sound3715 B hB hF
  have h3719 : mixedVector B (Sum.inr 3719) = Sparse.eval nodeValue3719 (mixedVector B) := by
    change mixedMoment B node3719 node3719Labels = _
    exact sound3719 B hB hF
  have h3723 : mixedVector B (Sum.inr 3723) = Sparse.eval nodeValue3723 (mixedVector B) := by
    change mixedMoment B node3723 node3723Labels = _
    exact sound3723 B hB hF
  have h3837 : mixedVector B (Sum.inr 3837) = Sparse.eval nodeValue3837 (mixedVector B) := by
    change mixedMoment B node3837 node3837Labels = _
    exact sound3837 B hB hF
  have h3839 : mixedVector B (Sum.inr 3839) = Sparse.eval nodeValue3839 (mixedVector B) := by
    change mixedMoment B node3839 node3839Labels = _
    exact sound3839 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm877, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2545, h3715, h3719, h3723, h3837, h3839, h4092, reducedSource766] using sourceEq877 B hB

theorem rowSound766 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row766 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck766, numericCheck766, reducedZero766 B hB hF, mul_zero]

theorem reducedZero767 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource767 (mixedVector B) = 0 := by
  have h3196 : mixedVector B (Sum.inr 3196) = Sparse.eval nodeValue3196 (mixedVector B) := by
    change mixedMoment B node3196 node3196Labels = _
    exact sound3196 B hB hF
  have h3780 : mixedVector B (Sum.inr 3780) = Sparse.eval nodeValue3780 (mixedVector B) := by
    change mixedMoment B node3780 node3780Labels = _
    exact sound3780 B hB hF
  have h3782 : mixedVector B (Sum.inr 3782) = Sparse.eval nodeValue3782 (mixedVector B) := by
    change mixedMoment B node3782 node3782Labels = _
    exact sound3782 B hB hF
  have h3814 : mixedVector B (Sum.inr 3814) = Sparse.eval nodeValue3814 (mixedVector B) := by
    change mixedMoment B node3814 node3814Labels = _
    exact sound3814 B hB hF
  have h3839 : mixedVector B (Sum.inr 3839) = Sparse.eval nodeValue3839 (mixedVector B) := by
    change mixedMoment B node3839 node3839Labels = _
    exact sound3839 B hB hF
  have h3841 : mixedVector B (Sum.inr 3841) = Sparse.eval nodeValue3841 (mixedVector B) := by
    change mixedMoment B node3841 node3841Labels = _
    exact sound3841 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm878, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h3196, h3780, h3782, h3814, h3839, h3841, h4092, reducedSource767] using sourceEq878 B hB

theorem rowSound767 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row767 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck767, numericCheck767, reducedZero767 B hB hF, mul_zero]

theorem sourceRowsAt752 : MixedData.sourceRows (752 : Fin 2425) =
    MixedData.row752 := by decide +kernel

theorem sourceRowsAt753 : MixedData.sourceRows (753 : Fin 2425) =
    MixedData.row753 := by decide +kernel

theorem sourceRowsAt754 : MixedData.sourceRows (754 : Fin 2425) =
    MixedData.row754 := by decide +kernel

theorem sourceRowsAt755 : MixedData.sourceRows (755 : Fin 2425) =
    MixedData.row755 := by decide +kernel

theorem sourceRowsAt756 : MixedData.sourceRows (756 : Fin 2425) =
    MixedData.row756 := by decide +kernel

theorem sourceRowsAt757 : MixedData.sourceRows (757 : Fin 2425) =
    MixedData.row757 := by decide +kernel

theorem sourceRowsAt758 : MixedData.sourceRows (758 : Fin 2425) =
    MixedData.row758 := by decide +kernel

theorem sourceRowsAt759 : MixedData.sourceRows (759 : Fin 2425) =
    MixedData.row759 := by decide +kernel

theorem sourceRowsAt760 : MixedData.sourceRows (760 : Fin 2425) =
    MixedData.row760 := by decide +kernel

theorem sourceRowsAt761 : MixedData.sourceRows (761 : Fin 2425) =
    MixedData.row761 := by decide +kernel

theorem sourceRowsAt762 : MixedData.sourceRows (762 : Fin 2425) =
    MixedData.row762 := by decide +kernel

theorem sourceRowsAt763 : MixedData.sourceRows (763 : Fin 2425) =
    MixedData.row763 := by decide +kernel

theorem sourceRowsAt764 : MixedData.sourceRows (764 : Fin 2425) =
    MixedData.row764 := by decide +kernel

theorem sourceRowsAt765 : MixedData.sourceRows (765 : Fin 2425) =
    MixedData.row765 := by decide +kernel

theorem sourceRowsAt766 : MixedData.sourceRows (766 : Fin 2425) =
    MixedData.row766 := by decide +kernel

theorem sourceRowsAt767 : MixedData.sourceRows (767 : Fin 2425) =
    MixedData.row767 := by decide +kernel

theorem chunkSound47_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) (k : Fin 2425)
    (hk : k.val / 16 = 47) :
    Integer.Sparse.eval (MixedData.sourceRows k) (numericVector B) = 0 := by
  have heq : k.val = 752 ∨ k.val = 753 ∨ k.val = 754 ∨ k.val = 755 ∨ k.val = 756 ∨ k.val = 757 ∨ k.val = 758 ∨ k.val = 759 ∨ k.val = 760 ∨ k.val = 761 ∨ k.val = 762 ∨ k.val = 763 ∨ k.val = 764 ∨ k.val = 765 ∨ k.val = 766 ∨ k.val = 767 := by omega
  rcases heq with h752 | h753 | h754 | h755 | h756 | h757 | h758 | h759 | h760 | h761 | h762 | h763 | h764 | h765 | h766 | h767
  · have he : k = (752 : Fin 2425) := Fin.ext h752
    subst k
    rw [sourceRowsAt752]
    exact rowSound752 B hB hF
  · have he : k = (753 : Fin 2425) := Fin.ext h753
    subst k
    rw [sourceRowsAt753]
    exact rowSound753 B hB hF
  · have he : k = (754 : Fin 2425) := Fin.ext h754
    subst k
    rw [sourceRowsAt754]
    exact rowSound754 B hB hF
  · have he : k = (755 : Fin 2425) := Fin.ext h755
    subst k
    rw [sourceRowsAt755]
    exact rowSound755 B hB hF
  · have he : k = (756 : Fin 2425) := Fin.ext h756
    subst k
    rw [sourceRowsAt756]
    exact rowSound756 B hB hF
  · have he : k = (757 : Fin 2425) := Fin.ext h757
    subst k
    rw [sourceRowsAt757]
    exact rowSound757 B hB hF
  · have he : k = (758 : Fin 2425) := Fin.ext h758
    subst k
    rw [sourceRowsAt758]
    exact rowSound758_e B hB hF
  · have he : k = (759 : Fin 2425) := Fin.ext h759
    subst k
    rw [sourceRowsAt759]
    exact rowSound759_e B hB hF
  · have he : k = (760 : Fin 2425) := Fin.ext h760
    subst k
    rw [sourceRowsAt760]
    exact rowSound760 B hB hF
  · have he : k = (761 : Fin 2425) := Fin.ext h761
    subst k
    rw [sourceRowsAt761]
    exact rowSound761 B hB hF
  · have he : k = (762 : Fin 2425) := Fin.ext h762
    subst k
    rw [sourceRowsAt762]
    exact rowSound762 B hB hF
  · have he : k = (763 : Fin 2425) := Fin.ext h763
    subst k
    rw [sourceRowsAt763]
    exact rowSound763 B hB hF
  · have he : k = (764 : Fin 2425) := Fin.ext h764
    subst k
    rw [sourceRowsAt764]
    exact rowSound764 B hB hF
  · have he : k = (765 : Fin 2425) := Fin.ext h765
    subst k
    rw [sourceRowsAt765]
    exact rowSound765 B hB hF
  · have he : k = (766 : Fin 2425) := Fin.ext h766
    subst k
    rw [sourceRowsAt766]
    exact rowSound766 B hB hF
  · have he : k = (767 : Fin 2425) := Fin.ext h767
    subst k
    rw [sourceRowsAt767]
    exact rowSound767 B hB hF

end MUB6.Certificate.MixedSourceBridge

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedSourceBridge.chunkSound47_e_oai := @OAI.MUB6.Certificate.MixedSourceBridge.chunkSound47_e_oai
