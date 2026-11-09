-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedSourceBridge.chunkSound29_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T04:19:12.01746+00:00
-- url     : https://prove2.me/submissions/eca1c257-7652-420c-9c6e-730cbb314d2a

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E077
import Definitions.Def_OAIQ106E086
import Definitions.Def_OAIQ106E115
import Definitions.Def_OAIQ106E117
import Definitions.Def_OAIQ106E118
import Definitions.Def_OAIQ106E119
import Definitions.Def_OAIQ106E121
import Definitions.Def_OAIQ106E127
import Definitions.Def_OAIQ106E140
import Definitions.Def_OAIQ106E141
import Definitions.Def_OAIQ106E142
import Definitions.Def_OAIQ106E144
import Definitions.Def_OAIQ106E145
import Definitions.Def_OAIQ106E146
import Definitions.Def_OAIQ106E147
import Definitions.Def_OAIQ106E148
import Definitions.Def_OAIQ106E170
import Definitions.Def_OAIQ106E171
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound470_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound473_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound474_e

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical38
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical4873 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4873 raw4873Labels = mixedMoment B node3860 node3860Labels := by
  calc
    mixedMoment B raw4873 raw4873Labels = mixedMoment B raw4873step0 raw4873step0Labels := by
      have hz : ∀ j, raw4873 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4873step0 = (fun i j => raw4873 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4873step0 raw4873; decide +kernel
      have hl : raw4873step0Labels = raw4873Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4873 raw4873Labels permutation434 hz
    mixedMoment B raw4873step0 raw4873step0Labels = mixedMoment B raw4873step1 raw4873step1Labels := by
      have hz : ∀ j, raw4873step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4873step1 = (fun i j => raw4873step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4873step1 raw4873step0; decide +kernel
      have hl : raw4873step1Labels = raw4873step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4873step0 raw4873step0Labels permutation80 hz
    mixedMoment B raw4873step1 raw4873step1Labels = mixedMoment B raw4873step2 raw4873step2Labels := by
      have ha : raw4873step2 = (fun i j => raw4873step1 (permutation29 i) (permutation7 j)) := by apply Matrix.ext; unfold raw4873step2 raw4873step1; decide +kernel
      have hl : raw4873step2Labels = raw4873step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4873step1 raw4873step1Labels permutation29 permutation7
    mixedMoment B raw4873step2 raw4873step2Labels = mixedMoment B raw4873step3 raw4873step3Labels := by
      have ha : raw4873step3 = raw4873step2 := by apply Matrix.ext; unfold raw4873step3 raw4873step2; decide +kernel
      have hl : raw4873step2Labels = labelEmbedding1 ∘ raw4873step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4873step2 raw4873step2Labels raw4873step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3860 node3860Labels := by rfl

theorem canonical4878 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4878 raw4878Labels = mixedMoment B node3547 node3547Labels := by
  calc
    mixedMoment B raw4878 raw4878Labels = mixedMoment B raw4878step0 raw4878step0Labels := by
      have hz : ∀ j, raw4878 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4878step0 = (fun i j => raw4878 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4878step0 raw4878; decide +kernel
      have hl : raw4878step0Labels = raw4878Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4878 raw4878Labels permutation434 hz
    mixedMoment B raw4878step0 raw4878step0Labels = mixedMoment B raw4878step1 raw4878step1Labels := by
      have hz : ∀ j, raw4878step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4878step1 = (fun i j => raw4878step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4878step1 raw4878step0; decide +kernel
      have hl : raw4878step1Labels = raw4878step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4878step0 raw4878step0Labels permutation80 hz
    mixedMoment B raw4878step1 raw4878step1Labels = mixedMoment B raw4878step2 raw4878step2Labels := by
      have ha : raw4878step2 = (fun i j => raw4878step1 (permutation10 i) (permutation7 j)) := by apply Matrix.ext; unfold raw4878step2 raw4878step1; decide +kernel
      have hl : raw4878step2Labels = raw4878step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4878step1 raw4878step1Labels permutation10 permutation7
    mixedMoment B raw4878step2 raw4878step2Labels = mixedMoment B raw4878step3 raw4878step3Labels := by
      have ha : raw4878step3 = -raw4878step2 := by apply Matrix.ext; change ∀ i j, raw4878step3 i j = -(raw4878step2 i j); unfold raw4878step3 raw4878step2; decide +kernel
      have hl : raw4878step3Labels = raw4878step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw4878step3 raw4878step3Labels = mixedMoment B raw4878step4 raw4878step4Labels := by
      have ha : raw4878step4 = raw4878step3 := by apply Matrix.ext; unfold raw4878step4 raw4878step3; decide +kernel
      have hl : raw4878step3Labels = labelEmbedding1 ∘ raw4878step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4878step3 raw4878step3Labels raw4878step4Labels labelEmbedding1 hl
    _ = mixedMoment B node3547 node3547Labels := by rfl

theorem canonical4883 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4883 raw4883Labels = mixedMoment B node3533 node3533Labels := by
  calc
    mixedMoment B raw4883 raw4883Labels = mixedMoment B raw4883step0 raw4883step0Labels := by
      have hz : ∀ j, raw4883 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4883step0 = (fun i j => raw4883 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4883step0 raw4883; decide +kernel
      have hl : raw4883step0Labels = raw4883Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4883 raw4883Labels permutation434 hz
    mixedMoment B raw4883step0 raw4883step0Labels = mixedMoment B raw4883step1 raw4883step1Labels := by
      have ha : raw4883step1 = (fun i j => raw4883step0 (permutation46 i) (permutation7 j)) := by apply Matrix.ext; unfold raw4883step1 raw4883step0; decide +kernel
      have hl : raw4883step1Labels = raw4883step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4883step0 raw4883step0Labels permutation46 permutation7
    mixedMoment B raw4883step1 raw4883step1Labels = mixedMoment B raw4883step2 raw4883step2Labels := by
      have ha : raw4883step2 = -raw4883step1 := by apply Matrix.ext; change ∀ i j, raw4883step2 i j = -(raw4883step1 i j); unfold raw4883step2 raw4883step1; decide +kernel
      have hl : raw4883step2Labels = raw4883step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw4883step2 raw4883step2Labels = mixedMoment B raw4883step3 raw4883step3Labels := by
      have ha : raw4883step3 = raw4883step2 := by apply Matrix.ext; unfold raw4883step3 raw4883step2; decide +kernel
      have hl : raw4883step2Labels = labelEmbedding1 ∘ raw4883step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4883step2 raw4883step2Labels raw4883step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3533 node3533Labels := by rfl

theorem canonical4888 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4888 raw4888Labels = mixedMoment B node3533 node3533Labels := by
  calc
    mixedMoment B raw4888 raw4888Labels = mixedMoment B raw4888step0 raw4888step0Labels := by
      have hz : ∀ j, raw4888 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4888step0 = (fun i j => raw4888 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4888step0 raw4888; decide +kernel
      have hl : raw4888step0Labels = raw4888Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4888 raw4888Labels permutation346 hz
    mixedMoment B raw4888step0 raw4888step0Labels = mixedMoment B raw4888step1 raw4888step1Labels := by
      have ha : raw4888step1 = (fun i j => raw4888step0 (permutation46 i) (permutation7 j)) := by apply Matrix.ext; unfold raw4888step1 raw4888step0; decide +kernel
      have hl : raw4888step1Labels = raw4888step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4888step0 raw4888step0Labels permutation46 permutation7
    mixedMoment B raw4888step1 raw4888step1Labels = mixedMoment B raw4888step2 raw4888step2Labels := by
      have ha : raw4888step2 = -raw4888step1 := by apply Matrix.ext; change ∀ i j, raw4888step2 i j = -(raw4888step1 i j); unfold raw4888step2 raw4888step1; decide +kernel
      have hl : raw4888step2Labels = raw4888step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw4888step2 raw4888step2Labels = mixedMoment B raw4888step3 raw4888step3Labels := by
      have ha : raw4888step3 = raw4888step2 := by apply Matrix.ext; unfold raw4888step3 raw4888step2; decide +kernel
      have hl : raw4888step2Labels = labelEmbedding1 ∘ raw4888step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4888step2 raw4888step2Labels raw4888step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3533 node3533Labels := by rfl

theorem canonical4889 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4889 raw4889Labels = mixedMoment B node3302 node3302Labels := by
  calc
    mixedMoment B raw4889 raw4889Labels = mixedMoment B raw4889step0 raw4889step0Labels := by
      have hz : ∀ j, raw4889 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4889step0 = (fun i j => raw4889 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4889step0 raw4889; decide +kernel
      have hl : raw4889step0Labels = raw4889Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4889 raw4889Labels permutation434 hz
    mixedMoment B raw4889step0 raw4889step0Labels = mixedMoment B raw4889step1 raw4889step1Labels := by
      have hz : ∀ j, raw4889step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4889step1 = (fun i j => raw4889step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4889step1 raw4889step0; decide +kernel
      have hl : raw4889step1Labels = raw4889step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4889step0 raw4889step0Labels permutation80 hz
    mixedMoment B raw4889step1 raw4889step1Labels = mixedMoment B raw4889step2 raw4889step2Labels := by
      have ha : raw4889step2 = (fun i j => raw4889step1 (permutation9 i) (permutation5 j)) := by apply Matrix.ext; unfold raw4889step2 raw4889step1; decide +kernel
      have hl : raw4889step2Labels = raw4889step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4889step1 raw4889step1Labels permutation9 permutation5
    mixedMoment B raw4889step2 raw4889step2Labels = mixedMoment B raw4889step3 raw4889step3Labels := by
      have ha : raw4889step3 = -raw4889step2 := by apply Matrix.ext; change ∀ i j, raw4889step3 i j = -(raw4889step2 i j); unfold raw4889step3 raw4889step2; decide +kernel
      have hl : raw4889step3Labels = raw4889step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw4889step3 raw4889step3Labels = mixedMoment B raw4889step4 raw4889step4Labels := by
      have ha : raw4889step4 = raw4889step3 := by apply Matrix.ext; unfold raw4889step4 raw4889step3; decide +kernel
      have hl : raw4889step3Labels = labelEmbedding1 ∘ raw4889step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4889step3 raw4889step3Labels raw4889step4Labels labelEmbedding1 hl
    _ = mixedMoment B node3302 node3302Labels := by rfl

theorem canonical4890 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4890 raw4890Labels = mixedMoment B node3579 node3579Labels := by
  calc
    mixedMoment B raw4890 raw4890Labels = mixedMoment B raw4890step0 raw4890step0Labels := by
      have hz : ∀ j, raw4890 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4890step0 = (fun i j => raw4890 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4890step0 raw4890; decide +kernel
      have hl : raw4890step0Labels = raw4890Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4890 raw4890Labels permutation434 hz
    mixedMoment B raw4890step0 raw4890step0Labels = mixedMoment B raw4890step1 raw4890step1Labels := by
      have hz : ∀ j, raw4890step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4890step1 = (fun i j => raw4890step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4890step1 raw4890step0; decide +kernel
      have hl : raw4890step1Labels = raw4890step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4890step0 raw4890step0Labels permutation80 hz
    mixedMoment B raw4890step1 raw4890step1Labels = mixedMoment B raw4890step2 raw4890step2Labels := by
      have ha : raw4890step2 = (fun i j => raw4890step1 (permutation29 i) (permutation7 j)) := by apply Matrix.ext; unfold raw4890step2 raw4890step1; decide +kernel
      have hl : raw4890step2Labels = raw4890step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4890step1 raw4890step1Labels permutation29 permutation7
    mixedMoment B raw4890step2 raw4890step2Labels = mixedMoment B raw4890step3 raw4890step3Labels := by
      have ha : raw4890step3 = raw4890step2 := by apply Matrix.ext; unfold raw4890step3 raw4890step2; decide +kernel
      have hl : raw4890step2Labels = labelEmbedding1 ∘ raw4890step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4890step2 raw4890step2Labels raw4890step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3579 node3579Labels := by rfl

theorem canonical4891 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4891 raw4891Labels = mixedMoment B node3530 node3530Labels := by
  calc
    mixedMoment B raw4891 raw4891Labels = mixedMoment B raw4891step0 raw4891step0Labels := by
      have hz : ∀ j, raw4891 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4891step0 = (fun i j => raw4891 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4891step0 raw4891; decide +kernel
      have hl : raw4891step0Labels = raw4891Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4891 raw4891Labels permutation434 hz
    mixedMoment B raw4891step0 raw4891step0Labels = mixedMoment B raw4891step1 raw4891step1Labels := by
      have ha : raw4891step1 = (fun i j => raw4891step0 (permutation137 i) (permutation7 j)) := by apply Matrix.ext; unfold raw4891step1 raw4891step0; decide +kernel
      have hl : raw4891step1Labels = raw4891step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4891step0 raw4891step0Labels permutation137 permutation7
    mixedMoment B raw4891step1 raw4891step1Labels = mixedMoment B raw4891step2 raw4891step2Labels := by
      have ha : raw4891step2 = raw4891step1 := by apply Matrix.ext; unfold raw4891step2 raw4891step1; decide +kernel
      have hl : raw4891step1Labels = labelEmbedding1 ∘ raw4891step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4891step1 raw4891step1Labels raw4891step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3530 node3530Labels := by rfl

theorem canonical4892 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4892 raw4892Labels = mixedMoment B node3530 node3530Labels := by
  calc
    mixedMoment B raw4892 raw4892Labels = mixedMoment B raw4892step0 raw4892step0Labels := by
      have hz : ∀ j, raw4892 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4892step0 = (fun i j => raw4892 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4892step0 raw4892; decide +kernel
      have hl : raw4892step0Labels = raw4892Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4892 raw4892Labels permutation346 hz
    mixedMoment B raw4892step0 raw4892step0Labels = mixedMoment B raw4892step1 raw4892step1Labels := by
      have ha : raw4892step1 = (fun i j => raw4892step0 (permutation137 i) (permutation7 j)) := by apply Matrix.ext; unfold raw4892step1 raw4892step0; decide +kernel
      have hl : raw4892step1Labels = raw4892step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4892step0 raw4892step0Labels permutation137 permutation7
    mixedMoment B raw4892step1 raw4892step1Labels = mixedMoment B raw4892step2 raw4892step2Labels := by
      have ha : raw4892step2 = raw4892step1 := by apply Matrix.ext; unfold raw4892step2 raw4892step1; decide +kernel
      have hl : raw4892step1Labels = labelEmbedding1 ∘ raw4892step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4892step1 raw4892step1Labels raw4892step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3530 node3530Labels := by rfl

theorem canonical4904 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4904 raw4904Labels = mixedMoment B node3905 node3905Labels := by
  calc
    mixedMoment B raw4904 raw4904Labels = mixedMoment B raw4904step0 raw4904step0Labels := by
      have hz : ∀ j, raw4904 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4904step0 = (fun i j => raw4904 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4904step0 raw4904; decide +kernel
      have hl : raw4904step0Labels = raw4904Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4904 raw4904Labels permutation434 hz
    mixedMoment B raw4904step0 raw4904step0Labels = mixedMoment B raw4904step1 raw4904step1Labels := by
      have hz : ∀ j, raw4904step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4904step1 = (fun i j => raw4904step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4904step1 raw4904step0; decide +kernel
      have hl : raw4904step1Labels = raw4904step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4904step0 raw4904step0Labels permutation80 hz
    mixedMoment B raw4904step1 raw4904step1Labels = mixedMoment B raw4904step2 raw4904step2Labels := by
      have ha : raw4904step2 = (fun i j => raw4904step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4904step2 raw4904step1; decide +kernel
      have hl : raw4904step2Labels = raw4904step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4904step1 raw4904step1Labels permutation10 permutation2
    _ = mixedMoment B node3905 node3905Labels := by rfl

theorem canonical4905 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4905 raw4905Labels = mixedMoment B node4092 node4092Labels := by
  calc
    mixedMoment B raw4905 raw4905Labels = mixedMoment B raw4905step0 raw4905step0Labels := by
      have hz : ∀ j, raw4905 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4905step0 = (fun i j => raw4905 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4905step0 raw4905; decide +kernel
      have hl : raw4905step0Labels = raw4905Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4905 raw4905Labels permutation434 hz
    mixedMoment B raw4905step0 raw4905step0Labels = mixedMoment B raw4905step1 raw4905step1Labels := by
      have hz : ∀ j, raw4905step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4905step1 = (fun i j => raw4905step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4905step1 raw4905step0; decide +kernel
      have hl : raw4905step1Labels = raw4905step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4905step0 raw4905step0Labels permutation80 hz
    mixedMoment B raw4905step1 raw4905step1Labels = mixedMoment B raw4905step2 raw4905step2Labels := by
      have ha : raw4905step2 = (fun i j => raw4905step1 (permutation10 i) (permutation0 j)) := by apply Matrix.ext; unfold raw4905step2 raw4905step1; decide +kernel
      have hl : raw4905step2Labels = raw4905step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4905step1 raw4905step1Labels permutation10 permutation0
    _ = mixedMoment B node4092 node4092Labels := by rfl

theorem canonical4909 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4909 raw4909Labels = mixedMoment B node1264 node1264Labels := by
  calc
    mixedMoment B raw4909 raw4909Labels = mixedMoment B raw4909step0 raw4909step0Labels := by
      have hz : ∀ j, raw4909 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4909step0 = (fun i j => raw4909 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4909step0 raw4909; decide +kernel
      have hl : raw4909step0Labels = raw4909Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4909 raw4909Labels permutation434 hz
    mixedMoment B raw4909step0 raw4909step0Labels = mixedMoment B raw4909step1 raw4909step1Labels := by
      have hz : ∀ j, raw4909step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4909step1 = (fun i j => raw4909step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4909step1 raw4909step0; decide +kernel
      have hl : raw4909step1Labels = raw4909step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4909step0 raw4909step0Labels permutation80 hz
    _ = mixedMoment B node1264 node1264Labels := by rfl

theorem canonical4914 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4914 raw4914Labels = mixedMoment B node2742 node2742Labels := by
  calc
    mixedMoment B raw4914 raw4914Labels = mixedMoment B raw4914step0 raw4914step0Labels := by
      have hz : ∀ j, raw4914 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4914step0 = (fun i j => raw4914 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4914step0 raw4914; decide +kernel
      have hl : raw4914step0Labels = raw4914Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4914 raw4914Labels permutation434 hz
    mixedMoment B raw4914step0 raw4914step0Labels = mixedMoment B raw4914step1 raw4914step1Labels := by
      have hz : ∀ j, raw4914step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4914step1 = (fun i j => raw4914step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4914step1 raw4914step0; decide +kernel
      have hl : raw4914step1Labels = raw4914step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4914step0 raw4914step0Labels permutation80 hz
    mixedMoment B raw4914step1 raw4914step1Labels = mixedMoment B raw4914step2 raw4914step2Labels := by
      have ha : raw4914step2 = (fun i j => raw4914step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4914step2 raw4914step1; decide +kernel
      have hl : raw4914step2Labels = raw4914step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4914step1 raw4914step1Labels permutation10 permutation2
    _ = mixedMoment B node2742 node2742Labels := by rfl

theorem canonical4917 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4917 raw4917Labels = mixedMoment B node2635 node2635Labels := by
  calc
    mixedMoment B raw4917 raw4917Labels = mixedMoment B raw4917step0 raw4917step0Labels := by
      have hz : ∀ j, raw4917 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4917step0 = (fun i j => raw4917 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4917step0 raw4917; decide +kernel
      have hl : raw4917step0Labels = raw4917Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4917 raw4917Labels permutation434 hz
    mixedMoment B raw4917step0 raw4917step0Labels = mixedMoment B raw4917step1 raw4917step1Labels := by
      have hz : ∀ j, raw4917step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4917step1 = (fun i j => raw4917step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4917step1 raw4917step0; decide +kernel
      have hl : raw4917step1Labels = raw4917step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4917step0 raw4917step0Labels permutation80 hz
    _ = mixedMoment B node2635 node2635Labels := by rfl

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

theorem canonical544 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw544 raw544Labels = mixedMoment B node3888 node3888Labels := by
  calc
    mixedMoment B raw544 raw544Labels = mixedMoment B raw544step0 raw544step0Labels := by
      have ha : raw544step0 = (fun i j => raw544 (permutation8 i) (permutation5 j)) := by apply Matrix.ext; unfold raw544step0 raw544; decide +kernel
      have hl : raw544step0Labels = raw544Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw544 raw544Labels permutation8 permutation5
    mixedMoment B raw544step0 raw544step0Labels = mixedMoment B raw544step1 raw544step1Labels := by
      have ha : raw544step1 = raw544step0 := by apply Matrix.ext; unfold raw544step1 raw544step0; decide +kernel
      have hl : raw544step0Labels = labelEmbedding1 ∘ raw544step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw544step0 raw544step0Labels raw544step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3888 node3888Labels := by rfl

theorem canonical545 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw545 raw545Labels = mixedMoment B node503 node503Labels := by
  calc
    mixedMoment B raw545 raw545Labels = mixedMoment B raw545step0 raw545step0Labels := by
      have ha : raw545step0 = (fun i j => raw545 (permutation8 i) (permutation5 j)) := by apply Matrix.ext; unfold raw545step0 raw545; decide +kernel
      have hl : raw545step0Labels = raw545Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw545 raw545Labels permutation8 permutation5
    _ = mixedMoment B node503 node503Labels := by rfl

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

theorem canonical5760 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5760 raw5760Labels = mixedMoment B node2277 node2277Labels := by
  calc
    mixedMoment B raw5760 raw5760Labels = mixedMoment B raw5760step0 raw5760step0Labels := by
      have hz : ∀ j, raw5760 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw5760step0 = (fun i j => raw5760 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw5760step0 raw5760; decide +kernel
      have hl : raw5760step0Labels = raw5760Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5760 raw5760Labels permutation265 hz
    mixedMoment B raw5760step0 raw5760step0Labels = mixedMoment B raw5760step1 raw5760step1Labels := by
      have ha : raw5760step1 = (fun i j => raw5760step0 (permutation50 i) (permutation4 j)) := by apply Matrix.ext; unfold raw5760step1 raw5760step0; decide +kernel
      have hl : raw5760step1Labels = raw5760step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5760step0 raw5760step0Labels permutation50 permutation4
    mixedMoment B raw5760step1 raw5760step1Labels = mixedMoment B raw5760step2 raw5760step2Labels := by
      have ha : raw5760step2 = -raw5760step1 := by apply Matrix.ext; change ∀ i j, raw5760step2 i j = -(raw5760step1 i j); unfold raw5760step2 raw5760step1; decide +kernel
      have hl : raw5760step2Labels = raw5760step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2277 node2277Labels := by rfl

theorem canonical5763 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5763 raw5763Labels = mixedMoment B node2131 node2131Labels := by
  calc
    mixedMoment B raw5763 raw5763Labels = mixedMoment B raw5763step0 raw5763step0Labels := by
      have ha : raw5763step0 = (fun i j => raw5763 (permutation246 i) (permutation4 j)) := by apply Matrix.ext; unfold raw5763step0 raw5763; decide +kernel
      have hl : raw5763step0Labels = raw5763Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5763 raw5763Labels permutation246 permutation4
    mixedMoment B raw5763step0 raw5763step0Labels = mixedMoment B raw5763step1 raw5763step1Labels := by
      have ha : raw5763step1 = -raw5763step0 := by apply Matrix.ext; change ∀ i j, raw5763step1 i j = -(raw5763step0 i j); unfold raw5763step1 raw5763step0; decide +kernel
      have hl : raw5763step1Labels = raw5763step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2131 node2131Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical59
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical7553 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7553 raw7553Labels = mixedMoment B node2552 node2552Labels := by
  calc
    mixedMoment B raw7553 raw7553Labels = mixedMoment B raw7553step0 raw7553step0Labels := by
      have ha : raw7553step0 = (fun i j => raw7553 (permutation620 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7553step0 raw7553; decide +kernel
      have hl : raw7553step0Labels = raw7553Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7553 raw7553Labels permutation620 permutation2
    _ = mixedMoment B node2552 node2552Labels := by rfl

theorem canonical7556 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7556 raw7556Labels = mixedMoment B node2738 node2738Labels := by
  calc
    mixedMoment B raw7556 raw7556Labels = mixedMoment B raw7556step0 raw7556step0Labels := by
      have hz : ∀ j, raw7556 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw7556step0 = (fun i j => raw7556 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw7556step0 raw7556; decide +kernel
      have hl : raw7556step0Labels = raw7556Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7556 raw7556Labels permutation265 hz
    mixedMoment B raw7556step0 raw7556step0Labels = mixedMoment B raw7556step1 raw7556step1Labels := by
      have ha : raw7556step1 = (fun i j => raw7556step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7556step1 raw7556step0; decide +kernel
      have hl : raw7556step1Labels = raw7556step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7556step0 raw7556step0Labels permutation149 permutation2
    _ = mixedMoment B node2738 node2738Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical64
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical8316 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8316 raw8316Labels = mixedMoment B node2740 node2740Labels := by
  calc
    mixedMoment B raw8316 raw8316Labels = mixedMoment B raw8316step0 raw8316step0Labels := by
      have hz : ∀ j, raw8316 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8316step0 = (fun i j => raw8316 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8316step0 raw8316; decide +kernel
      have hl : raw8316step0Labels = raw8316Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8316 raw8316Labels permutation346 hz
    mixedMoment B raw8316step0 raw8316step0Labels = mixedMoment B raw8316step1 raw8316step1Labels := by
      have hz : ∀ j, raw8316step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8316step1 = (fun i j => raw8316step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8316step1 raw8316step0; decide +kernel
      have hl : raw8316step1Labels = raw8316step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8316step0 raw8316step0Labels permutation56 hz
    mixedMoment B raw8316step1 raw8316step1Labels = mixedMoment B raw8316step2 raw8316step2Labels := by
      have ha : raw8316step2 = (fun i j => raw8316step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw8316step2 raw8316step1; decide +kernel
      have hl : raw8316step2Labels = raw8316step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8316step1 raw8316step1Labels permutation31 permutation2
    _ = mixedMoment B node2740 node2740Labels := by rfl

theorem canonical8319 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8319 raw8319Labels = mixedMoment B node2132 node2132Labels := by
  calc
    mixedMoment B raw8319 raw8319Labels = mixedMoment B raw8319step0 raw8319step0Labels := by
      have hz : ∀ j, raw8319 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8319step0 = (fun i j => raw8319 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8319step0 raw8319; decide +kernel
      have hl : raw8319step0Labels = raw8319Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8319 raw8319Labels permutation265 hz
    mixedMoment B raw8319step0 raw8319step0Labels = mixedMoment B raw8319step1 raw8319step1Labels := by
      have ha : raw8319step1 = (fun i j => raw8319step0 (permutation50 i) (permutation4 j)) := by apply Matrix.ext; unfold raw8319step1 raw8319step0; decide +kernel
      have hl : raw8319step1Labels = raw8319step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8319step0 raw8319step0Labels permutation50 permutation4
    mixedMoment B raw8319step1 raw8319step1Labels = mixedMoment B raw8319step2 raw8319step2Labels := by
      have ha : raw8319step2 = -raw8319step1 := by apply Matrix.ext; change ∀ i j, raw8319step2 i j = -(raw8319step1 i j); unfold raw8319step2 raw8319step1; decide +kernel
      have hl : raw8319step2Labels = raw8319step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2132 node2132Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical72
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical9251 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9251 raw9251Labels = mixedMoment B node2509 node2509Labels := by
  calc
    mixedMoment B raw9251 raw9251Labels = mixedMoment B raw9251step0 raw9251step0Labels := by
      have hz : ∀ j, raw9251 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9251step0 = (fun i j => raw9251 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9251step0 raw9251; decide +kernel
      have hl : raw9251step0Labels = raw9251Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9251 raw9251Labels permutation265 hz
    mixedMoment B raw9251step0 raw9251step0Labels = mixedMoment B raw9251step1 raw9251step1Labels := by
      have ha : raw9251step1 = (fun i j => raw9251step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9251step1 raw9251step0; decide +kernel
      have hl : raw9251step1Labels = raw9251step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9251step0 raw9251step0Labels permutation149 permutation2
    _ = mixedMoment B node2509 node2509Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical73
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical9451 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9451 raw9451Labels = mixedMoment B node3075 node3075Labels := by
  calc
    mixedMoment B raw9451 raw9451Labels = mixedMoment B raw9451step0 raw9451step0Labels := by
      have hz : ∀ j, raw9451 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9451step0 = (fun i j => raw9451 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9451step0 raw9451; decide +kernel
      have hl : raw9451step0Labels = raw9451Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9451 raw9451Labels permutation265 hz
    _ = mixedMoment B node3075 node3075Labels := by rfl

theorem canonical9452 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9452 raw9452Labels = mixedMoment B node3525 node3525Labels := by
  calc
    mixedMoment B raw9452 raw9452Labels = mixedMoment B raw9452step0 raw9452step0Labels := by
      have ha : raw9452step0 = (fun i j => raw9452 (permutation682 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9452step0 raw9452; decide +kernel
      have hl : raw9452step0Labels = raw9452Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9452 raw9452Labels permutation682 permutation2
    mixedMoment B raw9452step0 raw9452step0Labels = mixedMoment B raw9452step1 raw9452step1Labels := by
      have ha : raw9452step1 = -raw9452step0 := by apply Matrix.ext; change ∀ i j, raw9452step1 i j = -(raw9452step0 i j); unfold raw9452step1 raw9452step0; decide +kernel
      have hl : raw9452step1Labels = raw9452step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3525 node3525Labels := by rfl

theorem canonical9453 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9453 raw9453Labels = mixedMoment B node3534 node3534Labels := by
  calc
    mixedMoment B raw9453 raw9453Labels = mixedMoment B raw9453step0 raw9453step0Labels := by
      have hz : ∀ j, raw9453 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9453step0 = (fun i j => raw9453 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9453step0 raw9453; decide +kernel
      have hl : raw9453step0Labels = raw9453Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9453 raw9453Labels permutation265 hz
    mixedMoment B raw9453step0 raw9453step0Labels = mixedMoment B raw9453step1 raw9453step1Labels := by
      have ha : raw9453step1 = (fun i j => raw9453step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9453step1 raw9453step0; decide +kernel
      have hl : raw9453step1Labels = raw9453step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9453step0 raw9453step0Labels permutation151 permutation2
    mixedMoment B raw9453step1 raw9453step1Labels = mixedMoment B raw9453step2 raw9453step2Labels := by
      have ha : raw9453step2 = -raw9453step1 := by apply Matrix.ext; change ∀ i j, raw9453step2 i j = -(raw9453step1 i j); unfold raw9453step2 raw9453step1; decide +kernel
      have hl : raw9453step2Labels = raw9453step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3534 node3534Labels := by rfl

theorem canonical9454 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9454 raw9454Labels = mixedMoment B node3534 node3534Labels := by
  calc
    mixedMoment B raw9454 raw9454Labels = mixedMoment B raw9454step0 raw9454step0Labels := by
      have hz : ∀ j, raw9454 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9454step0 = (fun i j => raw9454 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9454step0 raw9454; decide +kernel
      have hl : raw9454step0Labels = raw9454Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9454 raw9454Labels permutation265 hz
    mixedMoment B raw9454step0 raw9454step0Labels = mixedMoment B raw9454step1 raw9454step1Labels := by
      have ha : raw9454step1 = (fun i j => raw9454step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9454step1 raw9454step0; decide +kernel
      have hl : raw9454step1Labels = raw9454step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9454step0 raw9454step0Labels permutation149 permutation2
    mixedMoment B raw9454step1 raw9454step1Labels = mixedMoment B raw9454step2 raw9454step2Labels := by
      have ha : raw9454step2 = -raw9454step1 := by apply Matrix.ext; change ∀ i j, raw9454step2 i j = -(raw9454step1 i j); unfold raw9454step2 raw9454step1; decide +kernel
      have hl : raw9454step2Labels = raw9454step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3534 node3534Labels := by rfl

theorem canonical9455 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9455 raw9455Labels = mixedMoment B node3623 node3623Labels := by
  calc
    mixedMoment B raw9455 raw9455Labels = mixedMoment B raw9455step0 raw9455step0Labels := by
      have hz : ∀ j, raw9455 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw9455step0 = (fun i j => raw9455 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw9455step0 raw9455; decide +kernel
      have hl : raw9455step0Labels = raw9455Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9455 raw9455Labels permutation520 hz
    mixedMoment B raw9455step0 raw9455step0Labels = mixedMoment B raw9455step1 raw9455step1Labels := by
      have hz : ∀ j, raw9455step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw9455step1 = (fun i j => raw9455step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw9455step1 raw9455step0; decide +kernel
      have hl : raw9455step1Labels = raw9455step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9455step0 raw9455step0Labels permutation56 hz
    mixedMoment B raw9455step1 raw9455step1Labels = mixedMoment B raw9455step2 raw9455step2Labels := by
      have ha : raw9455step2 = (fun i j => raw9455step1 (permutation29 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9455step2 raw9455step1; decide +kernel
      have hl : raw9455step2Labels = raw9455step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9455step1 raw9455step1Labels permutation29 permutation2
    mixedMoment B raw9455step2 raw9455step2Labels = mixedMoment B raw9455step3 raw9455step3Labels := by
      have ha : raw9455step3 = -raw9455step2 := by apply Matrix.ext; change ∀ i j, raw9455step3 i j = -(raw9455step2 i j); unfold raw9455step3 raw9455step2; decide +kernel
      have hl : raw9455step3Labels = raw9455step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3623 node3623Labels := by rfl

theorem canonical9456 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9456 raw9456Labels = mixedMoment B node3581 node3581Labels := by
  calc
    mixedMoment B raw9456 raw9456Labels = mixedMoment B raw9456step0 raw9456step0Labels := by
      have hz : ∀ j, raw9456 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9456step0 = (fun i j => raw9456 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9456step0 raw9456; decide +kernel
      have hl : raw9456step0Labels = raw9456Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9456 raw9456Labels permutation265 hz
    mixedMoment B raw9456step0 raw9456step0Labels = mixedMoment B raw9456step1 raw9456step1Labels := by
      have ha : raw9456step1 = (fun i j => raw9456step0 (permutation132 i) (permutation4 j)) := by apply Matrix.ext; unfold raw9456step1 raw9456step0; decide +kernel
      have hl : raw9456step1Labels = raw9456step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9456step0 raw9456step0Labels permutation132 permutation4
    mixedMoment B raw9456step1 raw9456step1Labels = mixedMoment B raw9456step2 raw9456step2Labels := by
      have ha : raw9456step2 = -raw9456step1 := by apply Matrix.ext; change ∀ i j, raw9456step2 i j = -(raw9456step1 i j); unfold raw9456step2 raw9456step1; decide +kernel
      have hl : raw9456step2Labels = raw9456step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3581 node3581Labels := by rfl

theorem canonical9457 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9457 raw9457Labels = mixedMoment B node4083 node4083Labels := by
  calc
    mixedMoment B raw9457 raw9457Labels = mixedMoment B raw9457step0 raw9457step0Labels := by
      have hz : ∀ j, raw9457 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw9457step0 = (fun i j => raw9457 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw9457step0 raw9457; decide +kernel
      have hl : raw9457step0Labels = raw9457Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9457 raw9457Labels permutation520 hz
    mixedMoment B raw9457step0 raw9457step0Labels = mixedMoment B raw9457step1 raw9457step1Labels := by
      have hz : ∀ j, raw9457step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw9457step1 = (fun i j => raw9457step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw9457step1 raw9457step0; decide +kernel
      have hl : raw9457step1Labels = raw9457step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9457step0 raw9457step0Labels permutation56 hz
    mixedMoment B raw9457step1 raw9457step1Labels = mixedMoment B raw9457step2 raw9457step2Labels := by
      have ha : raw9457step2 = (fun i j => raw9457step1 (permutation26 i) (permutation0 j)) := by apply Matrix.ext; unfold raw9457step2 raw9457step1; decide +kernel
      have hl : raw9457step2Labels = raw9457step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9457step1 raw9457step1Labels permutation26 permutation0
    mixedMoment B raw9457step2 raw9457step2Labels = mixedMoment B raw9457step3 raw9457step3Labels := by
      have ha : raw9457step3 = -raw9457step2 := by apply Matrix.ext; change ∀ i j, raw9457step3 i j = -(raw9457step2 i j); unfold raw9457step3 raw9457step2; decide +kernel
      have hl : raw9457step3Labels = raw9457step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4083 node4083Labels := by rfl

theorem canonical9458 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9458 raw9458Labels = mixedMoment B node1382 node1382Labels := by
  calc
    mixedMoment B raw9458 raw9458Labels = mixedMoment B raw9458step0 raw9458step0Labels := by
      have ha : raw9458step0 = (fun i j => raw9458 (permutation182 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9458step0 raw9458; decide +kernel
      have hl : raw9458step0Labels = raw9458Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9458 raw9458Labels permutation182 permutation2
    _ = mixedMoment B node1382 node1382Labels := by rfl

theorem canonical9459 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9459 raw9459Labels = mixedMoment B node1404 node1404Labels := by
  calc
    mixedMoment B raw9459 raw9459Labels = mixedMoment B raw9459step0 raw9459step0Labels := by
      have hz : ∀ j, raw9459 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9459step0 = (fun i j => raw9459 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9459step0 raw9459; decide +kernel
      have hl : raw9459step0Labels = raw9459Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9459 raw9459Labels permutation265 hz
    mixedMoment B raw9459step0 raw9459step0Labels = mixedMoment B raw9459step1 raw9459step1Labels := by
      have ha : raw9459step1 = (fun i j => raw9459step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9459step1 raw9459step0; decide +kernel
      have hl : raw9459step1Labels = raw9459step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9459step0 raw9459step0Labels permutation38 permutation2
    _ = mixedMoment B node1404 node1404Labels := by rfl

theorem canonical9460 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9460 raw9460Labels = mixedMoment B node1404 node1404Labels := by
  calc
    mixedMoment B raw9460 raw9460Labels = mixedMoment B raw9460step0 raw9460step0Labels := by
      have hz : ∀ j, raw9460 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9460step0 = (fun i j => raw9460 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9460step0 raw9460; decide +kernel
      have hl : raw9460step0Labels = raw9460Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9460 raw9460Labels permutation265 hz
    _ = mixedMoment B node1404 node1404Labels := by rfl

theorem canonical9461 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9461 raw9461Labels = mixedMoment B node1390 node1390Labels := by
  calc
    mixedMoment B raw9461 raw9461Labels = mixedMoment B raw9461step0 raw9461step0Labels := by
      have hz : ∀ j, raw9461 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9461step0 = (fun i j => raw9461 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9461step0 raw9461; decide +kernel
      have hl : raw9461step0Labels = raw9461Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9461 raw9461Labels permutation265 hz
    _ = mixedMoment B node1390 node1390Labels := by rfl

theorem canonical9462 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9462 raw9462Labels = mixedMoment B node1385 node1385Labels := by
  calc
    mixedMoment B raw9462 raw9462Labels = mixedMoment B raw9462step0 raw9462step0Labels := by
      have hz : ∀ j, raw9462 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9462step0 = (fun i j => raw9462 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9462step0 raw9462; decide +kernel
      have hl : raw9462step0Labels = raw9462Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9462 raw9462Labels permutation265 hz
    _ = mixedMoment B node1385 node1385Labels := by rfl

theorem canonical9463 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9463 raw9463Labels = mixedMoment B node2923 node2923Labels := by
  calc
    mixedMoment B raw9463 raw9463Labels = mixedMoment B raw9463step0 raw9463step0Labels := by
      have ha : raw9463step0 = (fun i j => raw9463 (permutation182 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9463step0 raw9463; decide +kernel
      have hl : raw9463step0Labels = raw9463Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9463 raw9463Labels permutation182 permutation2
    _ = mixedMoment B node2923 node2923Labels := by rfl

theorem canonical9464 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9464 raw9464Labels = mixedMoment B node2923 node2923Labels := by
  calc
    mixedMoment B raw9464 raw9464Labels = mixedMoment B raw9464step0 raw9464step0Labels := by
      have ha : raw9464step0 = (fun i j => raw9464 (permutation206 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9464step0 raw9464; decide +kernel
      have hl : raw9464step0Labels = raw9464Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9464 raw9464Labels permutation206 permutation2
    _ = mixedMoment B node2923 node2923Labels := by rfl

theorem canonical9465 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9465 raw9465Labels = mixedMoment B node3075 node3075Labels := by
  calc
    mixedMoment B raw9465 raw9465Labels = mixedMoment B raw9465step0 raw9465step0Labels := by
      have hz : ∀ j, raw9465 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw9465step0 = (fun i j => raw9465 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw9465step0 raw9465; decide +kernel
      have hl : raw9465step0Labels = raw9465Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9465 raw9465Labels permutation520 hz
    mixedMoment B raw9465step0 raw9465step0Labels = mixedMoment B raw9465step1 raw9465step1Labels := by
      have ha : raw9465step1 = (fun i j => raw9465step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9465step1 raw9465step0; decide +kernel
      have hl : raw9465step1Labels = raw9465step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9465step0 raw9465step0Labels permutation40 permutation2
    _ = mixedMoment B node3075 node3075Labels := by rfl

theorem canonical9466 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9466 raw9466Labels = mixedMoment B node3073 node3073Labels := by
  calc
    mixedMoment B raw9466 raw9466Labels = mixedMoment B raw9466step0 raw9466step0Labels := by
      have ha : raw9466step0 = (fun i j => raw9466 (permutation182 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9466step0 raw9466; decide +kernel
      have hl : raw9466step0Labels = raw9466Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9466 raw9466Labels permutation182 permutation2
    _ = mixedMoment B node3073 node3073Labels := by rfl

theorem canonical9467 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9467 raw9467Labels = mixedMoment B node2983 node2983Labels := by
  calc
    mixedMoment B raw9467 raw9467Labels = mixedMoment B raw9467step0 raw9467step0Labels := by
      have ha : raw9467step0 = (fun i j => raw9467 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9467step0 raw9467; decide +kernel
      have hl : raw9467step0Labels = raw9467Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9467 raw9467Labels permutation158 permutation2
    _ = mixedMoment B node2983 node2983Labels := by rfl

theorem canonical9468 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9468 raw9468Labels = mixedMoment B node2983 node2983Labels := by
  calc
    _ = mixedMoment B node2983 node2983Labels := by rfl

theorem canonical9469 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9469 raw9469Labels = mixedMoment B node2980 node2980Labels := by
  calc
    _ = mixedMoment B node2980 node2980Labels := by rfl

theorem canonical9470 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9470 raw9470Labels = mixedMoment B node2009 node2009Labels := by
  calc
    mixedMoment B raw9470 raw9470Labels = mixedMoment B raw9470step0 raw9470step0Labels := by
      have ha : raw9470step0 = (fun i j => raw9470 (permutation682 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9470step0 raw9470; decide +kernel
      have hl : raw9470step0Labels = raw9470Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9470 raw9470Labels permutation682 permutation2
    mixedMoment B raw9470step0 raw9470step0Labels = mixedMoment B raw9470step1 raw9470step1Labels := by
      have ha : raw9470step1 = -raw9470step0 := by apply Matrix.ext; change ∀ i j, raw9470step1 i j = -(raw9470step0 i j); unfold raw9470step1 raw9470step0; decide +kernel
      have hl : raw9470step1Labels = raw9470step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2009 node2009Labels := by rfl

theorem canonical9471 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9471 raw9471Labels = mixedMoment B node2952 node2952Labels := by
  calc
    mixedMoment B raw9471 raw9471Labels = mixedMoment B raw9471step0 raw9471step0Labels := by
      have hz : ∀ j, raw9471 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9471step0 = (fun i j => raw9471 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9471step0 raw9471; decide +kernel
      have hl : raw9471step0Labels = raw9471Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9471 raw9471Labels permutation265 hz
    _ = mixedMoment B node2952 node2952Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical74
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical9472 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9472 raw9472Labels = mixedMoment B node2930 node2930Labels := by
  calc
    mixedMoment B raw9472 raw9472Labels = mixedMoment B raw9472step0 raw9472step0Labels := by
      have hz : ∀ j, raw9472 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9472step0 = (fun i j => raw9472 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9472step0 raw9472; decide +kernel
      have hl : raw9472step0Labels = raw9472Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9472 raw9472Labels permutation265 hz
    _ = mixedMoment B node2930 node2930Labels := by rfl

theorem canonical9473 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9473 raw9473Labels = mixedMoment B node2025 node2025Labels := by
  calc
    mixedMoment B raw9473 raw9473Labels = mixedMoment B raw9473step0 raw9473step0Labels := by
      have hz : ∀ j, raw9473 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9473step0 = (fun i j => raw9473 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9473step0 raw9473; decide +kernel
      have hl : raw9473step0Labels = raw9473Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9473 raw9473Labels permutation265 hz
    mixedMoment B raw9473step0 raw9473step0Labels = mixedMoment B raw9473step1 raw9473step1Labels := by
      have ha : raw9473step1 = (fun i j => raw9473step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9473step1 raw9473step0; decide +kernel
      have hl : raw9473step1Labels = raw9473step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9473step0 raw9473step0Labels permutation151 permutation2
    mixedMoment B raw9473step1 raw9473step1Labels = mixedMoment B raw9473step2 raw9473step2Labels := by
      have ha : raw9473step2 = -raw9473step1 := by apply Matrix.ext; change ∀ i j, raw9473step2 i j = -(raw9473step1 i j); unfold raw9473step2 raw9473step1; decide +kernel
      have hl : raw9473step2Labels = raw9473step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2025 node2025Labels := by rfl

theorem canonical9474 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9474 raw9474Labels = mixedMoment B node2930 node2930Labels := by
  calc
    mixedMoment B raw9474 raw9474Labels = mixedMoment B raw9474step0 raw9474step0Labels := by
      have hz : ∀ j, raw9474 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9474step0 = (fun i j => raw9474 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9474step0 raw9474; decide +kernel
      have hl : raw9474step0Labels = raw9474Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9474 raw9474Labels permutation265 hz
    mixedMoment B raw9474step0 raw9474step0Labels = mixedMoment B raw9474step1 raw9474step1Labels := by
      have ha : raw9474step1 = (fun i j => raw9474step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9474step1 raw9474step0; decide +kernel
      have hl : raw9474step1Labels = raw9474step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9474step0 raw9474step0Labels permutation38 permutation2
    _ = mixedMoment B node2930 node2930Labels := by rfl

theorem canonical9475 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9475 raw9475Labels = mixedMoment B node3079 node3079Labels := by
  calc
    mixedMoment B raw9475 raw9475Labels = mixedMoment B raw9475step0 raw9475step0Labels := by
      have hz : ∀ j, raw9475 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9475step0 = (fun i j => raw9475 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9475step0 raw9475; decide +kernel
      have hl : raw9475step0Labels = raw9475Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9475 raw9475Labels permutation265 hz
    mixedMoment B raw9475step0 raw9475step0Labels = mixedMoment B raw9475step1 raw9475step1Labels := by
      have ha : raw9475step1 = (fun i j => raw9475step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9475step1 raw9475step0; decide +kernel
      have hl : raw9475step1Labels = raw9475step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9475step0 raw9475step0Labels permutation33 permutation2
    _ = mixedMoment B node3079 node3079Labels := by rfl

theorem canonical9503 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9503 raw9503Labels = mixedMoment B node2740 node2740Labels := by
  calc
    mixedMoment B raw9503 raw9503Labels = mixedMoment B raw9503step0 raw9503step0Labels := by
      have hz : ∀ j, raw9503 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw9503step0 = (fun i j => raw9503 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw9503step0 raw9503; decide +kernel
      have hl : raw9503step0Labels = raw9503Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9503 raw9503Labels permutation434 hz
    mixedMoment B raw9503step0 raw9503step0Labels = mixedMoment B raw9503step1 raw9503step1Labels := by
      have hz : ∀ j, raw9503step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw9503step1 = (fun i j => raw9503step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw9503step1 raw9503step0; decide +kernel
      have hl : raw9503step1Labels = raw9503step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9503step0 raw9503step0Labels permutation56 hz
    mixedMoment B raw9503step1 raw9503step1Labels = mixedMoment B raw9503step2 raw9503step2Labels := by
      have ha : raw9503step2 = (fun i j => raw9503step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9503step2 raw9503step1; decide +kernel
      have hl : raw9503step2Labels = raw9503step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9503step1 raw9503step1Labels permutation31 permutation2
    _ = mixedMoment B node2740 node2740Labels := by rfl

theorem canonical9504 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9504 raw9504Labels = mixedMoment B node1234 node1234Labels := by
  calc
    mixedMoment B raw9504 raw9504Labels = mixedMoment B raw9504step0 raw9504step0Labels := by
      have hz : ∀ j, raw9504 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9504step0 = (fun i j => raw9504 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9504step0 raw9504; decide +kernel
      have hl : raw9504step0Labels = raw9504Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9504 raw9504Labels permutation265 hz
    mixedMoment B raw9504step0 raw9504step0Labels = mixedMoment B raw9504step1 raw9504step1Labels := by
      have ha : raw9504step1 = (fun i j => raw9504step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9504step1 raw9504step0; decide +kernel
      have hl : raw9504step1Labels = raw9504step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9504step0 raw9504step0Labels permutation149 permutation2
    _ = mixedMoment B node1234 node1234Labels := by rfl

theorem canonical9505 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9505 raw9505Labels = mixedMoment B node2133 node2133Labels := by
  calc
    mixedMoment B raw9505 raw9505Labels = mixedMoment B raw9505step0 raw9505step0Labels := by
      have hz : ∀ j, raw9505 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9505step0 = (fun i j => raw9505 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9505step0 raw9505; decide +kernel
      have hl : raw9505step0Labels = raw9505Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9505 raw9505Labels permutation265 hz
    mixedMoment B raw9505step0 raw9505step0Labels = mixedMoment B raw9505step1 raw9505step1Labels := by
      have ha : raw9505step1 = (fun i j => raw9505step0 (permutation53 i) (permutation4 j)) := by apply Matrix.ext; unfold raw9505step1 raw9505step0; decide +kernel
      have hl : raw9505step1Labels = raw9505step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9505step0 raw9505step0Labels permutation53 permutation4
    mixedMoment B raw9505step1 raw9505step1Labels = mixedMoment B raw9505step2 raw9505step2Labels := by
      have ha : raw9505step2 = -raw9505step1 := by apply Matrix.ext; change ∀ i j, raw9505step2 i j = -(raw9505step1 i j); unfold raw9505step2 raw9505step1; decide +kernel
      have hl : raw9505step2Labels = raw9505step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2133 node2133Labels := by rfl

theorem canonical9506 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9506 raw9506Labels = mixedMoment B node2133 node2133Labels := by
  calc
    mixedMoment B raw9506 raw9506Labels = mixedMoment B raw9506step0 raw9506step0Labels := by
      have hz : ∀ j, raw9506 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9506step0 = (fun i j => raw9506 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9506step0 raw9506; decide +kernel
      have hl : raw9506step0Labels = raw9506Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9506 raw9506Labels permutation265 hz
    mixedMoment B raw9506step0 raw9506step0Labels = mixedMoment B raw9506step1 raw9506step1Labels := by
      have ha : raw9506step1 = (fun i j => raw9506step0 (permutation51 i) (permutation4 j)) := by apply Matrix.ext; unfold raw9506step1 raw9506step0; decide +kernel
      have hl : raw9506step1Labels = raw9506step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9506step0 raw9506step0Labels permutation51 permutation4
    mixedMoment B raw9506step1 raw9506step1Labels = mixedMoment B raw9506step2 raw9506step2Labels := by
      have ha : raw9506step2 = -raw9506step1 := by apply Matrix.ext; change ∀ i j, raw9506step2 i j = -(raw9506step1 i j); unfold raw9506step2 raw9506step1; decide +kernel
      have hl : raw9506step2Labels = raw9506step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2133 node2133Labels := by rfl

theorem canonical9553 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9553 raw9553Labels = mixedMoment B node3886 node3886Labels := by
  calc
    mixedMoment B raw9553 raw9553Labels = mixedMoment B raw9553step0 raw9553step0Labels := by
      have hz : ∀ j, raw9553 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw9553step0 = (fun i j => raw9553 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw9553step0 raw9553; decide +kernel
      have hl : raw9553step0Labels = raw9553Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9553 raw9553Labels permutation434 hz
    mixedMoment B raw9553step0 raw9553step0Labels = mixedMoment B raw9553step1 raw9553step1Labels := by
      have hz : ∀ j, raw9553step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw9553step1 = (fun i j => raw9553step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw9553step1 raw9553step0; decide +kernel
      have hl : raw9553step1Labels = raw9553step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9553step0 raw9553step0Labels permutation80 hz
    mixedMoment B raw9553step1 raw9553step1Labels = mixedMoment B raw9553step2 raw9553step2Labels := by
      have ha : raw9553step2 = (fun i j => raw9553step1 (permutation29 i) (permutation7 j)) := by apply Matrix.ext; unfold raw9553step2 raw9553step1; decide +kernel
      have hl : raw9553step2Labels = raw9553step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9553step1 raw9553step1Labels permutation29 permutation7
    mixedMoment B raw9553step2 raw9553step2Labels = mixedMoment B raw9553step3 raw9553step3Labels := by
      have ha : raw9553step3 = raw9553step2 := by apply Matrix.ext; unfold raw9553step3 raw9553step2; decide +kernel
      have hl : raw9553step2Labels = labelEmbedding1 ∘ raw9553step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9553step2 raw9553step2Labels raw9553step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3886 node3886Labels := by rfl

theorem canonical9554 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9554 raw9554Labels = mixedMoment B node3850 node3850Labels := by
  calc
    mixedMoment B raw9554 raw9554Labels = mixedMoment B raw9554step0 raw9554step0Labels := by
      have hz : ∀ j, raw9554 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw9554step0 = (fun i j => raw9554 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw9554step0 raw9554; decide +kernel
      have hl : raw9554step0Labels = raw9554Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9554 raw9554Labels permutation434 hz
    mixedMoment B raw9554step0 raw9554step0Labels = mixedMoment B raw9554step1 raw9554step1Labels := by
      have ha : raw9554step1 = (fun i j => raw9554step0 (permutation137 i) (permutation7 j)) := by apply Matrix.ext; unfold raw9554step1 raw9554step0; decide +kernel
      have hl : raw9554step1Labels = raw9554step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9554step0 raw9554step0Labels permutation137 permutation7
    mixedMoment B raw9554step1 raw9554step1Labels = mixedMoment B raw9554step2 raw9554step2Labels := by
      have ha : raw9554step2 = raw9554step1 := by apply Matrix.ext; unfold raw9554step2 raw9554step1; decide +kernel
      have hl : raw9554step1Labels = labelEmbedding1 ∘ raw9554step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9554step1 raw9554step1Labels raw9554step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3850 node3850Labels := by rfl

theorem canonical9555 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9555 raw9555Labels = mixedMoment B node3850 node3850Labels := by
  calc
    mixedMoment B raw9555 raw9555Labels = mixedMoment B raw9555step0 raw9555step0Labels := by
      have hz : ∀ j, raw9555 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw9555step0 = (fun i j => raw9555 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw9555step0 raw9555; decide +kernel
      have hl : raw9555step0Labels = raw9555Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9555 raw9555Labels permutation346 hz
    mixedMoment B raw9555step0 raw9555step0Labels = mixedMoment B raw9555step1 raw9555step1Labels := by
      have ha : raw9555step1 = (fun i j => raw9555step0 (permutation137 i) (permutation7 j)) := by apply Matrix.ext; unfold raw9555step1 raw9555step0; decide +kernel
      have hl : raw9555step1Labels = raw9555step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9555step0 raw9555step0Labels permutation137 permutation7
    mixedMoment B raw9555step1 raw9555step1Labels = mixedMoment B raw9555step2 raw9555step2Labels := by
      have ha : raw9555step2 = raw9555step1 := by apply Matrix.ext; unfold raw9555step2 raw9555step1; decide +kernel
      have hl : raw9555step1Labels = labelEmbedding1 ∘ raw9555step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9555step1 raw9555step1Labels raw9555step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3850 node3850Labels := by rfl

theorem canonical9556 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9556 raw9556Labels = mixedMoment B node3888 node3888Labels := by
  calc
    mixedMoment B raw9556 raw9556Labels = mixedMoment B raw9556step0 raw9556step0Labels := by
      have hz : ∀ j, raw9556 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw9556step0 = (fun i j => raw9556 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw9556step0 raw9556; decide +kernel
      have hl : raw9556step0Labels = raw9556Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9556 raw9556Labels permutation434 hz
    mixedMoment B raw9556step0 raw9556step0Labels = mixedMoment B raw9556step1 raw9556step1Labels := by
      have hz : ∀ j, raw9556step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw9556step1 = (fun i j => raw9556step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw9556step1 raw9556step0; decide +kernel
      have hl : raw9556step1Labels = raw9556step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9556step0 raw9556step0Labels permutation80 hz
    mixedMoment B raw9556step1 raw9556step1Labels = mixedMoment B raw9556step2 raw9556step2Labels := by
      have ha : raw9556step2 = (fun i j => raw9556step1 (permutation10 i) (permutation7 j)) := by apply Matrix.ext; unfold raw9556step2 raw9556step1; decide +kernel
      have hl : raw9556step2Labels = raw9556step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9556step1 raw9556step1Labels permutation10 permutation7
    mixedMoment B raw9556step2 raw9556step2Labels = mixedMoment B raw9556step3 raw9556step3Labels := by
      have ha : raw9556step3 = -raw9556step2 := by apply Matrix.ext; change ∀ i j, raw9556step3 i j = -(raw9556step2 i j); unfold raw9556step3 raw9556step2; decide +kernel
      have hl : raw9556step3Labels = raw9556step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw9556step3 raw9556step3Labels = mixedMoment B raw9556step4 raw9556step4Labels := by
      have ha : raw9556step4 = raw9556step3 := by apply Matrix.ext; unfold raw9556step4 raw9556step3; decide +kernel
      have hl : raw9556step3Labels = labelEmbedding1 ∘ raw9556step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9556step3 raw9556step3Labels raw9556step4Labels labelEmbedding1 hl
    _ = mixedMoment B node3888 node3888Labels := by rfl

theorem canonical9557 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9557 raw9557Labels = mixedMoment B node3305 node3305Labels := by
  calc
    mixedMoment B raw9557 raw9557Labels = mixedMoment B raw9557step0 raw9557step0Labels := by
      have hz : ∀ j, raw9557 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw9557step0 = (fun i j => raw9557 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw9557step0 raw9557; decide +kernel
      have hl : raw9557step0Labels = raw9557Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9557 raw9557Labels permutation434 hz
    mixedMoment B raw9557step0 raw9557step0Labels = mixedMoment B raw9557step1 raw9557step1Labels := by
      have hz : ∀ j, raw9557step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw9557step1 = (fun i j => raw9557step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw9557step1 raw9557step0; decide +kernel
      have hl : raw9557step1Labels = raw9557step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9557step0 raw9557step0Labels permutation80 hz
    mixedMoment B raw9557step1 raw9557step1Labels = mixedMoment B raw9557step2 raw9557step2Labels := by
      have ha : raw9557step2 = (fun i j => raw9557step1 (permutation10 i) (permutation7 j)) := by apply Matrix.ext; unfold raw9557step2 raw9557step1; decide +kernel
      have hl : raw9557step2Labels = raw9557step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9557step1 raw9557step1Labels permutation10 permutation7
    mixedMoment B raw9557step2 raw9557step2Labels = mixedMoment B raw9557step3 raw9557step3Labels := by
      have ha : raw9557step3 = -raw9557step2 := by apply Matrix.ext; change ∀ i j, raw9557step3 i j = -(raw9557step2 i j); unfold raw9557step3 raw9557step2; decide +kernel
      have hl : raw9557step3Labels = raw9557step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw9557step3 raw9557step3Labels = mixedMoment B raw9557step4 raw9557step4Labels := by
      have ha : raw9557step4 = raw9557step3 := by apply Matrix.ext; unfold raw9557step4 raw9557step3; decide +kernel
      have hl : raw9557step3Labels = labelEmbedding1 ∘ raw9557step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9557step3 raw9557step3Labels raw9557step4Labels labelEmbedding1 hl
    _ = mixedMoment B node3305 node3305Labels := by rfl

theorem canonical9558 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9558 raw9558Labels = mixedMoment B node3564 node3564Labels := by
  calc
    mixedMoment B raw9558 raw9558Labels = mixedMoment B raw9558step0 raw9558step0Labels := by
      have hz : ∀ j, raw9558 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw9558step0 = (fun i j => raw9558 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw9558step0 raw9558; decide +kernel
      have hl : raw9558step0Labels = raw9558Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9558 raw9558Labels permutation434 hz
    mixedMoment B raw9558step0 raw9558step0Labels = mixedMoment B raw9558step1 raw9558step1Labels := by
      have ha : raw9558step1 = (fun i j => raw9558step0 (permutation46 i) (permutation7 j)) := by apply Matrix.ext; unfold raw9558step1 raw9558step0; decide +kernel
      have hl : raw9558step1Labels = raw9558step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9558step0 raw9558step0Labels permutation46 permutation7
    mixedMoment B raw9558step1 raw9558step1Labels = mixedMoment B raw9558step2 raw9558step2Labels := by
      have ha : raw9558step2 = -raw9558step1 := by apply Matrix.ext; change ∀ i j, raw9558step2 i j = -(raw9558step1 i j); unfold raw9558step2 raw9558step1; decide +kernel
      have hl : raw9558step2Labels = raw9558step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw9558step2 raw9558step2Labels = mixedMoment B raw9558step3 raw9558step3Labels := by
      have ha : raw9558step3 = raw9558step2 := by apply Matrix.ext; unfold raw9558step3 raw9558step2; decide +kernel
      have hl : raw9558step2Labels = labelEmbedding1 ∘ raw9558step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9558step2 raw9558step2Labels raw9558step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3564 node3564Labels := by rfl

theorem canonical9559 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9559 raw9559Labels = mixedMoment B node3564 node3564Labels := by
  calc
    mixedMoment B raw9559 raw9559Labels = mixedMoment B raw9559step0 raw9559step0Labels := by
      have hz : ∀ j, raw9559 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw9559step0 = (fun i j => raw9559 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw9559step0 raw9559; decide +kernel
      have hl : raw9559step0Labels = raw9559Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9559 raw9559Labels permutation346 hz
    mixedMoment B raw9559step0 raw9559step0Labels = mixedMoment B raw9559step1 raw9559step1Labels := by
      have ha : raw9559step1 = (fun i j => raw9559step0 (permutation46 i) (permutation7 j)) := by apply Matrix.ext; unfold raw9559step1 raw9559step0; decide +kernel
      have hl : raw9559step1Labels = raw9559step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9559step0 raw9559step0Labels permutation46 permutation7
    mixedMoment B raw9559step1 raw9559step1Labels = mixedMoment B raw9559step2 raw9559step2Labels := by
      have ha : raw9559step2 = -raw9559step1 := by apply Matrix.ext; change ∀ i j, raw9559step2 i j = -(raw9559step1 i j); unfold raw9559step2 raw9559step1; decide +kernel
      have hl : raw9559step2Labels = raw9559step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw9559step2 raw9559step2Labels = mixedMoment B raw9559step3 raw9559step3Labels := by
      have ha : raw9559step3 = raw9559step2 := by apply Matrix.ext; unfold raw9559step3 raw9559step2; decide +kernel
      have hl : raw9559step2Labels = labelEmbedding1 ∘ raw9559step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9559step2 raw9559step2Labels raw9559step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3564 node3564Labels := by rfl

theorem canonical9560 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9560 raw9560Labels = mixedMoment B node3583 node3583Labels := by
  calc
    mixedMoment B raw9560 raw9560Labels = mixedMoment B raw9560step0 raw9560step0Labels := by
      have hz : ∀ j, raw9560 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw9560step0 = (fun i j => raw9560 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw9560step0 raw9560; decide +kernel
      have hl : raw9560step0Labels = raw9560Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9560 raw9560Labels permutation434 hz
    mixedMoment B raw9560step0 raw9560step0Labels = mixedMoment B raw9560step1 raw9560step1Labels := by
      have hz : ∀ j, raw9560step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw9560step1 = (fun i j => raw9560step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw9560step1 raw9560step0; decide +kernel
      have hl : raw9560step1Labels = raw9560step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9560step0 raw9560step0Labels permutation80 hz
    mixedMoment B raw9560step1 raw9560step1Labels = mixedMoment B raw9560step2 raw9560step2Labels := by
      have ha : raw9560step2 = (fun i j => raw9560step1 (permutation10 i) (permutation7 j)) := by apply Matrix.ext; unfold raw9560step2 raw9560step1; decide +kernel
      have hl : raw9560step2Labels = raw9560step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9560step1 raw9560step1Labels permutation10 permutation7
    mixedMoment B raw9560step2 raw9560step2Labels = mixedMoment B raw9560step3 raw9560step3Labels := by
      have ha : raw9560step3 = -raw9560step2 := by apply Matrix.ext; change ∀ i j, raw9560step3 i j = -(raw9560step2 i j); unfold raw9560step3 raw9560step2; decide +kernel
      have hl : raw9560step3Labels = raw9560step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw9560step3 raw9560step3Labels = mixedMoment B raw9560step4 raw9560step4Labels := by
      have ha : raw9560step4 = raw9560step3 := by apply Matrix.ext; unfold raw9560step4 raw9560step3; decide +kernel
      have hl : raw9560step3Labels = labelEmbedding1 ∘ raw9560step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9560step3 raw9560step3Labels raw9560step4Labels labelEmbedding1 hl
    _ = mixedMoment B node3583 node3583Labels := by rfl

theorem canonical9561 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9561 raw9561Labels = mixedMoment B node3296 node3296Labels := by
  calc
    mixedMoment B raw9561 raw9561Labels = mixedMoment B raw9561step0 raw9561step0Labels := by
      have hz : ∀ j, raw9561 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw9561step0 = (fun i j => raw9561 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw9561step0 raw9561; decide +kernel
      have hl : raw9561step0Labels = raw9561Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9561 raw9561Labels permutation434 hz
    mixedMoment B raw9561step0 raw9561step0Labels = mixedMoment B raw9561step1 raw9561step1Labels := by
      have ha : raw9561step1 = (fun i j => raw9561step0 (permutation36 i) (permutation5 j)) := by apply Matrix.ext; unfold raw9561step1 raw9561step0; decide +kernel
      have hl : raw9561step1Labels = raw9561step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9561step0 raw9561step0Labels permutation36 permutation5
    mixedMoment B raw9561step1 raw9561step1Labels = mixedMoment B raw9561step2 raw9561step2Labels := by
      have ha : raw9561step2 = -raw9561step1 := by apply Matrix.ext; change ∀ i j, raw9561step2 i j = -(raw9561step1 i j); unfold raw9561step2 raw9561step1; decide +kernel
      have hl : raw9561step2Labels = raw9561step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw9561step2 raw9561step2Labels = mixedMoment B raw9561step3 raw9561step3Labels := by
      have ha : raw9561step3 = raw9561step2 := by apply Matrix.ext; unfold raw9561step3 raw9561step2; decide +kernel
      have hl : raw9561step2Labels = labelEmbedding1 ∘ raw9561step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9561step2 raw9561step2Labels raw9561step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3296 node3296Labels := by rfl

theorem canonical9562 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9562 raw9562Labels = mixedMoment B node3570 node3570Labels := by
  calc
    mixedMoment B raw9562 raw9562Labels = mixedMoment B raw9562step0 raw9562step0Labels := by
      have hz : ∀ j, raw9562 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw9562step0 = (fun i j => raw9562 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw9562step0 raw9562; decide +kernel
      have hl : raw9562step0Labels = raw9562Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9562 raw9562Labels permutation434 hz
    mixedMoment B raw9562step0 raw9562step0Labels = mixedMoment B raw9562step1 raw9562step1Labels := by
      have ha : raw9562step1 = (fun i j => raw9562step0 (permutation46 i) (permutation7 j)) := by apply Matrix.ext; unfold raw9562step1 raw9562step0; decide +kernel
      have hl : raw9562step1Labels = raw9562step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9562step0 raw9562step0Labels permutation46 permutation7
    mixedMoment B raw9562step1 raw9562step1Labels = mixedMoment B raw9562step2 raw9562step2Labels := by
      have ha : raw9562step2 = -raw9562step1 := by apply Matrix.ext; change ∀ i j, raw9562step2 i j = -(raw9562step1 i j); unfold raw9562step2 raw9562step1; decide +kernel
      have hl : raw9562step2Labels = raw9562step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw9562step2 raw9562step2Labels = mixedMoment B raw9562step3 raw9562step3Labels := by
      have ha : raw9562step3 = raw9562step2 := by apply Matrix.ext; unfold raw9562step3 raw9562step2; decide +kernel
      have hl : raw9562step2Labels = labelEmbedding1 ∘ raw9562step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9562step2 raw9562step2Labels raw9562step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3570 node3570Labels := by rfl

theorem canonical9563 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9563 raw9563Labels = mixedMoment B node3557 node3557Labels := by
  calc
    mixedMoment B raw9563 raw9563Labels = mixedMoment B raw9563step0 raw9563step0Labels := by
      have ha : raw9563step0 = (fun i j => raw9563 (permutation236 i) (permutation7 j)) := by apply Matrix.ext; unfold raw9563step0 raw9563; decide +kernel
      have hl : raw9563step0Labels = raw9563Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9563 raw9563Labels permutation236 permutation7
    mixedMoment B raw9563step0 raw9563step0Labels = mixedMoment B raw9563step1 raw9563step1Labels := by
      have ha : raw9563step1 = -raw9563step0 := by apply Matrix.ext; change ∀ i j, raw9563step1 i j = -(raw9563step0 i j); unfold raw9563step1 raw9563step0; decide +kernel
      have hl : raw9563step1Labels = raw9563step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw9563step1 raw9563step1Labels = mixedMoment B raw9563step2 raw9563step2Labels := by
      have ha : raw9563step2 = raw9563step1 := by apply Matrix.ext; unfold raw9563step2 raw9563step1; decide +kernel
      have hl : raw9563step1Labels = labelEmbedding1 ∘ raw9563step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9563step1 raw9563step1Labels raw9563step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3557 node3557Labels := by rfl

theorem canonical9564 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9564 raw9564Labels = mixedMoment B node3572 node3572Labels := by
  calc
    mixedMoment B raw9564 raw9564Labels = mixedMoment B raw9564step0 raw9564step0Labels := by
      have hz : ∀ j, raw9564 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw9564step0 = (fun i j => raw9564 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw9564step0 raw9564; decide +kernel
      have hl : raw9564step0Labels = raw9564Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9564 raw9564Labels permutation434 hz
    mixedMoment B raw9564step0 raw9564step0Labels = mixedMoment B raw9564step1 raw9564step1Labels := by
      have ha : raw9564step1 = (fun i j => raw9564step0 (permutation46 i) (permutation7 j)) := by apply Matrix.ext; unfold raw9564step1 raw9564step0; decide +kernel
      have hl : raw9564step1Labels = raw9564step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9564step0 raw9564step0Labels permutation46 permutation7
    mixedMoment B raw9564step1 raw9564step1Labels = mixedMoment B raw9564step2 raw9564step2Labels := by
      have ha : raw9564step2 = -raw9564step1 := by apply Matrix.ext; change ∀ i j, raw9564step2 i j = -(raw9564step1 i j); unfold raw9564step2 raw9564step1; decide +kernel
      have hl : raw9564step2Labels = raw9564step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw9564step2 raw9564step2Labels = mixedMoment B raw9564step3 raw9564step3Labels := by
      have ha : raw9564step3 = raw9564step2 := by apply Matrix.ext; unfold raw9564step3 raw9564step2; decide +kernel
      have hl : raw9564step2Labels = labelEmbedding1 ∘ raw9564step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9564step2 raw9564step2Labels raw9564step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3572 node3572Labels := by rfl

theorem canonical9565 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9565 raw9565Labels = mixedMoment B node3296 node3296Labels := by
  calc
    mixedMoment B raw9565 raw9565Labels = mixedMoment B raw9565step0 raw9565step0Labels := by
      have hz : ∀ j, raw9565 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw9565step0 = (fun i j => raw9565 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw9565step0 raw9565; decide +kernel
      have hl : raw9565step0Labels = raw9565Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9565 raw9565Labels permutation346 hz
    mixedMoment B raw9565step0 raw9565step0Labels = mixedMoment B raw9565step1 raw9565step1Labels := by
      have ha : raw9565step1 = (fun i j => raw9565step0 (permutation36 i) (permutation5 j)) := by apply Matrix.ext; unfold raw9565step1 raw9565step0; decide +kernel
      have hl : raw9565step1Labels = raw9565step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9565step0 raw9565step0Labels permutation36 permutation5
    mixedMoment B raw9565step1 raw9565step1Labels = mixedMoment B raw9565step2 raw9565step2Labels := by
      have ha : raw9565step2 = -raw9565step1 := by apply Matrix.ext; change ∀ i j, raw9565step2 i j = -(raw9565step1 i j); unfold raw9565step2 raw9565step1; decide +kernel
      have hl : raw9565step2Labels = raw9565step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw9565step2 raw9565step2Labels = mixedMoment B raw9565step3 raw9565step3Labels := by
      have ha : raw9565step3 = raw9565step2 := by apply Matrix.ext; unfold raw9565step3 raw9565step2; decide +kernel
      have hl : raw9565step2Labels = labelEmbedding1 ∘ raw9565step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9565step2 raw9565step2Labels raw9565step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3296 node3296Labels := by rfl

theorem canonical9566 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9566 raw9566Labels = mixedMoment B node3570 node3570Labels := by
  calc
    mixedMoment B raw9566 raw9566Labels = mixedMoment B raw9566step0 raw9566step0Labels := by
      have hz : ∀ j, raw9566 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw9566step0 = (fun i j => raw9566 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw9566step0 raw9566; decide +kernel
      have hl : raw9566step0Labels = raw9566Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9566 raw9566Labels permutation346 hz
    mixedMoment B raw9566step0 raw9566step0Labels = mixedMoment B raw9566step1 raw9566step1Labels := by
      have ha : raw9566step1 = (fun i j => raw9566step0 (permutation46 i) (permutation7 j)) := by apply Matrix.ext; unfold raw9566step1 raw9566step0; decide +kernel
      have hl : raw9566step1Labels = raw9566step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9566step0 raw9566step0Labels permutation46 permutation7
    mixedMoment B raw9566step1 raw9566step1Labels = mixedMoment B raw9566step2 raw9566step2Labels := by
      have ha : raw9566step2 = -raw9566step1 := by apply Matrix.ext; change ∀ i j, raw9566step2 i j = -(raw9566step1 i j); unfold raw9566step2 raw9566step1; decide +kernel
      have hl : raw9566step2Labels = raw9566step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw9566step2 raw9566step2Labels = mixedMoment B raw9566step3 raw9566step3Labels := by
      have ha : raw9566step3 = raw9566step2 := by apply Matrix.ext; unfold raw9566step3 raw9566step2; decide +kernel
      have hl : raw9566step2Labels = labelEmbedding1 ∘ raw9566step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9566step2 raw9566step2Labels raw9566step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3570 node3570Labels := by rfl

theorem canonical9567 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9567 raw9567Labels = mixedMoment B node3557 node3557Labels := by
  calc
    mixedMoment B raw9567 raw9567Labels = mixedMoment B raw9567step0 raw9567step0Labels := by
      have ha : raw9567step0 = (fun i j => raw9567 (permutation232 i) (permutation7 j)) := by apply Matrix.ext; unfold raw9567step0 raw9567; decide +kernel
      have hl : raw9567step0Labels = raw9567Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9567 raw9567Labels permutation232 permutation7
    mixedMoment B raw9567step0 raw9567step0Labels = mixedMoment B raw9567step1 raw9567step1Labels := by
      have ha : raw9567step1 = -raw9567step0 := by apply Matrix.ext; change ∀ i j, raw9567step1 i j = -(raw9567step0 i j); unfold raw9567step1 raw9567step0; decide +kernel
      have hl : raw9567step1Labels = raw9567step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw9567step1 raw9567step1Labels = mixedMoment B raw9567step2 raw9567step2Labels := by
      have ha : raw9567step2 = raw9567step1 := by apply Matrix.ext; unfold raw9567step2 raw9567step1; decide +kernel
      have hl : raw9567step1Labels = labelEmbedding1 ∘ raw9567step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9567step1 raw9567step1Labels raw9567step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3557 node3557Labels := by rfl

theorem canonical9568 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9568 raw9568Labels = mixedMoment B node3572 node3572Labels := by
  calc
    mixedMoment B raw9568 raw9568Labels = mixedMoment B raw9568step0 raw9568step0Labels := by
      have hz : ∀ j, raw9568 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw9568step0 = (fun i j => raw9568 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw9568step0 raw9568; decide +kernel
      have hl : raw9568step0Labels = raw9568Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9568 raw9568Labels permutation346 hz
    mixedMoment B raw9568step0 raw9568step0Labels = mixedMoment B raw9568step1 raw9568step1Labels := by
      have ha : raw9568step1 = (fun i j => raw9568step0 (permutation46 i) (permutation7 j)) := by apply Matrix.ext; unfold raw9568step1 raw9568step0; decide +kernel
      have hl : raw9568step1Labels = raw9568step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9568step0 raw9568step0Labels permutation46 permutation7
    mixedMoment B raw9568step1 raw9568step1Labels = mixedMoment B raw9568step2 raw9568step2Labels := by
      have ha : raw9568step2 = -raw9568step1 := by apply Matrix.ext; change ∀ i j, raw9568step2 i j = -(raw9568step1 i j); unfold raw9568step2 raw9568step1; decide +kernel
      have hl : raw9568step2Labels = raw9568step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw9568step2 raw9568step2Labels = mixedMoment B raw9568step3 raw9568step3Labels := by
      have ha : raw9568step3 = raw9568step2 := by apply Matrix.ext; unfold raw9568step3 raw9568step2; decide +kernel
      have hl : raw9568step2Labels = labelEmbedding1 ∘ raw9568step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9568step2 raw9568step2Labels raw9568step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3572 node3572Labels := by rfl

theorem canonical9569 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9569 raw9569Labels = mixedMoment B node2683 node2683Labels := by
  calc
    mixedMoment B raw9569 raw9569Labels = mixedMoment B raw9569step0 raw9569step0Labels := by
      have hz : ∀ j, raw9569 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw9569step0 = (fun i j => raw9569 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw9569step0 raw9569; decide +kernel
      have hl : raw9569step0Labels = raw9569Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9569 raw9569Labels permutation434 hz
    mixedMoment B raw9569step0 raw9569step0Labels = mixedMoment B raw9569step1 raw9569step1Labels := by
      have hz : ∀ j, raw9569step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw9569step1 = (fun i j => raw9569step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw9569step1 raw9569step0; decide +kernel
      have hl : raw9569step1Labels = raw9569step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9569step0 raw9569step0Labels permutation80 hz
    mixedMoment B raw9569step1 raw9569step1Labels = mixedMoment B raw9569step2 raw9569step2Labels := by
      have ha : raw9569step2 = (fun i j => raw9569step1 (permutation25 i) (permutation5 j)) := by apply Matrix.ext; unfold raw9569step2 raw9569step1; decide +kernel
      have hl : raw9569step2Labels = raw9569step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9569step1 raw9569step1Labels permutation25 permutation5
    mixedMoment B raw9569step2 raw9569step2Labels = mixedMoment B raw9569step3 raw9569step3Labels := by
      have ha : raw9569step3 = raw9569step2 := by apply Matrix.ext; unfold raw9569step3 raw9569step2; decide +kernel
      have hl : raw9569step2Labels = labelEmbedding1 ∘ raw9569step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9569step2 raw9569step2Labels raw9569step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2683 node2683Labels := by rfl

theorem canonical9570 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9570 raw9570Labels = mixedMoment B node2687 node2687Labels := by
  calc
    mixedMoment B raw9570 raw9570Labels = mixedMoment B raw9570step0 raw9570step0Labels := by
      have hz : ∀ j, raw9570 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw9570step0 = (fun i j => raw9570 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw9570step0 raw9570; decide +kernel
      have hl : raw9570step0Labels = raw9570Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9570 raw9570Labels permutation434 hz
    mixedMoment B raw9570step0 raw9570step0Labels = mixedMoment B raw9570step1 raw9570step1Labels := by
      have hz : ∀ j, raw9570step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw9570step1 = (fun i j => raw9570step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw9570step1 raw9570step0; decide +kernel
      have hl : raw9570step1Labels = raw9570step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9570step0 raw9570step0Labels permutation80 hz
    mixedMoment B raw9570step1 raw9570step1Labels = mixedMoment B raw9570step2 raw9570step2Labels := by
      have ha : raw9570step2 = (fun i j => raw9570step1 (permutation24 i) (permutation5 j)) := by apply Matrix.ext; unfold raw9570step2 raw9570step1; decide +kernel
      have hl : raw9570step2Labels = raw9570step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9570step1 raw9570step1Labels permutation24 permutation5
    mixedMoment B raw9570step2 raw9570step2Labels = mixedMoment B raw9570step3 raw9570step3Labels := by
      have ha : raw9570step3 = raw9570step2 := by apply Matrix.ext; unfold raw9570step3 raw9570step2; decide +kernel
      have hl : raw9570step2Labels = labelEmbedding1 ∘ raw9570step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9570step2 raw9570step2Labels raw9570step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2687 node2687Labels := by rfl

theorem canonical9571 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9571 raw9571Labels = mixedMoment B node2681 node2681Labels := by
  calc
    mixedMoment B raw9571 raw9571Labels = mixedMoment B raw9571step0 raw9571step0Labels := by
      have hz : ∀ j, raw9571 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw9571step0 = (fun i j => raw9571 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw9571step0 raw9571; decide +kernel
      have hl : raw9571step0Labels = raw9571Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9571 raw9571Labels permutation434 hz
    mixedMoment B raw9571step0 raw9571step0Labels = mixedMoment B raw9571step1 raw9571step1Labels := by
      have ha : raw9571step1 = (fun i j => raw9571step0 (permutation125 i) (permutation5 j)) := by apply Matrix.ext; unfold raw9571step1 raw9571step0; decide +kernel
      have hl : raw9571step1Labels = raw9571step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9571step0 raw9571step0Labels permutation125 permutation5
    mixedMoment B raw9571step1 raw9571step1Labels = mixedMoment B raw9571step2 raw9571step2Labels := by
      have ha : raw9571step2 = raw9571step1 := by apply Matrix.ext; unfold raw9571step2 raw9571step1; decide +kernel
      have hl : raw9571step1Labels = labelEmbedding1 ∘ raw9571step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9571step1 raw9571step1Labels raw9571step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2681 node2681Labels := by rfl

theorem canonical9572 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9572 raw9572Labels = mixedMoment B node2681 node2681Labels := by
  calc
    mixedMoment B raw9572 raw9572Labels = mixedMoment B raw9572step0 raw9572step0Labels := by
      have hz : ∀ j, raw9572 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw9572step0 = (fun i j => raw9572 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw9572step0 raw9572; decide +kernel
      have hl : raw9572step0Labels = raw9572Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9572 raw9572Labels permutation346 hz
    mixedMoment B raw9572step0 raw9572step0Labels = mixedMoment B raw9572step1 raw9572step1Labels := by
      have ha : raw9572step1 = (fun i j => raw9572step0 (permutation125 i) (permutation5 j)) := by apply Matrix.ext; unfold raw9572step1 raw9572step0; decide +kernel
      have hl : raw9572step1Labels = raw9572step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9572step0 raw9572step0Labels permutation125 permutation5
    mixedMoment B raw9572step1 raw9572step1Labels = mixedMoment B raw9572step2 raw9572step2Labels := by
      have ha : raw9572step2 = raw9572step1 := by apply Matrix.ext; unfold raw9572step2 raw9572step1; decide +kernel
      have hl : raw9572step1Labels = labelEmbedding1 ∘ raw9572step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9572step1 raw9572step1Labels raw9572step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2681 node2681Labels := by rfl

theorem canonical9573 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9573 raw9573Labels = mixedMoment B node2781 node2781Labels := by
  calc
    mixedMoment B raw9573 raw9573Labels = mixedMoment B raw9573step0 raw9573step0Labels := by
      have hz : ∀ j, raw9573 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw9573step0 = (fun i j => raw9573 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw9573step0 raw9573; decide +kernel
      have hl : raw9573step0Labels = raw9573Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9573 raw9573Labels permutation434 hz
    mixedMoment B raw9573step0 raw9573step0Labels = mixedMoment B raw9573step1 raw9573step1Labels := by
      have hz : ∀ j, raw9573step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw9573step1 = (fun i j => raw9573step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw9573step1 raw9573step0; decide +kernel
      have hl : raw9573step1Labels = raw9573step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9573step0 raw9573step0Labels permutation80 hz
    mixedMoment B raw9573step1 raw9573step1Labels = mixedMoment B raw9573step2 raw9573step2Labels := by
      have ha : raw9573step2 = (fun i j => raw9573step1 (permutation25 i) (permutation5 j)) := by apply Matrix.ext; unfold raw9573step2 raw9573step1; decide +kernel
      have hl : raw9573step2Labels = raw9573step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9573step1 raw9573step1Labels permutation25 permutation5
    mixedMoment B raw9573step2 raw9573step2Labels = mixedMoment B raw9573step3 raw9573step3Labels := by
      have ha : raw9573step3 = raw9573step2 := by apply Matrix.ext; unfold raw9573step3 raw9573step2; decide +kernel
      have hl : raw9573step2Labels = labelEmbedding1 ∘ raw9573step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9573step2 raw9573step2Labels raw9573step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2781 node2781Labels := by rfl

theorem canonical9574 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9574 raw9574Labels = mixedMoment B node3545 node3545Labels := by
  calc
    mixedMoment B raw9574 raw9574Labels = mixedMoment B raw9574step0 raw9574step0Labels := by
      have hz : ∀ j, raw9574 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw9574step0 = (fun i j => raw9574 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw9574step0 raw9574; decide +kernel
      have hl : raw9574step0Labels = raw9574Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9574 raw9574Labels permutation434 hz
    mixedMoment B raw9574step0 raw9574step0Labels = mixedMoment B raw9574step1 raw9574step1Labels := by
      have hz : ∀ j, raw9574step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw9574step1 = (fun i j => raw9574step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw9574step1 raw9574step0; decide +kernel
      have hl : raw9574step1Labels = raw9574step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9574step0 raw9574step0Labels permutation80 hz
    mixedMoment B raw9574step1 raw9574step1Labels = mixedMoment B raw9574step2 raw9574step2Labels := by
      have ha : raw9574step2 = (fun i j => raw9574step1 (permutation29 i) (permutation7 j)) := by apply Matrix.ext; unfold raw9574step2 raw9574step1; decide +kernel
      have hl : raw9574step2Labels = raw9574step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9574step1 raw9574step1Labels permutation29 permutation7
    mixedMoment B raw9574step2 raw9574step2Labels = mixedMoment B raw9574step3 raw9574step3Labels := by
      have ha : raw9574step3 = raw9574step2 := by apply Matrix.ext; unfold raw9574step3 raw9574step2; decide +kernel
      have hl : raw9574step2Labels = labelEmbedding1 ∘ raw9574step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9574step2 raw9574step2Labels raw9574step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3545 node3545Labels := by rfl

theorem canonical9575 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9575 raw9575Labels = mixedMoment B node2765 node2765Labels := by
  calc
    mixedMoment B raw9575 raw9575Labels = mixedMoment B raw9575step0 raw9575step0Labels := by
      have hz : ∀ j, raw9575 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw9575step0 = (fun i j => raw9575 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw9575step0 raw9575; decide +kernel
      have hl : raw9575step0Labels = raw9575Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9575 raw9575Labels permutation434 hz
    mixedMoment B raw9575step0 raw9575step0Labels = mixedMoment B raw9575step1 raw9575step1Labels := by
      have hz : ∀ j, raw9575step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw9575step1 = (fun i j => raw9575step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw9575step1 raw9575step0; decide +kernel
      have hl : raw9575step1Labels = raw9575step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9575step0 raw9575step0Labels permutation80 hz
    _ = mixedMoment B node2765 node2765Labels := by rfl

theorem canonical9576 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9576 raw9576Labels = mixedMoment B node3886 node3886Labels := by
  calc
    mixedMoment B raw9576 raw9576Labels = mixedMoment B raw9576step0 raw9576step0Labels := by
      have hz : ∀ j, raw9576 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw9576step0 = (fun i j => raw9576 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw9576step0 raw9576; decide +kernel
      have hl : raw9576step0Labels = raw9576Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9576 raw9576Labels permutation434 hz
    mixedMoment B raw9576step0 raw9576step0Labels = mixedMoment B raw9576step1 raw9576step1Labels := by
      have hz : ∀ j, raw9576step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw9576step1 = (fun i j => raw9576step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw9576step1 raw9576step0; decide +kernel
      have hl : raw9576step1Labels = raw9576step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9576step0 raw9576step0Labels permutation80 hz
    _ = mixedMoment B node3886 node3886Labels := by rfl

theorem canonical9577 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9577 raw9577Labels = mixedMoment B node3850 node3850Labels := by
  calc
    mixedMoment B raw9577 raw9577Labels = mixedMoment B raw9577step0 raw9577step0Labels := by
      have hz : ∀ j, raw9577 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw9577step0 = (fun i j => raw9577 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw9577step0 raw9577; decide +kernel
      have hl : raw9577step0Labels = raw9577Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9577 raw9577Labels permutation434 hz
    mixedMoment B raw9577step0 raw9577step0Labels = mixedMoment B raw9577step1 raw9577step1Labels := by
      have ha : raw9577step1 = (fun i j => raw9577step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9577step1 raw9577step0; decide +kernel
      have hl : raw9577step1Labels = raw9577step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9577step0 raw9577step0Labels permutation38 permutation2
    _ = mixedMoment B node3850 node3850Labels := by rfl

theorem canonical9578 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9578 raw9578Labels = mixedMoment B node3850 node3850Labels := by
  calc
    mixedMoment B raw9578 raw9578Labels = mixedMoment B raw9578step0 raw9578step0Labels := by
      have hz : ∀ j, raw9578 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw9578step0 = (fun i j => raw9578 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw9578step0 raw9578; decide +kernel
      have hl : raw9578step0Labels = raw9578Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9578 raw9578Labels permutation346 hz
    mixedMoment B raw9578step0 raw9578step0Labels = mixedMoment B raw9578step1 raw9578step1Labels := by
      have ha : raw9578step1 = (fun i j => raw9578step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9578step1 raw9578step0; decide +kernel
      have hl : raw9578step1Labels = raw9578step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9578step0 raw9578step0Labels permutation38 permutation2
    _ = mixedMoment B node3850 node3850Labels := by rfl

theorem canonical9579 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9579 raw9579Labels = mixedMoment B node3913 node3913Labels := by
  calc
    mixedMoment B raw9579 raw9579Labels = mixedMoment B raw9579step0 raw9579step0Labels := by
      have hz : ∀ j, raw9579 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw9579step0 = (fun i j => raw9579 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw9579step0 raw9579; decide +kernel
      have hl : raw9579step0Labels = raw9579Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9579 raw9579Labels permutation434 hz
    mixedMoment B raw9579step0 raw9579step0Labels = mixedMoment B raw9579step1 raw9579step1Labels := by
      have hz : ∀ j, raw9579step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw9579step1 = (fun i j => raw9579step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw9579step1 raw9579step0; decide +kernel
      have hl : raw9579step1Labels = raw9579step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9579step0 raw9579step0Labels permutation80 hz
    _ = mixedMoment B node3913 node3913Labels := by rfl

theorem canonical9580 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9580 raw9580Labels = mixedMoment B node1294 node1294Labels := by
  calc
    mixedMoment B raw9580 raw9580Labels = mixedMoment B raw9580step0 raw9580step0Labels := by
      have hz : ∀ j, raw9580 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw9580step0 = (fun i j => raw9580 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw9580step0 raw9580; decide +kernel
      have hl : raw9580step0Labels = raw9580Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9580 raw9580Labels permutation434 hz
    mixedMoment B raw9580step0 raw9580step0Labels = mixedMoment B raw9580step1 raw9580step1Labels := by
      have hz : ∀ j, raw9580step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw9580step1 = (fun i j => raw9580step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw9580step1 raw9580step0; decide +kernel
      have hl : raw9580step1Labels = raw9580step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9580step0 raw9580step0Labels permutation80 hz
    mixedMoment B raw9580step1 raw9580step1Labels = mixedMoment B raw9580step2 raw9580step2Labels := by
      have ha : raw9580step2 = (fun i j => raw9580step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9580step2 raw9580step1; decide +kernel
      have hl : raw9580step2Labels = raw9580step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9580step1 raw9580step1Labels permutation10 permutation2
    _ = mixedMoment B node1294 node1294Labels := by rfl

theorem canonical9581 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9581 raw9581Labels = mixedMoment B node1261 node1261Labels := by
  calc
    mixedMoment B raw9581 raw9581Labels = mixedMoment B raw9581step0 raw9581step0Labels := by
      have hz : ∀ j, raw9581 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw9581step0 = (fun i j => raw9581 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw9581step0 raw9581; decide +kernel
      have hl : raw9581step0Labels = raw9581Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9581 raw9581Labels permutation434 hz
    mixedMoment B raw9581step0 raw9581step0Labels = mixedMoment B raw9581step1 raw9581step1Labels := by
      have ha : raw9581step1 = (fun i j => raw9581step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9581step1 raw9581step0; decide +kernel
      have hl : raw9581step1Labels = raw9581step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9581step0 raw9581step0Labels permutation34 permutation2
    _ = mixedMoment B node1261 node1261Labels := by rfl

theorem canonical9582 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9582 raw9582Labels = mixedMoment B node1261 node1261Labels := by
  calc
    mixedMoment B raw9582 raw9582Labels = mixedMoment B raw9582step0 raw9582step0Labels := by
      have hz : ∀ j, raw9582 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw9582step0 = (fun i j => raw9582 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw9582step0 raw9582; decide +kernel
      have hl : raw9582step0Labels = raw9582Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9582 raw9582Labels permutation346 hz
    mixedMoment B raw9582step0 raw9582step0Labels = mixedMoment B raw9582step1 raw9582step1Labels := by
      have ha : raw9582step1 = (fun i j => raw9582step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9582step1 raw9582step0; decide +kernel
      have hl : raw9582step1Labels = raw9582step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9582step0 raw9582step0Labels permutation34 permutation2
    _ = mixedMoment B node1261 node1261Labels := by rfl

theorem canonical9583 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9583 raw9583Labels = mixedMoment B node1273 node1273Labels := by
  calc
    mixedMoment B raw9583 raw9583Labels = mixedMoment B raw9583step0 raw9583step0Labels := by
      have hz : ∀ j, raw9583 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw9583step0 = (fun i j => raw9583 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw9583step0 raw9583; decide +kernel
      have hl : raw9583step0Labels = raw9583Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9583 raw9583Labels permutation434 hz
    mixedMoment B raw9583step0 raw9583step0Labels = mixedMoment B raw9583step1 raw9583step1Labels := by
      have hz : ∀ j, raw9583step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw9583step1 = (fun i j => raw9583step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw9583step1 raw9583step0; decide +kernel
      have hl : raw9583step1Labels = raw9583step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9583step0 raw9583step0Labels permutation80 hz
    _ = mixedMoment B node1273 node1273Labels := by rfl

theorem canonical9584 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9584 raw9584Labels = mixedMoment B node2590 node2590Labels := by
  calc
    mixedMoment B raw9584 raw9584Labels = mixedMoment B raw9584step0 raw9584step0Labels := by
      have hz : ∀ j, raw9584 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw9584step0 = (fun i j => raw9584 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw9584step0 raw9584; decide +kernel
      have hl : raw9584step0Labels = raw9584Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9584 raw9584Labels permutation434 hz
    mixedMoment B raw9584step0 raw9584step0Labels = mixedMoment B raw9584step1 raw9584step1Labels := by
      have ha : raw9584step1 = (fun i j => raw9584step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9584step1 raw9584step0; decide +kernel
      have hl : raw9584step1Labels = raw9584step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9584step0 raw9584step0Labels permutation40 permutation2
    _ = mixedMoment B node2590 node2590Labels := by rfl

theorem canonical9585 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9585 raw9585Labels = mixedMoment B node2590 node2590Labels := by
  calc
    mixedMoment B raw9585 raw9585Labels = mixedMoment B raw9585step0 raw9585step0Labels := by
      have hz : ∀ j, raw9585 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw9585step0 = (fun i j => raw9585 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw9585step0 raw9585; decide +kernel
      have hl : raw9585step0Labels = raw9585Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9585 raw9585Labels permutation346 hz
    mixedMoment B raw9585step0 raw9585step0Labels = mixedMoment B raw9585step1 raw9585step1Labels := by
      have ha : raw9585step1 = (fun i j => raw9585step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9585step1 raw9585step0; decide +kernel
      have hl : raw9585step1Labels = raw9585step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9585step0 raw9585step0Labels permutation40 permutation2
    _ = mixedMoment B node2590 node2590Labels := by rfl

theorem canonical9586 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9586 raw9586Labels = mixedMoment B node2782 node2782Labels := by
  calc
    mixedMoment B raw9586 raw9586Labels = mixedMoment B raw9586step0 raw9586step0Labels := by
      have hz : ∀ j, raw9586 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw9586step0 = (fun i j => raw9586 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw9586step0 raw9586; decide +kernel
      have hl : raw9586step0Labels = raw9586Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9586 raw9586Labels permutation434 hz
    mixedMoment B raw9586step0 raw9586step0Labels = mixedMoment B raw9586step1 raw9586step1Labels := by
      have hz : ∀ j, raw9586step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw9586step1 = (fun i j => raw9586step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw9586step1 raw9586step0; decide +kernel
      have hl : raw9586step1Labels = raw9586step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9586step0 raw9586step0Labels permutation80 hz
    mixedMoment B raw9586step1 raw9586step1Labels = mixedMoment B raw9586step2 raw9586step2Labels := by
      have ha : raw9586step2 = (fun i j => raw9586step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9586step2 raw9586step1; decide +kernel
      have hl : raw9586step2Labels = raw9586step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9586step1 raw9586step1Labels permutation10 permutation2
    _ = mixedMoment B node2782 node2782Labels := by rfl

theorem canonical9587 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9587 raw9587Labels = mixedMoment B node2632 node2632Labels := by
  calc
    mixedMoment B raw9587 raw9587Labels = mixedMoment B raw9587step0 raw9587step0Labels := by
      have hz : ∀ j, raw9587 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw9587step0 = (fun i j => raw9587 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw9587step0 raw9587; decide +kernel
      have hl : raw9587step0Labels = raw9587Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9587 raw9587Labels permutation434 hz
    mixedMoment B raw9587step0 raw9587step0Labels = mixedMoment B raw9587step1 raw9587step1Labels := by
      have ha : raw9587step1 = (fun i j => raw9587step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9587step1 raw9587step0; decide +kernel
      have hl : raw9587step1Labels = raw9587step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9587step0 raw9587step0Labels permutation34 permutation2
    _ = mixedMoment B node2632 node2632Labels := by rfl

theorem canonical9588 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9588 raw9588Labels = mixedMoment B node2632 node2632Labels := by
  calc
    mixedMoment B raw9588 raw9588Labels = mixedMoment B raw9588step0 raw9588step0Labels := by
      have hz : ∀ j, raw9588 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw9588step0 = (fun i j => raw9588 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw9588step0 raw9588; decide +kernel
      have hl : raw9588step0Labels = raw9588Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9588 raw9588Labels permutation346 hz
    mixedMoment B raw9588step0 raw9588step0Labels = mixedMoment B raw9588step1 raw9588step1Labels := by
      have ha : raw9588step1 = (fun i j => raw9588step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9588step1 raw9588step0; decide +kernel
      have hl : raw9588step1Labels = raw9588step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9588step0 raw9588step0Labels permutation34 permutation2
    _ = mixedMoment B node2632 node2632Labels := by rfl

theorem canonical9589 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9589 raw9589Labels = mixedMoment B node2643 node2643Labels := by
  calc
    mixedMoment B raw9589 raw9589Labels = mixedMoment B raw9589step0 raw9589step0Labels := by
      have hz : ∀ j, raw9589 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw9589step0 = (fun i j => raw9589 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw9589step0 raw9589; decide +kernel
      have hl : raw9589step0Labels = raw9589Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9589 raw9589Labels permutation434 hz
    mixedMoment B raw9589step0 raw9589step0Labels = mixedMoment B raw9589step1 raw9589step1Labels := by
      have hz : ∀ j, raw9589step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw9589step1 = (fun i j => raw9589step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw9589step1 raw9589step0; decide +kernel
      have hl : raw9589step1Labels = raw9589step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9589step0 raw9589step0Labels permutation80 hz
    _ = mixedMoment B node2643 node2643Labels := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical124
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical3978 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3978 = injectiveMoment H node210 := by
  calc
    injectiveMoment H raw3978 = injectiveMoment H raw3978step0 := by
      have heq : raw3978step0 = -raw3978 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3978).symm
    injectiveMoment H raw3978step0 = injectiveMoment H raw3978step1 := by
      have heq : raw3978step1 = (fun i j => raw3978step0 (permutation11 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3978step0 permutation11 permutation8
    _ = injectiveMoment H node210 := by rfl

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

theorem canonical4159 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4159 = injectiveMoment H node36 := by
  calc
    injectiveMoment H raw4159 = injectiveMoment H raw4159step0 := by
      have heq : raw4159step0 = -raw4159 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4159).symm
    injectiveMoment H raw4159step0 = injectiveMoment H raw4159step1 := by
      have heq : raw4159step1 = (fun i j => raw4159step0 (permutation7 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4159step0 permutation7 permutation5
    _ = injectiveMoment H node36 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical160
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical5141 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5141 = injectiveMoment H node46 := by
  rfl

end MUB6.Certificate.PairSemantics

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

theorem canonical5183 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5183 = injectiveMoment H node4 := by
  clear _hH
  calc
    injectiveMoment H raw5183 = injectiveMoment H raw5183step0 := by
      have hz : ∀ j, raw5183 (permutation5 0) j = 0 := by decide +kernel
      have heq : raw5183step0 = (fun i j => raw5183 (permutation5 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw5183 permutation5 hz
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical280
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical8979 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8979 = injectiveMoment H node11 := by
  calc
    injectiveMoment H raw8979 = injectiveMoment H raw8979step0 := by
      have hz : ∀ j, raw8979 (permutation9 0) j = 0 := by decide +kernel
      have heq : raw8979step0 = (fun i j => raw8979 (permutation9 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw8979 permutation9 hz
    _ = injectiveMoment H node11 := by rfl

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

theorem sound36 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node36 = Sparse.eval value36 (momentVector H) := by
  have hc : momentVector H 3 = injectiveMoment H node36 := rfl
  simp [value36, Sparse.eval, hc]

theorem sound44 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node44 = Sparse.eval value44 (momentVector H) := by
  have hc : momentVector H 4 = injectiveMoment H node44 := rfl
  simp [value44, Sparse.eval, hc]

theorem sound46 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node46 = Sparse.eval value46 (momentVector H) := by
  have heq : pivotMatrix46 = (fun u v => node46 (pivotPermutation46 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node46 = injectiveMoment H pivotMatrix46 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix46 0 = Pi.single (1 : Fin 2) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix46 1 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix46 (0 : Fin 3)) =
      Sparse.eval value10 (momentVector H) := by
    have heq : mergeFirst pivotMatrix46 (0 : Fin 3) = raw917 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical917 hH).trans (sound10 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix46 (1 : Fin 3)) =
      Sparse.eval value4 (momentVector H) := by
    have heq : mergeFirst pivotMatrix46 (1 : Fin 3) = raw5183 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical5183 hH).trans (sound4 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix46 (2 : Fin 3)) =
      Sparse.eval value11 (momentVector H) := by
    have heq : mergeFirst pivotMatrix46 (2 : Fin 3) = raw5199 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical5199 hH).trans (sound11 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node46 + (injectiveMoment H (mergeFirst pivotMatrix46 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix46 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix46 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value46, value10, value11, value4, Sparse.eval] at hc ⊢
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical155
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical4966 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4966 = injectiveMoment H node44 := by
  rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound3
attribute [-simp] _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_toRational _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

theorem sound210 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node210 = Sparse.eval value210 (momentVector H) := by
  have heq : pivotMatrix210 = (fun u v => node210 (pivotPermutation210 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node210 = injectiveMoment H pivotMatrix210 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix210 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix210 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix210 (0 : Fin 3)) =
      Sparse.eval value44 (momentVector H) := by
    have heq : mergeFirst pivotMatrix210 (0 : Fin 3) = raw4966 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical4966 hH).trans (sound44 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix210 (1 : Fin 3)) =
      Sparse.eval value62 (momentVector H) := by
    have heq : mergeFirst pivotMatrix210 (1 : Fin 3) = raw4160 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical4160 hH).trans (sound62 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix210 (2 : Fin 3)) =
      Sparse.eval value36 (momentVector H) := by
    have heq : mergeFirst pivotMatrix210 (2 : Fin 3) = raw4159 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical4159 hH).trans (sound36 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node210 + (injectiveMoment H (mergeFirst pivotMatrix210 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix210 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix210 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value210, value36, value44, value62, Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_SingleGroup30
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singlePair503 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node503 node503Labels = Sparse.eval singlePairValue503 (familyPairVector B) := by
  have hp := single_label_three B hB node503
  have hl : node503Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node503 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node503 (EqualityPatterns.family3.label 0) = PairSemantics.raw7980 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node503 PairSemantics.raw7980; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7980 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node503 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value11 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node503 (EqualityPatterns.family3.label 1) = PairSemantics.raw5197 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node503 PairSemantics.raw5197; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5197 hH).trans (PairSemantics.sound11 hH)
  have hm2 : familyPairMoment B (groupedColumns node503 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value11 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node503 (EqualityPatterns.family3.label 2) = PairSemantics.raw8979 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node503 PairSemantics.raw8979; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical8979 hH).trans (PairSemantics.sound11 hH)
  have hm3 : familyPairMoment B (groupedColumns node503 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value46 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node503 (EqualityPatterns.family3.label 3) = PairSemantics.raw5141 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node503 PairSemantics.raw5141; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5141 hH).trans (PairSemantics.sound46 hH)
  have hm4 : familyPairMoment B (groupedColumns node503 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value210 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node503 (EqualityPatterns.family3.label 4) = PairSemantics.raw3978 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node503 PairSemantics.raw3978; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical3978 hH).trans (PairSemantics.sound210 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue503, PairSemantics.value0, PairSemantics.value11, PairSemantics.value46, PairSemantics.value210, Sparse.eval] at hp ⊢
  linarith only [hp]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons60
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singleton3888 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node3888 node3888Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node503 node503Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw544 singletonSmall3888
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall3888) = raw544Labels := by decide +kernel
  rw [hl, canonical544 B hB] at h
  have hc0 : mixedMoment B raw544 (Fin.cases (0 : Fin 1) singletonSmall3888) =
      mixedMoment B node503 node503Labels := by
    have ha : raw544 = raw545 := by apply Matrix.ext; unfold raw544 raw545; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall3888 = raw545Labels := by decide +kernel
    rw [ha, hj, canonical545 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound19
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound1234 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1234 node1234Labels = Sparse.eval nodeValue1234 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1234) = mixedMoment B node1234 node1234Labels := rfl
  simpa [nodeValue1234, Sparse.eval] using hc.symm

theorem sound1261 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1261 node1261Labels = Sparse.eval nodeValue1261 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1261) = mixedMoment B node1261 node1261Labels := rfl
  simpa [nodeValue1261, Sparse.eval] using hc.symm

theorem sound1264 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1264 node1264Labels = Sparse.eval nodeValue1264 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1264) = mixedMoment B node1264 node1264Labels := rfl
  simpa [nodeValue1264, Sparse.eval] using hc.symm

theorem sound1273 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1273 node1273Labels = Sparse.eval nodeValue1273 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1273) = mixedMoment B node1273 node1273Labels := rfl
  simpa [nodeValue1273, Sparse.eval] using hc.symm

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

theorem sound1294 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1294 node1294Labels = Sparse.eval nodeValue1294 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1294) = mixedMoment B node1294 node1294Labels := rfl
  simpa [nodeValue1294, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound21
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound1382 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1382 node1382Labels = Sparse.eval nodeValue1382 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1382) = mixedMoment B node1382 node1382Labels := rfl
  simpa [nodeValue1382, Sparse.eval] using hc.symm

theorem sound1385 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1385 node1385Labels = Sparse.eval nodeValue1385 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1385) = mixedMoment B node1385 node1385Labels := rfl
  simpa [nodeValue1385, Sparse.eval] using hc.symm

theorem sound1390 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1390 node1390Labels = Sparse.eval nodeValue1390 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1390) = mixedMoment B node1390 node1390Labels := rfl
  simpa [nodeValue1390, Sparse.eval] using hc.symm

theorem sound1404 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1404 node1404Labels = Sparse.eval nodeValue1404 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1404) = mixedMoment B node1404 node1404Labels := rfl
  simpa [nodeValue1404, Sparse.eval] using hc.symm

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

theorem sound2009 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2009 node2009Labels = Sparse.eval nodeValue2009 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2009) = mixedMoment B node2009 node2009Labels := rfl
  simpa [nodeValue2009, Sparse.eval] using hc.symm

theorem sound2025 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2025 node2025Labels = Sparse.eval nodeValue2025 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2025) = mixedMoment B node2025 node2025Labels := rfl
  simpa [nodeValue2025, Sparse.eval] using hc.symm

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

theorem sound2131 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2131 node2131Labels = Sparse.eval nodeValue2131 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2131) = mixedMoment B node2131 node2131Labels := rfl
  simpa [nodeValue2131, Sparse.eval] using hc.symm

theorem sound2132 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2132 node2132Labels = Sparse.eval nodeValue2132 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2132) = mixedMoment B node2132 node2132Labels := rfl
  simpa [nodeValue2132, Sparse.eval] using hc.symm

theorem sound2133 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2133 node2133Labels = Sparse.eval nodeValue2133 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2133) = mixedMoment B node2133 node2133Labels := rfl
  simpa [nodeValue2133, Sparse.eval] using hc.symm

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

theorem sound2277 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2277 node2277Labels = Sparse.eval nodeValue2277 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2277) = mixedMoment B node2277 node2277Labels := rfl
  simpa [nodeValue2277, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros39
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero2552 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node2552 node2552Labels = 0 := by
  exact mixedMoment_alpha B hF node2552 node2552Labels 1 permutation161
    (by decide +kernel)

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

theorem sound2552 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2552 node2552Labels = Sparse.eval nodeValue2552 (mixedVector B) := by
  simpa only [nodeValue2552, Sparse.eval_nil] using zero2552 B _hB _hF

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

theorem sound2590 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2590 node2590Labels = Sparse.eval nodeValue2590 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2590) = mixedMoment B node2590 node2590Labels := rfl
  simpa [nodeValue2590, Sparse.eval] using hc.symm

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

theorem sound2632 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2632 node2632Labels = Sparse.eval nodeValue2632 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2632) = mixedMoment B node2632 node2632Labels := rfl
  simpa [nodeValue2632, Sparse.eval] using hc.symm

theorem sound2635 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2635 node2635Labels = Sparse.eval nodeValue2635 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2635) = mixedMoment B node2635 node2635Labels := rfl
  simpa [nodeValue2635, Sparse.eval] using hc.symm

theorem sound2643 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2643 node2643Labels = Sparse.eval nodeValue2643 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2643) = mixedMoment B node2643 node2643Labels := rfl
  simpa [nodeValue2643, Sparse.eval] using hc.symm

theorem sound2681 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2681 node2681Labels = Sparse.eval nodeValue2681 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2681) = mixedMoment B node2681 node2681Labels := rfl
  simpa [nodeValue2681, Sparse.eval] using hc.symm

theorem sound2683 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2683 node2683Labels = Sparse.eval nodeValue2683 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2683) = mixedMoment B node2683 node2683Labels := rfl
  simpa [nodeValue2683, Sparse.eval] using hc.symm

theorem sound2687 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2687 node2687Labels = Sparse.eval nodeValue2687 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2687) = mixedMoment B node2687 node2687Labels := rfl
  simpa [nodeValue2687, Sparse.eval] using hc.symm

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

theorem zero2742 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2742 node2742Labels = 0 := by
  exact mixedMoment_order_one B hB node2742 node2742Labels 1
    (by decide +kernel) (by decide +kernel)

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

theorem sound2738 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2738 node2738Labels = Sparse.eval nodeValue2738 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2738) = mixedMoment B node2738 node2738Labels := rfl
  simpa [nodeValue2738, Sparse.eval] using hc.symm

theorem sound2740 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2740 node2740Labels = Sparse.eval nodeValue2740 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2740) = mixedMoment B node2740 node2740Labels := rfl
  simpa [nodeValue2740, Sparse.eval] using hc.symm

theorem sound2742 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2742 node2742Labels = Sparse.eval nodeValue2742 (mixedVector B) := by
  simpa only [nodeValue2742, Sparse.eval_nil] using zero2742 B _hB _hF

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

theorem sound2781 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2781 node2781Labels = Sparse.eval nodeValue2781 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2781) = mixedMoment B node2781 node2781Labels := rfl
  simpa [nodeValue2781, Sparse.eval] using hc.symm

theorem sound2782 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2782 node2782Labels = Sparse.eval nodeValue2782 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2782) = mixedMoment B node2782 node2782Labels := rfl
  simpa [nodeValue2782, Sparse.eval] using hc.symm

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

theorem sound2923 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2923 node2923Labels = Sparse.eval nodeValue2923 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2923) = mixedMoment B node2923 node2923Labels := rfl
  simpa [nodeValue2923, Sparse.eval] using hc.symm

theorem sound2930 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2930 node2930Labels = Sparse.eval nodeValue2930 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2930) = mixedMoment B node2930 node2930Labels := rfl
  simpa [nodeValue2930, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound46
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound2952 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2952 node2952Labels = Sparse.eval nodeValue2952 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2952) = mixedMoment B node2952 node2952Labels := rfl
  simpa [nodeValue2952, Sparse.eval] using hc.symm

theorem sound2980 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2980 node2980Labels = Sparse.eval nodeValue2980 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2980) = mixedMoment B node2980 node2980Labels := rfl
  simpa [nodeValue2980, Sparse.eval] using hc.symm

theorem sound2983 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2983 node2983Labels = Sparse.eval nodeValue2983 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2983) = mixedMoment B node2983 node2983Labels := rfl
  simpa [nodeValue2983, Sparse.eval] using hc.symm

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

theorem sound3073 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3073 node3073Labels = Sparse.eval nodeValue3073 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3073) = mixedMoment B node3073 node3073Labels := rfl
  simpa [nodeValue3073, Sparse.eval] using hc.symm

theorem sound3075 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3075 node3075Labels = Sparse.eval nodeValue3075 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3075) = mixedMoment B node3075 node3075Labels := rfl
  simpa [nodeValue3075, Sparse.eval] using hc.symm

theorem sound3079 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3079 node3079Labels = Sparse.eval nodeValue3079 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3079) = mixedMoment B node3079 node3079Labels := rfl
  simpa [nodeValue3079, Sparse.eval] using hc.symm

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

theorem sound3296 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3296 node3296Labels = Sparse.eval nodeValue3296 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3296) = mixedMoment B node3296 node3296Labels := rfl
  simpa [nodeValue3296, Sparse.eval] using hc.symm

theorem sound3302 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3302 node3302Labels = Sparse.eval nodeValue3302 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3302) = mixedMoment B node3302 node3302Labels := rfl
  simpa [nodeValue3302, Sparse.eval] using hc.symm

theorem sound3305 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3305 node3305Labels = Sparse.eval nodeValue3305 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3305) = mixedMoment B node3305 node3305Labels := rfl
  simpa [nodeValue3305, Sparse.eval] using hc.symm

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

theorem zero3547 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3547 node3547Labels = 0 := by
  exact mixedMoment_order_one B hB node3547 node3547Labels 1
    (by decide +kernel) (by decide +kernel)

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

theorem sound3530 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3530 node3530Labels = Sparse.eval nodeValue3530 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3530) = mixedMoment B node3530 node3530Labels := rfl
  simpa [nodeValue3530, Sparse.eval] using hc.symm

theorem sound3533 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3533 node3533Labels = Sparse.eval nodeValue3533 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3533) = mixedMoment B node3533 node3533Labels := rfl
  simpa [nodeValue3533, Sparse.eval] using hc.symm

theorem sound3534 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3534 node3534Labels = Sparse.eval nodeValue3534 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3534) = mixedMoment B node3534 node3534Labels := rfl
  simpa [nodeValue3534, Sparse.eval] using hc.symm

theorem sound3545 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3545 node3545Labels = Sparse.eval nodeValue3545 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3545) = mixedMoment B node3545 node3545Labels := rfl
  simpa [nodeValue3545, Sparse.eval] using hc.symm

theorem sound3547 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3547 node3547Labels = Sparse.eval nodeValue3547 (mixedVector B) := by
  simpa only [nodeValue3547, Sparse.eval_nil] using zero3547 B _hB _hF

theorem sound3557 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3557 node3557Labels = Sparse.eval nodeValue3557 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3557) = mixedMoment B node3557 node3557Labels := rfl
  simpa [nodeValue3557, Sparse.eval] using hc.symm

theorem sound3564 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3564 node3564Labels = Sparse.eval nodeValue3564 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3564) = mixedMoment B node3564 node3564Labels := rfl
  simpa [nodeValue3564, Sparse.eval] using hc.symm

theorem sound3570 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3570 node3570Labels = Sparse.eval nodeValue3570 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3570) = mixedMoment B node3570 node3570Labels := rfl
  simpa [nodeValue3570, Sparse.eval] using hc.symm

theorem sound3572 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3572 node3572Labels = Sparse.eval nodeValue3572 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3572) = mixedMoment B node3572 node3572Labels := rfl
  simpa [nodeValue3572, Sparse.eval] using hc.symm

theorem sound3579 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3579 node3579Labels = Sparse.eval nodeValue3579 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3579) = mixedMoment B node3579 node3579Labels := rfl
  simpa [nodeValue3579, Sparse.eval] using hc.symm

theorem sound3581 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3581 node3581Labels = Sparse.eval nodeValue3581 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3581) = mixedMoment B node3581 node3581Labels := rfl
  simpa [nodeValue3581, Sparse.eval] using hc.symm

theorem sound3583 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3583 node3583Labels = Sparse.eval nodeValue3583 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3583) = mixedMoment B node3583 node3583Labels := rfl
  simpa [nodeValue3583, Sparse.eval] using hc.symm

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

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound7
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound503 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node503 node503Labels = Sparse.eval nodeValue503 (mixedVector B) := by
  calc
    _ = Sparse.eval singlePairValue503 (familyPairVector B) := singlePair503 B _hB
    _ = _ := by norm_num [singlePairValue503, nodeValue503, Sparse.eval, mixedVector] <;> ring

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros60
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero3860 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3860 node3860Labels = 0 := by
  exact mixedMoment_order_one B hB node3860 node3860Labels 1
    (by decide +kernel) (by decide +kernel)

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

theorem sound3850 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3850 node3850Labels = Sparse.eval nodeValue3850 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3850) = mixedMoment B node3850 node3850Labels := rfl
  simpa [nodeValue3850, Sparse.eval] using hc.symm

theorem sound3860 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3860 node3860Labels = Sparse.eval nodeValue3860 (mixedVector B) := by
  simpa only [nodeValue3860, Sparse.eval_nil] using zero3860 B _hB _hF

theorem sound3886 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3886 node3886Labels = Sparse.eval nodeValue3886 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3886) = mixedMoment B node3886 node3886Labels := rfl
  simpa [nodeValue3886, Sparse.eval] using hc.symm

theorem sound3888 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3888 node3888Labels = Sparse.eval nodeValue3888 (mixedVector B) := by
  have h := singleton3888 B _hB
  rw [sound503 B _hB _hF] at h
  norm_num [nodeValue3888, nodeValue503, Sparse.eval] at h ⊢
  linarith only [h]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros61
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero3905 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3905 node3905Labels = 0 := by
  exact mixedMoment_order_one B hB node3905 node3905Labels 1
    (by decide +kernel) (by decide +kernel)

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

theorem sound3905 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3905 node3905Labels = Sparse.eval nodeValue3905 (mixedVector B) := by
  simpa only [nodeValue3905, Sparse.eval_nil] using zero3905 B _hB _hF

theorem sound3913 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3913 node3913Labels = Sparse.eval nodeValue3913 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3913) = mixedMoment B node3913 node3913Labels := rfl
  simpa [nodeValue3913, Sparse.eval] using hc.symm

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

theorem sound4092 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4092 node4092Labels = Sparse.eval nodeValue4092 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4092) = mixedMoment B node4092 node4092Labels := rfl
  simpa [nodeValue4092, Sparse.eval] using hc.symm

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources17
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sourceEq552 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm552 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA552 + difference 0 0) (sourceB552 + difference 0 0) sourceC552) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3075) := by
    have ha : (tripleCharges (sourceA552 + difference 0 0) (sourceB552 + difference 0 0) sourceC552) = raw9451 := by
      apply Matrix.ext; unfold tripleCharges sourceA552 sourceB552 sourceC552 difference raw9451; decide +kernel
    rw [ha]
    exact (canonical9451 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA552 + difference 0 1) (sourceB552 + difference 1 0) sourceC552) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3525) := by
    have ha : (tripleCharges (sourceA552 + difference 0 1) (sourceB552 + difference 1 0) sourceC552) = raw9452 := by
      apply Matrix.ext; unfold tripleCharges sourceA552 sourceB552 sourceC552 difference raw9452; decide +kernel
    rw [ha]
    exact (canonical9452 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA552 + difference 0 2) (sourceB552 + difference 2 0) sourceC552) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3534) := by
    have ha : (tripleCharges (sourceA552 + difference 0 2) (sourceB552 + difference 2 0) sourceC552) = raw9453 := by
      apply Matrix.ext; unfold tripleCharges sourceA552 sourceB552 sourceC552 difference raw9453; decide +kernel
    rw [ha]
    exact (canonical9453 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA552 + difference 0 3) (sourceB552 + difference 3 0) sourceC552) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3534) := by
    have ha : (tripleCharges (sourceA552 + difference 0 3) (sourceB552 + difference 3 0) sourceC552) = raw9454 := by
      apply Matrix.ext; unfold tripleCharges sourceA552 sourceB552 sourceC552 difference raw9454; decide +kernel
    rw [ha]
    exact (canonical9454 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA552 + difference 0 4) (sourceB552 + difference 4 0) sourceC552) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3623) := by
    have ha : (tripleCharges (sourceA552 + difference 0 4) (sourceB552 + difference 4 0) sourceC552) = raw9455 := by
      apply Matrix.ext; unfold tripleCharges sourceA552 sourceB552 sourceC552 difference raw9455; decide +kernel
    rw [ha]
    exact (canonical9455 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA552 + difference 0 5) (sourceB552 + difference 5 0) sourceC552) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3581) := by
    have ha : (tripleCharges (sourceA552 + difference 0 5) (sourceB552 + difference 5 0) sourceC552) = raw9456 := by
      apply Matrix.ext; unfold tripleCharges sourceA552 sourceB552 sourceC552 difference raw9456; decide +kernel
    rw [ha]
    exact (canonical9456 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA552 + sourceB552) sourceC552) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4083) := by
    have ha : (doubleCharges (sourceA552 + sourceB552) sourceC552) = raw9457 := by
      apply Matrix.ext; unfold doubleCharges sourceA552 sourceB552 sourceC552 raw9457; decide +kernel
    rw [ha]
    exact (canonical9457 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA552 sourceB552 sourceC552
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm552, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq553 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm553 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA553 + difference 0 0) (sourceB553 + difference 0 0) sourceC553) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3075) := by
    have ha : (tripleCharges (sourceA553 + difference 0 0) (sourceB553 + difference 0 0) sourceC553) = raw9451 := by
      apply Matrix.ext; unfold tripleCharges sourceA553 sourceB553 sourceC553 difference raw9451; decide +kernel
    rw [ha]
    exact (canonical9451 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA553 + difference 1 0) (sourceB553 + difference 0 1) sourceC553) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1382) := by
    have ha : (tripleCharges (sourceA553 + difference 1 0) (sourceB553 + difference 0 1) sourceC553) = raw9458 := by
      apply Matrix.ext; unfold tripleCharges sourceA553 sourceB553 sourceC553 difference raw9458; decide +kernel
    rw [ha]
    exact (canonical9458 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA553 + difference 2 0) (sourceB553 + difference 0 2) sourceC553) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1404) := by
    have ha : (tripleCharges (sourceA553 + difference 2 0) (sourceB553 + difference 0 2) sourceC553) = raw9459 := by
      apply Matrix.ext; unfold tripleCharges sourceA553 sourceB553 sourceC553 difference raw9459; decide +kernel
    rw [ha]
    exact (canonical9459 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA553 + difference 3 0) (sourceB553 + difference 0 3) sourceC553) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1404) := by
    have ha : (tripleCharges (sourceA553 + difference 3 0) (sourceB553 + difference 0 3) sourceC553) = raw9460 := by
      apply Matrix.ext; unfold tripleCharges sourceA553 sourceB553 sourceC553 difference raw9460; decide +kernel
    rw [ha]
    exact (canonical9460 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA553 + difference 4 0) (sourceB553 + difference 0 4) sourceC553) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1390) := by
    have ha : (tripleCharges (sourceA553 + difference 4 0) (sourceB553 + difference 0 4) sourceC553) = raw9461 := by
      apply Matrix.ext; unfold tripleCharges sourceA553 sourceB553 sourceC553 difference raw9461; decide +kernel
    rw [ha]
    exact (canonical9461 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA553 + difference 5 0) (sourceB553 + difference 0 5) sourceC553) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1385) := by
    have ha : (tripleCharges (sourceA553 + difference 5 0) (sourceB553 + difference 0 5) sourceC553) = raw9462 := by
      apply Matrix.ext; unfold tripleCharges sourceA553 sourceB553 sourceC553 difference raw9462; decide +kernel
    rw [ha]
    exact (canonical9462 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA553 + sourceB553) sourceC553) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4083) := by
    have ha : (doubleCharges (sourceA553 + sourceB553) sourceC553) = raw9457 := by
      apply Matrix.ext; unfold doubleCharges sourceA553 sourceB553 sourceC553 raw9457; decide +kernel
    rw [ha]
    exact (canonical9457 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA553 sourceB553 sourceC553
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm553, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq554 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm554 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA554 + difference 1 0) (sourceB554 + difference 0 1) sourceC554) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1382) := by
    have ha : (tripleCharges (sourceA554 + difference 1 0) (sourceB554 + difference 0 1) sourceC554) = raw9458 := by
      apply Matrix.ext; unfold tripleCharges sourceA554 sourceB554 sourceC554 difference raw9458; decide +kernel
    rw [ha]
    exact (canonical9458 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA554 + difference 1 1) (sourceB554 + difference 1 1) sourceC554) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3075) := by
    have ha : (tripleCharges (sourceA554 + difference 1 1) (sourceB554 + difference 1 1) sourceC554) = raw9451 := by
      apply Matrix.ext; unfold tripleCharges sourceA554 sourceB554 sourceC554 difference raw9451; decide +kernel
    rw [ha]
    exact (canonical9451 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA554 + difference 1 2) (sourceB554 + difference 2 1) sourceC554) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2923) := by
    have ha : (tripleCharges (sourceA554 + difference 1 2) (sourceB554 + difference 2 1) sourceC554) = raw9463 := by
      apply Matrix.ext; unfold tripleCharges sourceA554 sourceB554 sourceC554 difference raw9463; decide +kernel
    rw [ha]
    exact (canonical9463 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA554 + difference 1 3) (sourceB554 + difference 3 1) sourceC554) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2923) := by
    have ha : (tripleCharges (sourceA554 + difference 1 3) (sourceB554 + difference 3 1) sourceC554) = raw9464 := by
      apply Matrix.ext; unfold tripleCharges sourceA554 sourceB554 sourceC554 difference raw9464; decide +kernel
    rw [ha]
    exact (canonical9464 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA554 + difference 1 4) (sourceB554 + difference 4 1) sourceC554) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3075) := by
    have ha : (tripleCharges (sourceA554 + difference 1 4) (sourceB554 + difference 4 1) sourceC554) = raw9465 := by
      apply Matrix.ext; unfold tripleCharges sourceA554 sourceB554 sourceC554 difference raw9465; decide +kernel
    rw [ha]
    exact (canonical9465 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA554 + difference 1 5) (sourceB554 + difference 5 1) sourceC554) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3073) := by
    have ha : (tripleCharges (sourceA554 + difference 1 5) (sourceB554 + difference 5 1) sourceC554) = raw9466 := by
      apply Matrix.ext; unfold tripleCharges sourceA554 sourceB554 sourceC554 difference raw9466; decide +kernel
    rw [ha]
    exact (canonical9466 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA554 + sourceB554) sourceC554) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4083) := by
    have ha : (doubleCharges (sourceA554 + sourceB554) sourceC554) = raw9457 := by
      apply Matrix.ext; unfold doubleCharges sourceA554 sourceB554 sourceC554 raw9457; decide +kernel
    rw [ha]
    exact (canonical9457 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA554 sourceB554 sourceC554
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm554, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq555 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm555 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA555 + difference 0 1) (sourceB555 + difference 1 0) sourceC555) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3525) := by
    have ha : (tripleCharges (sourceA555 + difference 0 1) (sourceB555 + difference 1 0) sourceC555) = raw9452 := by
      apply Matrix.ext; unfold tripleCharges sourceA555 sourceB555 sourceC555 difference raw9452; decide +kernel
    rw [ha]
    exact (canonical9452 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA555 + difference 1 1) (sourceB555 + difference 1 1) sourceC555) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3075) := by
    have ha : (tripleCharges (sourceA555 + difference 1 1) (sourceB555 + difference 1 1) sourceC555) = raw9451 := by
      apply Matrix.ext; unfold tripleCharges sourceA555 sourceB555 sourceC555 difference raw9451; decide +kernel
    rw [ha]
    exact (canonical9451 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA555 + difference 2 1) (sourceB555 + difference 1 2) sourceC555) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2983) := by
    have ha : (tripleCharges (sourceA555 + difference 2 1) (sourceB555 + difference 1 2) sourceC555) = raw9467 := by
      apply Matrix.ext; unfold tripleCharges sourceA555 sourceB555 sourceC555 difference raw9467; decide +kernel
    rw [ha]
    exact (canonical9467 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA555 + difference 3 1) (sourceB555 + difference 1 3) sourceC555) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2983) := by
    have ha : (tripleCharges (sourceA555 + difference 3 1) (sourceB555 + difference 1 3) sourceC555) = raw9468 := by
      apply Matrix.ext; unfold tripleCharges sourceA555 sourceB555 sourceC555 difference raw9468; decide +kernel
    rw [ha]
    exact (canonical9468 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA555 + difference 4 1) (sourceB555 + difference 1 4) sourceC555) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2980) := by
    have ha : (tripleCharges (sourceA555 + difference 4 1) (sourceB555 + difference 1 4) sourceC555) = raw9469 := by
      apply Matrix.ext; unfold tripleCharges sourceA555 sourceB555 sourceC555 difference raw9469; decide +kernel
    rw [ha]
    exact (canonical9469 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA555 + difference 5 1) (sourceB555 + difference 1 5) sourceC555) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2009) := by
    have ha : (tripleCharges (sourceA555 + difference 5 1) (sourceB555 + difference 1 5) sourceC555) = raw9470 := by
      apply Matrix.ext; unfold tripleCharges sourceA555 sourceB555 sourceC555 difference raw9470; decide +kernel
    rw [ha]
    exact (canonical9470 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA555 + sourceB555) sourceC555) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4083) := by
    have ha : (doubleCharges (sourceA555 + sourceB555) sourceC555) = raw9457 := by
      apply Matrix.ext; unfold doubleCharges sourceA555 sourceB555 sourceC555 raw9457; decide +kernel
    rw [ha]
    exact (canonical9457 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA555 sourceB555 sourceC555
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm555, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq556 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm556 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA556 + difference 0 2) (sourceB556 + difference 2 0) sourceC556) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3534) := by
    have ha : (tripleCharges (sourceA556 + difference 0 2) (sourceB556 + difference 2 0) sourceC556) = raw9453 := by
      apply Matrix.ext; unfold tripleCharges sourceA556 sourceB556 sourceC556 difference raw9453; decide +kernel
    rw [ha]
    exact (canonical9453 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA556 + difference 1 2) (sourceB556 + difference 2 1) sourceC556) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2923) := by
    have ha : (tripleCharges (sourceA556 + difference 1 2) (sourceB556 + difference 2 1) sourceC556) = raw9463 := by
      apply Matrix.ext; unfold tripleCharges sourceA556 sourceB556 sourceC556 difference raw9463; decide +kernel
    rw [ha]
    exact (canonical9463 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA556 + difference 2 2) (sourceB556 + difference 2 2) sourceC556) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3075) := by
    have ha : (tripleCharges (sourceA556 + difference 2 2) (sourceB556 + difference 2 2) sourceC556) = raw9451 := by
      apply Matrix.ext; unfold tripleCharges sourceA556 sourceB556 sourceC556 difference raw9451; decide +kernel
    rw [ha]
    exact (canonical9451 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA556 + difference 3 2) (sourceB556 + difference 2 3) sourceC556) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2952) := by
    have ha : (tripleCharges (sourceA556 + difference 3 2) (sourceB556 + difference 2 3) sourceC556) = raw9471 := by
      apply Matrix.ext; unfold tripleCharges sourceA556 sourceB556 sourceC556 difference raw9471; decide +kernel
    rw [ha]
    exact (canonical9471 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA556 + difference 4 2) (sourceB556 + difference 2 4) sourceC556) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2930) := by
    have ha : (tripleCharges (sourceA556 + difference 4 2) (sourceB556 + difference 2 4) sourceC556) = raw9472 := by
      apply Matrix.ext; unfold tripleCharges sourceA556 sourceB556 sourceC556 difference raw9472; decide +kernel
    rw [ha]
    exact (canonical9472 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA556 + difference 5 2) (sourceB556 + difference 2 5) sourceC556) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2025) := by
    have ha : (tripleCharges (sourceA556 + difference 5 2) (sourceB556 + difference 2 5) sourceC556) = raw9473 := by
      apply Matrix.ext; unfold tripleCharges sourceA556 sourceB556 sourceC556 difference raw9473; decide +kernel
    rw [ha]
    exact (canonical9473 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA556 + sourceB556) sourceC556) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4083) := by
    have ha : (doubleCharges (sourceA556 + sourceB556) sourceC556) = raw9457 := by
      apply Matrix.ext; unfold doubleCharges sourceA556 sourceB556 sourceC556 raw9457; decide +kernel
    rw [ha]
    exact (canonical9457 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA556 sourceB556 sourceC556
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm556, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq557 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm557 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA557 + difference 4 0) (sourceB557 + difference 0 4) sourceC557) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1390) := by
    have ha : (tripleCharges (sourceA557 + difference 4 0) (sourceB557 + difference 0 4) sourceC557) = raw9461 := by
      apply Matrix.ext; unfold tripleCharges sourceA557 sourceB557 sourceC557 difference raw9461; decide +kernel
    rw [ha]
    exact (canonical9461 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA557 + difference 4 1) (sourceB557 + difference 1 4) sourceC557) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2980) := by
    have ha : (tripleCharges (sourceA557 + difference 4 1) (sourceB557 + difference 1 4) sourceC557) = raw9469 := by
      apply Matrix.ext; unfold tripleCharges sourceA557 sourceB557 sourceC557 difference raw9469; decide +kernel
    rw [ha]
    exact (canonical9469 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA557 + difference 4 2) (sourceB557 + difference 2 4) sourceC557) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2930) := by
    have ha : (tripleCharges (sourceA557 + difference 4 2) (sourceB557 + difference 2 4) sourceC557) = raw9472 := by
      apply Matrix.ext; unfold tripleCharges sourceA557 sourceB557 sourceC557 difference raw9472; decide +kernel
    rw [ha]
    exact (canonical9472 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA557 + difference 4 3) (sourceB557 + difference 3 4) sourceC557) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2930) := by
    have ha : (tripleCharges (sourceA557 + difference 4 3) (sourceB557 + difference 3 4) sourceC557) = raw9474 := by
      apply Matrix.ext; unfold tripleCharges sourceA557 sourceB557 sourceC557 difference raw9474; decide +kernel
    rw [ha]
    exact (canonical9474 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA557 + difference 4 4) (sourceB557 + difference 4 4) sourceC557) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3075) := by
    have ha : (tripleCharges (sourceA557 + difference 4 4) (sourceB557 + difference 4 4) sourceC557) = raw9451 := by
      apply Matrix.ext; unfold tripleCharges sourceA557 sourceB557 sourceC557 difference raw9451; decide +kernel
    rw [ha]
    exact (canonical9451 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA557 + difference 4 5) (sourceB557 + difference 5 4) sourceC557) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3079) := by
    have ha : (tripleCharges (sourceA557 + difference 4 5) (sourceB557 + difference 5 4) sourceC557) = raw9475 := by
      apply Matrix.ext; unfold tripleCharges sourceA557 sourceB557 sourceC557 difference raw9475; decide +kernel
    rw [ha]
    exact (canonical9475 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA557 + sourceB557) sourceC557) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4083) := by
    have ha : (doubleCharges (sourceA557 + sourceB557) sourceC557) = raw9457 := by
      apply Matrix.ext; unfold doubleCharges sourceA557 sourceB557 sourceC557 raw9457; decide +kernel
    rw [ha]
    exact (canonical9457 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA557 sourceB557 sourceC557
    (0 : Fin 2) 1 (4 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm557, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq561 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm561 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA561 + difference 0 0) (sourceB561 + difference 0 0) sourceC561) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2738) := by
    have ha : (tripleCharges (sourceA561 + difference 0 0) (sourceB561 + difference 0 0) sourceC561) = raw7556 := by
      apply Matrix.ext; unfold tripleCharges sourceA561 sourceB561 sourceC561 difference raw7556; decide +kernel
    rw [ha]
    exact (canonical7556 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA561 + difference 0 1) (sourceB561 + difference 1 0) sourceC561) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2552) := by
    have ha : (tripleCharges (sourceA561 + difference 0 1) (sourceB561 + difference 1 0) sourceC561) = raw7553 := by
      apply Matrix.ext; unfold tripleCharges sourceA561 sourceB561 sourceC561 difference raw7553; decide +kernel
    rw [ha]
    exact (canonical7553 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA561 + difference 0 2) (sourceB561 + difference 2 0) sourceC561) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2740) := by
    have ha : (tripleCharges (sourceA561 + difference 0 2) (sourceB561 + difference 2 0) sourceC561) = raw8316 := by
      apply Matrix.ext; unfold tripleCharges sourceA561 sourceB561 sourceC561 difference raw8316; decide +kernel
    rw [ha]
    exact (canonical8316 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA561 + difference 0 3) (sourceB561 + difference 3 0) sourceC561) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2740) := by
    have ha : (tripleCharges (sourceA561 + difference 0 3) (sourceB561 + difference 3 0) sourceC561) = raw9503 := by
      apply Matrix.ext; unfold tripleCharges sourceA561 sourceB561 sourceC561 difference raw9503; decide +kernel
    rw [ha]
    exact (canonical9503 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA561 + difference 0 4) (sourceB561 + difference 4 0) sourceC561) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2509) := by
    have ha : (tripleCharges (sourceA561 + difference 0 4) (sourceB561 + difference 4 0) sourceC561) = raw9251 := by
      apply Matrix.ext; unfold tripleCharges sourceA561 sourceB561 sourceC561 difference raw9251; decide +kernel
    rw [ha]
    exact (canonical9251 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA561 + difference 0 5) (sourceB561 + difference 5 0) sourceC561) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1234) := by
    have ha : (tripleCharges (sourceA561 + difference 0 5) (sourceB561 + difference 5 0) sourceC561) = raw9504 := by
      apply Matrix.ext; unfold tripleCharges sourceA561 sourceB561 sourceC561 difference raw9504; decide +kernel
    rw [ha]
    exact (canonical9504 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA561 + sourceB561) sourceC561) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA561 + sourceB561) sourceC561) = raw5754 := by
      apply Matrix.ext; unfold doubleCharges sourceA561 sourceB561 sourceC561 raw5754; decide +kernel
    rw [ha]
    exact (canonical5754 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA561 sourceB561 sourceC561
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm561, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq562 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm562 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA562 + difference 0 0) (sourceB562 + difference 0 0) sourceC562) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2738) := by
    have ha : (tripleCharges (sourceA562 + difference 0 0) (sourceB562 + difference 0 0) sourceC562) = raw7556 := by
      apply Matrix.ext; unfold tripleCharges sourceA562 sourceB562 sourceC562 difference raw7556; decide +kernel
    rw [ha]
    exact (canonical7556 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA562 + difference 1 0) (sourceB562 + difference 0 1) sourceC562) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2131) := by
    have ha : (tripleCharges (sourceA562 + difference 1 0) (sourceB562 + difference 0 1) sourceC562) = raw5763 := by
      apply Matrix.ext; unfold tripleCharges sourceA562 sourceB562 sourceC562 difference raw5763; decide +kernel
    rw [ha]
    exact (canonical5763 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA562 + difference 2 0) (sourceB562 + difference 0 2) sourceC562) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2133) := by
    have ha : (tripleCharges (sourceA562 + difference 2 0) (sourceB562 + difference 0 2) sourceC562) = raw9505 := by
      apply Matrix.ext; unfold tripleCharges sourceA562 sourceB562 sourceC562 difference raw9505; decide +kernel
    rw [ha]
    exact (canonical9505 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA562 + difference 3 0) (sourceB562 + difference 0 3) sourceC562) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2133) := by
    have ha : (tripleCharges (sourceA562 + difference 3 0) (sourceB562 + difference 0 3) sourceC562) = raw9506 := by
      apply Matrix.ext; unfold tripleCharges sourceA562 sourceB562 sourceC562 difference raw9506; decide +kernel
    rw [ha]
    exact (canonical9506 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA562 + difference 4 0) (sourceB562 + difference 0 4) sourceC562) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2132) := by
    have ha : (tripleCharges (sourceA562 + difference 4 0) (sourceB562 + difference 0 4) sourceC562) = raw8319 := by
      apply Matrix.ext; unfold tripleCharges sourceA562 sourceB562 sourceC562 difference raw8319; decide +kernel
    rw [ha]
    exact (canonical8319 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA562 + difference 5 0) (sourceB562 + difference 0 5) sourceC562) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2277) := by
    have ha : (tripleCharges (sourceA562 + difference 5 0) (sourceB562 + difference 0 5) sourceC562) = raw5760 := by
      apply Matrix.ext; unfold tripleCharges sourceA562 sourceB562 sourceC562 difference raw5760; decide +kernel
    rw [ha]
    exact (canonical5760 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA562 + sourceB562) sourceC562) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA562 + sourceB562) sourceC562) = raw5754 := by
      apply Matrix.ext; unfold doubleCharges sourceA562 sourceB562 sourceC562 raw5754; decide +kernel
    rw [ha]
    exact (canonical5754 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA562 sourceB562 sourceC562
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm562, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq566 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm566 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA566 + difference 0 1) (sourceB566 + difference 1 0) sourceC566) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3886) := by
    have ha : (tripleCharges (sourceA566 + difference 0 1) (sourceB566 + difference 1 0) sourceC566) = raw9553 := by
      apply Matrix.ext; unfold tripleCharges sourceA566 sourceB566 sourceC566 difference raw9553; decide +kernel
    rw [ha]
    exact (canonical9553 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA566 + difference 0 2) (sourceB566 + difference 2 0) sourceC566) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3850) := by
    have ha : (tripleCharges (sourceA566 + difference 0 2) (sourceB566 + difference 2 0) sourceC566) = raw9554 := by
      apply Matrix.ext; unfold tripleCharges sourceA566 sourceB566 sourceC566 difference raw9554; decide +kernel
    rw [ha]
    exact (canonical9554 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA566 + difference 0 3) (sourceB566 + difference 3 0) sourceC566) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3850) := by
    have ha : (tripleCharges (sourceA566 + difference 0 3) (sourceB566 + difference 3 0) sourceC566) = raw9555 := by
      apply Matrix.ext; unfold tripleCharges sourceA566 sourceB566 sourceC566 difference raw9555; decide +kernel
    rw [ha]
    exact (canonical9555 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA566 + difference 0 4) (sourceB566 + difference 4 0) sourceC566) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3860) := by
    have ha : (tripleCharges (sourceA566 + difference 0 4) (sourceB566 + difference 4 0) sourceC566) = raw4873 := by
      apply Matrix.ext; unfold tripleCharges sourceA566 sourceB566 sourceC566 difference raw4873; decide +kernel
    rw [ha]
    exact (canonical4873 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA566 + difference 0 5) (sourceB566 + difference 5 0) sourceC566) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3888) := by
    have ha : (tripleCharges (sourceA566 + difference 0 5) (sourceB566 + difference 5 0) sourceC566) = raw9556 := by
      apply Matrix.ext; unfold tripleCharges sourceA566 sourceB566 sourceC566 difference raw9556; decide +kernel
    rw [ha]
    exact (canonical9556 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA566 + difference 1 0) (sourceB566 + difference 0 1) sourceC566) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3305) := by
    have ha : (tripleCharges (sourceA566 + difference 1 0) (sourceB566 + difference 0 1) sourceC566) = raw9557 := by
      apply Matrix.ext; unfold tripleCharges sourceA566 sourceB566 sourceC566 difference raw9557; decide +kernel
    rw [ha]
    exact (canonical9557 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA566 + difference 1 2) (sourceB566 + difference 2 1) sourceC566) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3564) := by
    have ha : (tripleCharges (sourceA566 + difference 1 2) (sourceB566 + difference 2 1) sourceC566) = raw9558 := by
      apply Matrix.ext; unfold tripleCharges sourceA566 sourceB566 sourceC566 difference raw9558; decide +kernel
    rw [ha]
    exact (canonical9558 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA566 + difference 1 3) (sourceB566 + difference 3 1) sourceC566) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3564) := by
    have ha : (tripleCharges (sourceA566 + difference 1 3) (sourceB566 + difference 3 1) sourceC566) = raw9559 := by
      apply Matrix.ext; unfold tripleCharges sourceA566 sourceB566 sourceC566 difference raw9559; decide +kernel
    rw [ha]
    exact (canonical9559 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA566 + difference 1 4) (sourceB566 + difference 4 1) sourceC566) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3547) := by
    have ha : (tripleCharges (sourceA566 + difference 1 4) (sourceB566 + difference 4 1) sourceC566) = raw4878 := by
      apply Matrix.ext; unfold tripleCharges sourceA566 sourceB566 sourceC566 difference raw4878; decide +kernel
    rw [ha]
    exact (canonical4878 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA566 + difference 1 5) (sourceB566 + difference 5 1) sourceC566) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3583) := by
    have ha : (tripleCharges (sourceA566 + difference 1 5) (sourceB566 + difference 5 1) sourceC566) = raw9560 := by
      apply Matrix.ext; unfold tripleCharges sourceA566 sourceB566 sourceC566 difference raw9560; decide +kernel
    rw [ha]
    exact (canonical9560 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA566 + difference 2 0) (sourceB566 + difference 0 2) sourceC566) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3296) := by
    have ha : (tripleCharges (sourceA566 + difference 2 0) (sourceB566 + difference 0 2) sourceC566) = raw9561 := by
      apply Matrix.ext; unfold tripleCharges sourceA566 sourceB566 sourceC566 difference raw9561; decide +kernel
    rw [ha]
    exact (canonical9561 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA566 + difference 2 1) (sourceB566 + difference 1 2) sourceC566) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3570) := by
    have ha : (tripleCharges (sourceA566 + difference 2 1) (sourceB566 + difference 1 2) sourceC566) = raw9562 := by
      apply Matrix.ext; unfold tripleCharges sourceA566 sourceB566 sourceC566 difference raw9562; decide +kernel
    rw [ha]
    exact (canonical9562 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA566 + difference 2 3) (sourceB566 + difference 3 2) sourceC566) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3557) := by
    have ha : (tripleCharges (sourceA566 + difference 2 3) (sourceB566 + difference 3 2) sourceC566) = raw9563 := by
      apply Matrix.ext; unfold tripleCharges sourceA566 sourceB566 sourceC566 difference raw9563; decide +kernel
    rw [ha]
    exact (canonical9563 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA566 + difference 2 4) (sourceB566 + difference 4 2) sourceC566) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3533) := by
    have ha : (tripleCharges (sourceA566 + difference 2 4) (sourceB566 + difference 4 2) sourceC566) = raw4883 := by
      apply Matrix.ext; unfold tripleCharges sourceA566 sourceB566 sourceC566 difference raw4883; decide +kernel
    rw [ha]
    exact (canonical4883 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA566 + difference 2 5) (sourceB566 + difference 5 2) sourceC566) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3572) := by
    have ha : (tripleCharges (sourceA566 + difference 2 5) (sourceB566 + difference 5 2) sourceC566) = raw9564 := by
      apply Matrix.ext; unfold tripleCharges sourceA566 sourceB566 sourceC566 difference raw9564; decide +kernel
    rw [ha]
    exact (canonical9564 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA566 + difference 3 0) (sourceB566 + difference 0 3) sourceC566) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3296) := by
    have ha : (tripleCharges (sourceA566 + difference 3 0) (sourceB566 + difference 0 3) sourceC566) = raw9565 := by
      apply Matrix.ext; unfold tripleCharges sourceA566 sourceB566 sourceC566 difference raw9565; decide +kernel
    rw [ha]
    exact (canonical9565 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA566 + difference 3 1) (sourceB566 + difference 1 3) sourceC566) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3570) := by
    have ha : (tripleCharges (sourceA566 + difference 3 1) (sourceB566 + difference 1 3) sourceC566) = raw9566 := by
      apply Matrix.ext; unfold tripleCharges sourceA566 sourceB566 sourceC566 difference raw9566; decide +kernel
    rw [ha]
    exact (canonical9566 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA566 + difference 3 2) (sourceB566 + difference 2 3) sourceC566) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3557) := by
    have ha : (tripleCharges (sourceA566 + difference 3 2) (sourceB566 + difference 2 3) sourceC566) = raw9567 := by
      apply Matrix.ext; unfold tripleCharges sourceA566 sourceB566 sourceC566 difference raw9567; decide +kernel
    rw [ha]
    exact (canonical9567 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA566 + difference 3 4) (sourceB566 + difference 4 3) sourceC566) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3533) := by
    have ha : (tripleCharges (sourceA566 + difference 3 4) (sourceB566 + difference 4 3) sourceC566) = raw4888 := by
      apply Matrix.ext; unfold tripleCharges sourceA566 sourceB566 sourceC566 difference raw4888; decide +kernel
    rw [ha]
    exact (canonical4888 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA566 + difference 3 5) (sourceB566 + difference 5 3) sourceC566) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3572) := by
    have ha : (tripleCharges (sourceA566 + difference 3 5) (sourceB566 + difference 5 3) sourceC566) = raw9568 := by
      apply Matrix.ext; unfold tripleCharges sourceA566 sourceB566 sourceC566 difference raw9568; decide +kernel
    rw [ha]
    exact (canonical9568 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA566 + difference 4 0) (sourceB566 + difference 0 4) sourceC566) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2683) := by
    have ha : (tripleCharges (sourceA566 + difference 4 0) (sourceB566 + difference 0 4) sourceC566) = raw9569 := by
      apply Matrix.ext; unfold tripleCharges sourceA566 sourceB566 sourceC566 difference raw9569; decide +kernel
    rw [ha]
    exact (canonical9569 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA566 + difference 4 1) (sourceB566 + difference 1 4) sourceC566) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2687) := by
    have ha : (tripleCharges (sourceA566 + difference 4 1) (sourceB566 + difference 1 4) sourceC566) = raw9570 := by
      apply Matrix.ext; unfold tripleCharges sourceA566 sourceB566 sourceC566 difference raw9570; decide +kernel
    rw [ha]
    exact (canonical9570 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA566 + difference 4 2) (sourceB566 + difference 2 4) sourceC566) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2681) := by
    have ha : (tripleCharges (sourceA566 + difference 4 2) (sourceB566 + difference 2 4) sourceC566) = raw9571 := by
      apply Matrix.ext; unfold tripleCharges sourceA566 sourceB566 sourceC566 difference raw9571; decide +kernel
    rw [ha]
    exact (canonical9571 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA566 + difference 4 3) (sourceB566 + difference 3 4) sourceC566) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2681) := by
    have ha : (tripleCharges (sourceA566 + difference 4 3) (sourceB566 + difference 3 4) sourceC566) = raw9572 := by
      apply Matrix.ext; unfold tripleCharges sourceA566 sourceB566 sourceC566 difference raw9572; decide +kernel
    rw [ha]
    exact (canonical9572 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA566 + difference 4 5) (sourceB566 + difference 5 4) sourceC566) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2781) := by
    have ha : (tripleCharges (sourceA566 + difference 4 5) (sourceB566 + difference 5 4) sourceC566) = raw9573 := by
      apply Matrix.ext; unfold tripleCharges sourceA566 sourceB566 sourceC566 difference raw9573; decide +kernel
    rw [ha]
    exact (canonical9573 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA566 + difference 5 0) (sourceB566 + difference 0 5) sourceC566) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3302) := by
    have ha : (tripleCharges (sourceA566 + difference 5 0) (sourceB566 + difference 0 5) sourceC566) = raw4889 := by
      apply Matrix.ext; unfold tripleCharges sourceA566 sourceB566 sourceC566 difference raw4889; decide +kernel
    rw [ha]
    exact (canonical4889 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA566 + difference 5 1) (sourceB566 + difference 1 5) sourceC566) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3579) := by
    have ha : (tripleCharges (sourceA566 + difference 5 1) (sourceB566 + difference 1 5) sourceC566) = raw4890 := by
      apply Matrix.ext; unfold tripleCharges sourceA566 sourceB566 sourceC566 difference raw4890; decide +kernel
    rw [ha]
    exact (canonical4890 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA566 + difference 5 2) (sourceB566 + difference 2 5) sourceC566) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3530) := by
    have ha : (tripleCharges (sourceA566 + difference 5 2) (sourceB566 + difference 2 5) sourceC566) = raw4891 := by
      apply Matrix.ext; unfold tripleCharges sourceA566 sourceB566 sourceC566 difference raw4891; decide +kernel
    rw [ha]
    exact (canonical4891 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA566 + difference 5 3) (sourceB566 + difference 3 5) sourceC566) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3530) := by
    have ha : (tripleCharges (sourceA566 + difference 5 3) (sourceB566 + difference 3 5) sourceC566) = raw4892 := by
      apply Matrix.ext; unfold tripleCharges sourceA566 sourceB566 sourceC566 difference raw4892; decide +kernel
    rw [ha]
    exact (canonical4892 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA566 + difference 5 4) (sourceB566 + difference 4 5) sourceC566) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3545) := by
    have ha : (tripleCharges (sourceA566 + difference 5 4) (sourceB566 + difference 4 5) sourceC566) = raw9574 := by
      apply Matrix.ext; unfold tripleCharges sourceA566 sourceB566 sourceC566 difference raw9574; decide +kernel
    rw [ha]
    exact (canonical9574 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA566 sourceB566 sourceC566
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm566, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq567 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm567 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA567 + difference 0 0) (sourceB567 + difference 0 0) sourceC567) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2765) := by
    have ha : (tripleCharges (sourceA567 + difference 0 0) (sourceB567 + difference 0 0) sourceC567) = raw9575 := by
      apply Matrix.ext; unfold tripleCharges sourceA567 sourceB567 sourceC567 difference raw9575; decide +kernel
    rw [ha]
    exact (canonical9575 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA567 + difference 0 1) (sourceB567 + difference 1 0) sourceC567) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3886) := by
    have ha : (tripleCharges (sourceA567 + difference 0 1) (sourceB567 + difference 1 0) sourceC567) = raw9576 := by
      apply Matrix.ext; unfold tripleCharges sourceA567 sourceB567 sourceC567 difference raw9576; decide +kernel
    rw [ha]
    exact (canonical9576 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA567 + difference 0 2) (sourceB567 + difference 2 0) sourceC567) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3850) := by
    have ha : (tripleCharges (sourceA567 + difference 0 2) (sourceB567 + difference 2 0) sourceC567) = raw9577 := by
      apply Matrix.ext; unfold tripleCharges sourceA567 sourceB567 sourceC567 difference raw9577; decide +kernel
    rw [ha]
    exact (canonical9577 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA567 + difference 0 3) (sourceB567 + difference 3 0) sourceC567) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3850) := by
    have ha : (tripleCharges (sourceA567 + difference 0 3) (sourceB567 + difference 3 0) sourceC567) = raw9578 := by
      apply Matrix.ext; unfold tripleCharges sourceA567 sourceB567 sourceC567 difference raw9578; decide +kernel
    rw [ha]
    exact (canonical9578 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA567 + difference 0 4) (sourceB567 + difference 4 0) sourceC567) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3905) := by
    have ha : (tripleCharges (sourceA567 + difference 0 4) (sourceB567 + difference 4 0) sourceC567) = raw4904 := by
      apply Matrix.ext; unfold tripleCharges sourceA567 sourceB567 sourceC567 difference raw4904; decide +kernel
    rw [ha]
    exact (canonical4904 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA567 + difference 0 5) (sourceB567 + difference 5 0) sourceC567) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3913) := by
    have ha : (tripleCharges (sourceA567 + difference 0 5) (sourceB567 + difference 5 0) sourceC567) = raw9579 := by
      apply Matrix.ext; unfold tripleCharges sourceA567 sourceB567 sourceC567 difference raw9579; decide +kernel
    rw [ha]
    exact (canonical9579 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA567 + sourceB567) sourceC567) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA567 + sourceB567) sourceC567) = raw4905 := by
      apply Matrix.ext; unfold doubleCharges sourceA567 sourceB567 sourceC567 raw4905; decide +kernel
    rw [ha]
    exact (canonical4905 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA567 sourceB567 sourceC567
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm567, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq568 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm568 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA568 + difference 0 0) (sourceB568 + difference 0 0) sourceC568) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2765) := by
    have ha : (tripleCharges (sourceA568 + difference 0 0) (sourceB568 + difference 0 0) sourceC568) = raw9575 := by
      apply Matrix.ext; unfold tripleCharges sourceA568 sourceB568 sourceC568 difference raw9575; decide +kernel
    rw [ha]
    exact (canonical9575 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA568 + difference 1 0) (sourceB568 + difference 0 1) sourceC568) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1294) := by
    have ha : (tripleCharges (sourceA568 + difference 1 0) (sourceB568 + difference 0 1) sourceC568) = raw9580 := by
      apply Matrix.ext; unfold tripleCharges sourceA568 sourceB568 sourceC568 difference raw9580; decide +kernel
    rw [ha]
    exact (canonical9580 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA568 + difference 2 0) (sourceB568 + difference 0 2) sourceC568) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1261) := by
    have ha : (tripleCharges (sourceA568 + difference 2 0) (sourceB568 + difference 0 2) sourceC568) = raw9581 := by
      apply Matrix.ext; unfold tripleCharges sourceA568 sourceB568 sourceC568 difference raw9581; decide +kernel
    rw [ha]
    exact (canonical9581 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA568 + difference 3 0) (sourceB568 + difference 0 3) sourceC568) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1261) := by
    have ha : (tripleCharges (sourceA568 + difference 3 0) (sourceB568 + difference 0 3) sourceC568) = raw9582 := by
      apply Matrix.ext; unfold tripleCharges sourceA568 sourceB568 sourceC568 difference raw9582; decide +kernel
    rw [ha]
    exact (canonical9582 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA568 + difference 4 0) (sourceB568 + difference 0 4) sourceC568) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1273) := by
    have ha : (tripleCharges (sourceA568 + difference 4 0) (sourceB568 + difference 0 4) sourceC568) = raw9583 := by
      apply Matrix.ext; unfold tripleCharges sourceA568 sourceB568 sourceC568 difference raw9583; decide +kernel
    rw [ha]
    exact (canonical9583 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA568 + difference 5 0) (sourceB568 + difference 0 5) sourceC568) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1264) := by
    have ha : (tripleCharges (sourceA568 + difference 5 0) (sourceB568 + difference 0 5) sourceC568) = raw4909 := by
      apply Matrix.ext; unfold tripleCharges sourceA568 sourceB568 sourceC568 difference raw4909; decide +kernel
    rw [ha]
    exact (canonical4909 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA568 + sourceB568) sourceC568) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA568 + sourceB568) sourceC568) = raw4905 := by
      apply Matrix.ext; unfold doubleCharges sourceA568 sourceB568 sourceC568 raw4905; decide +kernel
    rw [ha]
    exact (canonical4905 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA568 sourceB568 sourceC568
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm568, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq569 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm569 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA569 + difference 1 0) (sourceB569 + difference 0 1) sourceC569) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1294) := by
    have ha : (tripleCharges (sourceA569 + difference 1 0) (sourceB569 + difference 0 1) sourceC569) = raw9580 := by
      apply Matrix.ext; unfold tripleCharges sourceA569 sourceB569 sourceC569 difference raw9580; decide +kernel
    rw [ha]
    exact (canonical9580 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA569 + difference 1 1) (sourceB569 + difference 1 1) sourceC569) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2765) := by
    have ha : (tripleCharges (sourceA569 + difference 1 1) (sourceB569 + difference 1 1) sourceC569) = raw9575 := by
      apply Matrix.ext; unfold tripleCharges sourceA569 sourceB569 sourceC569 difference raw9575; decide +kernel
    rw [ha]
    exact (canonical9575 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA569 + difference 1 2) (sourceB569 + difference 2 1) sourceC569) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2590) := by
    have ha : (tripleCharges (sourceA569 + difference 1 2) (sourceB569 + difference 2 1) sourceC569) = raw9584 := by
      apply Matrix.ext; unfold tripleCharges sourceA569 sourceB569 sourceC569 difference raw9584; decide +kernel
    rw [ha]
    exact (canonical9584 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA569 + difference 1 3) (sourceB569 + difference 3 1) sourceC569) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2590) := by
    have ha : (tripleCharges (sourceA569 + difference 1 3) (sourceB569 + difference 3 1) sourceC569) = raw9585 := by
      apply Matrix.ext; unfold tripleCharges sourceA569 sourceB569 sourceC569 difference raw9585; decide +kernel
    rw [ha]
    exact (canonical9585 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA569 + difference 1 4) (sourceB569 + difference 4 1) sourceC569) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2742) := by
    have ha : (tripleCharges (sourceA569 + difference 1 4) (sourceB569 + difference 4 1) sourceC569) = raw4914 := by
      apply Matrix.ext; unfold tripleCharges sourceA569 sourceB569 sourceC569 difference raw4914; decide +kernel
    rw [ha]
    exact (canonical4914 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA569 + difference 1 5) (sourceB569 + difference 5 1) sourceC569) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2782) := by
    have ha : (tripleCharges (sourceA569 + difference 1 5) (sourceB569 + difference 5 1) sourceC569) = raw9586 := by
      apply Matrix.ext; unfold tripleCharges sourceA569 sourceB569 sourceC569 difference raw9586; decide +kernel
    rw [ha]
    exact (canonical9586 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA569 + sourceB569) sourceC569) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA569 + sourceB569) sourceC569) = raw4905 := by
      apply Matrix.ext; unfold doubleCharges sourceA569 sourceB569 sourceC569 raw4905; decide +kernel
    rw [ha]
    exact (canonical4905 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA569 sourceB569 sourceC569
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm569, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq570 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm570 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA570 + difference 0 1) (sourceB570 + difference 1 0) sourceC570) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3886) := by
    have ha : (tripleCharges (sourceA570 + difference 0 1) (sourceB570 + difference 1 0) sourceC570) = raw9576 := by
      apply Matrix.ext; unfold tripleCharges sourceA570 sourceB570 sourceC570 difference raw9576; decide +kernel
    rw [ha]
    exact (canonical9576 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA570 + difference 1 1) (sourceB570 + difference 1 1) sourceC570) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2765) := by
    have ha : (tripleCharges (sourceA570 + difference 1 1) (sourceB570 + difference 1 1) sourceC570) = raw9575 := by
      apply Matrix.ext; unfold tripleCharges sourceA570 sourceB570 sourceC570 difference raw9575; decide +kernel
    rw [ha]
    exact (canonical9575 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA570 + difference 2 1) (sourceB570 + difference 1 2) sourceC570) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2632) := by
    have ha : (tripleCharges (sourceA570 + difference 2 1) (sourceB570 + difference 1 2) sourceC570) = raw9587 := by
      apply Matrix.ext; unfold tripleCharges sourceA570 sourceB570 sourceC570 difference raw9587; decide +kernel
    rw [ha]
    exact (canonical9587 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA570 + difference 3 1) (sourceB570 + difference 1 3) sourceC570) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2632) := by
    have ha : (tripleCharges (sourceA570 + difference 3 1) (sourceB570 + difference 1 3) sourceC570) = raw9588 := by
      apply Matrix.ext; unfold tripleCharges sourceA570 sourceB570 sourceC570 difference raw9588; decide +kernel
    rw [ha]
    exact (canonical9588 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA570 + difference 4 1) (sourceB570 + difference 1 4) sourceC570) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2643) := by
    have ha : (tripleCharges (sourceA570 + difference 4 1) (sourceB570 + difference 1 4) sourceC570) = raw9589 := by
      apply Matrix.ext; unfold tripleCharges sourceA570 sourceB570 sourceC570 difference raw9589; decide +kernel
    rw [ha]
    exact (canonical9589 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA570 + difference 5 1) (sourceB570 + difference 1 5) sourceC570) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2635) := by
    have ha : (tripleCharges (sourceA570 + difference 5 1) (sourceB570 + difference 1 5) sourceC570) = raw4917 := by
      apply Matrix.ext; unfold tripleCharges sourceA570 sourceB570 sourceC570 difference raw4917; decide +kernel
    rw [ha]
    exact (canonical4917 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA570 + sourceB570) sourceC570) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA570 + sourceB570) sourceC570) = raw4905 := by
      apply Matrix.ext; unfold doubleCharges sourceA570 sourceB570 sourceC570 raw4905; decide +kernel
    rw [ha]
    exact (canonical4905 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA570 sourceB570 sourceC570
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm570, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic29
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reindexCheck464 : Integer.Sparse.reindex keyMap MixedData.row464 = numericRow464 := by decide +kernel

theorem numericCheck464 (x : Master → ℝ) : Integer.Sparse.eval numericRow464 x =
    (1 : ℝ) * reducedSource464 x := by
  norm_num [numericRow464, reducedSource464, Integer.Sparse.eval, Sparse.eval, nodeValue3075, nodeValue3525, nodeValue3534, nodeValue3581, nodeValue3623, nodeValue4083]

theorem reindexCheck465 : Integer.Sparse.reindex keyMap MixedData.row465 = numericRow465 := by decide +kernel

theorem numericCheck465 (x : Master → ℝ) : Integer.Sparse.eval numericRow465 x =
    (1 : ℝ) * reducedSource465 x := by
  norm_num [numericRow465, reducedSource465, Integer.Sparse.eval, Sparse.eval, nodeValue1382, nodeValue1385, nodeValue1390, nodeValue1404, nodeValue3075, nodeValue4083]

theorem reindexCheck466 : Integer.Sparse.reindex keyMap MixedData.row466 = numericRow466 := by decide +kernel

theorem numericCheck466 (x : Master → ℝ) : Integer.Sparse.eval numericRow466 x =
    (1 : ℝ) * reducedSource466 x := by
  norm_num [numericRow466, reducedSource466, Integer.Sparse.eval, Sparse.eval, nodeValue1382, nodeValue2923, nodeValue3073, nodeValue3075, nodeValue4083]

theorem reindexCheck467 : Integer.Sparse.reindex keyMap MixedData.row467 = numericRow467 := by decide +kernel

theorem numericCheck467 (x : Master → ℝ) : Integer.Sparse.eval numericRow467 x =
    (1 : ℝ) * reducedSource467 x := by
  norm_num [numericRow467, reducedSource467, Integer.Sparse.eval, Sparse.eval, nodeValue2009, nodeValue2980, nodeValue2983, nodeValue3075, nodeValue3525, nodeValue4083]

theorem reindexCheck468 : Integer.Sparse.reindex keyMap MixedData.row468 = numericRow468 := by decide +kernel

theorem numericCheck468 (x : Master → ℝ) : Integer.Sparse.eval numericRow468 x =
    (1 : ℝ) * reducedSource468 x := by
  norm_num [numericRow468, reducedSource468, Integer.Sparse.eval, Sparse.eval, nodeValue2025, nodeValue2923, nodeValue2930, nodeValue2952, nodeValue3075, nodeValue3534, nodeValue4083]

theorem reindexCheck469 : Integer.Sparse.reindex keyMap MixedData.row469 = numericRow469 := by decide +kernel

theorem numericCheck469 (x : Master → ℝ) : Integer.Sparse.eval numericRow469 x =
    (1 : ℝ) * reducedSource469 x := by
  norm_num [numericRow469, reducedSource469, Integer.Sparse.eval, Sparse.eval, nodeValue1390, nodeValue2930, nodeValue2980, nodeValue3075, nodeValue3079, nodeValue4083]

theorem reindexCheck471 : Integer.Sparse.reindex keyMap MixedData.row471 = numericRow471 := by decide +kernel

theorem numericCheck471 (x : Master → ℝ) : Integer.Sparse.eval numericRow471 x =
    (1 : ℝ) * reducedSource471 x := by
  norm_num [numericRow471, reducedSource471, Integer.Sparse.eval, Sparse.eval, nodeValue1234, nodeValue2509, nodeValue2552, nodeValue2738, nodeValue2740, nodeValue4084]

theorem reindexCheck472 : Integer.Sparse.reindex keyMap MixedData.row472 = numericRow472 := by decide +kernel

theorem numericCheck472 (x : Master → ℝ) : Integer.Sparse.eval numericRow472 x =
    (1 : ℝ) * reducedSource472 x := by
  norm_num [numericRow472, reducedSource472, Integer.Sparse.eval, Sparse.eval, nodeValue2131, nodeValue2132, nodeValue2133, nodeValue2277, nodeValue2738, nodeValue4084]

theorem reindexCheck475 : Integer.Sparse.reindex keyMap MixedData.row475 = numericRow475 := by decide +kernel

theorem numericCheck475 (x : Master → ℝ) : Integer.Sparse.eval numericRow475 x =
    (2160 : ℝ) * reducedSource475 x := by
  norm_num [numericRow475, reducedSource475, Integer.Sparse.eval, Sparse.eval, nodeValue2681, nodeValue2683, nodeValue2687, nodeValue2781, nodeValue3296, nodeValue3302, nodeValue3305, nodeValue3530, nodeValue3533, nodeValue3545, nodeValue3547, nodeValue3557, nodeValue3564, nodeValue3570, nodeValue3572, nodeValue3579, nodeValue3583, nodeValue3850, nodeValue3860, nodeValue3886, nodeValue3888]
  ring

theorem reindexCheck476 : Integer.Sparse.reindex keyMap MixedData.row476 = numericRow476 := by decide +kernel

theorem numericCheck476 (x : Master → ℝ) : Integer.Sparse.eval numericRow476 x =
    (1 : ℝ) * reducedSource476 x := by
  norm_num [numericRow476, reducedSource476, Integer.Sparse.eval, Sparse.eval, nodeValue2765, nodeValue3850, nodeValue3886, nodeValue3905, nodeValue3913, nodeValue4092]

theorem reindexCheck477 : Integer.Sparse.reindex keyMap MixedData.row477 = numericRow477 := by decide +kernel

theorem numericCheck477 (x : Master → ℝ) : Integer.Sparse.eval numericRow477 x =
    (1 : ℝ) * reducedSource477 x := by
  norm_num [numericRow477, reducedSource477, Integer.Sparse.eval, Sparse.eval, nodeValue1261, nodeValue1264, nodeValue1273, nodeValue1294, nodeValue2765, nodeValue4092]

theorem reindexCheck478 : Integer.Sparse.reindex keyMap MixedData.row478 = numericRow478 := by decide +kernel

theorem numericCheck478 (x : Master → ℝ) : Integer.Sparse.eval numericRow478 x =
    (1 : ℝ) * reducedSource478 x := by
  norm_num [numericRow478, reducedSource478, Integer.Sparse.eval, Sparse.eval, nodeValue1294, nodeValue2590, nodeValue2742, nodeValue2765, nodeValue2782, nodeValue4092]

theorem reindexCheck479 : Integer.Sparse.reindex keyMap MixedData.row479 = numericRow479 := by decide +kernel

theorem numericCheck479 (x : Master → ℝ) : Integer.Sparse.eval numericRow479 x =
    (1 : ℝ) * reducedSource479 x := by
  norm_num [numericRow479, reducedSource479, Integer.Sparse.eval, Sparse.eval, nodeValue2632, nodeValue2635, nodeValue2643, nodeValue2765, nodeValue3886, nodeValue4092]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Rows29
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero464 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource464 (mixedVector B) = 0 := by
  have h3075 : mixedVector B (Sum.inr 3075) = Sparse.eval nodeValue3075 (mixedVector B) := by
    change mixedMoment B node3075 node3075Labels = _
    exact sound3075 B hB hF
  have h3525 : mixedVector B (Sum.inr 3525) = Sparse.eval nodeValue3525 (mixedVector B) := by
    change mixedMoment B node3525 node3525Labels = _
    exact sound3525 B hB hF
  have h3534 : mixedVector B (Sum.inr 3534) = Sparse.eval nodeValue3534 (mixedVector B) := by
    change mixedMoment B node3534 node3534Labels = _
    exact sound3534 B hB hF
  have h3581 : mixedVector B (Sum.inr 3581) = Sparse.eval nodeValue3581 (mixedVector B) := by
    change mixedMoment B node3581 node3581Labels = _
    exact sound3581 B hB hF
  have h3623 : mixedVector B (Sum.inr 3623) = Sparse.eval nodeValue3623 (mixedVector B) := by
    change mixedMoment B node3623 node3623Labels = _
    exact sound3623 B hB hF
  have h4083 : mixedVector B (Sum.inr 4083) = Sparse.eval nodeValue4083 (mixedVector B) := by
    change mixedMoment B node4083 node4083Labels = _
    exact sound4083 B hB hF
  simpa only [sourceForm552, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h3075, h3525, h3534, h3581, h3623, h4083, reducedSource464] using sourceEq552 B hB

theorem rowSound464 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row464 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck464, numericCheck464, reducedZero464 B hB hF, mul_zero]

theorem reducedZero465 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource465 (mixedVector B) = 0 := by
  have h1382 : mixedVector B (Sum.inr 1382) = Sparse.eval nodeValue1382 (mixedVector B) := by
    change mixedMoment B node1382 node1382Labels = _
    exact sound1382 B hB hF
  have h1385 : mixedVector B (Sum.inr 1385) = Sparse.eval nodeValue1385 (mixedVector B) := by
    change mixedMoment B node1385 node1385Labels = _
    exact sound1385 B hB hF
  have h1390 : mixedVector B (Sum.inr 1390) = Sparse.eval nodeValue1390 (mixedVector B) := by
    change mixedMoment B node1390 node1390Labels = _
    exact sound1390 B hB hF
  have h1404 : mixedVector B (Sum.inr 1404) = Sparse.eval nodeValue1404 (mixedVector B) := by
    change mixedMoment B node1404 node1404Labels = _
    exact sound1404 B hB hF
  have h3075 : mixedVector B (Sum.inr 3075) = Sparse.eval nodeValue3075 (mixedVector B) := by
    change mixedMoment B node3075 node3075Labels = _
    exact sound3075 B hB hF
  have h4083 : mixedVector B (Sum.inr 4083) = Sparse.eval nodeValue4083 (mixedVector B) := by
    change mixedMoment B node4083 node4083Labels = _
    exact sound4083 B hB hF
  simpa only [sourceForm553, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1382, h1385, h1390, h1404, h3075, h4083, reducedSource465] using sourceEq553 B hB

theorem rowSound465 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row465 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck465, numericCheck465, reducedZero465 B hB hF, mul_zero]

theorem reducedZero466 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource466 (mixedVector B) = 0 := by
  have h1382 : mixedVector B (Sum.inr 1382) = Sparse.eval nodeValue1382 (mixedVector B) := by
    change mixedMoment B node1382 node1382Labels = _
    exact sound1382 B hB hF
  have h2923 : mixedVector B (Sum.inr 2923) = Sparse.eval nodeValue2923 (mixedVector B) := by
    change mixedMoment B node2923 node2923Labels = _
    exact sound2923 B hB hF
  have h3073 : mixedVector B (Sum.inr 3073) = Sparse.eval nodeValue3073 (mixedVector B) := by
    change mixedMoment B node3073 node3073Labels = _
    exact sound3073 B hB hF
  have h3075 : mixedVector B (Sum.inr 3075) = Sparse.eval nodeValue3075 (mixedVector B) := by
    change mixedMoment B node3075 node3075Labels = _
    exact sound3075 B hB hF
  have h4083 : mixedVector B (Sum.inr 4083) = Sparse.eval nodeValue4083 (mixedVector B) := by
    change mixedMoment B node4083 node4083Labels = _
    exact sound4083 B hB hF
  simpa only [sourceForm554, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1382, h2923, h3073, h3075, h4083, reducedSource466] using sourceEq554 B hB

theorem rowSound466 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row466 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck466, numericCheck466, reducedZero466 B hB hF, mul_zero]

theorem reducedZero467 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource467 (mixedVector B) = 0 := by
  have h2009 : mixedVector B (Sum.inr 2009) = Sparse.eval nodeValue2009 (mixedVector B) := by
    change mixedMoment B node2009 node2009Labels = _
    exact sound2009 B hB hF
  have h2980 : mixedVector B (Sum.inr 2980) = Sparse.eval nodeValue2980 (mixedVector B) := by
    change mixedMoment B node2980 node2980Labels = _
    exact sound2980 B hB hF
  have h2983 : mixedVector B (Sum.inr 2983) = Sparse.eval nodeValue2983 (mixedVector B) := by
    change mixedMoment B node2983 node2983Labels = _
    exact sound2983 B hB hF
  have h3075 : mixedVector B (Sum.inr 3075) = Sparse.eval nodeValue3075 (mixedVector B) := by
    change mixedMoment B node3075 node3075Labels = _
    exact sound3075 B hB hF
  have h3525 : mixedVector B (Sum.inr 3525) = Sparse.eval nodeValue3525 (mixedVector B) := by
    change mixedMoment B node3525 node3525Labels = _
    exact sound3525 B hB hF
  have h4083 : mixedVector B (Sum.inr 4083) = Sparse.eval nodeValue4083 (mixedVector B) := by
    change mixedMoment B node4083 node4083Labels = _
    exact sound4083 B hB hF
  simpa only [sourceForm555, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2009, h2980, h2983, h3075, h3525, h4083, reducedSource467] using sourceEq555 B hB

theorem rowSound467 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row467 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck467, numericCheck467, reducedZero467 B hB hF, mul_zero]

theorem reducedZero468 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource468 (mixedVector B) = 0 := by
  have h2025 : mixedVector B (Sum.inr 2025) = Sparse.eval nodeValue2025 (mixedVector B) := by
    change mixedMoment B node2025 node2025Labels = _
    exact sound2025 B hB hF
  have h2923 : mixedVector B (Sum.inr 2923) = Sparse.eval nodeValue2923 (mixedVector B) := by
    change mixedMoment B node2923 node2923Labels = _
    exact sound2923 B hB hF
  have h2930 : mixedVector B (Sum.inr 2930) = Sparse.eval nodeValue2930 (mixedVector B) := by
    change mixedMoment B node2930 node2930Labels = _
    exact sound2930 B hB hF
  have h2952 : mixedVector B (Sum.inr 2952) = Sparse.eval nodeValue2952 (mixedVector B) := by
    change mixedMoment B node2952 node2952Labels = _
    exact sound2952 B hB hF
  have h3075 : mixedVector B (Sum.inr 3075) = Sparse.eval nodeValue3075 (mixedVector B) := by
    change mixedMoment B node3075 node3075Labels = _
    exact sound3075 B hB hF
  have h3534 : mixedVector B (Sum.inr 3534) = Sparse.eval nodeValue3534 (mixedVector B) := by
    change mixedMoment B node3534 node3534Labels = _
    exact sound3534 B hB hF
  have h4083 : mixedVector B (Sum.inr 4083) = Sparse.eval nodeValue4083 (mixedVector B) := by
    change mixedMoment B node4083 node4083Labels = _
    exact sound4083 B hB hF
  simpa only [sourceForm556, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2025, h2923, h2930, h2952, h3075, h3534, h4083, reducedSource468] using sourceEq556 B hB

theorem rowSound468 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row468 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck468, numericCheck468, reducedZero468 B hB hF, mul_zero]

theorem reducedZero469 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource469 (mixedVector B) = 0 := by
  have h1390 : mixedVector B (Sum.inr 1390) = Sparse.eval nodeValue1390 (mixedVector B) := by
    change mixedMoment B node1390 node1390Labels = _
    exact sound1390 B hB hF
  have h2930 : mixedVector B (Sum.inr 2930) = Sparse.eval nodeValue2930 (mixedVector B) := by
    change mixedMoment B node2930 node2930Labels = _
    exact sound2930 B hB hF
  have h2980 : mixedVector B (Sum.inr 2980) = Sparse.eval nodeValue2980 (mixedVector B) := by
    change mixedMoment B node2980 node2980Labels = _
    exact sound2980 B hB hF
  have h3075 : mixedVector B (Sum.inr 3075) = Sparse.eval nodeValue3075 (mixedVector B) := by
    change mixedMoment B node3075 node3075Labels = _
    exact sound3075 B hB hF
  have h3079 : mixedVector B (Sum.inr 3079) = Sparse.eval nodeValue3079 (mixedVector B) := by
    change mixedMoment B node3079 node3079Labels = _
    exact sound3079 B hB hF
  have h4083 : mixedVector B (Sum.inr 4083) = Sparse.eval nodeValue4083 (mixedVector B) := by
    change mixedMoment B node4083 node4083Labels = _
    exact sound4083 B hB hF
  simpa only [sourceForm557, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1390, h2930, h2980, h3075, h3079, h4083, reducedSource469] using sourceEq557 B hB

theorem rowSound469 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row469 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck469, numericCheck469, reducedZero469 B hB hF, mul_zero]

theorem reducedZero471 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource471 (mixedVector B) = 0 := by
  have h1234 : mixedVector B (Sum.inr 1234) = Sparse.eval nodeValue1234 (mixedVector B) := by
    change mixedMoment B node1234 node1234Labels = _
    exact sound1234 B hB hF
  have h2509 : mixedVector B (Sum.inr 2509) = Sparse.eval nodeValue2509 (mixedVector B) := by
    change mixedMoment B node2509 node2509Labels = _
    exact sound2509 B hB hF
  have h2552 : mixedVector B (Sum.inr 2552) = Sparse.eval nodeValue2552 (mixedVector B) := by
    change mixedMoment B node2552 node2552Labels = _
    exact sound2552 B hB hF
  have h2738 : mixedVector B (Sum.inr 2738) = Sparse.eval nodeValue2738 (mixedVector B) := by
    change mixedMoment B node2738 node2738Labels = _
    exact sound2738 B hB hF
  have h2740 : mixedVector B (Sum.inr 2740) = Sparse.eval nodeValue2740 (mixedVector B) := by
    change mixedMoment B node2740 node2740Labels = _
    exact sound2740 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm561, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1234, h2509, h2552, h2738, h2740, h4084, reducedSource471] using sourceEq561 B hB

theorem rowSound471 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row471 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck471, numericCheck471, reducedZero471 B hB hF, mul_zero]

theorem reducedZero472 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource472 (mixedVector B) = 0 := by
  have h2131 : mixedVector B (Sum.inr 2131) = Sparse.eval nodeValue2131 (mixedVector B) := by
    change mixedMoment B node2131 node2131Labels = _
    exact sound2131 B hB hF
  have h2132 : mixedVector B (Sum.inr 2132) = Sparse.eval nodeValue2132 (mixedVector B) := by
    change mixedMoment B node2132 node2132Labels = _
    exact sound2132 B hB hF
  have h2133 : mixedVector B (Sum.inr 2133) = Sparse.eval nodeValue2133 (mixedVector B) := by
    change mixedMoment B node2133 node2133Labels = _
    exact sound2133 B hB hF
  have h2277 : mixedVector B (Sum.inr 2277) = Sparse.eval nodeValue2277 (mixedVector B) := by
    change mixedMoment B node2277 node2277Labels = _
    exact sound2277 B hB hF
  have h2738 : mixedVector B (Sum.inr 2738) = Sparse.eval nodeValue2738 (mixedVector B) := by
    change mixedMoment B node2738 node2738Labels = _
    exact sound2738 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm562, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2131, h2132, h2133, h2277, h2738, h4084, reducedSource472] using sourceEq562 B hB

theorem rowSound472 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row472 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck472, numericCheck472, reducedZero472 B hB hF, mul_zero]

theorem reducedZero475 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource475 (mixedVector B) = 0 := by
  have h2681 : mixedVector B (Sum.inr 2681) = Sparse.eval nodeValue2681 (mixedVector B) := by
    change mixedMoment B node2681 node2681Labels = _
    exact sound2681 B hB hF
  have h2683 : mixedVector B (Sum.inr 2683) = Sparse.eval nodeValue2683 (mixedVector B) := by
    change mixedMoment B node2683 node2683Labels = _
    exact sound2683 B hB hF
  have h2687 : mixedVector B (Sum.inr 2687) = Sparse.eval nodeValue2687 (mixedVector B) := by
    change mixedMoment B node2687 node2687Labels = _
    exact sound2687 B hB hF
  have h2781 : mixedVector B (Sum.inr 2781) = Sparse.eval nodeValue2781 (mixedVector B) := by
    change mixedMoment B node2781 node2781Labels = _
    exact sound2781 B hB hF
  have h3296 : mixedVector B (Sum.inr 3296) = Sparse.eval nodeValue3296 (mixedVector B) := by
    change mixedMoment B node3296 node3296Labels = _
    exact sound3296 B hB hF
  have h3302 : mixedVector B (Sum.inr 3302) = Sparse.eval nodeValue3302 (mixedVector B) := by
    change mixedMoment B node3302 node3302Labels = _
    exact sound3302 B hB hF
  have h3305 : mixedVector B (Sum.inr 3305) = Sparse.eval nodeValue3305 (mixedVector B) := by
    change mixedMoment B node3305 node3305Labels = _
    exact sound3305 B hB hF
  have h3530 : mixedVector B (Sum.inr 3530) = Sparse.eval nodeValue3530 (mixedVector B) := by
    change mixedMoment B node3530 node3530Labels = _
    exact sound3530 B hB hF
  have h3533 : mixedVector B (Sum.inr 3533) = Sparse.eval nodeValue3533 (mixedVector B) := by
    change mixedMoment B node3533 node3533Labels = _
    exact sound3533 B hB hF
  have h3545 : mixedVector B (Sum.inr 3545) = Sparse.eval nodeValue3545 (mixedVector B) := by
    change mixedMoment B node3545 node3545Labels = _
    exact sound3545 B hB hF
  have h3547 : mixedVector B (Sum.inr 3547) = Sparse.eval nodeValue3547 (mixedVector B) := by
    change mixedMoment B node3547 node3547Labels = _
    exact sound3547 B hB hF
  have h3557 : mixedVector B (Sum.inr 3557) = Sparse.eval nodeValue3557 (mixedVector B) := by
    change mixedMoment B node3557 node3557Labels = _
    exact sound3557 B hB hF
  have h3564 : mixedVector B (Sum.inr 3564) = Sparse.eval nodeValue3564 (mixedVector B) := by
    change mixedMoment B node3564 node3564Labels = _
    exact sound3564 B hB hF
  have h3570 : mixedVector B (Sum.inr 3570) = Sparse.eval nodeValue3570 (mixedVector B) := by
    change mixedMoment B node3570 node3570Labels = _
    exact sound3570 B hB hF
  have h3572 : mixedVector B (Sum.inr 3572) = Sparse.eval nodeValue3572 (mixedVector B) := by
    change mixedMoment B node3572 node3572Labels = _
    exact sound3572 B hB hF
  have h3579 : mixedVector B (Sum.inr 3579) = Sparse.eval nodeValue3579 (mixedVector B) := by
    change mixedMoment B node3579 node3579Labels = _
    exact sound3579 B hB hF
  have h3583 : mixedVector B (Sum.inr 3583) = Sparse.eval nodeValue3583 (mixedVector B) := by
    change mixedMoment B node3583 node3583Labels = _
    exact sound3583 B hB hF
  have h3850 : mixedVector B (Sum.inr 3850) = Sparse.eval nodeValue3850 (mixedVector B) := by
    change mixedMoment B node3850 node3850Labels = _
    exact sound3850 B hB hF
  have h3860 : mixedVector B (Sum.inr 3860) = Sparse.eval nodeValue3860 (mixedVector B) := by
    change mixedMoment B node3860 node3860Labels = _
    exact sound3860 B hB hF
  have h3886 : mixedVector B (Sum.inr 3886) = Sparse.eval nodeValue3886 (mixedVector B) := by
    change mixedMoment B node3886 node3886Labels = _
    exact sound3886 B hB hF
  have h3888 : mixedVector B (Sum.inr 3888) = Sparse.eval nodeValue3888 (mixedVector B) := by
    change mixedMoment B node3888 node3888Labels = _
    exact sound3888 B hB hF
  simpa only [sourceForm566, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2681, h2683, h2687, h2781, h3296, h3302, h3305, h3530, h3533, h3545, h3547, h3557, h3564, h3570, h3572, h3579, h3583, h3850, h3860, h3886, h3888, reducedSource475] using sourceEq566 B hB

theorem rowSound475 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row475 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck475, numericCheck475, reducedZero475 B hB hF, mul_zero]

theorem reducedZero476 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource476 (mixedVector B) = 0 := by
  have h2765 : mixedVector B (Sum.inr 2765) = Sparse.eval nodeValue2765 (mixedVector B) := by
    change mixedMoment B node2765 node2765Labels = _
    exact sound2765 B hB hF
  have h3850 : mixedVector B (Sum.inr 3850) = Sparse.eval nodeValue3850 (mixedVector B) := by
    change mixedMoment B node3850 node3850Labels = _
    exact sound3850 B hB hF
  have h3886 : mixedVector B (Sum.inr 3886) = Sparse.eval nodeValue3886 (mixedVector B) := by
    change mixedMoment B node3886 node3886Labels = _
    exact sound3886 B hB hF
  have h3905 : mixedVector B (Sum.inr 3905) = Sparse.eval nodeValue3905 (mixedVector B) := by
    change mixedMoment B node3905 node3905Labels = _
    exact sound3905 B hB hF
  have h3913 : mixedVector B (Sum.inr 3913) = Sparse.eval nodeValue3913 (mixedVector B) := by
    change mixedMoment B node3913 node3913Labels = _
    exact sound3913 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm567, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2765, h3850, h3886, h3905, h3913, h4092, reducedSource476] using sourceEq567 B hB

theorem rowSound476 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row476 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck476, numericCheck476, reducedZero476 B hB hF, mul_zero]

theorem reducedZero477 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource477 (mixedVector B) = 0 := by
  have h1261 : mixedVector B (Sum.inr 1261) = Sparse.eval nodeValue1261 (mixedVector B) := by
    change mixedMoment B node1261 node1261Labels = _
    exact sound1261 B hB hF
  have h1264 : mixedVector B (Sum.inr 1264) = Sparse.eval nodeValue1264 (mixedVector B) := by
    change mixedMoment B node1264 node1264Labels = _
    exact sound1264 B hB hF
  have h1273 : mixedVector B (Sum.inr 1273) = Sparse.eval nodeValue1273 (mixedVector B) := by
    change mixedMoment B node1273 node1273Labels = _
    exact sound1273 B hB hF
  have h1294 : mixedVector B (Sum.inr 1294) = Sparse.eval nodeValue1294 (mixedVector B) := by
    change mixedMoment B node1294 node1294Labels = _
    exact sound1294 B hB hF
  have h2765 : mixedVector B (Sum.inr 2765) = Sparse.eval nodeValue2765 (mixedVector B) := by
    change mixedMoment B node2765 node2765Labels = _
    exact sound2765 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm568, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1261, h1264, h1273, h1294, h2765, h4092, reducedSource477] using sourceEq568 B hB

theorem rowSound477 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row477 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck477, numericCheck477, reducedZero477 B hB hF, mul_zero]

theorem reducedZero478 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource478 (mixedVector B) = 0 := by
  have h1294 : mixedVector B (Sum.inr 1294) = Sparse.eval nodeValue1294 (mixedVector B) := by
    change mixedMoment B node1294 node1294Labels = _
    exact sound1294 B hB hF
  have h2590 : mixedVector B (Sum.inr 2590) = Sparse.eval nodeValue2590 (mixedVector B) := by
    change mixedMoment B node2590 node2590Labels = _
    exact sound2590 B hB hF
  have h2742 : mixedVector B (Sum.inr 2742) = Sparse.eval nodeValue2742 (mixedVector B) := by
    change mixedMoment B node2742 node2742Labels = _
    exact sound2742 B hB hF
  have h2765 : mixedVector B (Sum.inr 2765) = Sparse.eval nodeValue2765 (mixedVector B) := by
    change mixedMoment B node2765 node2765Labels = _
    exact sound2765 B hB hF
  have h2782 : mixedVector B (Sum.inr 2782) = Sparse.eval nodeValue2782 (mixedVector B) := by
    change mixedMoment B node2782 node2782Labels = _
    exact sound2782 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm569, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1294, h2590, h2742, h2765, h2782, h4092, reducedSource478] using sourceEq569 B hB

theorem rowSound478 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row478 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck478, numericCheck478, reducedZero478 B hB hF, mul_zero]

theorem reducedZero479 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource479 (mixedVector B) = 0 := by
  have h2632 : mixedVector B (Sum.inr 2632) = Sparse.eval nodeValue2632 (mixedVector B) := by
    change mixedMoment B node2632 node2632Labels = _
    exact sound2632 B hB hF
  have h2635 : mixedVector B (Sum.inr 2635) = Sparse.eval nodeValue2635 (mixedVector B) := by
    change mixedMoment B node2635 node2635Labels = _
    exact sound2635 B hB hF
  have h2643 : mixedVector B (Sum.inr 2643) = Sparse.eval nodeValue2643 (mixedVector B) := by
    change mixedMoment B node2643 node2643Labels = _
    exact sound2643 B hB hF
  have h2765 : mixedVector B (Sum.inr 2765) = Sparse.eval nodeValue2765 (mixedVector B) := by
    change mixedMoment B node2765 node2765Labels = _
    exact sound2765 B hB hF
  have h3886 : mixedVector B (Sum.inr 3886) = Sparse.eval nodeValue3886 (mixedVector B) := by
    change mixedMoment B node3886 node3886Labels = _
    exact sound3886 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm570, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2632, h2635, h2643, h2765, h3886, h4092, reducedSource479] using sourceEq570 B hB

theorem rowSound479 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row479 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck479, numericCheck479, reducedZero479 B hB hF, mul_zero]

theorem sourceRowsAt464 : MixedData.sourceRows (464 : Fin 2425) =
    MixedData.row464 := by decide +kernel

theorem sourceRowsAt465 : MixedData.sourceRows (465 : Fin 2425) =
    MixedData.row465 := by decide +kernel

theorem sourceRowsAt466 : MixedData.sourceRows (466 : Fin 2425) =
    MixedData.row466 := by decide +kernel

theorem sourceRowsAt467 : MixedData.sourceRows (467 : Fin 2425) =
    MixedData.row467 := by decide +kernel

theorem sourceRowsAt468 : MixedData.sourceRows (468 : Fin 2425) =
    MixedData.row468 := by decide +kernel

theorem sourceRowsAt469 : MixedData.sourceRows (469 : Fin 2425) =
    MixedData.row469 := by decide +kernel

theorem sourceRowsAt470 : MixedData.sourceRows (470 : Fin 2425) =
    MixedData.row470 := by decide +kernel

theorem sourceRowsAt471 : MixedData.sourceRows (471 : Fin 2425) =
    MixedData.row471 := by decide +kernel

theorem sourceRowsAt472 : MixedData.sourceRows (472 : Fin 2425) =
    MixedData.row472 := by decide +kernel

theorem sourceRowsAt473 : MixedData.sourceRows (473 : Fin 2425) =
    MixedData.row473 := by decide +kernel

theorem sourceRowsAt474 : MixedData.sourceRows (474 : Fin 2425) =
    MixedData.row474 := by decide +kernel

theorem sourceRowsAt475 : MixedData.sourceRows (475 : Fin 2425) =
    MixedData.row475 := by decide +kernel

theorem sourceRowsAt476 : MixedData.sourceRows (476 : Fin 2425) =
    MixedData.row476 := by decide +kernel

theorem sourceRowsAt477 : MixedData.sourceRows (477 : Fin 2425) =
    MixedData.row477 := by decide +kernel

theorem sourceRowsAt478 : MixedData.sourceRows (478 : Fin 2425) =
    MixedData.row478 := by decide +kernel

theorem sourceRowsAt479 : MixedData.sourceRows (479 : Fin 2425) =
    MixedData.row479 := by decide +kernel

theorem chunkSound29_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) (k : Fin 2425)
    (hk : k.val / 16 = 29) :
    Integer.Sparse.eval (MixedData.sourceRows k) (numericVector B) = 0 := by
  have heq : k.val = 464 ∨ k.val = 465 ∨ k.val = 466 ∨ k.val = 467 ∨ k.val = 468 ∨ k.val = 469 ∨ k.val = 470 ∨ k.val = 471 ∨ k.val = 472 ∨ k.val = 473 ∨ k.val = 474 ∨ k.val = 475 ∨ k.val = 476 ∨ k.val = 477 ∨ k.val = 478 ∨ k.val = 479 := by omega
  rcases heq with h464 | h465 | h466 | h467 | h468 | h469 | h470 | h471 | h472 | h473 | h474 | h475 | h476 | h477 | h478 | h479
  · have he : k = (464 : Fin 2425) := Fin.ext h464
    subst k
    rw [sourceRowsAt464]
    exact rowSound464 B hB hF
  · have he : k = (465 : Fin 2425) := Fin.ext h465
    subst k
    rw [sourceRowsAt465]
    exact rowSound465 B hB hF
  · have he : k = (466 : Fin 2425) := Fin.ext h466
    subst k
    rw [sourceRowsAt466]
    exact rowSound466 B hB hF
  · have he : k = (467 : Fin 2425) := Fin.ext h467
    subst k
    rw [sourceRowsAt467]
    exact rowSound467 B hB hF
  · have he : k = (468 : Fin 2425) := Fin.ext h468
    subst k
    rw [sourceRowsAt468]
    exact rowSound468 B hB hF
  · have he : k = (469 : Fin 2425) := Fin.ext h469
    subst k
    rw [sourceRowsAt469]
    exact rowSound469 B hB hF
  · have he : k = (470 : Fin 2425) := Fin.ext h470
    subst k
    rw [sourceRowsAt470]
    exact rowSound470_e B hB hF
  · have he : k = (471 : Fin 2425) := Fin.ext h471
    subst k
    rw [sourceRowsAt471]
    exact rowSound471 B hB hF
  · have he : k = (472 : Fin 2425) := Fin.ext h472
    subst k
    rw [sourceRowsAt472]
    exact rowSound472 B hB hF
  · have he : k = (473 : Fin 2425) := Fin.ext h473
    subst k
    rw [sourceRowsAt473]
    exact rowSound473_e B hB hF
  · have he : k = (474 : Fin 2425) := Fin.ext h474
    subst k
    rw [sourceRowsAt474]
    exact rowSound474_e B hB hF
  · have he : k = (475 : Fin 2425) := Fin.ext h475
    subst k
    rw [sourceRowsAt475]
    exact rowSound475 B hB hF
  · have he : k = (476 : Fin 2425) := Fin.ext h476
    subst k
    rw [sourceRowsAt476]
    exact rowSound476 B hB hF
  · have he : k = (477 : Fin 2425) := Fin.ext h477
    subst k
    rw [sourceRowsAt477]
    exact rowSound477 B hB hF
  · have he : k = (478 : Fin 2425) := Fin.ext h478
    subst k
    rw [sourceRowsAt478]
    exact rowSound478 B hB hF
  · have he : k = (479 : Fin 2425) := Fin.ext h479
    subst k
    rw [sourceRowsAt479]
    exact rowSound479 B hB hF

end MUB6.Certificate.MixedSourceBridge

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedSourceBridge.chunkSound29_e_oai := @OAI.MUB6.Certificate.MixedSourceBridge.chunkSound29_e_oai
