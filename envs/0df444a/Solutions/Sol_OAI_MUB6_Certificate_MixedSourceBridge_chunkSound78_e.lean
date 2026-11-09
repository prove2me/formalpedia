-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedSourceBridge.chunkSound78_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T04:34:46.401097+00:00
-- url     : https://prove2.me/submissions/ada776df-9a53-4336-9087-a13c7c7c74b2

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E077
import Definitions.Def_OAIQ106E086
import Definitions.Def_OAIQ106E089
import Definitions.Def_OAIQ106E090
import Definitions.Def_OAIQ106E096
import Definitions.Def_OAIQ106E098
import Definitions.Def_OAIQ106E190
import Definitions.Def_OAIQ106E113
import Definitions.Def_OAIQ106E118
import Definitions.Def_OAIQ106E119
import Definitions.Def_OAIQ106E120
import Definitions.Def_OAIQ106E124
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
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound1261_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound1262_e

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical92 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw92 raw92Labels = mixedMoment B node1312 node1312Labels := by
  calc
    mixedMoment B raw92 raw92Labels = mixedMoment B raw92step0 raw92step0Labels := by
      have ha : raw92step0 = (fun i j => raw92 (permutation2 i) (permutation5 j)) := by apply Matrix.ext; unfold raw92step0 raw92; decide +kernel
      have hl : raw92step0Labels = raw92Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw92 raw92Labels permutation2 permutation5
    mixedMoment B raw92step0 raw92step0Labels = mixedMoment B raw92step1 raw92step1Labels := by
      have ha : raw92step1 = raw92step0 := by apply Matrix.ext; unfold raw92step1 raw92step0; decide +kernel
      have hl : raw92step0Labels = labelEmbedding1 ∘ raw92step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw92step0 raw92step0Labels raw92step1Labels labelEmbedding1 hl
    _ = mixedMoment B node1312 node1312Labels := by rfl

theorem canonical93 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw93 raw93Labels = mixedMoment B node161 node161Labels := by
  calc
    mixedMoment B raw93 raw93Labels = mixedMoment B raw93step0 raw93step0Labels := by
      have ha : raw93step0 = (fun i j => raw93 (permutation2 i) (permutation4 j)) := by apply Matrix.ext; unfold raw93step0 raw93; decide +kernel
      have hl : raw93step0Labels = raw93Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw93 raw93Labels permutation2 permutation4
    _ = mixedMoment B node161 node161Labels := by rfl

end MUB6.Certificate.MixedSemantics

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

theorem canonical1308 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1308 raw1308Labels = mixedMoment B node4510 node4510Labels := by
  calc
    mixedMoment B raw1308 raw1308Labels = mixedMoment B raw1308step0 raw1308step0Labels := by
      have ha : raw1308step0 = (fun i j => raw1308 (permutation2 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1308step0 raw1308; decide +kernel
      have hl : raw1308step0Labels = raw1308Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1308 raw1308Labels permutation2 permutation4
    mixedMoment B raw1308step0 raw1308step0Labels = mixedMoment B raw1308step1 raw1308step1Labels := by
      have ha : raw1308step1 = raw1308step0 := by apply Matrix.ext; unfold raw1308step1 raw1308step0; decide +kernel
      have hl : raw1308step0Labels = labelEmbedding7 ∘ raw1308step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1308step0 raw1308step0Labels raw1308step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4510 node4510Labels := by rfl

theorem canonical1309 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1309 raw1309Labels = mixedMoment B node1094 node1094Labels := by
  calc
    mixedMoment B raw1309 raw1309Labels = mixedMoment B raw1309step0 raw1309step0Labels := by
      have ha : raw1309step0 = (fun i j => raw1309 (permutation2 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1309step0 raw1309; decide +kernel
      have hl : raw1309step0Labels = raw1309Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1309 raw1309Labels permutation2 permutation4
    _ = mixedMoment B node1094 node1094Labels := by rfl

theorem canonical1310 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1310 raw1310Labels = mixedMoment B node1741 node1741Labels := by
  calc
    mixedMoment B raw1310 raw1310Labels = mixedMoment B raw1310step0 raw1310step0Labels := by
      have ha : raw1310step0 = (fun i j => raw1310 (permutation2 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1310step0 raw1310; decide +kernel
      have hl : raw1310step0Labels = raw1310Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1310 raw1310Labels permutation2 permutation6
    mixedMoment B raw1310step0 raw1310step0Labels = mixedMoment B raw1310step1 raw1310step1Labels := by
      have ha : raw1310step1 = -raw1310step0 := by apply Matrix.ext; change ∀ i j, raw1310step1 i j = -(raw1310step0 i j); unfold raw1310step1 raw1310step0; decide +kernel
      have hl : raw1310step1Labels = raw1310step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1310step1 raw1310step1Labels = mixedMoment B raw1310step2 raw1310step2Labels := by
      have ha : raw1310step2 = raw1310step1 := by apply Matrix.ext; unfold raw1310step2 raw1310step1; decide +kernel
      have hl : raw1310step1Labels = labelEmbedding1 ∘ raw1310step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1310step1 raw1310step1Labels raw1310step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1741 node1741Labels := by rfl

end MUB6.Certificate.MixedSemantics

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

theorem canonical1437 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1437 raw1437Labels = mixedMoment B node4612 node4612Labels := by
  calc
    mixedMoment B raw1437 raw1437Labels = mixedMoment B raw1437step0 raw1437step0Labels := by
      have ha : raw1437step0 = (fun i j => raw1437 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1437step0 raw1437; decide +kernel
      have hl : raw1437step0Labels = raw1437Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1437 raw1437Labels permutation8 permutation4
    mixedMoment B raw1437step0 raw1437step0Labels = mixedMoment B raw1437step1 raw1437step1Labels := by
      have ha : raw1437step1 = raw1437step0 := by apply Matrix.ext; unfold raw1437step1 raw1437step0; decide +kernel
      have hl : raw1437step0Labels = labelEmbedding7 ∘ raw1437step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1437step0 raw1437step0Labels raw1437step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4612 node4612Labels := by rfl

theorem canonical1438 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1438 raw1438Labels = mixedMoment B node1246 node1246Labels := by
  calc
    mixedMoment B raw1438 raw1438Labels = mixedMoment B raw1438step0 raw1438step0Labels := by
      have ha : raw1438step0 = (fun i j => raw1438 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1438step0 raw1438; decide +kernel
      have hl : raw1438step0Labels = raw1438Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1438 raw1438Labels permutation8 permutation4
    _ = mixedMoment B node1246 node1246Labels := by rfl

theorem canonical1439 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1439 raw1439Labels = mixedMoment B node3301 node3301Labels := by
  calc
    mixedMoment B raw1439 raw1439Labels = mixedMoment B raw1439step0 raw1439step0Labels := by
      have ha : raw1439step0 = (fun i j => raw1439 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1439step0 raw1439; decide +kernel
      have hl : raw1439step0Labels = raw1439Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1439 raw1439Labels permutation8 permutation6
    mixedMoment B raw1439step0 raw1439step0Labels = mixedMoment B raw1439step1 raw1439step1Labels := by
      have ha : raw1439step1 = -raw1439step0 := by apply Matrix.ext; change ∀ i j, raw1439step1 i j = -(raw1439step0 i j); unfold raw1439step1 raw1439step0; decide +kernel
      have hl : raw1439step1Labels = raw1439step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1439step1 raw1439step1Labels = mixedMoment B raw1439step2 raw1439step2Labels := by
      have ha : raw1439step2 = raw1439step1 := by apply Matrix.ext; unfold raw1439step2 raw1439step1; decide +kernel
      have hl : raw1439step1Labels = labelEmbedding1 ∘ raw1439step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1439step1 raw1439step1Labels raw1439step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3301 node3301Labels := by rfl

theorem canonical1464 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1464 raw1464Labels = mixedMoment B node4628 node4628Labels := by
  calc
    mixedMoment B raw1464 raw1464Labels = mixedMoment B raw1464step0 raw1464step0Labels := by
      have ha : raw1464step0 = (fun i j => raw1464 (permutation2 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1464step0 raw1464; decide +kernel
      have hl : raw1464step0Labels = raw1464Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1464 raw1464Labels permutation2 permutation4
    mixedMoment B raw1464step0 raw1464step0Labels = mixedMoment B raw1464step1 raw1464step1Labels := by
      have ha : raw1464step1 = raw1464step0 := by apply Matrix.ext; unfold raw1464step1 raw1464step0; decide +kernel
      have hl : raw1464step0Labels = labelEmbedding7 ∘ raw1464step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1464step0 raw1464step0Labels raw1464step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4628 node4628Labels := by rfl

theorem canonical1465 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1465 raw1465Labels = mixedMoment B node1312 node1312Labels := by
  calc
    mixedMoment B raw1465 raw1465Labels = mixedMoment B raw1465step0 raw1465step0Labels := by
      have ha : raw1465step0 = (fun i j => raw1465 (permutation2 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1465step0 raw1465; decide +kernel
      have hl : raw1465step0Labels = raw1465Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1465 raw1465Labels permutation2 permutation4
    _ = mixedMoment B node1312 node1312Labels := by rfl

theorem canonical1466 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1466 raw1466Labels = mixedMoment B node3312 node3312Labels := by
  calc
    mixedMoment B raw1466 raw1466Labels = mixedMoment B raw1466step0 raw1466step0Labels := by
      have ha : raw1466step0 = (fun i j => raw1466 (permutation2 i) (permutation3 j)) := by apply Matrix.ext; unfold raw1466step0 raw1466; decide +kernel
      have hl : raw1466step0Labels = raw1466Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1466 raw1466Labels permutation2 permutation3
    mixedMoment B raw1466step0 raw1466step0Labels = mixedMoment B raw1466step1 raw1466step1Labels := by
      have ha : raw1466step1 = -raw1466step0 := by apply Matrix.ext; change ∀ i j, raw1466step1 i j = -(raw1466step0 i j); unfold raw1466step1 raw1466step0; decide +kernel
      have hl : raw1466step1Labels = raw1466step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1466step1 raw1466step1Labels = mixedMoment B raw1466step2 raw1466step2Labels := by
      have ha : raw1466step2 = raw1466step1 := by apply Matrix.ext; unfold raw1466step2 raw1466step1; decide +kernel
      have hl : raw1466step1Labels = labelEmbedding1 ∘ raw1466step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1466step1 raw1466step1Labels raw1466step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3312 node3312Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical158
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical20281 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20281 raw20281Labels = mixedMoment B node1119 node1119Labels := by
  calc
    mixedMoment B raw20281 raw20281Labels = mixedMoment B raw20281step0 raw20281step0Labels := by
      have hz : ∀ j, raw20281 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20281step0 = (fun i j => raw20281 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20281step0 raw20281; decide +kernel
      have hl : raw20281step0Labels = raw20281Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20281 raw20281Labels permutation346 hz
    _ = mixedMoment B node1119 node1119Labels := by rfl

theorem canonical20283 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20283 raw20283Labels = mixedMoment B node4092 node4092Labels := by
  calc
    mixedMoment B raw20283 raw20283Labels = mixedMoment B raw20283step0 raw20283step0Labels := by
      have hz : ∀ j, raw20283 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw20283step0 = (fun i j => raw20283 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw20283step0 raw20283; decide +kernel
      have hl : raw20283step0Labels = raw20283Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20283 raw20283Labels permutation520 hz
    mixedMoment B raw20283step0 raw20283step0Labels = mixedMoment B raw20283step1 raw20283step1Labels := by
      have hz : ∀ j, raw20283step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20283step1 = (fun i j => raw20283step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20283step1 raw20283step0; decide +kernel
      have hl : raw20283step1Labels = raw20283step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20283step0 raw20283step0Labels permutation80 hz
    _ = mixedMoment B node4092 node4092Labels := by rfl

theorem canonical20287 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20287 raw20287Labels = mixedMoment B node1236 node1236Labels := by
  calc
    mixedMoment B raw20287 raw20287Labels = mixedMoment B raw20287step0 raw20287step0Labels := by
      have hz : ∀ j, raw20287 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20287step0 = (fun i j => raw20287 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20287step0 raw20287; decide +kernel
      have hl : raw20287step0Labels = raw20287Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20287 raw20287Labels permutation346 hz
    mixedMoment B raw20287step0 raw20287step0Labels = mixedMoment B raw20287step1 raw20287step1Labels := by
      have ha : raw20287step1 = (fun i j => raw20287step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20287step1 raw20287step0; decide +kernel
      have hl : raw20287step1Labels = raw20287step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20287step0 raw20287step0Labels permutation34 permutation2
    _ = mixedMoment B node1236 node1236Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical174
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical22326 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22326 raw22326Labels = mixedMoment B node3301 node3301Labels := by
  calc
    mixedMoment B raw22326 raw22326Labels = mixedMoment B raw22326step0 raw22326step0Labels := by
      have hz : ∀ j, raw22326 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22326step0 = (fun i j => raw22326 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22326step0 raw22326; decide +kernel
      have hl : raw22326step0Labels = raw22326Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22326 raw22326Labels permutation346 hz
    mixedMoment B raw22326step0 raw22326step0Labels = mixedMoment B raw22326step1 raw22326step1Labels := by
      have hz : ∀ j, raw22326step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw22326step1 = (fun i j => raw22326step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw22326step1 raw22326step0; decide +kernel
      have hl : raw22326step1Labels = raw22326step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22326step0 raw22326step0Labels permutation56 hz
    mixedMoment B raw22326step1 raw22326step1Labels = mixedMoment B raw22326step2 raw22326step2Labels := by
      have ha : raw22326step2 = (fun i j => raw22326step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22326step2 raw22326step1; decide +kernel
      have hl : raw22326step2Labels = raw22326step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22326step1 raw22326step1Labels permutation9 permutation2
    mixedMoment B raw22326step2 raw22326step2Labels = mixedMoment B raw22326step3 raw22326step3Labels := by
      have ha : raw22326step3 = -raw22326step2 := by apply Matrix.ext; change ∀ i j, raw22326step3 i j = -(raw22326step2 i j); unfold raw22326step3 raw22326step2; decide +kernel
      have hl : raw22326step3Labels = raw22326step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3301 node3301Labels := by rfl

theorem canonical22329 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22329 raw22329Labels = mixedMoment B node4071 node4071Labels := by
  calc
    mixedMoment B raw22329 raw22329Labels = mixedMoment B raw22329step0 raw22329step0Labels := by
      have hz : ∀ j, raw22329 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22329step0 = (fun i j => raw22329 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22329step0 raw22329; decide +kernel
      have hl : raw22329step0Labels = raw22329Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22329 raw22329Labels permutation434 hz
    mixedMoment B raw22329step0 raw22329step0Labels = mixedMoment B raw22329step1 raw22329step1Labels := by
      have hz : ∀ j, raw22329step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22329step1 = (fun i j => raw22329step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22329step1 raw22329step0; decide +kernel
      have hl : raw22329step1Labels = raw22329step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22329step0 raw22329step0Labels permutation80 hz
    mixedMoment B raw22329step1 raw22329step1Labels = mixedMoment B raw22329step2 raw22329step2Labels := by
      have hz : ∀ j, raw22329step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw22329step2 = (fun i j => raw22329step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw22329step2 raw22329step1; decide +kernel
      have hl : raw22329step2Labels = raw22329step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22329step1 raw22329step1Labels permutation14 hz
    mixedMoment B raw22329step2 raw22329step2Labels = mixedMoment B raw22329step3 raw22329step3Labels := by
      have ha : raw22329step3 = -raw22329step2 := by apply Matrix.ext; change ∀ i j, raw22329step3 i j = -(raw22329step2 i j); unfold raw22329step3 raw22329step2; decide +kernel
      have hl : raw22329step3Labels = raw22329step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4071 node4071Labels := by rfl

theorem canonical22332 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22332 raw22332Labels = mixedMoment B node1751 node1751Labels := by
  calc
    mixedMoment B raw22332 raw22332Labels = mixedMoment B raw22332step0 raw22332step0Labels := by
      have hz : ∀ j, raw22332 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22332step0 = (fun i j => raw22332 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22332step0 raw22332; decide +kernel
      have hl : raw22332step0Labels = raw22332Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22332 raw22332Labels permutation346 hz
    mixedMoment B raw22332step0 raw22332step0Labels = mixedMoment B raw22332step1 raw22332step1Labels := by
      have hz : ∀ j, raw22332step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw22332step1 = (fun i j => raw22332step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw22332step1 raw22332step0; decide +kernel
      have hl : raw22332step1Labels = raw22332step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22332step0 raw22332step0Labels permutation56 hz
    mixedMoment B raw22332step1 raw22332step1Labels = mixedMoment B raw22332step2 raw22332step2Labels := by
      have ha : raw22332step2 = (fun i j => raw22332step1 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw22332step2 raw22332step1; decide +kernel
      have hl : raw22332step2Labels = raw22332step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22332step1 raw22332step1Labels permutation8 permutation4
    mixedMoment B raw22332step2 raw22332step2Labels = mixedMoment B raw22332step3 raw22332step3Labels := by
      have ha : raw22332step3 = -raw22332step2 := by apply Matrix.ext; change ∀ i j, raw22332step3 i j = -(raw22332step2 i j); unfold raw22332step3 raw22332step2; decide +kernel
      have hl : raw22332step3Labels = raw22332step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1751 node1751Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical175
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical22406 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22406 raw22406Labels = mixedMoment B node2683 node2683Labels := by
  calc
    mixedMoment B raw22406 raw22406Labels = mixedMoment B raw22406step0 raw22406step0Labels := by
      have hz : ∀ j, raw22406 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22406step0 = (fun i j => raw22406 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22406step0 raw22406; decide +kernel
      have hl : raw22406step0Labels = raw22406Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22406 raw22406Labels permutation434 hz
    mixedMoment B raw22406step0 raw22406step0Labels = mixedMoment B raw22406step1 raw22406step1Labels := by
      have hz : ∀ j, raw22406step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22406step1 = (fun i j => raw22406step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22406step1 raw22406step0; decide +kernel
      have hl : raw22406step1Labels = raw22406step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22406step0 raw22406step0Labels permutation80 hz
    mixedMoment B raw22406step1 raw22406step1Labels = mixedMoment B raw22406step2 raw22406step2Labels := by
      have ha : raw22406step2 = (fun i j => raw22406step1 (permutation31 i) (permutation4 j)) := by apply Matrix.ext; unfold raw22406step2 raw22406step1; decide +kernel
      have hl : raw22406step2Labels = raw22406step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22406step1 raw22406step1Labels permutation31 permutation4
    _ = mixedMoment B node2683 node2683Labels := by rfl

theorem canonical22407 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22407 raw22407Labels = mixedMoment B node1660 node1660Labels := by
  calc
    mixedMoment B raw22407 raw22407Labels = mixedMoment B raw22407step0 raw22407step0Labels := by
      have hz : ∀ j, raw22407 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22407step0 = (fun i j => raw22407 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22407step0 raw22407; decide +kernel
      have hl : raw22407step0Labels = raw22407Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22407 raw22407Labels permutation434 hz
    mixedMoment B raw22407step0 raw22407step0Labels = mixedMoment B raw22407step1 raw22407step1Labels := by
      have hz : ∀ j, raw22407step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22407step1 = (fun i j => raw22407step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22407step1 raw22407step0; decide +kernel
      have hl : raw22407step1Labels = raw22407step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22407step0 raw22407step0Labels permutation80 hz
    mixedMoment B raw22407step1 raw22407step1Labels = mixedMoment B raw22407step2 raw22407step2Labels := by
      have ha : raw22407step2 = (fun i j => raw22407step1 (permutation12 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22407step2 raw22407step1; decide +kernel
      have hl : raw22407step2Labels = raw22407step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22407step1 raw22407step1Labels permutation12 permutation2
    mixedMoment B raw22407step2 raw22407step2Labels = mixedMoment B raw22407step3 raw22407step3Labels := by
      have ha : raw22407step3 = -raw22407step2 := by apply Matrix.ext; change ∀ i j, raw22407step3 i j = -(raw22407step2 i j); unfold raw22407step3 raw22407step2; decide +kernel
      have hl : raw22407step3Labels = raw22407step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1660 node1660Labels := by rfl

theorem canonical22408 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22408 raw22408Labels = mixedMoment B node1655 node1655Labels := by
  calc
    mixedMoment B raw22408 raw22408Labels = mixedMoment B raw22408step0 raw22408step0Labels := by
      have hz : ∀ j, raw22408 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22408step0 = (fun i j => raw22408 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22408step0 raw22408; decide +kernel
      have hl : raw22408step0Labels = raw22408Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22408 raw22408Labels permutation434 hz
    mixedMoment B raw22408step0 raw22408step0Labels = mixedMoment B raw22408step1 raw22408step1Labels := by
      have ha : raw22408step1 = (fun i j => raw22408step0 (permutation50 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22408step1 raw22408step0; decide +kernel
      have hl : raw22408step1Labels = raw22408step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22408step0 raw22408step0Labels permutation50 permutation2
    mixedMoment B raw22408step1 raw22408step1Labels = mixedMoment B raw22408step2 raw22408step2Labels := by
      have ha : raw22408step2 = -raw22408step1 := by apply Matrix.ext; change ∀ i j, raw22408step2 i j = -(raw22408step1 i j); unfold raw22408step2 raw22408step1; decide +kernel
      have hl : raw22408step2Labels = raw22408step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1655 node1655Labels := by rfl

theorem canonical22409 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22409 raw22409Labels = mixedMoment B node1655 node1655Labels := by
  calc
    mixedMoment B raw22409 raw22409Labels = mixedMoment B raw22409step0 raw22409step0Labels := by
      have hz : ∀ j, raw22409 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22409step0 = (fun i j => raw22409 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22409step0 raw22409; decide +kernel
      have hl : raw22409step0Labels = raw22409Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22409 raw22409Labels permutation346 hz
    mixedMoment B raw22409step0 raw22409step0Labels = mixedMoment B raw22409step1 raw22409step1Labels := by
      have ha : raw22409step1 = (fun i j => raw22409step0 (permutation50 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22409step1 raw22409step0; decide +kernel
      have hl : raw22409step1Labels = raw22409step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22409step0 raw22409step0Labels permutation50 permutation2
    mixedMoment B raw22409step1 raw22409step1Labels = mixedMoment B raw22409step2 raw22409step2Labels := by
      have ha : raw22409step2 = -raw22409step1 := by apply Matrix.ext; change ∀ i j, raw22409step2 i j = -(raw22409step1 i j); unfold raw22409step2 raw22409step1; decide +kernel
      have hl : raw22409step2Labels = raw22409step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1655 node1655Labels := by rfl

theorem canonical22410 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22410 raw22410Labels = mixedMoment B node1657 node1657Labels := by
  calc
    mixedMoment B raw22410 raw22410Labels = mixedMoment B raw22410step0 raw22410step0Labels := by
      have hz : ∀ j, raw22410 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22410step0 = (fun i j => raw22410 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22410step0 raw22410; decide +kernel
      have hl : raw22410step0Labels = raw22410Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22410 raw22410Labels permutation434 hz
    mixedMoment B raw22410step0 raw22410step0Labels = mixedMoment B raw22410step1 raw22410step1Labels := by
      have hz : ∀ j, raw22410step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22410step1 = (fun i j => raw22410step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22410step1 raw22410step0; decide +kernel
      have hl : raw22410step1Labels = raw22410step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22410step0 raw22410step0Labels permutation80 hz
    mixedMoment B raw22410step1 raw22410step1Labels = mixedMoment B raw22410step2 raw22410step2Labels := by
      have ha : raw22410step2 = (fun i j => raw22410step1 (permutation12 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22410step2 raw22410step1; decide +kernel
      have hl : raw22410step2Labels = raw22410step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22410step1 raw22410step1Labels permutation12 permutation2
    mixedMoment B raw22410step2 raw22410step2Labels = mixedMoment B raw22410step3 raw22410step3Labels := by
      have ha : raw22410step3 = -raw22410step2 := by apply Matrix.ext; change ∀ i j, raw22410step3 i j = -(raw22410step2 i j); unfold raw22410step3 raw22410step2; decide +kernel
      have hl : raw22410step3Labels = raw22410step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1657 node1657Labels := by rfl

theorem canonical22411 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22411 raw22411Labels = mixedMoment B node1738 node1738Labels := by
  calc
    mixedMoment B raw22411 raw22411Labels = mixedMoment B raw22411step0 raw22411step0Labels := by
      have hz : ∀ j, raw22411 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22411step0 = (fun i j => raw22411 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22411step0 raw22411; decide +kernel
      have hl : raw22411step0Labels = raw22411Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22411 raw22411Labels permutation434 hz
    mixedMoment B raw22411step0 raw22411step0Labels = mixedMoment B raw22411step1 raw22411step1Labels := by
      have hz : ∀ j, raw22411step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22411step1 = (fun i j => raw22411step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22411step1 raw22411step0; decide +kernel
      have hl : raw22411step1Labels = raw22411step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22411step0 raw22411step0Labels permutation80 hz
    mixedMoment B raw22411step1 raw22411step1Labels = mixedMoment B raw22411step2 raw22411step2Labels := by
      have ha : raw22411step2 = (fun i j => raw22411step1 (permutation12 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22411step2 raw22411step1; decide +kernel
      have hl : raw22411step2Labels = raw22411step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22411step1 raw22411step1Labels permutation12 permutation2
    mixedMoment B raw22411step2 raw22411step2Labels = mixedMoment B raw22411step3 raw22411step3Labels := by
      have ha : raw22411step3 = -raw22411step2 := by apply Matrix.ext; change ∀ i j, raw22411step3 i j = -(raw22411step2 i j); unfold raw22411step3 raw22411step2; decide +kernel
      have hl : raw22411step3Labels = raw22411step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1738 node1738Labels := by rfl

theorem canonical22412 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22412 raw22412Labels = mixedMoment B node1741 node1741Labels := by
  calc
    mixedMoment B raw22412 raw22412Labels = mixedMoment B raw22412step0 raw22412step0Labels := by
      have hz : ∀ j, raw22412 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22412step0 = (fun i j => raw22412 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22412step0 raw22412; decide +kernel
      have hl : raw22412step0Labels = raw22412Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22412 raw22412Labels permutation434 hz
    mixedMoment B raw22412step0 raw22412step0Labels = mixedMoment B raw22412step1 raw22412step1Labels := by
      have hz : ∀ j, raw22412step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22412step1 = (fun i j => raw22412step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22412step1 raw22412step0; decide +kernel
      have hl : raw22412step1Labels = raw22412step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22412step0 raw22412step0Labels permutation80 hz
    mixedMoment B raw22412step1 raw22412step1Labels = mixedMoment B raw22412step2 raw22412step2Labels := by
      have hz : ∀ j, raw22412step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw22412step2 = (fun i j => raw22412step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw22412step2 raw22412step1; decide +kernel
      have hl : raw22412step2Labels = raw22412step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22412step1 raw22412step1Labels permutation14 hz
    mixedMoment B raw22412step2 raw22412step2Labels = mixedMoment B raw22412step3 raw22412step3Labels := by
      have ha : raw22412step3 = (fun i j => raw22412step2 (permutation2 i) (permutation4 j)) := by apply Matrix.ext; unfold raw22412step3 raw22412step2; decide +kernel
      have hl : raw22412step3Labels = raw22412step2Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22412step2 raw22412step2Labels permutation2 permutation4
    mixedMoment B raw22412step3 raw22412step3Labels = mixedMoment B raw22412step4 raw22412step4Labels := by
      have ha : raw22412step4 = -raw22412step3 := by apply Matrix.ext; change ∀ i j, raw22412step4 i j = -(raw22412step3 i j); unfold raw22412step4 raw22412step3; decide +kernel
      have hl : raw22412step4Labels = raw22412step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1741 node1741Labels := by rfl

theorem canonical22413 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22413 raw22413Labels = mixedMoment B node2683 node2683Labels := by
  calc
    mixedMoment B raw22413 raw22413Labels = mixedMoment B raw22413step0 raw22413step0Labels := by
      have hz : ∀ j, raw22413 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22413step0 = (fun i j => raw22413 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22413step0 raw22413; decide +kernel
      have hl : raw22413step0Labels = raw22413Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22413 raw22413Labels permutation434 hz
    mixedMoment B raw22413step0 raw22413step0Labels = mixedMoment B raw22413step1 raw22413step1Labels := by
      have hz : ∀ j, raw22413step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw22413step1 = (fun i j => raw22413step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw22413step1 raw22413step0; decide +kernel
      have hl : raw22413step1Labels = raw22413step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22413step0 raw22413step0Labels permutation56 hz
    mixedMoment B raw22413step1 raw22413step1Labels = mixedMoment B raw22413step2 raw22413step2Labels := by
      have ha : raw22413step2 = (fun i j => raw22413step1 (permutation31 i) (permutation4 j)) := by apply Matrix.ext; unfold raw22413step2 raw22413step1; decide +kernel
      have hl : raw22413step2Labels = raw22413step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22413step1 raw22413step1Labels permutation31 permutation4
    _ = mixedMoment B node2683 node2683Labels := by rfl

theorem canonical22414 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22414 raw22414Labels = mixedMoment B node2683 node2683Labels := by
  calc
    mixedMoment B raw22414 raw22414Labels = mixedMoment B raw22414step0 raw22414step0Labels := by
      have hz : ∀ j, raw22414 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22414step0 = (fun i j => raw22414 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22414step0 raw22414; decide +kernel
      have hl : raw22414step0Labels = raw22414Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22414 raw22414Labels permutation346 hz
    mixedMoment B raw22414step0 raw22414step0Labels = mixedMoment B raw22414step1 raw22414step1Labels := by
      have hz : ∀ j, raw22414step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw22414step1 = (fun i j => raw22414step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw22414step1 raw22414step0; decide +kernel
      have hl : raw22414step1Labels = raw22414step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22414step0 raw22414step0Labels permutation56 hz
    mixedMoment B raw22414step1 raw22414step1Labels = mixedMoment B raw22414step2 raw22414step2Labels := by
      have ha : raw22414step2 = (fun i j => raw22414step1 (permutation31 i) (permutation4 j)) := by apply Matrix.ext; unfold raw22414step2 raw22414step1; decide +kernel
      have hl : raw22414step2Labels = raw22414step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22414step1 raw22414step1Labels permutation31 permutation4
    _ = mixedMoment B node2683 node2683Labels := by rfl

theorem canonical22415 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22415 raw22415Labels = mixedMoment B node2780 node2780Labels := by
  calc
    mixedMoment B raw22415 raw22415Labels = mixedMoment B raw22415step0 raw22415step0Labels := by
      have hz : ∀ j, raw22415 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22415step0 = (fun i j => raw22415 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22415step0 raw22415; decide +kernel
      have hl : raw22415step0Labels = raw22415Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22415 raw22415Labels permutation434 hz
    mixedMoment B raw22415step0 raw22415step0Labels = mixedMoment B raw22415step1 raw22415step1Labels := by
      have hz : ∀ j, raw22415step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22415step1 = (fun i j => raw22415step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22415step1 raw22415step0; decide +kernel
      have hl : raw22415step1Labels = raw22415step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22415step0 raw22415step0Labels permutation80 hz
    mixedMoment B raw22415step1 raw22415step1Labels = mixedMoment B raw22415step2 raw22415step2Labels := by
      have hz : ∀ j, raw22415step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw22415step2 = (fun i j => raw22415step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw22415step2 raw22415step1; decide +kernel
      have hl : raw22415step2Labels = raw22415step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22415step1 raw22415step1Labels permutation14 hz
    mixedMoment B raw22415step2 raw22415step2Labels = mixedMoment B raw22415step3 raw22415step3Labels := by
      have ha : raw22415step3 = (fun i j => raw22415step2 (permutation5 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22415step3 raw22415step2; decide +kernel
      have hl : raw22415step3Labels = raw22415step2Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22415step2 raw22415step2Labels permutation5 permutation2
    _ = mixedMoment B node2780 node2780Labels := by rfl

theorem canonical22416 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22416 raw22416Labels = mixedMoment B node3311 node3311Labels := by
  calc
    mixedMoment B raw22416 raw22416Labels = mixedMoment B raw22416step0 raw22416step0Labels := by
      have hz : ∀ j, raw22416 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22416step0 = (fun i j => raw22416 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22416step0 raw22416; decide +kernel
      have hl : raw22416step0Labels = raw22416Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22416 raw22416Labels permutation434 hz
    mixedMoment B raw22416step0 raw22416step0Labels = mixedMoment B raw22416step1 raw22416step1Labels := by
      have hz : ∀ j, raw22416step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22416step1 = (fun i j => raw22416step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22416step1 raw22416step0; decide +kernel
      have hl : raw22416step1Labels = raw22416step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22416step0 raw22416step0Labels permutation80 hz
    mixedMoment B raw22416step1 raw22416step1Labels = mixedMoment B raw22416step2 raw22416step2Labels := by
      have hz : ∀ j, raw22416step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw22416step2 = (fun i j => raw22416step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw22416step2 raw22416step1; decide +kernel
      have hl : raw22416step2Labels = raw22416step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22416step1 raw22416step1Labels permutation14 hz
    mixedMoment B raw22416step2 raw22416step2Labels = mixedMoment B raw22416step3 raw22416step3Labels := by
      have ha : raw22416step3 = (fun i j => raw22416step2 (permutation3 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22416step3 raw22416step2; decide +kernel
      have hl : raw22416step3Labels = raw22416step2Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22416step2 raw22416step2Labels permutation3 permutation2
    mixedMoment B raw22416step3 raw22416step3Labels = mixedMoment B raw22416step4 raw22416step4Labels := by
      have ha : raw22416step4 = -raw22416step3 := by apply Matrix.ext; change ∀ i j, raw22416step4 i j = -(raw22416step3 i j); unfold raw22416step4 raw22416step3; decide +kernel
      have hl : raw22416step4Labels = raw22416step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3311 node3311Labels := by rfl

theorem canonical22417 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22417 raw22417Labels = mixedMoment B node1627 node1627Labels := by
  calc
    mixedMoment B raw22417 raw22417Labels = mixedMoment B raw22417step0 raw22417step0Labels := by
      have hz : ∀ j, raw22417 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22417step0 = (fun i j => raw22417 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22417step0 raw22417; decide +kernel
      have hl : raw22417step0Labels = raw22417Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22417 raw22417Labels permutation434 hz
    mixedMoment B raw22417step0 raw22417step0Labels = mixedMoment B raw22417step1 raw22417step1Labels := by
      have hz : ∀ j, raw22417step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22417step1 = (fun i j => raw22417step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22417step1 raw22417step0; decide +kernel
      have hl : raw22417step1Labels = raw22417step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22417step0 raw22417step0Labels permutation80 hz
    mixedMoment B raw22417step1 raw22417step1Labels = mixedMoment B raw22417step2 raw22417step2Labels := by
      have ha : raw22417step2 = (fun i j => raw22417step1 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw22417step2 raw22417step1; decide +kernel
      have hl : raw22417step2Labels = raw22417step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22417step1 raw22417step1Labels permutation8 permutation4
    mixedMoment B raw22417step2 raw22417step2Labels = mixedMoment B raw22417step3 raw22417step3Labels := by
      have ha : raw22417step3 = -raw22417step2 := by apply Matrix.ext; change ∀ i j, raw22417step3 i j = -(raw22417step2 i j); unfold raw22417step3 raw22417step2; decide +kernel
      have hl : raw22417step3Labels = raw22417step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1627 node1627Labels := by rfl

theorem canonical22418 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22418 raw22418Labels = mixedMoment B node2409 node2409Labels := by
  calc
    mixedMoment B raw22418 raw22418Labels = mixedMoment B raw22418step0 raw22418step0Labels := by
      have hz : ∀ j, raw22418 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22418step0 = (fun i j => raw22418 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22418step0 raw22418; decide +kernel
      have hl : raw22418step0Labels = raw22418Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22418 raw22418Labels permutation434 hz
    mixedMoment B raw22418step0 raw22418step0Labels = mixedMoment B raw22418step1 raw22418step1Labels := by
      have hz : ∀ j, raw22418step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22418step1 = (fun i j => raw22418step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22418step1 raw22418step0; decide +kernel
      have hl : raw22418step1Labels = raw22418step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22418step0 raw22418step0Labels permutation80 hz
    mixedMoment B raw22418step1 raw22418step1Labels = mixedMoment B raw22418step2 raw22418step2Labels := by
      have ha : raw22418step2 = (fun i j => raw22418step1 (permutation31 i) (permutation4 j)) := by apply Matrix.ext; unfold raw22418step2 raw22418step1; decide +kernel
      have hl : raw22418step2Labels = raw22418step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22418step1 raw22418step1Labels permutation31 permutation4
    _ = mixedMoment B node2409 node2409Labels := by rfl

theorem canonical22419 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22419 raw22419Labels = mixedMoment B node2397 node2397Labels := by
  calc
    mixedMoment B raw22419 raw22419Labels = mixedMoment B raw22419step0 raw22419step0Labels := by
      have hz : ∀ j, raw22419 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22419step0 = (fun i j => raw22419 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22419step0 raw22419; decide +kernel
      have hl : raw22419step0Labels = raw22419Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22419 raw22419Labels permutation434 hz
    mixedMoment B raw22419step0 raw22419step0Labels = mixedMoment B raw22419step1 raw22419step1Labels := by
      have ha : raw22419step1 = (fun i j => raw22419step0 (permutation149 i) (permutation4 j)) := by apply Matrix.ext; unfold raw22419step1 raw22419step0; decide +kernel
      have hl : raw22419step1Labels = raw22419step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22419step0 raw22419step0Labels permutation149 permutation4
    _ = mixedMoment B node2397 node2397Labels := by rfl

theorem canonical22420 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22420 raw22420Labels = mixedMoment B node2397 node2397Labels := by
  calc
    mixedMoment B raw22420 raw22420Labels = mixedMoment B raw22420step0 raw22420step0Labels := by
      have hz : ∀ j, raw22420 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22420step0 = (fun i j => raw22420 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22420step0 raw22420; decide +kernel
      have hl : raw22420step0Labels = raw22420Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22420 raw22420Labels permutation346 hz
    mixedMoment B raw22420step0 raw22420step0Labels = mixedMoment B raw22420step1 raw22420step1Labels := by
      have ha : raw22420step1 = (fun i j => raw22420step0 (permutation149 i) (permutation4 j)) := by apply Matrix.ext; unfold raw22420step1 raw22420step0; decide +kernel
      have hl : raw22420step1Labels = raw22420step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22420step0 raw22420step0Labels permutation149 permutation4
    _ = mixedMoment B node2397 node2397Labels := by rfl

theorem canonical22421 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22421 raw22421Labels = mixedMoment B node3301 node3301Labels := by
  calc
    mixedMoment B raw22421 raw22421Labels = mixedMoment B raw22421step0 raw22421step0Labels := by
      have hz : ∀ j, raw22421 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22421step0 = (fun i j => raw22421 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22421step0 raw22421; decide +kernel
      have hl : raw22421step0Labels = raw22421Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22421 raw22421Labels permutation434 hz
    mixedMoment B raw22421step0 raw22421step0Labels = mixedMoment B raw22421step1 raw22421step1Labels := by
      have hz : ∀ j, raw22421step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22421step1 = (fun i j => raw22421step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22421step1 raw22421step0; decide +kernel
      have hl : raw22421step1Labels = raw22421step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22421step0 raw22421step0Labels permutation80 hz
    mixedMoment B raw22421step1 raw22421step1Labels = mixedMoment B raw22421step2 raw22421step2Labels := by
      have ha : raw22421step2 = (fun i j => raw22421step1 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw22421step2 raw22421step1; decide +kernel
      have hl : raw22421step2Labels = raw22421step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22421step1 raw22421step1Labels permutation8 permutation4
    mixedMoment B raw22421step2 raw22421step2Labels = mixedMoment B raw22421step3 raw22421step3Labels := by
      have ha : raw22421step3 = -raw22421step2 := by apply Matrix.ext; change ∀ i j, raw22421step3 i j = -(raw22421step2 i j); unfold raw22421step3 raw22421step2; decide +kernel
      have hl : raw22421step3Labels = raw22421step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3301 node3301Labels := by rfl

theorem canonical22422 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22422 raw22422Labels = mixedMoment B node3295 node3295Labels := by
  calc
    mixedMoment B raw22422 raw22422Labels = mixedMoment B raw22422step0 raw22422step0Labels := by
      have hz : ∀ j, raw22422 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22422step0 = (fun i j => raw22422 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22422step0 raw22422; decide +kernel
      have hl : raw22422step0Labels = raw22422Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22422 raw22422Labels permutation434 hz
    mixedMoment B raw22422step0 raw22422step0Labels = mixedMoment B raw22422step1 raw22422step1Labels := by
      have ha : raw22422step1 = (fun i j => raw22422step0 (permutation42 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22422step1 raw22422step0; decide +kernel
      have hl : raw22422step1Labels = raw22422step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22422step0 raw22422step0Labels permutation42 permutation2
    mixedMoment B raw22422step1 raw22422step1Labels = mixedMoment B raw22422step2 raw22422step2Labels := by
      have ha : raw22422step2 = -raw22422step1 := by apply Matrix.ext; change ∀ i j, raw22422step2 i j = -(raw22422step1 i j); unfold raw22422step2 raw22422step1; decide +kernel
      have hl : raw22422step2Labels = raw22422step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3295 node3295Labels := by rfl

theorem canonical22423 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22423 raw22423Labels = mixedMoment B node3295 node3295Labels := by
  calc
    mixedMoment B raw22423 raw22423Labels = mixedMoment B raw22423step0 raw22423step0Labels := by
      have hz : ∀ j, raw22423 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22423step0 = (fun i j => raw22423 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22423step0 raw22423; decide +kernel
      have hl : raw22423step0Labels = raw22423Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22423 raw22423Labels permutation346 hz
    mixedMoment B raw22423step0 raw22423step0Labels = mixedMoment B raw22423step1 raw22423step1Labels := by
      have ha : raw22423step1 = (fun i j => raw22423step0 (permutation42 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22423step1 raw22423step0; decide +kernel
      have hl : raw22423step1Labels = raw22423step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22423step0 raw22423step0Labels permutation42 permutation2
    mixedMoment B raw22423step1 raw22423step1Labels = mixedMoment B raw22423step2 raw22423step2Labels := by
      have ha : raw22423step2 = -raw22423step1 := by apply Matrix.ext; change ∀ i j, raw22423step2 i j = -(raw22423step1 i j); unfold raw22423step2 raw22423step1; decide +kernel
      have hl : raw22423step2Labels = raw22423step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3295 node3295Labels := by rfl

theorem canonical22424 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22424 raw22424Labels = mixedMoment B node2488 node2488Labels := by
  calc
    mixedMoment B raw22424 raw22424Labels = mixedMoment B raw22424step0 raw22424step0Labels := by
      have hz : ∀ j, raw22424 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22424step0 = (fun i j => raw22424 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22424step0 raw22424; decide +kernel
      have hl : raw22424step0Labels = raw22424Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22424 raw22424Labels permutation346 hz
    _ = mixedMoment B node2488 node2488Labels := by rfl

theorem canonical22425 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22425 raw22425Labels = mixedMoment B node1219 node1219Labels := by
  calc
    mixedMoment B raw22425 raw22425Labels = mixedMoment B raw22425step0 raw22425step0Labels := by
      have hz : ∀ j, raw22425 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22425step0 = (fun i j => raw22425 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22425step0 raw22425; decide +kernel
      have hl : raw22425step0Labels = raw22425Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22425 raw22425Labels permutation346 hz
    _ = mixedMoment B node1219 node1219Labels := by rfl

theorem canonical22426 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22426 raw22426Labels = mixedMoment B node1113 node1113Labels := by
  calc
    mixedMoment B raw22426 raw22426Labels = mixedMoment B raw22426step0 raw22426step0Labels := by
      have ha : raw22426step0 = (fun i j => raw22426 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22426step0 raw22426; decide +kernel
      have hl : raw22426step0Labels = raw22426Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22426 raw22426Labels permutation158 permutation2
    _ = mixedMoment B node1113 node1113Labels := by rfl

theorem canonical22427 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22427 raw22427Labels = mixedMoment B node1138 node1138Labels := by
  calc
    mixedMoment B raw22427 raw22427Labels = mixedMoment B raw22427step0 raw22427step0Labels := by
      have hz : ∀ j, raw22427 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22427step0 = (fun i j => raw22427 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22427step0 raw22427; decide +kernel
      have hl : raw22427step0Labels = raw22427Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22427 raw22427Labels permutation346 hz
    _ = mixedMoment B node1138 node1138Labels := by rfl

theorem canonical22428 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22428 raw22428Labels = mixedMoment B node1121 node1121Labels := by
  calc
    mixedMoment B raw22428 raw22428Labels = mixedMoment B raw22428step0 raw22428step0Labels := by
      have hz : ∀ j, raw22428 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22428step0 = (fun i j => raw22428 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22428step0 raw22428; decide +kernel
      have hl : raw22428step0Labels = raw22428Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22428 raw22428Labels permutation346 hz
    mixedMoment B raw22428step0 raw22428step0Labels = mixedMoment B raw22428step1 raw22428step1Labels := by
      have ha : raw22428step1 = (fun i j => raw22428step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22428step1 raw22428step0; decide +kernel
      have hl : raw22428step1Labels = raw22428step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22428step0 raw22428step0Labels permutation33 permutation2
    _ = mixedMoment B node1121 node1121Labels := by rfl

theorem canonical22429 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22429 raw22429Labels = mixedMoment B node631 node631Labels := by
  calc
    mixedMoment B raw22429 raw22429Labels = mixedMoment B raw22429step0 raw22429step0Labels := by
      have hz : ∀ j, raw22429 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22429step0 = (fun i j => raw22429 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22429step0 raw22429; decide +kernel
      have hl : raw22429step0Labels = raw22429Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22429 raw22429Labels permutation346 hz
    _ = mixedMoment B node631 node631Labels := by rfl

theorem canonical22430 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22430 raw22430Labels = mixedMoment B node1151 node1151Labels := by
  calc
    mixedMoment B raw22430 raw22430Labels = mixedMoment B raw22430step0 raw22430step0Labels := by
      have ha : raw22430step0 = (fun i j => raw22430 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22430step0 raw22430; decide +kernel
      have hl : raw22430step0Labels = raw22430Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22430 raw22430Labels permutation176 permutation2
    _ = mixedMoment B node1151 node1151Labels := by rfl

theorem canonical22431 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22431 raw22431Labels = mixedMoment B node1241 node1241Labels := by
  calc
    mixedMoment B raw22431 raw22431Labels = mixedMoment B raw22431step0 raw22431step0Labels := by
      have hz : ∀ j, raw22431 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22431step0 = (fun i j => raw22431 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22431step0 raw22431; decide +kernel
      have hl : raw22431step0Labels = raw22431Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22431 raw22431Labels permutation346 hz
    mixedMoment B raw22431step0 raw22431step0Labels = mixedMoment B raw22431step1 raw22431step1Labels := by
      have ha : raw22431step1 = (fun i j => raw22431step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22431step1 raw22431step0; decide +kernel
      have hl : raw22431step1Labels = raw22431step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22431step0 raw22431step0Labels permutation33 permutation2
    _ = mixedMoment B node1241 node1241Labels := by rfl

theorem canonical22432 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22432 raw22432Labels = mixedMoment B node1611 node1611Labels := by
  calc
    mixedMoment B raw22432 raw22432Labels = mixedMoment B raw22432step0 raw22432step0Labels := by
      have hz : ∀ j, raw22432 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22432step0 = (fun i j => raw22432 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22432step0 raw22432; decide +kernel
      have hl : raw22432step0Labels = raw22432Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22432 raw22432Labels permutation346 hz
    mixedMoment B raw22432step0 raw22432step0Labels = mixedMoment B raw22432step1 raw22432step1Labels := by
      have ha : raw22432step1 = (fun i j => raw22432step0 (permutation42 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22432step1 raw22432step0; decide +kernel
      have hl : raw22432step1Labels = raw22432step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22432step0 raw22432step0Labels permutation42 permutation2
    mixedMoment B raw22432step1 raw22432step1Labels = mixedMoment B raw22432step2 raw22432step2Labels := by
      have ha : raw22432step2 = -raw22432step1 := by apply Matrix.ext; change ∀ i j, raw22432step2 i j = -(raw22432step1 i j); unfold raw22432step2 raw22432step1; decide +kernel
      have hl : raw22432step2Labels = raw22432step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1611 node1611Labels := by rfl

theorem canonical22433 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22433 raw22433Labels = mixedMoment B node1606 node1606Labels := by
  calc
    mixedMoment B raw22433 raw22433Labels = mixedMoment B raw22433step0 raw22433step0Labels := by
      have ha : raw22433step0 = (fun i j => raw22433 (permutation218 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22433step0 raw22433; decide +kernel
      have hl : raw22433step0Labels = raw22433Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22433 raw22433Labels permutation218 permutation2
    mixedMoment B raw22433step0 raw22433step0Labels = mixedMoment B raw22433step1 raw22433step1Labels := by
      have ha : raw22433step1 = -raw22433step0 := by apply Matrix.ext; change ∀ i j, raw22433step1 i j = -(raw22433step0 i j); unfold raw22433step1 raw22433step0; decide +kernel
      have hl : raw22433step1Labels = raw22433step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1606 node1606Labels := by rfl

theorem canonical22434 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22434 raw22434Labels = mixedMoment B node1608 node1608Labels := by
  calc
    mixedMoment B raw22434 raw22434Labels = mixedMoment B raw22434step0 raw22434step0Labels := by
      have hz : ∀ j, raw22434 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22434step0 = (fun i j => raw22434 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22434step0 raw22434; decide +kernel
      have hl : raw22434step0Labels = raw22434Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22434 raw22434Labels permutation346 hz
    mixedMoment B raw22434step0 raw22434step0Labels = mixedMoment B raw22434step1 raw22434step1Labels := by
      have ha : raw22434step1 = (fun i j => raw22434step0 (permutation42 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22434step1 raw22434step0; decide +kernel
      have hl : raw22434step1Labels = raw22434step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22434step0 raw22434step0Labels permutation42 permutation2
    mixedMoment B raw22434step1 raw22434step1Labels = mixedMoment B raw22434step2 raw22434step2Labels := by
      have ha : raw22434step2 = -raw22434step1 := by apply Matrix.ext; change ∀ i j, raw22434step2 i j = -(raw22434step1 i j); unfold raw22434step2 raw22434step1; decide +kernel
      have hl : raw22434step2Labels = raw22434step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1608 node1608Labels := by rfl

theorem canonical22435 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22435 raw22435Labels = mixedMoment B node1618 node1618Labels := by
  calc
    mixedMoment B raw22435 raw22435Labels = mixedMoment B raw22435step0 raw22435step0Labels := by
      have hz : ∀ j, raw22435 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22435step0 = (fun i j => raw22435 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22435step0 raw22435; decide +kernel
      have hl : raw22435step0Labels = raw22435Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22435 raw22435Labels permutation346 hz
    mixedMoment B raw22435step0 raw22435step0Labels = mixedMoment B raw22435step1 raw22435step1Labels := by
      have ha : raw22435step1 = (fun i j => raw22435step0 (permutation39 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22435step1 raw22435step0; decide +kernel
      have hl : raw22435step1Labels = raw22435step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22435step0 raw22435step0Labels permutation39 permutation2
    mixedMoment B raw22435step1 raw22435step1Labels = mixedMoment B raw22435step2 raw22435step2Labels := by
      have ha : raw22435step2 = -raw22435step1 := by apply Matrix.ext; change ∀ i j, raw22435step2 i j = -(raw22435step1 i j); unfold raw22435step2 raw22435step1; decide +kernel
      have hl : raw22435step2Labels = raw22435step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1618 node1618Labels := by rfl

theorem canonical22439 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22439 raw22439Labels = mixedMoment B node3297 node3297Labels := by
  calc
    mixedMoment B raw22439 raw22439Labels = mixedMoment B raw22439step0 raw22439step0Labels := by
      have hz : ∀ j, raw22439 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22439step0 = (fun i j => raw22439 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22439step0 raw22439; decide +kernel
      have hl : raw22439step0Labels = raw22439Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22439 raw22439Labels permutation346 hz
    mixedMoment B raw22439step0 raw22439step0Labels = mixedMoment B raw22439step1 raw22439step1Labels := by
      have ha : raw22439step1 = (fun i j => raw22439step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22439step1 raw22439step0; decide +kernel
      have hl : raw22439step1Labels = raw22439step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22439step0 raw22439step0Labels permutation38 permutation2
    mixedMoment B raw22439step1 raw22439step1Labels = mixedMoment B raw22439step2 raw22439step2Labels := by
      have ha : raw22439step2 = -raw22439step1 := by apply Matrix.ext; change ∀ i j, raw22439step2 i j = -(raw22439step1 i j); unfold raw22439step2 raw22439step1; decide +kernel
      have hl : raw22439step2Labels = raw22439step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3297 node3297Labels := by rfl

theorem canonical22440 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22440 raw22440Labels = mixedMoment B node2489 node2489Labels := by
  calc
    mixedMoment B raw22440 raw22440Labels = mixedMoment B raw22440step0 raw22440step0Labels := by
      have hz : ∀ j, raw22440 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22440step0 = (fun i j => raw22440 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22440step0 raw22440; decide +kernel
      have hl : raw22440step0Labels = raw22440Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22440 raw22440Labels permutation346 hz
    _ = mixedMoment B node2489 node2489Labels := by rfl

theorem canonical22441 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22441 raw22441Labels = mixedMoment B node1220 node1220Labels := by
  calc
    mixedMoment B raw22441 raw22441Labels = mixedMoment B raw22441step0 raw22441step0Labels := by
      have hz : ∀ j, raw22441 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22441step0 = (fun i j => raw22441 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22441step0 raw22441; decide +kernel
      have hl : raw22441step0Labels = raw22441Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22441 raw22441Labels permutation346 hz
    _ = mixedMoment B node1220 node1220Labels := by rfl

theorem canonical22442 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22442 raw22442Labels = mixedMoment B node1114 node1114Labels := by
  calc
    mixedMoment B raw22442 raw22442Labels = mixedMoment B raw22442step0 raw22442step0Labels := by
      have ha : raw22442step0 = (fun i j => raw22442 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22442step0 raw22442; decide +kernel
      have hl : raw22442step0Labels = raw22442Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22442 raw22442Labels permutation158 permutation2
    _ = mixedMoment B node1114 node1114Labels := by rfl

theorem canonical22443 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22443 raw22443Labels = mixedMoment B node1139 node1139Labels := by
  calc
    mixedMoment B raw22443 raw22443Labels = mixedMoment B raw22443step0 raw22443step0Labels := by
      have hz : ∀ j, raw22443 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22443step0 = (fun i j => raw22443 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22443step0 raw22443; decide +kernel
      have hl : raw22443step0Labels = raw22443Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22443 raw22443Labels permutation346 hz
    _ = mixedMoment B node1139 node1139Labels := by rfl

theorem canonical22444 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22444 raw22444Labels = mixedMoment B node1120 node1120Labels := by
  calc
    mixedMoment B raw22444 raw22444Labels = mixedMoment B raw22444step0 raw22444step0Labels := by
      have hz : ∀ j, raw22444 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22444step0 = (fun i j => raw22444 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22444step0 raw22444; decide +kernel
      have hl : raw22444step0Labels = raw22444Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22444 raw22444Labels permutation346 hz
    mixedMoment B raw22444step0 raw22444step0Labels = mixedMoment B raw22444step1 raw22444step1Labels := by
      have ha : raw22444step1 = (fun i j => raw22444step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22444step1 raw22444step0; decide +kernel
      have hl : raw22444step1Labels = raw22444step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22444step0 raw22444step0Labels permutation33 permutation2
    _ = mixedMoment B node1120 node1120Labels := by rfl

theorem canonical22445 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22445 raw22445Labels = mixedMoment B node1120 node1120Labels := by
  calc
    mixedMoment B raw22445 raw22445Labels = mixedMoment B raw22445step0 raw22445step0Labels := by
      have hz : ∀ j, raw22445 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22445step0 = (fun i j => raw22445 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22445step0 raw22445; decide +kernel
      have hl : raw22445step0Labels = raw22445Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22445 raw22445Labels permutation346 hz
    _ = mixedMoment B node1120 node1120Labels := by rfl

theorem canonical22446 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22446 raw22446Labels = mixedMoment B node632 node632Labels := by
  calc
    mixedMoment B raw22446 raw22446Labels = mixedMoment B raw22446step0 raw22446step0Labels := by
      have hz : ∀ j, raw22446 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22446step0 = (fun i j => raw22446 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22446step0 raw22446; decide +kernel
      have hl : raw22446step0Labels = raw22446Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22446 raw22446Labels permutation346 hz
    _ = mixedMoment B node632 node632Labels := by rfl

theorem canonical22447 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22447 raw22447Labels = mixedMoment B node1152 node1152Labels := by
  calc
    mixedMoment B raw22447 raw22447Labels = mixedMoment B raw22447step0 raw22447step0Labels := by
      have ha : raw22447step0 = (fun i j => raw22447 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22447step0 raw22447; decide +kernel
      have hl : raw22447step0Labels = raw22447Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22447 raw22447Labels permutation176 permutation2
    _ = mixedMoment B node1152 node1152Labels := by rfl

theorem canonical22448 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22448 raw22448Labels = mixedMoment B node1240 node1240Labels := by
  calc
    mixedMoment B raw22448 raw22448Labels = mixedMoment B raw22448step0 raw22448step0Labels := by
      have hz : ∀ j, raw22448 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22448step0 = (fun i j => raw22448 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22448step0 raw22448; decide +kernel
      have hl : raw22448step0Labels = raw22448Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22448 raw22448Labels permutation346 hz
    _ = mixedMoment B node1240 node1240Labels := by rfl

theorem canonical22449 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22449 raw22449Labels = mixedMoment B node1240 node1240Labels := by
  calc
    mixedMoment B raw22449 raw22449Labels = mixedMoment B raw22449step0 raw22449step0Labels := by
      have hz : ∀ j, raw22449 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22449step0 = (fun i j => raw22449 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22449step0 raw22449; decide +kernel
      have hl : raw22449step0Labels = raw22449Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22449 raw22449Labels permutation346 hz
    mixedMoment B raw22449step0 raw22449step0Labels = mixedMoment B raw22449step1 raw22449step1Labels := by
      have ha : raw22449step1 = (fun i j => raw22449step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22449step1 raw22449step0; decide +kernel
      have hl : raw22449step1Labels = raw22449step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22449step0 raw22449step0Labels permutation33 permutation2
    _ = mixedMoment B node1240 node1240Labels := by rfl

theorem canonical22450 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22450 raw22450Labels = mixedMoment B node1626 node1626Labels := by
  calc
    mixedMoment B raw22450 raw22450Labels = mixedMoment B raw22450step0 raw22450step0Labels := by
      have hz : ∀ j, raw22450 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22450step0 = (fun i j => raw22450 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22450step0 raw22450; decide +kernel
      have hl : raw22450step0Labels = raw22450Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22450 raw22450Labels permutation346 hz
    mixedMoment B raw22450step0 raw22450step0Labels = mixedMoment B raw22450step1 raw22450step1Labels := by
      have ha : raw22450step1 = (fun i j => raw22450step0 (permutation41 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22450step1 raw22450step0; decide +kernel
      have hl : raw22450step1Labels = raw22450step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22450step0 raw22450step0Labels permutation41 permutation2
    mixedMoment B raw22450step1 raw22450step1Labels = mixedMoment B raw22450step2 raw22450step2Labels := by
      have ha : raw22450step2 = -raw22450step1 := by apply Matrix.ext; change ∀ i j, raw22450step2 i j = -(raw22450step1 i j); unfold raw22450step2 raw22450step1; decide +kernel
      have hl : raw22450step2Labels = raw22450step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1626 node1626Labels := by rfl

theorem canonical22451 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22451 raw22451Labels = mixedMoment B node1614 node1614Labels := by
  calc
    mixedMoment B raw22451 raw22451Labels = mixedMoment B raw22451step0 raw22451step0Labels := by
      have ha : raw22451step0 = (fun i j => raw22451 (permutation200 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22451step0 raw22451; decide +kernel
      have hl : raw22451step0Labels = raw22451Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22451 raw22451Labels permutation200 permutation2
    mixedMoment B raw22451step0 raw22451step0Labels = mixedMoment B raw22451step1 raw22451step1Labels := by
      have ha : raw22451step1 = -raw22451step0 := by apply Matrix.ext; change ∀ i j, raw22451step1 i j = -(raw22451step0 i j); unfold raw22451step1 raw22451step0; decide +kernel
      have hl : raw22451step1Labels = raw22451step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1614 node1614Labels := by rfl

theorem canonical22452 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22452 raw22452Labels = mixedMoment B node1751 node1751Labels := by
  calc
    mixedMoment B raw22452 raw22452Labels = mixedMoment B raw22452step0 raw22452step0Labels := by
      have hz : ∀ j, raw22452 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22452step0 = (fun i j => raw22452 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22452step0 raw22452; decide +kernel
      have hl : raw22452step0Labels = raw22452Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22452 raw22452Labels permutation434 hz
    mixedMoment B raw22452step0 raw22452step0Labels = mixedMoment B raw22452step1 raw22452step1Labels := by
      have hz : ∀ j, raw22452step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22452step1 = (fun i j => raw22452step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22452step1 raw22452step0; decide +kernel
      have hl : raw22452step1Labels = raw22452step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22452step0 raw22452step0Labels permutation80 hz
    mixedMoment B raw22452step1 raw22452step1Labels = mixedMoment B raw22452step2 raw22452step2Labels := by
      have ha : raw22452step2 = -raw22452step1 := by apply Matrix.ext; change ∀ i j, raw22452step2 i j = -(raw22452step1 i j); unfold raw22452step2 raw22452step1; decide +kernel
      have hl : raw22452step2Labels = raw22452step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1751 node1751Labels := by rfl

theorem canonical22453 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22453 raw22453Labels = mixedMoment B node1618 node1618Labels := by
  calc
    mixedMoment B raw22453 raw22453Labels = mixedMoment B raw22453step0 raw22453step0Labels := by
      have hz : ∀ j, raw22453 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22453step0 = (fun i j => raw22453 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22453step0 raw22453; decide +kernel
      have hl : raw22453step0Labels = raw22453Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22453 raw22453Labels permutation346 hz
    mixedMoment B raw22453step0 raw22453step0Labels = mixedMoment B raw22453step1 raw22453step1Labels := by
      have ha : raw22453step1 = (fun i j => raw22453step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22453step1 raw22453step0; decide +kernel
      have hl : raw22453step1Labels = raw22453step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22453step0 raw22453step0Labels permutation38 permutation2
    mixedMoment B raw22453step1 raw22453step1Labels = mixedMoment B raw22453step2 raw22453step2Labels := by
      have ha : raw22453step2 = -raw22453step1 := by apply Matrix.ext; change ∀ i j, raw22453step2 i j = -(raw22453step1 i j); unfold raw22453step2 raw22453step1; decide +kernel
      have hl : raw22453step2Labels = raw22453step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1618 node1618Labels := by rfl

theorem canonical22454 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22454 raw22454Labels = mixedMoment B node3297 node3297Labels := by
  calc
    mixedMoment B raw22454 raw22454Labels = mixedMoment B raw22454step0 raw22454step0Labels := by
      have hz : ∀ j, raw22454 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw22454step0 = (fun i j => raw22454 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw22454step0 raw22454; decide +kernel
      have hl : raw22454step0Labels = raw22454Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22454 raw22454Labels permutation265 hz
    mixedMoment B raw22454step0 raw22454step0Labels = mixedMoment B raw22454step1 raw22454step1Labels := by
      have ha : raw22454step1 = (fun i j => raw22454step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22454step1 raw22454step0; decide +kernel
      have hl : raw22454step1Labels = raw22454step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22454step0 raw22454step0Labels permutation38 permutation2
    mixedMoment B raw22454step1 raw22454step1Labels = mixedMoment B raw22454step2 raw22454step2Labels := by
      have ha : raw22454step2 = -raw22454step1 := by apply Matrix.ext; change ∀ i j, raw22454step2 i j = -(raw22454step1 i j); unfold raw22454step2 raw22454step1; decide +kernel
      have hl : raw22454step2Labels = raw22454step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3297 node3297Labels := by rfl

theorem canonical22455 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22455 raw22455Labels = mixedMoment B node3312 node3312Labels := by
  calc
    mixedMoment B raw22455 raw22455Labels = mixedMoment B raw22455step0 raw22455step0Labels := by
      have hz : ∀ j, raw22455 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22455step0 = (fun i j => raw22455 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22455step0 raw22455; decide +kernel
      have hl : raw22455step0Labels = raw22455Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22455 raw22455Labels permutation434 hz
    mixedMoment B raw22455step0 raw22455step0Labels = mixedMoment B raw22455step1 raw22455step1Labels := by
      have hz : ∀ j, raw22455step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22455step1 = (fun i j => raw22455step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22455step1 raw22455step0; decide +kernel
      have hl : raw22455step1Labels = raw22455step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22455step0 raw22455step0Labels permutation80 hz
    mixedMoment B raw22455step1 raw22455step1Labels = mixedMoment B raw22455step2 raw22455step2Labels := by
      have hz : ∀ j, raw22455step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw22455step2 = (fun i j => raw22455step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw22455step2 raw22455step1; decide +kernel
      have hl : raw22455step2Labels = raw22455step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22455step1 raw22455step1Labels permutation14 hz
    mixedMoment B raw22455step2 raw22455step2Labels = mixedMoment B raw22455step3 raw22455step3Labels := by
      have ha : raw22455step3 = -raw22455step2 := by apply Matrix.ext; change ∀ i j, raw22455step3 i j = -(raw22455step2 i j); unfold raw22455step3 raw22455step2; decide +kernel
      have hl : raw22455step3Labels = raw22455step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3312 node3312Labels := by rfl

theorem canonical22456 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22456 raw22456Labels = mixedMoment B node3301 node3301Labels := by
  calc
    mixedMoment B raw22456 raw22456Labels = mixedMoment B raw22456step0 raw22456step0Labels := by
      have hz : ∀ j, raw22456 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22456step0 = (fun i j => raw22456 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22456step0 raw22456; decide +kernel
      have hl : raw22456step0Labels = raw22456Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22456 raw22456Labels permutation346 hz
    mixedMoment B raw22456step0 raw22456step0Labels = mixedMoment B raw22456step1 raw22456step1Labels := by
      have hz : ∀ j, raw22456step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw22456step1 = (fun i j => raw22456step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw22456step1 raw22456step0; decide +kernel
      have hl : raw22456step1Labels = raw22456step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22456step0 raw22456step0Labels permutation56 hz
    mixedMoment B raw22456step1 raw22456step1Labels = mixedMoment B raw22456step2 raw22456step2Labels := by
      have ha : raw22456step2 = -raw22456step1 := by apply Matrix.ext; change ∀ i j, raw22456step2 i j = -(raw22456step1 i j); unfold raw22456step2 raw22456step1; decide +kernel
      have hl : raw22456step2Labels = raw22456step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3301 node3301Labels := by rfl

theorem canonical22457 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22457 raw22457Labels = mixedMoment B node1182 node1182Labels := by
  calc
    mixedMoment B raw22457 raw22457Labels = mixedMoment B raw22457step0 raw22457step0Labels := by
      have hz : ∀ j, raw22457 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22457step0 = (fun i j => raw22457 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22457step0 raw22457; decide +kernel
      have hl : raw22457step0Labels = raw22457Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22457 raw22457Labels permutation346 hz
    mixedMoment B raw22457step0 raw22457step0Labels = mixedMoment B raw22457step1 raw22457step1Labels := by
      have ha : raw22457step1 = (fun i j => raw22457step0 (permutation39 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22457step1 raw22457step0; decide +kernel
      have hl : raw22457step1Labels = raw22457step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22457step0 raw22457step0Labels permutation39 permutation2
    _ = mixedMoment B node1182 node1182Labels := by rfl

theorem canonical22458 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22458 raw22458Labels = mixedMoment B node2608 node2608Labels := by
  calc
    mixedMoment B raw22458 raw22458Labels = mixedMoment B raw22458step0 raw22458step0Labels := by
      have hz : ∀ j, raw22458 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22458step0 = (fun i j => raw22458 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22458step0 raw22458; decide +kernel
      have hl : raw22458step0Labels = raw22458Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22458 raw22458Labels permutation346 hz
    mixedMoment B raw22458step0 raw22458step0Labels = mixedMoment B raw22458step1 raw22458step1Labels := by
      have ha : raw22458step1 = (fun i j => raw22458step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22458step1 raw22458step0; decide +kernel
      have hl : raw22458step1Labels = raw22458step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22458step0 raw22458step0Labels permutation33 permutation2
    _ = mixedMoment B node2608 node2608Labels := by rfl

theorem canonical22459 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22459 raw22459Labels = mixedMoment B node2533 node2533Labels := by
  calc
    mixedMoment B raw22459 raw22459Labels = mixedMoment B raw22459step0 raw22459step0Labels := by
      have ha : raw22459step0 = (fun i j => raw22459 (permutation183 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22459step0 raw22459; decide +kernel
      have hl : raw22459step0Labels = raw22459Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22459 raw22459Labels permutation183 permutation2
    _ = mixedMoment B node2533 node2533Labels := by rfl

theorem canonical22460 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22460 raw22460Labels = mixedMoment B node2388 node2388Labels := by
  calc
    mixedMoment B raw22460 raw22460Labels = mixedMoment B raw22460step0 raw22460step0Labels := by
      have hz : ∀ j, raw22460 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22460step0 = (fun i j => raw22460 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22460step0 raw22460; decide +kernel
      have hl : raw22460step0Labels = raw22460Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22460 raw22460Labels permutation346 hz
    mixedMoment B raw22460step0 raw22460step0Labels = mixedMoment B raw22460step1 raw22460step1Labels := by
      have ha : raw22460step1 = (fun i j => raw22460step0 (permutation39 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22460step1 raw22460step0; decide +kernel
      have hl : raw22460step1Labels = raw22460step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22460step0 raw22460step0Labels permutation39 permutation2
    _ = mixedMoment B node2388 node2388Labels := by rfl

theorem canonical22461 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22461 raw22461Labels = mixedMoment B node2673 node2673Labels := by
  calc
    mixedMoment B raw22461 raw22461Labels = mixedMoment B raw22461step0 raw22461step0Labels := by
      have hz : ∀ j, raw22461 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22461step0 = (fun i j => raw22461 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22461step0 raw22461; decide +kernel
      have hl : raw22461step0Labels = raw22461Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22461 raw22461Labels permutation346 hz
    mixedMoment B raw22461step0 raw22461step0Labels = mixedMoment B raw22461step1 raw22461step1Labels := by
      have ha : raw22461step1 = (fun i j => raw22461step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22461step1 raw22461step0; decide +kernel
      have hl : raw22461step1Labels = raw22461step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22461step0 raw22461step0Labels permutation38 permutation2
    _ = mixedMoment B node2673 node2673Labels := by rfl

theorem canonical22462 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22462 raw22462Labels = mixedMoment B node2672 node2672Labels := by
  calc
    mixedMoment B raw22462 raw22462Labels = mixedMoment B raw22462step0 raw22462step0Labels := by
      have hz : ∀ j, raw22462 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22462step0 = (fun i j => raw22462 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22462step0 raw22462; decide +kernel
      have hl : raw22462step0Labels = raw22462Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22462 raw22462Labels permutation346 hz
    mixedMoment B raw22462step0 raw22462step0Labels = mixedMoment B raw22462step1 raw22462step1Labels := by
      have ha : raw22462step1 = (fun i j => raw22462step0 (permutation39 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22462step1 raw22462step0; decide +kernel
      have hl : raw22462step1Labels = raw22462step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22462step0 raw22462step0Labels permutation39 permutation2
    _ = mixedMoment B node2672 node2672Labels := by rfl

theorem canonical22463 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22463 raw22463Labels = mixedMoment B node4088 node4088Labels := by
  calc
    mixedMoment B raw22463 raw22463Labels = mixedMoment B raw22463step0 raw22463step0Labels := by
      have hz : ∀ j, raw22463 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22463step0 = (fun i j => raw22463 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22463step0 raw22463; decide +kernel
      have hl : raw22463step0Labels = raw22463Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22463 raw22463Labels permutation346 hz
    mixedMoment B raw22463step0 raw22463step0Labels = mixedMoment B raw22463step1 raw22463step1Labels := by
      have ha : raw22463step1 = (fun i j => raw22463step0 (permutation39 i) (permutation0 j)) := by apply Matrix.ext; unfold raw22463step1 raw22463step0; decide +kernel
      have hl : raw22463step1Labels = raw22463step0Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22463step0 raw22463step0Labels permutation39 permutation0
    _ = mixedMoment B node4088 node4088Labels := by rfl

theorem canonical22464 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22464 raw22464Labels = mixedMoment B node1196 node1196Labels := by
  calc
    mixedMoment B raw22464 raw22464Labels = mixedMoment B raw22464step0 raw22464step0Labels := by
      have ha : raw22464step0 = (fun i j => raw22464 (permutation183 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22464step0 raw22464; decide +kernel
      have hl : raw22464step0Labels = raw22464Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22464 raw22464Labels permutation183 permutation2
    _ = mixedMoment B node1196 node1196Labels := by rfl

theorem canonical22465 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22465 raw22465Labels = mixedMoment B node2609 node2609Labels := by
  calc
    mixedMoment B raw22465 raw22465Labels = mixedMoment B raw22465step0 raw22465step0Labels := by
      have ha : raw22465step0 = (fun i j => raw22465 (permutation153 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22465step0 raw22465; decide +kernel
      have hl : raw22465step0Labels = raw22465Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22465 raw22465Labels permutation153 permutation2
    _ = mixedMoment B node2609 node2609Labels := by rfl

theorem canonical22466 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22466 raw22466Labels = mixedMoment B node2452 node2452Labels := by
  calc
    mixedMoment B raw22466 raw22466Labels = mixedMoment B raw22466step0 raw22466step0Labels := by
      have ha : raw22466step0 = (fun i j => raw22466 (permutation183 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22466step0 raw22466; decide +kernel
      have hl : raw22466step0Labels = raw22466Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22466 raw22466Labels permutation183 permutation2
    _ = mixedMoment B node2452 node2452Labels := by rfl

theorem canonical22467 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22467 raw22467Labels = mixedMoment B node2452 node2452Labels := by
  calc
    mixedMoment B raw22467 raw22467Labels = mixedMoment B raw22467step0 raw22467step0Labels := by
      have ha : raw22467step0 = (fun i j => raw22467 (permutation207 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22467step0 raw22467; decide +kernel
      have hl : raw22467step0Labels = raw22467Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22467 raw22467Labels permutation207 permutation2
    _ = mixedMoment B node2452 node2452Labels := by rfl

theorem canonical22468 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22468 raw22468Labels = mixedMoment B node2695 node2695Labels := by
  calc
    mixedMoment B raw22468 raw22468Labels = mixedMoment B raw22468step0 raw22468step0Labels := by
      have ha : raw22468step0 = (fun i j => raw22468 (permutation182 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22468step0 raw22468; decide +kernel
      have hl : raw22468step0Labels = raw22468Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22468 raw22468Labels permutation182 permutation2
    _ = mixedMoment B node2695 node2695Labels := by rfl

theorem canonical22469 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22469 raw22469Labels = mixedMoment B node2694 node2694Labels := by
  calc
    mixedMoment B raw22469 raw22469Labels = mixedMoment B raw22469step0 raw22469step0Labels := by
      have ha : raw22469step0 = (fun i j => raw22469 (permutation183 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22469step0 raw22469; decide +kernel
      have hl : raw22469step0Labels = raw22469Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22469 raw22469Labels permutation183 permutation2
    _ = mixedMoment B node2694 node2694Labels := by rfl

theorem canonical22470 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22470 raw22470Labels = mixedMoment B node4090 node4090Labels := by
  calc
    mixedMoment B raw22470 raw22470Labels = mixedMoment B raw22470step0 raw22470step0Labels := by
      have ha : raw22470step0 = (fun i j => raw22470 (permutation183 i) (permutation0 j)) := by apply Matrix.ext; unfold raw22470step0 raw22470; decide +kernel
      have hl : raw22470step0Labels = raw22470Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22470 raw22470Labels permutation183 permutation0
    _ = mixedMoment B node4090 node4090Labels := by rfl

theorem canonical22506 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22506 raw22506Labels = mixedMoment B node4466 node4466Labels := by
  calc
    mixedMoment B raw22506 raw22506Labels = mixedMoment B raw22506step0 raw22506step0Labels := by
      have hz : ∀ j, raw22506 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22506step0 = (fun i j => raw22506 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22506step0 raw22506; decide +kernel
      have hl : raw22506step0Labels = raw22506Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22506 raw22506Labels permutation434 hz
    mixedMoment B raw22506step0 raw22506step0Labels = mixedMoment B raw22506step1 raw22506step1Labels := by
      have hz : ∀ j, raw22506step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22506step1 = (fun i j => raw22506step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22506step1 raw22506step0; decide +kernel
      have hl : raw22506step1Labels = raw22506step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22506step0 raw22506step0Labels permutation80 hz
    mixedMoment B raw22506step1 raw22506step1Labels = mixedMoment B raw22506step2 raw22506step2Labels := by
      have ha : raw22506step2 = (fun i j => raw22506step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw22506step2 raw22506step1; decide +kernel
      have hl : raw22506step2Labels = raw22506step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22506step1 raw22506step1Labels permutation9 permutation7
    mixedMoment B raw22506step2 raw22506step2Labels = mixedMoment B raw22506step3 raw22506step3Labels := by
      have ha : raw22506step3 = raw22506step2 := by apply Matrix.ext; unfold raw22506step3 raw22506step2; decide +kernel
      have hl : raw22506step2Labels = labelEmbedding10 ∘ raw22506step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22506step2 raw22506step2Labels raw22506step3Labels labelEmbedding10 hl
    _ = mixedMoment B node4466 node4466Labels := by rfl

theorem canonical22507 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22507 raw22507Labels = mixedMoment B node4466 node4466Labels := by
  calc
    mixedMoment B raw22507 raw22507Labels = mixedMoment B raw22507step0 raw22507step0Labels := by
      have hz : ∀ j, raw22507 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22507step0 = (fun i j => raw22507 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22507step0 raw22507; decide +kernel
      have hl : raw22507step0Labels = raw22507Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22507 raw22507Labels permutation434 hz
    mixedMoment B raw22507step0 raw22507step0Labels = mixedMoment B raw22507step1 raw22507step1Labels := by
      have hz : ∀ j, raw22507step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw22507step1 = (fun i j => raw22507step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw22507step1 raw22507step0; decide +kernel
      have hl : raw22507step1Labels = raw22507step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22507step0 raw22507step0Labels permutation56 hz
    mixedMoment B raw22507step1 raw22507step1Labels = mixedMoment B raw22507step2 raw22507step2Labels := by
      have ha : raw22507step2 = (fun i j => raw22507step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw22507step2 raw22507step1; decide +kernel
      have hl : raw22507step2Labels = raw22507step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22507step1 raw22507step1Labels permutation9 permutation7
    mixedMoment B raw22507step2 raw22507step2Labels = mixedMoment B raw22507step3 raw22507step3Labels := by
      have ha : raw22507step3 = raw22507step2 := by apply Matrix.ext; unfold raw22507step3 raw22507step2; decide +kernel
      have hl : raw22507step2Labels = labelEmbedding10 ∘ raw22507step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22507step2 raw22507step2Labels raw22507step3Labels labelEmbedding10 hl
    _ = mixedMoment B node4466 node4466Labels := by rfl

theorem canonical22508 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22508 raw22508Labels = mixedMoment B node4466 node4466Labels := by
  calc
    mixedMoment B raw22508 raw22508Labels = mixedMoment B raw22508step0 raw22508step0Labels := by
      have hz : ∀ j, raw22508 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22508step0 = (fun i j => raw22508 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22508step0 raw22508; decide +kernel
      have hl : raw22508step0Labels = raw22508Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22508 raw22508Labels permutation346 hz
    mixedMoment B raw22508step0 raw22508step0Labels = mixedMoment B raw22508step1 raw22508step1Labels := by
      have hz : ∀ j, raw22508step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw22508step1 = (fun i j => raw22508step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw22508step1 raw22508step0; decide +kernel
      have hl : raw22508step1Labels = raw22508step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22508step0 raw22508step0Labels permutation56 hz
    mixedMoment B raw22508step1 raw22508step1Labels = mixedMoment B raw22508step2 raw22508step2Labels := by
      have ha : raw22508step2 = (fun i j => raw22508step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw22508step2 raw22508step1; decide +kernel
      have hl : raw22508step2Labels = raw22508step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22508step1 raw22508step1Labels permutation9 permutation7
    mixedMoment B raw22508step2 raw22508step2Labels = mixedMoment B raw22508step3 raw22508step3Labels := by
      have ha : raw22508step3 = raw22508step2 := by apply Matrix.ext; unfold raw22508step3 raw22508step2; decide +kernel
      have hl : raw22508step2Labels = labelEmbedding10 ∘ raw22508step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22508step2 raw22508step2Labels raw22508step3Labels labelEmbedding10 hl
    _ = mixedMoment B node4466 node4466Labels := by rfl

theorem canonical22509 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22509 raw22509Labels = mixedMoment B node4510 node4510Labels := by
  calc
    mixedMoment B raw22509 raw22509Labels = mixedMoment B raw22509step0 raw22509step0Labels := by
      have hz : ∀ j, raw22509 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22509step0 = (fun i j => raw22509 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22509step0 raw22509; decide +kernel
      have hl : raw22509step0Labels = raw22509Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22509 raw22509Labels permutation434 hz
    mixedMoment B raw22509step0 raw22509step0Labels = mixedMoment B raw22509step1 raw22509step1Labels := by
      have hz : ∀ j, raw22509step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22509step1 = (fun i j => raw22509step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22509step1 raw22509step0; decide +kernel
      have hl : raw22509step1Labels = raw22509step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22509step0 raw22509step0Labels permutation80 hz
    mixedMoment B raw22509step1 raw22509step1Labels = mixedMoment B raw22509step2 raw22509step2Labels := by
      have hz : ∀ j, raw22509step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw22509step2 = (fun i j => raw22509step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw22509step2 raw22509step1; decide +kernel
      have hl : raw22509step2Labels = raw22509step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22509step1 raw22509step1Labels permutation14 hz
    mixedMoment B raw22509step2 raw22509step2Labels = mixedMoment B raw22509step3 raw22509step3Labels := by
      have ha : raw22509step3 = (fun i j => raw22509step2 (permutation3 i) (permutation7 j)) := by apply Matrix.ext; unfold raw22509step3 raw22509step2; decide +kernel
      have hl : raw22509step3Labels = raw22509step2Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22509step2 raw22509step2Labels permutation3 permutation7
    mixedMoment B raw22509step3 raw22509step3Labels = mixedMoment B raw22509step4 raw22509step4Labels := by
      have ha : raw22509step4 = raw22509step3 := by apply Matrix.ext; unfold raw22509step4 raw22509step3; decide +kernel
      have hl : raw22509step3Labels = labelEmbedding10 ∘ raw22509step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22509step3 raw22509step3Labels raw22509step4Labels labelEmbedding10 hl
    _ = mixedMoment B node4510 node4510Labels := by rfl

theorem canonical22510 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22510 raw22510Labels = mixedMoment B node4511 node4511Labels := by
  calc
    mixedMoment B raw22510 raw22510Labels = mixedMoment B raw22510step0 raw22510step0Labels := by
      have hz : ∀ j, raw22510 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22510step0 = (fun i j => raw22510 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22510step0 raw22510; decide +kernel
      have hl : raw22510step0Labels = raw22510Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22510 raw22510Labels permutation434 hz
    mixedMoment B raw22510step0 raw22510step0Labels = mixedMoment B raw22510step1 raw22510step1Labels := by
      have hz : ∀ j, raw22510step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22510step1 = (fun i j => raw22510step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22510step1 raw22510step0; decide +kernel
      have hl : raw22510step1Labels = raw22510step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22510step0 raw22510step0Labels permutation80 hz
    mixedMoment B raw22510step1 raw22510step1Labels = mixedMoment B raw22510step2 raw22510step2Labels := by
      have hz : ∀ j, raw22510step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw22510step2 = (fun i j => raw22510step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw22510step2 raw22510step1; decide +kernel
      have hl : raw22510step2Labels = raw22510step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22510step1 raw22510step1Labels permutation14 hz
    mixedMoment B raw22510step2 raw22510step2Labels = mixedMoment B raw22510step3 raw22510step3Labels := by
      have ha : raw22510step3 = (fun i j => raw22510step2 (permutation3 i) (permutation7 j)) := by apply Matrix.ext; unfold raw22510step3 raw22510step2; decide +kernel
      have hl : raw22510step3Labels = raw22510step2Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22510step2 raw22510step2Labels permutation3 permutation7
    mixedMoment B raw22510step3 raw22510step3Labels = mixedMoment B raw22510step4 raw22510step4Labels := by
      have ha : raw22510step4 = raw22510step3 := by apply Matrix.ext; unfold raw22510step4 raw22510step3; decide +kernel
      have hl : raw22510step3Labels = labelEmbedding10 ∘ raw22510step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22510step3 raw22510step3Labels raw22510step4Labels labelEmbedding10 hl
    _ = mixedMoment B node4511 node4511Labels := by rfl

theorem canonical22511 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22511 raw22511Labels = mixedMoment B node4466 node4466Labels := by
  calc
    mixedMoment B raw22511 raw22511Labels = mixedMoment B raw22511step0 raw22511step0Labels := by
      have hz : ∀ j, raw22511 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22511step0 = (fun i j => raw22511 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22511step0 raw22511; decide +kernel
      have hl : raw22511step0Labels = raw22511Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22511 raw22511Labels permutation434 hz
    mixedMoment B raw22511step0 raw22511step0Labels = mixedMoment B raw22511step1 raw22511step1Labels := by
      have hz : ∀ j, raw22511step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22511step1 = (fun i j => raw22511step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22511step1 raw22511step0; decide +kernel
      have hl : raw22511step1Labels = raw22511step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22511step0 raw22511step0Labels permutation80 hz
    mixedMoment B raw22511step1 raw22511step1Labels = mixedMoment B raw22511step2 raw22511step2Labels := by
      have ha : raw22511step2 = (fun i j => raw22511step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw22511step2 raw22511step1; decide +kernel
      have hl : raw22511step2Labels = raw22511step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22511step1 raw22511step1Labels permutation8 permutation6
    mixedMoment B raw22511step2 raw22511step2Labels = mixedMoment B raw22511step3 raw22511step3Labels := by
      have ha : raw22511step3 = raw22511step2 := by apply Matrix.ext; unfold raw22511step3 raw22511step2; decide +kernel
      have hl : raw22511step2Labels = labelEmbedding9 ∘ raw22511step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22511step2 raw22511step2Labels raw22511step3Labels labelEmbedding9 hl
    _ = mixedMoment B node4466 node4466Labels := by rfl

theorem canonical22512 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22512 raw22512Labels = mixedMoment B node4592 node4592Labels := by
  calc
    mixedMoment B raw22512 raw22512Labels = mixedMoment B raw22512step0 raw22512step0Labels := by
      have hz : ∀ j, raw22512 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22512step0 = (fun i j => raw22512 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22512step0 raw22512; decide +kernel
      have hl : raw22512step0Labels = raw22512Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22512 raw22512Labels permutation434 hz
    mixedMoment B raw22512step0 raw22512step0Labels = mixedMoment B raw22512step1 raw22512step1Labels := by
      have ha : raw22512step1 = (fun i j => raw22512step0 (permutation38 i) (permutation6 j)) := by apply Matrix.ext; unfold raw22512step1 raw22512step0; decide +kernel
      have hl : raw22512step1Labels = raw22512step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22512step0 raw22512step0Labels permutation38 permutation6
    mixedMoment B raw22512step1 raw22512step1Labels = mixedMoment B raw22512step2 raw22512step2Labels := by
      have ha : raw22512step2 = raw22512step1 := by apply Matrix.ext; unfold raw22512step2 raw22512step1; decide +kernel
      have hl : raw22512step1Labels = labelEmbedding9 ∘ raw22512step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22512step1 raw22512step1Labels raw22512step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4592 node4592Labels := by rfl

theorem canonical22513 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22513 raw22513Labels = mixedMoment B node4592 node4592Labels := by
  calc
    mixedMoment B raw22513 raw22513Labels = mixedMoment B raw22513step0 raw22513step0Labels := by
      have hz : ∀ j, raw22513 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22513step0 = (fun i j => raw22513 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22513step0 raw22513; decide +kernel
      have hl : raw22513step0Labels = raw22513Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22513 raw22513Labels permutation346 hz
    mixedMoment B raw22513step0 raw22513step0Labels = mixedMoment B raw22513step1 raw22513step1Labels := by
      have ha : raw22513step1 = (fun i j => raw22513step0 (permutation38 i) (permutation6 j)) := by apply Matrix.ext; unfold raw22513step1 raw22513step0; decide +kernel
      have hl : raw22513step1Labels = raw22513step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22513step0 raw22513step0Labels permutation38 permutation6
    mixedMoment B raw22513step1 raw22513step1Labels = mixedMoment B raw22513step2 raw22513step2Labels := by
      have ha : raw22513step2 = raw22513step1 := by apply Matrix.ext; unfold raw22513step2 raw22513step1; decide +kernel
      have hl : raw22513step1Labels = labelEmbedding9 ∘ raw22513step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22513step1 raw22513step1Labels raw22513step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4592 node4592Labels := by rfl

theorem canonical22514 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22514 raw22514Labels = mixedMoment B node4611 node4611Labels := by
  calc
    mixedMoment B raw22514 raw22514Labels = mixedMoment B raw22514step0 raw22514step0Labels := by
      have hz : ∀ j, raw22514 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22514step0 = (fun i j => raw22514 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22514step0 raw22514; decide +kernel
      have hl : raw22514step0Labels = raw22514Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22514 raw22514Labels permutation434 hz
    mixedMoment B raw22514step0 raw22514step0Labels = mixedMoment B raw22514step1 raw22514step1Labels := by
      have hz : ∀ j, raw22514step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22514step1 = (fun i j => raw22514step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22514step1 raw22514step0; decide +kernel
      have hl : raw22514step1Labels = raw22514step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22514step0 raw22514step0Labels permutation80 hz
    mixedMoment B raw22514step1 raw22514step1Labels = mixedMoment B raw22514step2 raw22514step2Labels := by
      have ha : raw22514step2 = (fun i j => raw22514step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw22514step2 raw22514step1; decide +kernel
      have hl : raw22514step2Labels = raw22514step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22514step1 raw22514step1Labels permutation9 permutation7
    mixedMoment B raw22514step2 raw22514step2Labels = mixedMoment B raw22514step3 raw22514step3Labels := by
      have ha : raw22514step3 = raw22514step2 := by apply Matrix.ext; unfold raw22514step3 raw22514step2; decide +kernel
      have hl : raw22514step2Labels = labelEmbedding10 ∘ raw22514step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22514step2 raw22514step2Labels raw22514step3Labels labelEmbedding10 hl
    _ = mixedMoment B node4611 node4611Labels := by rfl

theorem canonical22515 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22515 raw22515Labels = mixedMoment B node4612 node4612Labels := by
  calc
    mixedMoment B raw22515 raw22515Labels = mixedMoment B raw22515step0 raw22515step0Labels := by
      have hz : ∀ j, raw22515 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22515step0 = (fun i j => raw22515 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22515step0 raw22515; decide +kernel
      have hl : raw22515step0Labels = raw22515Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22515 raw22515Labels permutation434 hz
    mixedMoment B raw22515step0 raw22515step0Labels = mixedMoment B raw22515step1 raw22515step1Labels := by
      have hz : ∀ j, raw22515step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22515step1 = (fun i j => raw22515step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22515step1 raw22515step0; decide +kernel
      have hl : raw22515step1Labels = raw22515step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22515step0 raw22515step0Labels permutation80 hz
    mixedMoment B raw22515step1 raw22515step1Labels = mixedMoment B raw22515step2 raw22515step2Labels := by
      have ha : raw22515step2 = (fun i j => raw22515step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw22515step2 raw22515step1; decide +kernel
      have hl : raw22515step2Labels = raw22515step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22515step1 raw22515step1Labels permutation9 permutation7
    mixedMoment B raw22515step2 raw22515step2Labels = mixedMoment B raw22515step3 raw22515step3Labels := by
      have ha : raw22515step3 = raw22515step2 := by apply Matrix.ext; unfold raw22515step3 raw22515step2; decide +kernel
      have hl : raw22515step2Labels = labelEmbedding10 ∘ raw22515step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22515step2 raw22515step2Labels raw22515step3Labels labelEmbedding10 hl
    _ = mixedMoment B node4612 node4612Labels := by rfl

theorem canonical22516 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22516 raw22516Labels = mixedMoment B node4466 node4466Labels := by
  calc
    mixedMoment B raw22516 raw22516Labels = mixedMoment B raw22516step0 raw22516step0Labels := by
      have hz : ∀ j, raw22516 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22516step0 = (fun i j => raw22516 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22516step0 raw22516; decide +kernel
      have hl : raw22516step0Labels = raw22516Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22516 raw22516Labels permutation434 hz
    mixedMoment B raw22516step0 raw22516step0Labels = mixedMoment B raw22516step1 raw22516step1Labels := by
      have hz : ∀ j, raw22516step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw22516step1 = (fun i j => raw22516step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw22516step1 raw22516step0; decide +kernel
      have hl : raw22516step1Labels = raw22516step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22516step0 raw22516step0Labels permutation56 hz
    mixedMoment B raw22516step1 raw22516step1Labels = mixedMoment B raw22516step2 raw22516step2Labels := by
      have ha : raw22516step2 = (fun i j => raw22516step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw22516step2 raw22516step1; decide +kernel
      have hl : raw22516step2Labels = raw22516step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22516step1 raw22516step1Labels permutation8 permutation6
    mixedMoment B raw22516step2 raw22516step2Labels = mixedMoment B raw22516step3 raw22516step3Labels := by
      have ha : raw22516step3 = raw22516step2 := by apply Matrix.ext; unfold raw22516step3 raw22516step2; decide +kernel
      have hl : raw22516step2Labels = labelEmbedding9 ∘ raw22516step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22516step2 raw22516step2Labels raw22516step3Labels labelEmbedding9 hl
    _ = mixedMoment B node4466 node4466Labels := by rfl

theorem canonical22517 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22517 raw22517Labels = mixedMoment B node4592 node4592Labels := by
  calc
    mixedMoment B raw22517 raw22517Labels = mixedMoment B raw22517step0 raw22517step0Labels := by
      have hz : ∀ j, raw22517 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22517step0 = (fun i j => raw22517 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22517step0 raw22517; decide +kernel
      have hl : raw22517step0Labels = raw22517Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22517 raw22517Labels permutation434 hz
    mixedMoment B raw22517step0 raw22517step0Labels = mixedMoment B raw22517step1 raw22517step1Labels := by
      have ha : raw22517step1 = (fun i j => raw22517step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw22517step1 raw22517step0; decide +kernel
      have hl : raw22517step1Labels = raw22517step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22517step0 raw22517step0Labels permutation32 permutation6
    mixedMoment B raw22517step1 raw22517step1Labels = mixedMoment B raw22517step2 raw22517step2Labels := by
      have ha : raw22517step2 = raw22517step1 := by apply Matrix.ext; unfold raw22517step2 raw22517step1; decide +kernel
      have hl : raw22517step1Labels = labelEmbedding9 ∘ raw22517step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22517step1 raw22517step1Labels raw22517step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4592 node4592Labels := by rfl

theorem canonical22518 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22518 raw22518Labels = mixedMoment B node4592 node4592Labels := by
  calc
    mixedMoment B raw22518 raw22518Labels = mixedMoment B raw22518step0 raw22518step0Labels := by
      have hz : ∀ j, raw22518 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw22518step0 = (fun i j => raw22518 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw22518step0 raw22518; decide +kernel
      have hl : raw22518step0Labels = raw22518Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22518 raw22518Labels permutation265 hz
    mixedMoment B raw22518step0 raw22518step0Labels = mixedMoment B raw22518step1 raw22518step1Labels := by
      have ha : raw22518step1 = (fun i j => raw22518step0 (permutation38 i) (permutation6 j)) := by apply Matrix.ext; unfold raw22518step1 raw22518step0; decide +kernel
      have hl : raw22518step1Labels = raw22518step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22518step0 raw22518step0Labels permutation38 permutation6
    mixedMoment B raw22518step1 raw22518step1Labels = mixedMoment B raw22518step2 raw22518step2Labels := by
      have ha : raw22518step2 = raw22518step1 := by apply Matrix.ext; unfold raw22518step2 raw22518step1; decide +kernel
      have hl : raw22518step1Labels = labelEmbedding9 ∘ raw22518step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22518step1 raw22518step1Labels raw22518step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4592 node4592Labels := by rfl

theorem canonical22519 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22519 raw22519Labels = mixedMoment B node4611 node4611Labels := by
  calc
    mixedMoment B raw22519 raw22519Labels = mixedMoment B raw22519step0 raw22519step0Labels := by
      have hz : ∀ j, raw22519 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22519step0 = (fun i j => raw22519 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22519step0 raw22519; decide +kernel
      have hl : raw22519step0Labels = raw22519Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22519 raw22519Labels permutation434 hz
    mixedMoment B raw22519step0 raw22519step0Labels = mixedMoment B raw22519step1 raw22519step1Labels := by
      have hz : ∀ j, raw22519step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw22519step1 = (fun i j => raw22519step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw22519step1 raw22519step0; decide +kernel
      have hl : raw22519step1Labels = raw22519step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22519step0 raw22519step0Labels permutation56 hz
    mixedMoment B raw22519step1 raw22519step1Labels = mixedMoment B raw22519step2 raw22519step2Labels := by
      have ha : raw22519step2 = (fun i j => raw22519step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw22519step2 raw22519step1; decide +kernel
      have hl : raw22519step2Labels = raw22519step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22519step1 raw22519step1Labels permutation9 permutation7
    mixedMoment B raw22519step2 raw22519step2Labels = mixedMoment B raw22519step3 raw22519step3Labels := by
      have ha : raw22519step3 = raw22519step2 := by apply Matrix.ext; unfold raw22519step3 raw22519step2; decide +kernel
      have hl : raw22519step2Labels = labelEmbedding10 ∘ raw22519step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22519step2 raw22519step2Labels raw22519step3Labels labelEmbedding10 hl
    _ = mixedMoment B node4611 node4611Labels := by rfl

theorem canonical22520 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22520 raw22520Labels = mixedMoment B node4612 node4612Labels := by
  calc
    mixedMoment B raw22520 raw22520Labels = mixedMoment B raw22520step0 raw22520step0Labels := by
      have hz : ∀ j, raw22520 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22520step0 = (fun i j => raw22520 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22520step0 raw22520; decide +kernel
      have hl : raw22520step0Labels = raw22520Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22520 raw22520Labels permutation434 hz
    mixedMoment B raw22520step0 raw22520step0Labels = mixedMoment B raw22520step1 raw22520step1Labels := by
      have hz : ∀ j, raw22520step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw22520step1 = (fun i j => raw22520step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw22520step1 raw22520step0; decide +kernel
      have hl : raw22520step1Labels = raw22520step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22520step0 raw22520step0Labels permutation56 hz
    mixedMoment B raw22520step1 raw22520step1Labels = mixedMoment B raw22520step2 raw22520step2Labels := by
      have ha : raw22520step2 = (fun i j => raw22520step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw22520step2 raw22520step1; decide +kernel
      have hl : raw22520step2Labels = raw22520step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22520step1 raw22520step1Labels permutation9 permutation7
    mixedMoment B raw22520step2 raw22520step2Labels = mixedMoment B raw22520step3 raw22520step3Labels := by
      have ha : raw22520step3 = raw22520step2 := by apply Matrix.ext; unfold raw22520step3 raw22520step2; decide +kernel
      have hl : raw22520step2Labels = labelEmbedding10 ∘ raw22520step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22520step2 raw22520step2Labels raw22520step3Labels labelEmbedding10 hl
    _ = mixedMoment B node4612 node4612Labels := by rfl

theorem canonical22521 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22521 raw22521Labels = mixedMoment B node4466 node4466Labels := by
  calc
    mixedMoment B raw22521 raw22521Labels = mixedMoment B raw22521step0 raw22521step0Labels := by
      have hz : ∀ j, raw22521 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22521step0 = (fun i j => raw22521 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22521step0 raw22521; decide +kernel
      have hl : raw22521step0Labels = raw22521Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22521 raw22521Labels permutation346 hz
    mixedMoment B raw22521step0 raw22521step0Labels = mixedMoment B raw22521step1 raw22521step1Labels := by
      have hz : ∀ j, raw22521step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw22521step1 = (fun i j => raw22521step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw22521step1 raw22521step0; decide +kernel
      have hl : raw22521step1Labels = raw22521step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22521step0 raw22521step0Labels permutation56 hz
    mixedMoment B raw22521step1 raw22521step1Labels = mixedMoment B raw22521step2 raw22521step2Labels := by
      have ha : raw22521step2 = (fun i j => raw22521step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw22521step2 raw22521step1; decide +kernel
      have hl : raw22521step2Labels = raw22521step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22521step1 raw22521step1Labels permutation8 permutation6
    mixedMoment B raw22521step2 raw22521step2Labels = mixedMoment B raw22521step3 raw22521step3Labels := by
      have ha : raw22521step3 = raw22521step2 := by apply Matrix.ext; unfold raw22521step3 raw22521step2; decide +kernel
      have hl : raw22521step2Labels = labelEmbedding9 ∘ raw22521step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22521step2 raw22521step2Labels raw22521step3Labels labelEmbedding9 hl
    _ = mixedMoment B node4466 node4466Labels := by rfl

theorem canonical22522 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22522 raw22522Labels = mixedMoment B node4592 node4592Labels := by
  calc
    mixedMoment B raw22522 raw22522Labels = mixedMoment B raw22522step0 raw22522step0Labels := by
      have hz : ∀ j, raw22522 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22522step0 = (fun i j => raw22522 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22522step0 raw22522; decide +kernel
      have hl : raw22522step0Labels = raw22522Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22522 raw22522Labels permutation346 hz
    mixedMoment B raw22522step0 raw22522step0Labels = mixedMoment B raw22522step1 raw22522step1Labels := by
      have ha : raw22522step1 = (fun i j => raw22522step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw22522step1 raw22522step0; decide +kernel
      have hl : raw22522step1Labels = raw22522step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22522step0 raw22522step0Labels permutation32 permutation6
    mixedMoment B raw22522step1 raw22522step1Labels = mixedMoment B raw22522step2 raw22522step2Labels := by
      have ha : raw22522step2 = raw22522step1 := by apply Matrix.ext; unfold raw22522step2 raw22522step1; decide +kernel
      have hl : raw22522step1Labels = labelEmbedding9 ∘ raw22522step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22522step1 raw22522step1Labels raw22522step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4592 node4592Labels := by rfl

theorem canonical22523 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22523 raw22523Labels = mixedMoment B node4592 node4592Labels := by
  calc
    mixedMoment B raw22523 raw22523Labels = mixedMoment B raw22523step0 raw22523step0Labels := by
      have hz : ∀ j, raw22523 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw22523step0 = (fun i j => raw22523 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw22523step0 raw22523; decide +kernel
      have hl : raw22523step0Labels = raw22523Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22523 raw22523Labels permutation265 hz
    mixedMoment B raw22523step0 raw22523step0Labels = mixedMoment B raw22523step1 raw22523step1Labels := by
      have ha : raw22523step1 = (fun i j => raw22523step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw22523step1 raw22523step0; decide +kernel
      have hl : raw22523step1Labels = raw22523step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22523step0 raw22523step0Labels permutation32 permutation6
    mixedMoment B raw22523step1 raw22523step1Labels = mixedMoment B raw22523step2 raw22523step2Labels := by
      have ha : raw22523step2 = raw22523step1 := by apply Matrix.ext; unfold raw22523step2 raw22523step1; decide +kernel
      have hl : raw22523step1Labels = labelEmbedding9 ∘ raw22523step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22523step1 raw22523step1Labels raw22523step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4592 node4592Labels := by rfl

theorem canonical22524 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22524 raw22524Labels = mixedMoment B node4611 node4611Labels := by
  calc
    mixedMoment B raw22524 raw22524Labels = mixedMoment B raw22524step0 raw22524step0Labels := by
      have hz : ∀ j, raw22524 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22524step0 = (fun i j => raw22524 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22524step0 raw22524; decide +kernel
      have hl : raw22524step0Labels = raw22524Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22524 raw22524Labels permutation346 hz
    mixedMoment B raw22524step0 raw22524step0Labels = mixedMoment B raw22524step1 raw22524step1Labels := by
      have hz : ∀ j, raw22524step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw22524step1 = (fun i j => raw22524step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw22524step1 raw22524step0; decide +kernel
      have hl : raw22524step1Labels = raw22524step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22524step0 raw22524step0Labels permutation56 hz
    mixedMoment B raw22524step1 raw22524step1Labels = mixedMoment B raw22524step2 raw22524step2Labels := by
      have ha : raw22524step2 = (fun i j => raw22524step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw22524step2 raw22524step1; decide +kernel
      have hl : raw22524step2Labels = raw22524step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22524step1 raw22524step1Labels permutation9 permutation7
    mixedMoment B raw22524step2 raw22524step2Labels = mixedMoment B raw22524step3 raw22524step3Labels := by
      have ha : raw22524step3 = raw22524step2 := by apply Matrix.ext; unfold raw22524step3 raw22524step2; decide +kernel
      have hl : raw22524step2Labels = labelEmbedding10 ∘ raw22524step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22524step2 raw22524step2Labels raw22524step3Labels labelEmbedding10 hl
    _ = mixedMoment B node4611 node4611Labels := by rfl

theorem canonical22525 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22525 raw22525Labels = mixedMoment B node4612 node4612Labels := by
  calc
    mixedMoment B raw22525 raw22525Labels = mixedMoment B raw22525step0 raw22525step0Labels := by
      have hz : ∀ j, raw22525 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22525step0 = (fun i j => raw22525 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22525step0 raw22525; decide +kernel
      have hl : raw22525step0Labels = raw22525Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22525 raw22525Labels permutation346 hz
    mixedMoment B raw22525step0 raw22525step0Labels = mixedMoment B raw22525step1 raw22525step1Labels := by
      have hz : ∀ j, raw22525step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw22525step1 = (fun i j => raw22525step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw22525step1 raw22525step0; decide +kernel
      have hl : raw22525step1Labels = raw22525step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22525step0 raw22525step0Labels permutation56 hz
    mixedMoment B raw22525step1 raw22525step1Labels = mixedMoment B raw22525step2 raw22525step2Labels := by
      have ha : raw22525step2 = (fun i j => raw22525step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw22525step2 raw22525step1; decide +kernel
      have hl : raw22525step2Labels = raw22525step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22525step1 raw22525step1Labels permutation9 permutation7
    mixedMoment B raw22525step2 raw22525step2Labels = mixedMoment B raw22525step3 raw22525step3Labels := by
      have ha : raw22525step3 = raw22525step2 := by apply Matrix.ext; unfold raw22525step3 raw22525step2; decide +kernel
      have hl : raw22525step2Labels = labelEmbedding10 ∘ raw22525step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22525step2 raw22525step2Labels raw22525step3Labels labelEmbedding10 hl
    _ = mixedMoment B node4612 node4612Labels := by rfl

theorem canonical22526 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22526 raw22526Labels = mixedMoment B node4511 node4511Labels := by
  calc
    mixedMoment B raw22526 raw22526Labels = mixedMoment B raw22526step0 raw22526step0Labels := by
      have hz : ∀ j, raw22526 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22526step0 = (fun i j => raw22526 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22526step0 raw22526; decide +kernel
      have hl : raw22526step0Labels = raw22526Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22526 raw22526Labels permutation434 hz
    mixedMoment B raw22526step0 raw22526step0Labels = mixedMoment B raw22526step1 raw22526step1Labels := by
      have hz : ∀ j, raw22526step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22526step1 = (fun i j => raw22526step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22526step1 raw22526step0; decide +kernel
      have hl : raw22526step1Labels = raw22526step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22526step0 raw22526step0Labels permutation80 hz
    mixedMoment B raw22526step1 raw22526step1Labels = mixedMoment B raw22526step2 raw22526step2Labels := by
      have hz : ∀ j, raw22526step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw22526step2 = (fun i j => raw22526step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw22526step2 raw22526step1; decide +kernel
      have hl : raw22526step2Labels = raw22526step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22526step1 raw22526step1Labels permutation14 hz
    mixedMoment B raw22526step2 raw22526step2Labels = mixedMoment B raw22526step3 raw22526step3Labels := by
      have ha : raw22526step3 = (fun i j => raw22526step2 (permutation2 i) (permutation6 j)) := by apply Matrix.ext; unfold raw22526step3 raw22526step2; decide +kernel
      have hl : raw22526step3Labels = raw22526step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22526step2 raw22526step2Labels permutation2 permutation6
    mixedMoment B raw22526step3 raw22526step3Labels = mixedMoment B raw22526step4 raw22526step4Labels := by
      have ha : raw22526step4 = raw22526step3 := by apply Matrix.ext; unfold raw22526step4 raw22526step3; decide +kernel
      have hl : raw22526step3Labels = labelEmbedding9 ∘ raw22526step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22526step3 raw22526step3Labels raw22526step4Labels labelEmbedding9 hl
    _ = mixedMoment B node4511 node4511Labels := by rfl

theorem canonical22527 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22527 raw22527Labels = mixedMoment B node4612 node4612Labels := by
  calc
    mixedMoment B raw22527 raw22527Labels = mixedMoment B raw22527step0 raw22527step0Labels := by
      have hz : ∀ j, raw22527 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22527step0 = (fun i j => raw22527 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22527step0 raw22527; decide +kernel
      have hl : raw22527step0Labels = raw22527Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22527 raw22527Labels permutation434 hz
    mixedMoment B raw22527step0 raw22527step0Labels = mixedMoment B raw22527step1 raw22527step1Labels := by
      have hz : ∀ j, raw22527step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22527step1 = (fun i j => raw22527step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22527step1 raw22527step0; decide +kernel
      have hl : raw22527step1Labels = raw22527step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22527step0 raw22527step0Labels permutation80 hz
    mixedMoment B raw22527step1 raw22527step1Labels = mixedMoment B raw22527step2 raw22527step2Labels := by
      have ha : raw22527step2 = (fun i j => raw22527step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw22527step2 raw22527step1; decide +kernel
      have hl : raw22527step2Labels = raw22527step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22527step1 raw22527step1Labels permutation8 permutation6
    mixedMoment B raw22527step2 raw22527step2Labels = mixedMoment B raw22527step3 raw22527step3Labels := by
      have ha : raw22527step3 = raw22527step2 := by apply Matrix.ext; unfold raw22527step3 raw22527step2; decide +kernel
      have hl : raw22527step2Labels = labelEmbedding9 ∘ raw22527step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22527step2 raw22527step2Labels raw22527step3Labels labelEmbedding9 hl
    _ = mixedMoment B node4612 node4612Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical176
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical22528 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22528 raw22528Labels = mixedMoment B node4612 node4612Labels := by
  calc
    mixedMoment B raw22528 raw22528Labels = mixedMoment B raw22528step0 raw22528step0Labels := by
      have hz : ∀ j, raw22528 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22528step0 = (fun i j => raw22528 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22528step0 raw22528; decide +kernel
      have hl : raw22528step0Labels = raw22528Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22528 raw22528Labels permutation434 hz
    mixedMoment B raw22528step0 raw22528step0Labels = mixedMoment B raw22528step1 raw22528step1Labels := by
      have hz : ∀ j, raw22528step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw22528step1 = (fun i j => raw22528step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw22528step1 raw22528step0; decide +kernel
      have hl : raw22528step1Labels = raw22528step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22528step0 raw22528step0Labels permutation56 hz
    mixedMoment B raw22528step1 raw22528step1Labels = mixedMoment B raw22528step2 raw22528step2Labels := by
      have ha : raw22528step2 = (fun i j => raw22528step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw22528step2 raw22528step1; decide +kernel
      have hl : raw22528step2Labels = raw22528step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22528step1 raw22528step1Labels permutation8 permutation6
    mixedMoment B raw22528step2 raw22528step2Labels = mixedMoment B raw22528step3 raw22528step3Labels := by
      have ha : raw22528step3 = raw22528step2 := by apply Matrix.ext; unfold raw22528step3 raw22528step2; decide +kernel
      have hl : raw22528step2Labels = labelEmbedding9 ∘ raw22528step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22528step2 raw22528step2Labels raw22528step3Labels labelEmbedding9 hl
    _ = mixedMoment B node4612 node4612Labels := by rfl

theorem canonical22529 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22529 raw22529Labels = mixedMoment B node4612 node4612Labels := by
  calc
    mixedMoment B raw22529 raw22529Labels = mixedMoment B raw22529step0 raw22529step0Labels := by
      have hz : ∀ j, raw22529 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22529step0 = (fun i j => raw22529 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22529step0 raw22529; decide +kernel
      have hl : raw22529step0Labels = raw22529Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22529 raw22529Labels permutation346 hz
    mixedMoment B raw22529step0 raw22529step0Labels = mixedMoment B raw22529step1 raw22529step1Labels := by
      have hz : ∀ j, raw22529step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw22529step1 = (fun i j => raw22529step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw22529step1 raw22529step0; decide +kernel
      have hl : raw22529step1Labels = raw22529step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22529step0 raw22529step0Labels permutation56 hz
    mixedMoment B raw22529step1 raw22529step1Labels = mixedMoment B raw22529step2 raw22529step2Labels := by
      have ha : raw22529step2 = (fun i j => raw22529step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw22529step2 raw22529step1; decide +kernel
      have hl : raw22529step2Labels = raw22529step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22529step1 raw22529step1Labels permutation8 permutation6
    mixedMoment B raw22529step2 raw22529step2Labels = mixedMoment B raw22529step3 raw22529step3Labels := by
      have ha : raw22529step3 = raw22529step2 := by apply Matrix.ext; unfold raw22529step3 raw22529step2; decide +kernel
      have hl : raw22529step2Labels = labelEmbedding9 ∘ raw22529step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22529step2 raw22529step2Labels raw22529step3Labels labelEmbedding9 hl
    _ = mixedMoment B node4612 node4612Labels := by rfl

theorem canonical22530 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22530 raw22530Labels = mixedMoment B node4628 node4628Labels := by
  calc
    mixedMoment B raw22530 raw22530Labels = mixedMoment B raw22530step0 raw22530step0Labels := by
      have hz : ∀ j, raw22530 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22530step0 = (fun i j => raw22530 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22530step0 raw22530; decide +kernel
      have hl : raw22530step0Labels = raw22530Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22530 raw22530Labels permutation434 hz
    mixedMoment B raw22530step0 raw22530step0Labels = mixedMoment B raw22530step1 raw22530step1Labels := by
      have hz : ∀ j, raw22530step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22530step1 = (fun i j => raw22530step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22530step1 raw22530step0; decide +kernel
      have hl : raw22530step1Labels = raw22530step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22530step0 raw22530step0Labels permutation80 hz
    mixedMoment B raw22530step1 raw22530step1Labels = mixedMoment B raw22530step2 raw22530step2Labels := by
      have hz : ∀ j, raw22530step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw22530step2 = (fun i j => raw22530step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw22530step2 raw22530step1; decide +kernel
      have hl : raw22530step2Labels = raw22530step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22530step1 raw22530step1Labels permutation14 hz
    mixedMoment B raw22530step2 raw22530step2Labels = mixedMoment B raw22530step3 raw22530step3Labels := by
      have ha : raw22530step3 = (fun i j => raw22530step2 (permutation2 i) (permutation6 j)) := by apply Matrix.ext; unfold raw22530step3 raw22530step2; decide +kernel
      have hl : raw22530step3Labels = raw22530step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22530step2 raw22530step2Labels permutation2 permutation6
    mixedMoment B raw22530step3 raw22530step3Labels = mixedMoment B raw22530step4 raw22530step4Labels := by
      have ha : raw22530step4 = raw22530step3 := by apply Matrix.ext; unfold raw22530step4 raw22530step3; decide +kernel
      have hl : raw22530step3Labels = labelEmbedding9 ∘ raw22530step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22530step3 raw22530step3Labels raw22530step4Labels labelEmbedding9 hl
    _ = mixedMoment B node4628 node4628Labels := by rfl

theorem canonical22531 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22531 raw22531Labels = mixedMoment B node4510 node4510Labels := by
  calc
    mixedMoment B raw22531 raw22531Labels = mixedMoment B raw22531step0 raw22531step0Labels := by
      have hz : ∀ j, raw22531 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22531step0 = (fun i j => raw22531 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22531step0 raw22531; decide +kernel
      have hl : raw22531step0Labels = raw22531Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22531 raw22531Labels permutation434 hz
    mixedMoment B raw22531step0 raw22531step0Labels = mixedMoment B raw22531step1 raw22531step1Labels := by
      have hz : ∀ j, raw22531step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22531step1 = (fun i j => raw22531step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22531step1 raw22531step0; decide +kernel
      have hl : raw22531step1Labels = raw22531step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22531step0 raw22531step0Labels permutation80 hz
    mixedMoment B raw22531step1 raw22531step1Labels = mixedMoment B raw22531step2 raw22531step2Labels := by
      have hz : ∀ j, raw22531step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw22531step2 = (fun i j => raw22531step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw22531step2 raw22531step1; decide +kernel
      have hl : raw22531step2Labels = raw22531step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22531step1 raw22531step1Labels permutation14 hz
    mixedMoment B raw22531step2 raw22531step2Labels = mixedMoment B raw22531step3 raw22531step3Labels := by
      have ha : raw22531step3 = (fun i j => raw22531step2 (permutation2 i) (permutation6 j)) := by apply Matrix.ext; unfold raw22531step3 raw22531step2; decide +kernel
      have hl : raw22531step3Labels = raw22531step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22531step2 raw22531step2Labels permutation2 permutation6
    mixedMoment B raw22531step3 raw22531step3Labels = mixedMoment B raw22531step4 raw22531step4Labels := by
      have ha : raw22531step4 = raw22531step3 := by apply Matrix.ext; unfold raw22531step4 raw22531step3; decide +kernel
      have hl : raw22531step3Labels = labelEmbedding9 ∘ raw22531step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22531step3 raw22531step3Labels raw22531step4Labels labelEmbedding9 hl
    _ = mixedMoment B node4510 node4510Labels := by rfl

theorem canonical22532 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22532 raw22532Labels = mixedMoment B node4611 node4611Labels := by
  calc
    mixedMoment B raw22532 raw22532Labels = mixedMoment B raw22532step0 raw22532step0Labels := by
      have hz : ∀ j, raw22532 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22532step0 = (fun i j => raw22532 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22532step0 raw22532; decide +kernel
      have hl : raw22532step0Labels = raw22532Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22532 raw22532Labels permutation434 hz
    mixedMoment B raw22532step0 raw22532step0Labels = mixedMoment B raw22532step1 raw22532step1Labels := by
      have hz : ∀ j, raw22532step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22532step1 = (fun i j => raw22532step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22532step1 raw22532step0; decide +kernel
      have hl : raw22532step1Labels = raw22532step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22532step0 raw22532step0Labels permutation80 hz
    mixedMoment B raw22532step1 raw22532step1Labels = mixedMoment B raw22532step2 raw22532step2Labels := by
      have ha : raw22532step2 = (fun i j => raw22532step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw22532step2 raw22532step1; decide +kernel
      have hl : raw22532step2Labels = raw22532step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22532step1 raw22532step1Labels permutation8 permutation6
    mixedMoment B raw22532step2 raw22532step2Labels = mixedMoment B raw22532step3 raw22532step3Labels := by
      have ha : raw22532step3 = raw22532step2 := by apply Matrix.ext; unfold raw22532step3 raw22532step2; decide +kernel
      have hl : raw22532step2Labels = labelEmbedding9 ∘ raw22532step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22532step2 raw22532step2Labels raw22532step3Labels labelEmbedding9 hl
    _ = mixedMoment B node4611 node4611Labels := by rfl

theorem canonical22533 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22533 raw22533Labels = mixedMoment B node4611 node4611Labels := by
  calc
    mixedMoment B raw22533 raw22533Labels = mixedMoment B raw22533step0 raw22533step0Labels := by
      have hz : ∀ j, raw22533 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22533step0 = (fun i j => raw22533 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22533step0 raw22533; decide +kernel
      have hl : raw22533step0Labels = raw22533Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22533 raw22533Labels permutation434 hz
    mixedMoment B raw22533step0 raw22533step0Labels = mixedMoment B raw22533step1 raw22533step1Labels := by
      have hz : ∀ j, raw22533step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw22533step1 = (fun i j => raw22533step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw22533step1 raw22533step0; decide +kernel
      have hl : raw22533step1Labels = raw22533step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22533step0 raw22533step0Labels permutation56 hz
    mixedMoment B raw22533step1 raw22533step1Labels = mixedMoment B raw22533step2 raw22533step2Labels := by
      have ha : raw22533step2 = (fun i j => raw22533step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw22533step2 raw22533step1; decide +kernel
      have hl : raw22533step2Labels = raw22533step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22533step1 raw22533step1Labels permutation8 permutation6
    mixedMoment B raw22533step2 raw22533step2Labels = mixedMoment B raw22533step3 raw22533step3Labels := by
      have ha : raw22533step3 = raw22533step2 := by apply Matrix.ext; unfold raw22533step3 raw22533step2; decide +kernel
      have hl : raw22533step2Labels = labelEmbedding9 ∘ raw22533step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22533step2 raw22533step2Labels raw22533step3Labels labelEmbedding9 hl
    _ = mixedMoment B node4611 node4611Labels := by rfl

theorem canonical22534 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22534 raw22534Labels = mixedMoment B node4611 node4611Labels := by
  calc
    mixedMoment B raw22534 raw22534Labels = mixedMoment B raw22534step0 raw22534step0Labels := by
      have hz : ∀ j, raw22534 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22534step0 = (fun i j => raw22534 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22534step0 raw22534; decide +kernel
      have hl : raw22534step0Labels = raw22534Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22534 raw22534Labels permutation346 hz
    mixedMoment B raw22534step0 raw22534step0Labels = mixedMoment B raw22534step1 raw22534step1Labels := by
      have hz : ∀ j, raw22534step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw22534step1 = (fun i j => raw22534step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw22534step1 raw22534step0; decide +kernel
      have hl : raw22534step1Labels = raw22534step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22534step0 raw22534step0Labels permutation56 hz
    mixedMoment B raw22534step1 raw22534step1Labels = mixedMoment B raw22534step2 raw22534step2Labels := by
      have ha : raw22534step2 = (fun i j => raw22534step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw22534step2 raw22534step1; decide +kernel
      have hl : raw22534step2Labels = raw22534step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22534step1 raw22534step1Labels permutation8 permutation6
    mixedMoment B raw22534step2 raw22534step2Labels = mixedMoment B raw22534step3 raw22534step3Labels := by
      have ha : raw22534step3 = raw22534step2 := by apply Matrix.ext; unfold raw22534step3 raw22534step2; decide +kernel
      have hl : raw22534step2Labels = labelEmbedding9 ∘ raw22534step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22534step2 raw22534step2Labels raw22534step3Labels labelEmbedding9 hl
    _ = mixedMoment B node4611 node4611Labels := by rfl

theorem canonical22535 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22535 raw22535Labels = mixedMoment B node4626 node4626Labels := by
  calc
    mixedMoment B raw22535 raw22535Labels = mixedMoment B raw22535step0 raw22535step0Labels := by
      have hz : ∀ j, raw22535 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22535step0 = (fun i j => raw22535 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22535step0 raw22535; decide +kernel
      have hl : raw22535step0Labels = raw22535Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22535 raw22535Labels permutation434 hz
    mixedMoment B raw22535step0 raw22535step0Labels = mixedMoment B raw22535step1 raw22535step1Labels := by
      have hz : ∀ j, raw22535step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22535step1 = (fun i j => raw22535step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22535step1 raw22535step0; decide +kernel
      have hl : raw22535step1Labels = raw22535step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22535step0 raw22535step0Labels permutation80 hz
    mixedMoment B raw22535step1 raw22535step1Labels = mixedMoment B raw22535step2 raw22535step2Labels := by
      have hz : ∀ j, raw22535step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw22535step2 = (fun i j => raw22535step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw22535step2 raw22535step1; decide +kernel
      have hl : raw22535step2Labels = raw22535step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22535step1 raw22535step1Labels permutation14 hz
    mixedMoment B raw22535step2 raw22535step2Labels = mixedMoment B raw22535step3 raw22535step3Labels := by
      have ha : raw22535step3 = (fun i j => raw22535step2 (permutation2 i) (permutation6 j)) := by apply Matrix.ext; unfold raw22535step3 raw22535step2; decide +kernel
      have hl : raw22535step3Labels = raw22535step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22535step2 raw22535step2Labels permutation2 permutation6
    mixedMoment B raw22535step3 raw22535step3Labels = mixedMoment B raw22535step4 raw22535step4Labels := by
      have ha : raw22535step4 = raw22535step3 := by apply Matrix.ext; unfold raw22535step4 raw22535step3; decide +kernel
      have hl : raw22535step3Labels = labelEmbedding9 ∘ raw22535step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22535step3 raw22535step3Labels raw22535step4Labels labelEmbedding9 hl
    _ = mixedMoment B node4626 node4626Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical32
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical4206 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4206 raw4206Labels = mixedMoment B node4091 node4091Labels := by
  calc
    mixedMoment B raw4206 raw4206Labels = mixedMoment B raw4206step0 raw4206step0Labels := by
      have hz : ∀ j, raw4206 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4206step0 = (fun i j => raw4206 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4206step0 raw4206; decide +kernel
      have hl : raw4206step0Labels = raw4206Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4206 raw4206Labels permutation346 hz
    _ = mixedMoment B node4091 node4091Labels := by rfl

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

theorem canonical1272 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1272 raw1272Labels = mixedMoment B node4466 node4466Labels := by
  calc
    mixedMoment B raw1272 raw1272Labels = mixedMoment B raw1272step0 raw1272step0Labels := by
      have ha : raw1272step0 = (fun i j => raw1272 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1272step0 raw1272; decide +kernel
      have hl : raw1272step0Labels = raw1272Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1272 raw1272Labels permutation8 permutation4
    mixedMoment B raw1272step0 raw1272step0Labels = mixedMoment B raw1272step1 raw1272step1Labels := by
      have ha : raw1272step1 = raw1272step0 := by apply Matrix.ext; unfold raw1272step1 raw1272step0; decide +kernel
      have hl : raw1272step0Labels = labelEmbedding7 ∘ raw1272step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1272step0 raw1272step0Labels raw1272step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4466 node4466Labels := by rfl

theorem canonical1273 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1273 raw1273Labels = mixedMoment B node1049 node1049Labels := by
  calc
    mixedMoment B raw1273 raw1273Labels = mixedMoment B raw1273step0 raw1273step0Labels := by
      have ha : raw1273step0 = (fun i j => raw1273 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1273step0 raw1273; decide +kernel
      have hl : raw1273step0Labels = raw1273Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1273 raw1273Labels permutation8 permutation4
    _ = mixedMoment B node1049 node1049Labels := by rfl

theorem canonical1274 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1274 raw1274Labels = mixedMoment B node1738 node1738Labels := by
  calc
    mixedMoment B raw1274 raw1274Labels = mixedMoment B raw1274step0 raw1274step0Labels := by
      have ha : raw1274step0 = (fun i j => raw1274 (permutation10 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1274step0 raw1274; decide +kernel
      have hl : raw1274step0Labels = raw1274Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1274 raw1274Labels permutation10 permutation6
    mixedMoment B raw1274step0 raw1274step0Labels = mixedMoment B raw1274step1 raw1274step1Labels := by
      have ha : raw1274step1 = -raw1274step0 := by apply Matrix.ext; change ∀ i j, raw1274step1 i j = -(raw1274step0 i j); unfold raw1274step1 raw1274step0; decide +kernel
      have hl : raw1274step1Labels = raw1274step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1274step1 raw1274step1Labels = mixedMoment B raw1274step2 raw1274step2Labels := by
      have ha : raw1274step2 = raw1274step1 := by apply Matrix.ext; unfold raw1274step2 raw1274step1; decide +kernel
      have hl : raw1274step1Labels = labelEmbedding1 ∘ raw1274step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1274step1 raw1274step1Labels raw1274step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1738 node1738Labels := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical249
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical7979 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7979 = injectiveMoment H node0 := by
  calc
    injectiveMoment H raw7979 = injectiveMoment H raw7979step0 := by
      have hz : ∀ j, raw7979 (permutation7 0) j = 0 := by decide +kernel
      have heq : raw7979step0 = (fun i j => raw7979 (permutation7 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7979 permutation7 hz
    injectiveMoment H raw7979step0 = injectiveMoment H raw7979step1 := by
      have hz : ∀ j, raw7979step0 (permutation2 0) j = 0 := by decide +kernel
      have heq : raw7979step1 = (fun i j => raw7979step0 (permutation2 i.succ) j) := by ext i j; fin_cases i; fin_cases j; decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7979step0 permutation2 hz
    injectiveMoment H raw7979step1 = injectiveMoment H raw7979step2 := by
      have hz : ∀ j, raw7979step1 (permutation0 0) j = 0 := by decide +kernel
      have heq : raw7979step2 = (fun i j => raw7979step1 (permutation0 i.succ) j) := by ext i j; fin_cases i
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7979step1 permutation0 hz
    injectiveMoment H raw7979step2 = injectiveMoment H raw7979step3 := by
      have hz : ∀ i, raw7979step2 i (permutation0 0) = 0 := by decide +kernel
      have heq : raw7979step3 = (fun i j => raw7979step2 i (permutation0 j.succ)) := by ext i j; fin_cases i
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw7979step2 permutation0 hz
    _ = injectiveMoment H node0 := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical5
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical179 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw179 = injectiveMoment H node35 := by
  calc
    injectiveMoment H raw179 = injectiveMoment H raw179step0 := by
      have heq : raw179step0 = -raw179 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw179).symm
    injectiveMoment H raw179step0 = injectiveMoment H raw179step1 := by
      have heq : raw179step1 = (fun i j => raw179step0 (permutation3 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw179step0 permutation3 permutation6
    _ = injectiveMoment H node35 := by rfl

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

theorem canonical214 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw214 = injectiveMoment H node9 := by
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

theorem sound9 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node9 = Sparse.eval value9 (momentVector H) := by
  have hc : momentVector H 5 = injectiveMoment H node9 := rfl
  simp [value9, Sparse.eval, hc]

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

theorem sound35 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node35 = Sparse.eval value35 (momentVector H) := by
  have hc : momentVector H 8 = injectiveMoment H node35 := rfl
  simp [value35, Sparse.eval, hc]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_SingleGroup9
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singlePair161 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node161 node161Labels = Sparse.eval singlePairValue161 (familyPairVector B) := by
  have hp := single_label_three B hB node161
  have hl : node161Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node161 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node161 (EqualityPatterns.family3.label 0) = PairSemantics.raw7979 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext
      unfold node161 PairSemantics.raw7979
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7979 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node161 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value11 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node161 (EqualityPatterns.family3.label 1) = PairSemantics.raw5199 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext
      unfold node161 PairSemantics.raw5199
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5199 hH).trans (PairSemantics.sound11 hH)
  have hm2 : familyPairMoment B (groupedColumns node161 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value11 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node161 (EqualityPatterns.family3.label 2) = PairSemantics.raw5199 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext
      unfold node161 PairSemantics.raw5199
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5199 hH).trans (PairSemantics.sound11 hH)
  have hm3 : familyPairMoment B (groupedColumns node161 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value9 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node161 (EqualityPatterns.family3.label 3) = PairSemantics.raw214 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext
      unfold node161 PairSemantics.raw214
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical214 hH).trans (PairSemantics.sound9 hH)
  have hm4 : familyPairMoment B (groupedColumns node161 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value35 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node161 (EqualityPatterns.family3.label 4) = PairSemantics.raw179 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext
      unfold node161 PairSemantics.raw179
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical179 hH).trans (PairSemantics.sound35 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue161, PairSemantics.value0, PairSemantics.value9, PairSemantics.value11, PairSemantics.value35, Sparse.eval] at hp ⊢
  linarith only [hp]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons20
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singleton1312 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node1312 node1312Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node161 node161Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw92 singletonSmall1312
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall1312) = raw92Labels := by decide +kernel
  rw [hl, canonical92 B hB] at h
  have hc0 : mixedMoment B raw92 (Fin.cases (0 : Fin 1) singletonSmall1312) =
      mixedMoment B node161 node161Labels := by
    have ha : raw92 = raw93 := by apply Matrix.ext; unfold raw92 raw93; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall1312 = raw93Labels := by decide +kernel
    rw [ha, hj, canonical93 B hB]
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

theorem singleton4466 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4466 node4466Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1049 node1049Labels + mixedMoment B node1738 node1738Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1272 singletonSmall4466
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4466) = raw1272Labels := by decide +kernel
  rw [hl, canonical1272 B hB] at h
  have hc0 : mixedMoment B raw1272 (Fin.cases (0 : Fin 2) singletonSmall4466) =
      mixedMoment B node1049 node1049Labels := by
    have ha : raw1272 = raw1273 := by apply Matrix.ext; unfold raw1272 raw1273; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4466 = raw1273Labels := by decide +kernel
    rw [ha, hj, canonical1273 B hB]
  have hc1 : mixedMoment B raw1272 (Fin.cases (1 : Fin 2) singletonSmall4466) =
      mixedMoment B node1738 node1738Labels := by
    have ha : raw1272 = raw1274 := by apply Matrix.ext; unfold raw1272 raw1274; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4466 = raw1274Labels := by decide +kernel
    rw [ha, hj, canonical1274 B hB]
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

theorem singleton4510 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4510 node4510Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1094 node1094Labels + mixedMoment B node1741 node1741Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1308 singletonSmall4510
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4510) = raw1308Labels := by decide +kernel
  rw [hl, canonical1308 B hB] at h
  have hc0 : mixedMoment B raw1308 (Fin.cases (0 : Fin 2) singletonSmall4510) =
      mixedMoment B node1094 node1094Labels := by
    have ha : raw1308 = raw1309 := by apply Matrix.ext; unfold raw1308 raw1309; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4510 = raw1309Labels := by decide +kernel
    rw [ha, hj, canonical1309 B hB]
  have hc1 : mixedMoment B raw1308 (Fin.cases (1 : Fin 2) singletonSmall4510) =
      mixedMoment B node1741 node1741Labels := by
    have ha : raw1308 = raw1310 := by apply Matrix.ext; unfold raw1308 raw1310; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4510 = raw1310Labels := by decide +kernel
    rw [ha, hj, canonical1310 B hB]
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

theorem singleton4612 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4612 node4612Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1246 node1246Labels + mixedMoment B node3301 node3301Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1437 singletonSmall4612
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4612) = raw1437Labels := by decide +kernel
  rw [hl, canonical1437 B hB] at h
  have hc0 : mixedMoment B raw1437 (Fin.cases (0 : Fin 2) singletonSmall4612) =
      mixedMoment B node1246 node1246Labels := by
    have ha : raw1437 = raw1438 := by apply Matrix.ext; unfold raw1437 raw1438; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4612 = raw1438Labels := by decide +kernel
    rw [ha, hj, canonical1438 B hB]
  have hc1 : mixedMoment B raw1437 (Fin.cases (1 : Fin 2) singletonSmall4612) =
      mixedMoment B node3301 node3301Labels := by
    have ha : raw1437 = raw1439 := by apply Matrix.ext; unfold raw1437 raw1439; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4612 = raw1439Labels := by decide +kernel
    rw [ha, hj, canonical1439 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4628 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4628 node4628Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1312 node1312Labels + mixedMoment B node3312 node3312Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1464 singletonSmall4628
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4628) = raw1464Labels := by decide +kernel
  rw [hl, canonical1464 B hB] at h
  have hc0 : mixedMoment B raw1464 (Fin.cases (0 : Fin 2) singletonSmall4628) =
      mixedMoment B node1312 node1312Labels := by
    have ha : raw1464 = raw1465 := by apply Matrix.ext; unfold raw1464 raw1465; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4628 = raw1465Labels := by decide +kernel
    rw [ha, hj, canonical1465 B hB]
  have hc1 : mixedMoment B raw1464 (Fin.cases (1 : Fin 2) singletonSmall4628) =
      mixedMoment B node3312 node3312Labels := by
    have ha : raw1464 = raw1466 := by apply Matrix.ext; unfold raw1464 raw1466; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4628 = raw1466Labels := by decide +kernel
    rw [ha, hj, canonical1466 B hB]
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

theorem sound1049 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1049 node1049Labels = Sparse.eval nodeValue1049 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1049) = mixedMoment B node1049 node1049Labels := rfl
  simpa [nodeValue1049, Sparse.eval] using hc.symm

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

theorem sound1094 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1094 node1094Labels = Sparse.eval nodeValue1094 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1094) = mixedMoment B node1094 node1094Labels := rfl
  simpa [nodeValue1094, Sparse.eval] using hc.symm

theorem sound1113 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1113 node1113Labels = Sparse.eval nodeValue1113 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1113) = mixedMoment B node1113 node1113Labels := rfl
  simpa [nodeValue1113, Sparse.eval] using hc.symm

theorem sound1114 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1114 node1114Labels = Sparse.eval nodeValue1114 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1114) = mixedMoment B node1114 node1114Labels := rfl
  simpa [nodeValue1114, Sparse.eval] using hc.symm

theorem sound1119 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1119 node1119Labels = Sparse.eval nodeValue1119 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1119) = mixedMoment B node1119 node1119Labels := rfl
  simpa [nodeValue1119, Sparse.eval] using hc.symm

theorem sound1120 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1120 node1120Labels = Sparse.eval nodeValue1120 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1120) = mixedMoment B node1120 node1120Labels := rfl
  simpa [nodeValue1120, Sparse.eval] using hc.symm

theorem sound1121 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1121 node1121Labels = Sparse.eval nodeValue1121 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1121) = mixedMoment B node1121 node1121Labels := rfl
  simpa [nodeValue1121, Sparse.eval] using hc.symm

theorem sound1138 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1138 node1138Labels = Sparse.eval nodeValue1138 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1138) = mixedMoment B node1138 node1138Labels := rfl
  simpa [nodeValue1138, Sparse.eval] using hc.symm

theorem sound1139 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1139 node1139Labels = Sparse.eval nodeValue1139 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1139) = mixedMoment B node1139 node1139Labels := rfl
  simpa [nodeValue1139, Sparse.eval] using hc.symm

theorem sound1151 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1151 node1151Labels = Sparse.eval nodeValue1151 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1151) = mixedMoment B node1151 node1151Labels := rfl
  simpa [nodeValue1151, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound161 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node161 node161Labels = Sparse.eval nodeValue161 (mixedVector B) := by
  calc
    _ = Sparse.eval singlePairValue161 (familyPairVector B) := singlePair161 B _hB
    _ = _ := by
      norm_num [singlePairValue161, nodeValue161, Sparse.eval, mixedVector]
      ring

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound18
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound1152 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1152 node1152Labels = Sparse.eval nodeValue1152 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1152) = mixedMoment B node1152 node1152Labels := rfl
  simpa [nodeValue1152, Sparse.eval] using hc.symm

theorem sound1182 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1182 node1182Labels = Sparse.eval nodeValue1182 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1182) = mixedMoment B node1182 node1182Labels := rfl
  simpa [nodeValue1182, Sparse.eval] using hc.symm

theorem sound1196 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1196 node1196Labels = Sparse.eval nodeValue1196 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1196) = mixedMoment B node1196 node1196Labels := rfl
  simpa [nodeValue1196, Sparse.eval] using hc.symm

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

theorem sound1219 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1219 node1219Labels = Sparse.eval nodeValue1219 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1219) = mixedMoment B node1219 node1219Labels := rfl
  simpa [nodeValue1219, Sparse.eval] using hc.symm

theorem sound1220 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1220 node1220Labels = Sparse.eval nodeValue1220 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1220) = mixedMoment B node1220 node1220Labels := rfl
  simpa [nodeValue1220, Sparse.eval] using hc.symm

theorem sound1236 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1236 node1236Labels = Sparse.eval nodeValue1236 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1236) = mixedMoment B node1236 node1236Labels := rfl
  simpa [nodeValue1236, Sparse.eval] using hc.symm

theorem sound1240 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1240 node1240Labels = Sparse.eval nodeValue1240 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1240) = mixedMoment B node1240 node1240Labels := rfl
  simpa [nodeValue1240, Sparse.eval] using hc.symm

theorem sound1241 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1241 node1241Labels = Sparse.eval nodeValue1241 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1241) = mixedMoment B node1241 node1241Labels := rfl
  simpa [nodeValue1241, Sparse.eval] using hc.symm

theorem sound1246 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1246 node1246Labels = Sparse.eval nodeValue1246 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1246) = mixedMoment B node1246 node1246Labels := rfl
  simpa [nodeValue1246, Sparse.eval] using hc.symm

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

theorem sound1312 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1312 node1312Labels = Sparse.eval nodeValue1312 (mixedVector B) := by
  have h := singleton1312 B _hB
  rw [sound161 B _hB _hF] at h
  norm_num [nodeValue1312, nodeValue161, Sparse.eval] at h ⊢
  linarith only [h]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros25
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero1614 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node1614 node1614Labels = 0 := by
  exact mixedMoment_alpha B hF node1614 node1614Labels 1 permutation446
    (by decide +kernel)

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

theorem sound1606 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1606 node1606Labels = Sparse.eval nodeValue1606 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1606) = mixedMoment B node1606 node1606Labels := rfl
  simpa [nodeValue1606, Sparse.eval] using hc.symm

theorem sound1608 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1608 node1608Labels = Sparse.eval nodeValue1608 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1608) = mixedMoment B node1608 node1608Labels := rfl
  simpa [nodeValue1608, Sparse.eval] using hc.symm

theorem sound1611 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1611 node1611Labels = Sparse.eval nodeValue1611 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1611) = mixedMoment B node1611 node1611Labels := rfl
  simpa [nodeValue1611, Sparse.eval] using hc.symm

theorem sound1614 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1614 node1614Labels = Sparse.eval nodeValue1614 (mixedVector B) := by
  simpa only [nodeValue1614, Sparse.eval_nil] using zero1614 B _hB _hF

theorem sound1618 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1618 node1618Labels = Sparse.eval nodeValue1618 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1618) = mixedMoment B node1618 node1618Labels := rfl
  simpa [nodeValue1618, Sparse.eval] using hc.symm

theorem sound1626 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1626 node1626Labels = Sparse.eval nodeValue1626 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1626) = mixedMoment B node1626 node1626Labels := rfl
  simpa [nodeValue1626, Sparse.eval] using hc.symm

theorem sound1627 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1627 node1627Labels = Sparse.eval nodeValue1627 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1627) = mixedMoment B node1627 node1627Labels := rfl
  simpa [nodeValue1627, Sparse.eval] using hc.symm

theorem sound1655 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1655 node1655Labels = Sparse.eval nodeValue1655 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1655) = mixedMoment B node1655 node1655Labels := rfl
  simpa [nodeValue1655, Sparse.eval] using hc.symm

theorem sound1657 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1657 node1657Labels = Sparse.eval nodeValue1657 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1657) = mixedMoment B node1657 node1657Labels := rfl
  simpa [nodeValue1657, Sparse.eval] using hc.symm

theorem sound1660 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1660 node1660Labels = Sparse.eval nodeValue1660 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1660) = mixedMoment B node1660 node1660Labels := rfl
  simpa [nodeValue1660, Sparse.eval] using hc.symm

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

theorem sound1738 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1738 node1738Labels = Sparse.eval nodeValue1738 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1738) = mixedMoment B node1738 node1738Labels := rfl
  simpa [nodeValue1738, Sparse.eval] using hc.symm

theorem sound1741 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1741 node1741Labels = Sparse.eval nodeValue1741 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1741) = mixedMoment B node1741 node1741Labels := rfl
  simpa [nodeValue1741, Sparse.eval] using hc.symm

theorem sound1751 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1751 node1751Labels = Sparse.eval nodeValue1751 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1751) = mixedMoment B node1751 node1751Labels := rfl
  simpa [nodeValue1751, Sparse.eval] using hc.symm

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

theorem sound2388 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2388 node2388Labels = Sparse.eval nodeValue2388 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2388) = mixedMoment B node2388 node2388Labels := rfl
  simpa [nodeValue2388, Sparse.eval] using hc.symm

theorem sound2397 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2397 node2397Labels = Sparse.eval nodeValue2397 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2397) = mixedMoment B node2397 node2397Labels := rfl
  simpa [nodeValue2397, Sparse.eval] using hc.symm

theorem sound2409 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2409 node2409Labels = Sparse.eval nodeValue2409 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2409) = mixedMoment B node2409 node2409Labels := rfl
  simpa [nodeValue2409, Sparse.eval] using hc.symm

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

theorem sound2452 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2452 node2452Labels = Sparse.eval nodeValue2452 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2452) = mixedMoment B node2452 node2452Labels := rfl
  simpa [nodeValue2452, Sparse.eval] using hc.symm

theorem sound2488 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2488 node2488Labels = Sparse.eval nodeValue2488 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2488) = mixedMoment B node2488 node2488Labels := rfl
  simpa [nodeValue2488, Sparse.eval] using hc.symm

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

theorem sound2533 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2533 node2533Labels = Sparse.eval nodeValue2533 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2533) = mixedMoment B node2533 node2533Labels := rfl
  simpa [nodeValue2533, Sparse.eval] using hc.symm

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

theorem sound2608 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2608 node2608Labels = Sparse.eval nodeValue2608 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2608) = mixedMoment B node2608 node2608Labels := rfl
  simpa [nodeValue2608, Sparse.eval] using hc.symm

theorem sound2609 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2609 node2609Labels = Sparse.eval nodeValue2609 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2609) = mixedMoment B node2609 node2609Labels := rfl
  simpa [nodeValue2609, Sparse.eval] using hc.symm

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

theorem sound2673 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2673 node2673Labels = Sparse.eval nodeValue2673 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2673) = mixedMoment B node2673 node2673Labels := rfl
  simpa [nodeValue2673, Sparse.eval] using hc.symm

theorem sound2683 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2683 node2683Labels = Sparse.eval nodeValue2683 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2683) = mixedMoment B node2683 node2683Labels := rfl
  simpa [nodeValue2683, Sparse.eval] using hc.symm

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

theorem zero2695 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node2695 node2695Labels = 0 := by
  exact mixedMoment_alpha B hF node2695 node2695Labels 1 permutation212
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

theorem sound2694 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2694 node2694Labels = Sparse.eval nodeValue2694 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2694) = mixedMoment B node2694 node2694Labels := rfl
  simpa [nodeValue2694, Sparse.eval] using hc.symm

theorem sound2695 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2695 node2695Labels = Sparse.eval nodeValue2695 (mixedVector B) := by
  simpa only [nodeValue2695, Sparse.eval_nil] using zero2695 B _hB _hF

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

theorem sound2780 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2780 node2780Labels = Sparse.eval nodeValue2780 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2780) = mixedMoment B node2780 node2780Labels := rfl
  simpa [nodeValue2780, Sparse.eval] using hc.symm

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

theorem sound3295 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3295 node3295Labels = Sparse.eval nodeValue3295 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3295) = mixedMoment B node3295 node3295Labels := rfl
  simpa [nodeValue3295, Sparse.eval] using hc.symm

theorem sound3297 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3297 node3297Labels = Sparse.eval nodeValue3297 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3297) = mixedMoment B node3297 node3297Labels := rfl
  simpa [nodeValue3297, Sparse.eval] using hc.symm

theorem sound3301 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3301 node3301Labels = Sparse.eval nodeValue3301 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3301) = mixedMoment B node3301 node3301Labels := rfl
  simpa [nodeValue3301, Sparse.eval] using hc.symm

theorem sound3311 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3311 node3311Labels = Sparse.eval nodeValue3311 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3311) = mixedMoment B node3311 node3311Labels := rfl
  simpa [nodeValue3311, Sparse.eval] using hc.symm

theorem sound3312 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3312 node3312Labels = Sparse.eval nodeValue3312 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3312) = mixedMoment B node3312 node3312Labels := rfl
  simpa [nodeValue3312, Sparse.eval] using hc.symm

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

theorem sound4071 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4071 node4071Labels = Sparse.eval nodeValue4071 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4071) = mixedMoment B node4071 node4071Labels := rfl
  simpa [nodeValue4071, Sparse.eval] using hc.symm

theorem sound4088 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4088 node4088Labels = Sparse.eval nodeValue4088 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4088) = mixedMoment B node4088 node4088Labels := rfl
  simpa [nodeValue4088, Sparse.eval] using hc.symm

theorem sound4090 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4090 node4090Labels = Sparse.eval nodeValue4090 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4090) = mixedMoment B node4090 node4090Labels := rfl
  simpa [nodeValue4090, Sparse.eval] using hc.symm

theorem sound4091 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4091 node4091Labels = Sparse.eval nodeValue4091 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4091) = mixedMoment B node4091 node4091Labels := rfl
  simpa [nodeValue4091, Sparse.eval] using hc.symm

theorem sound4092 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4092 node4092Labels = Sparse.eval nodeValue4092 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4092) = mixedMoment B node4092 node4092Labels := rfl
  simpa [nodeValue4092, Sparse.eval] using hc.symm

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

theorem sound4466 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4466 node4466Labels = Sparse.eval nodeValue4466 (mixedVector B) := by
  have h := singleton4466 B _hB
  rw [sound1049 B _hB _hF, sound1738 B _hB _hF] at h
  norm_num [nodeValue4466, nodeValue1049, nodeValue1738, Sparse.eval] at h ⊢
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

theorem zero4511 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4511 node4511Labels = 0 := by
  exact mixedMoment_order_one B hB node4511 node4511Labels 1
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

theorem sound4510 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4510 node4510Labels = Sparse.eval nodeValue4510 (mixedVector B) := by
  have h := singleton4510 B _hB
  rw [sound1094 B _hB _hF, sound1741 B _hB _hF] at h
  norm_num [nodeValue4510, nodeValue1094, nodeValue1741, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4511 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4511 node4511Labels = Sparse.eval nodeValue4511 (mixedVector B) := by
  simpa only [nodeValue4511, Sparse.eval_nil] using zero4511 B _hB _hF

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

theorem sound4592 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4592 node4592Labels = Sparse.eval nodeValue4592 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4592) = mixedMoment B node4592 node4592Labels := rfl
  simpa [nodeValue4592, Sparse.eval] using hc.symm

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

theorem sound4612 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4612 node4612Labels = Sparse.eval nodeValue4612 (mixedVector B) := by
  have h := singleton4612 B _hB
  rw [sound1246 B _hB _hF, sound3301 B _hB _hF] at h
  norm_num [nodeValue4612, nodeValue1246, nodeValue3301, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4626 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4626 node4626Labels = Sparse.eval nodeValue4626 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4626) = mixedMoment B node4626 node4626Labels := rfl
  simpa [nodeValue4626, Sparse.eval] using hc.symm

theorem sound4628 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4628 node4628Labels = Sparse.eval nodeValue4628 (mixedVector B) := by
  have h := singleton4628 B _hB
  rw [sound1312 B _hB _hF, sound3312 B _hB _hF] at h
  norm_num [nodeValue4628, nodeValue1312, nodeValue3312, Sparse.eval] at h ⊢
  linarith only [h]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound9
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound631 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node631 node631Labels = Sparse.eval nodeValue631 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 631) = mixedMoment B node631 node631Labels := rfl
  simpa [nodeValue631, Sparse.eval] using hc.symm

theorem sound632 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node632 node632Labels = Sparse.eval nodeValue632 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 632) = mixedMoment B node632 node632Labels := rfl
  simpa [nodeValue632, Sparse.eval] using hc.symm

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources45
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sourceEq1459 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1459 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1459 + difference 0 0) (sourceB1459 + difference 0 0) sourceC1459) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2683) := by
    have ha : (tripleCharges (sourceA1459 + difference 0 0) (sourceB1459 + difference 0 0) sourceC1459) = raw22406 := by
      apply Matrix.ext; unfold tripleCharges sourceA1459 sourceB1459 sourceC1459 difference raw22406; decide +kernel
    rw [ha]
    exact (canonical22406 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1459 + difference 0 1) (sourceB1459 + difference 1 0) sourceC1459) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1660) := by
    have ha : (tripleCharges (sourceA1459 + difference 0 1) (sourceB1459 + difference 1 0) sourceC1459) = raw22407 := by
      apply Matrix.ext; unfold tripleCharges sourceA1459 sourceB1459 sourceC1459 difference raw22407; decide +kernel
    rw [ha]
    exact (canonical22407 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1459 + difference 0 2) (sourceB1459 + difference 2 0) sourceC1459) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1655) := by
    have ha : (tripleCharges (sourceA1459 + difference 0 2) (sourceB1459 + difference 2 0) sourceC1459) = raw22408 := by
      apply Matrix.ext; unfold tripleCharges sourceA1459 sourceB1459 sourceC1459 difference raw22408; decide +kernel
    rw [ha]
    exact (canonical22408 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1459 + difference 0 3) (sourceB1459 + difference 3 0) sourceC1459) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1655) := by
    have ha : (tripleCharges (sourceA1459 + difference 0 3) (sourceB1459 + difference 3 0) sourceC1459) = raw22409 := by
      apply Matrix.ext; unfold tripleCharges sourceA1459 sourceB1459 sourceC1459 difference raw22409; decide +kernel
    rw [ha]
    exact (canonical22409 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1459 + difference 0 4) (sourceB1459 + difference 4 0) sourceC1459) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1657) := by
    have ha : (tripleCharges (sourceA1459 + difference 0 4) (sourceB1459 + difference 4 0) sourceC1459) = raw22410 := by
      apply Matrix.ext; unfold tripleCharges sourceA1459 sourceB1459 sourceC1459 difference raw22410; decide +kernel
    rw [ha]
    exact (canonical22410 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1459 + difference 0 5) (sourceB1459 + difference 5 0) sourceC1459) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1738) := by
    have ha : (tripleCharges (sourceA1459 + difference 0 5) (sourceB1459 + difference 5 0) sourceC1459) = raw22411 := by
      apply Matrix.ext; unfold tripleCharges sourceA1459 sourceB1459 sourceC1459 difference raw22411; decide +kernel
    rw [ha]
    exact (canonical22411 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1459 + sourceB1459) sourceC1459) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4071) := by
    have ha : (doubleCharges (sourceA1459 + sourceB1459) sourceC1459) = raw22329 := by
      apply Matrix.ext; unfold doubleCharges sourceA1459 sourceB1459 sourceC1459 raw22329; decide +kernel
    rw [ha]
    exact (canonical22329 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1459 sourceB1459 sourceC1459
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1459, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1460 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1460 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1460 + difference 1 0) (sourceB1460 + difference 0 1) sourceC1460) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1741) := by
    have ha : (tripleCharges (sourceA1460 + difference 1 0) (sourceB1460 + difference 0 1) sourceC1460) = raw22412 := by
      apply Matrix.ext; unfold tripleCharges sourceA1460 sourceB1460 sourceC1460 difference raw22412; decide +kernel
    rw [ha]
    exact (canonical22412 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1460 + difference 1 1) (sourceB1460 + difference 1 1) sourceC1460) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2683) := by
    have ha : (tripleCharges (sourceA1460 + difference 1 1) (sourceB1460 + difference 1 1) sourceC1460) = raw22406 := by
      apply Matrix.ext; unfold tripleCharges sourceA1460 sourceB1460 sourceC1460 difference raw22406; decide +kernel
    rw [ha]
    exact (canonical22406 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1460 + difference 1 2) (sourceB1460 + difference 2 1) sourceC1460) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2683) := by
    have ha : (tripleCharges (sourceA1460 + difference 1 2) (sourceB1460 + difference 2 1) sourceC1460) = raw22413 := by
      apply Matrix.ext; unfold tripleCharges sourceA1460 sourceB1460 sourceC1460 difference raw22413; decide +kernel
    rw [ha]
    exact (canonical22413 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1460 + difference 1 3) (sourceB1460 + difference 3 1) sourceC1460) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2683) := by
    have ha : (tripleCharges (sourceA1460 + difference 1 3) (sourceB1460 + difference 3 1) sourceC1460) = raw22414 := by
      apply Matrix.ext; unfold tripleCharges sourceA1460 sourceB1460 sourceC1460 difference raw22414; decide +kernel
    rw [ha]
    exact (canonical22414 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1460 + difference 1 4) (sourceB1460 + difference 4 1) sourceC1460) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2780) := by
    have ha : (tripleCharges (sourceA1460 + difference 1 4) (sourceB1460 + difference 4 1) sourceC1460) = raw22415 := by
      apply Matrix.ext; unfold tripleCharges sourceA1460 sourceB1460 sourceC1460 difference raw22415; decide +kernel
    rw [ha]
    exact (canonical22415 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1460 + difference 1 5) (sourceB1460 + difference 5 1) sourceC1460) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3311) := by
    have ha : (tripleCharges (sourceA1460 + difference 1 5) (sourceB1460 + difference 5 1) sourceC1460) = raw22416 := by
      apply Matrix.ext; unfold tripleCharges sourceA1460 sourceB1460 sourceC1460 difference raw22416; decide +kernel
    rw [ha]
    exact (canonical22416 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1460 + sourceB1460) sourceC1460) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4071) := by
    have ha : (doubleCharges (sourceA1460 + sourceB1460) sourceC1460) = raw22329 := by
      apply Matrix.ext; unfold doubleCharges sourceA1460 sourceB1460 sourceC1460 raw22329; decide +kernel
    rw [ha]
    exact (canonical22329 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1460 sourceB1460 sourceC1460
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1460, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1461 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1461 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1461 + difference 4 0) (sourceB1461 + difference 0 4) sourceC1461) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1627) := by
    have ha : (tripleCharges (sourceA1461 + difference 4 0) (sourceB1461 + difference 0 4) sourceC1461) = raw22417 := by
      apply Matrix.ext; unfold tripleCharges sourceA1461 sourceB1461 sourceC1461 difference raw22417; decide +kernel
    rw [ha]
    exact (canonical22417 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1461 + difference 4 1) (sourceB1461 + difference 1 4) sourceC1461) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2409) := by
    have ha : (tripleCharges (sourceA1461 + difference 4 1) (sourceB1461 + difference 1 4) sourceC1461) = raw22418 := by
      apply Matrix.ext; unfold tripleCharges sourceA1461 sourceB1461 sourceC1461 difference raw22418; decide +kernel
    rw [ha]
    exact (canonical22418 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1461 + difference 4 2) (sourceB1461 + difference 2 4) sourceC1461) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2397) := by
    have ha : (tripleCharges (sourceA1461 + difference 4 2) (sourceB1461 + difference 2 4) sourceC1461) = raw22419 := by
      apply Matrix.ext; unfold tripleCharges sourceA1461 sourceB1461 sourceC1461 difference raw22419; decide +kernel
    rw [ha]
    exact (canonical22419 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1461 + difference 4 3) (sourceB1461 + difference 3 4) sourceC1461) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2397) := by
    have ha : (tripleCharges (sourceA1461 + difference 4 3) (sourceB1461 + difference 3 4) sourceC1461) = raw22420 := by
      apply Matrix.ext; unfold tripleCharges sourceA1461 sourceB1461 sourceC1461 difference raw22420; decide +kernel
    rw [ha]
    exact (canonical22420 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1461 + difference 4 4) (sourceB1461 + difference 4 4) sourceC1461) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2683) := by
    have ha : (tripleCharges (sourceA1461 + difference 4 4) (sourceB1461 + difference 4 4) sourceC1461) = raw22406 := by
      apply Matrix.ext; unfold tripleCharges sourceA1461 sourceB1461 sourceC1461 difference raw22406; decide +kernel
    rw [ha]
    exact (canonical22406 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1461 + difference 4 5) (sourceB1461 + difference 5 4) sourceC1461) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3301) := by
    have ha : (tripleCharges (sourceA1461 + difference 4 5) (sourceB1461 + difference 5 4) sourceC1461) = raw22421 := by
      apply Matrix.ext; unfold tripleCharges sourceA1461 sourceB1461 sourceC1461 difference raw22421; decide +kernel
    rw [ha]
    exact (canonical22421 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1461 + sourceB1461) sourceC1461) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4071) := by
    have ha : (doubleCharges (sourceA1461 + sourceB1461) sourceC1461) = raw22329 := by
      apply Matrix.ext; unfold doubleCharges sourceA1461 sourceB1461 sourceC1461 raw22329; decide +kernel
    rw [ha]
    exact (canonical22329 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1461 sourceB1461 sourceC1461
    (0 : Fin 2) 1 (4 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1461, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1462 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1462 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1462 + difference 0 5) (sourceB1462 + difference 5 0) sourceC1462) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1738) := by
    have ha : (tripleCharges (sourceA1462 + difference 0 5) (sourceB1462 + difference 5 0) sourceC1462) = raw22411 := by
      apply Matrix.ext; unfold tripleCharges sourceA1462 sourceB1462 sourceC1462 difference raw22411; decide +kernel
    rw [ha]
    exact (canonical22411 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1462 + difference 1 5) (sourceB1462 + difference 5 1) sourceC1462) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3311) := by
    have ha : (tripleCharges (sourceA1462 + difference 1 5) (sourceB1462 + difference 5 1) sourceC1462) = raw22416 := by
      apply Matrix.ext; unfold tripleCharges sourceA1462 sourceB1462 sourceC1462 difference raw22416; decide +kernel
    rw [ha]
    exact (canonical22416 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1462 + difference 2 5) (sourceB1462 + difference 5 2) sourceC1462) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3295) := by
    have ha : (tripleCharges (sourceA1462 + difference 2 5) (sourceB1462 + difference 5 2) sourceC1462) = raw22422 := by
      apply Matrix.ext; unfold tripleCharges sourceA1462 sourceB1462 sourceC1462 difference raw22422; decide +kernel
    rw [ha]
    exact (canonical22422 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1462 + difference 3 5) (sourceB1462 + difference 5 3) sourceC1462) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3295) := by
    have ha : (tripleCharges (sourceA1462 + difference 3 5) (sourceB1462 + difference 5 3) sourceC1462) = raw22423 := by
      apply Matrix.ext; unfold tripleCharges sourceA1462 sourceB1462 sourceC1462 difference raw22423; decide +kernel
    rw [ha]
    exact (canonical22423 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1462 + difference 4 5) (sourceB1462 + difference 5 4) sourceC1462) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3301) := by
    have ha : (tripleCharges (sourceA1462 + difference 4 5) (sourceB1462 + difference 5 4) sourceC1462) = raw22421 := by
      apply Matrix.ext; unfold tripleCharges sourceA1462 sourceB1462 sourceC1462 difference raw22421; decide +kernel
    rw [ha]
    exact (canonical22421 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1462 + difference 5 5) (sourceB1462 + difference 5 5) sourceC1462) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2683) := by
    have ha : (tripleCharges (sourceA1462 + difference 5 5) (sourceB1462 + difference 5 5) sourceC1462) = raw22406 := by
      apply Matrix.ext; unfold tripleCharges sourceA1462 sourceB1462 sourceC1462 difference raw22406; decide +kernel
    rw [ha]
    exact (canonical22406 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1462 + sourceB1462) sourceC1462) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4071) := by
    have ha : (doubleCharges (sourceA1462 + sourceB1462) sourceC1462) = raw22329 := by
      apply Matrix.ext; unfold doubleCharges sourceA1462 sourceB1462 sourceC1462 raw22329; decide +kernel
    rw [ha]
    exact (canonical22329 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1462 sourceB1462 sourceC1462
    (0 : Fin 2) 1 (5 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1462, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1463 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1463 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1463 + difference 0 1) (sourceB1463 + difference 1 0) sourceC1463) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2488) := by
    have ha : (tripleCharges (sourceA1463 + difference 0 1) (sourceB1463 + difference 1 0) sourceC1463) = raw22424 := by
      apply Matrix.ext; unfold tripleCharges sourceA1463 sourceB1463 sourceC1463 difference raw22424; decide +kernel
    rw [ha]
    exact (canonical22424 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1463 + difference 1 1) (sourceB1463 + difference 1 1) sourceC1463) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1219) := by
    have ha : (tripleCharges (sourceA1463 + difference 1 1) (sourceB1463 + difference 1 1) sourceC1463) = raw22425 := by
      apply Matrix.ext; unfold tripleCharges sourceA1463 sourceB1463 sourceC1463 difference raw22425; decide +kernel
    rw [ha]
    exact (canonical22425 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1463 + difference 2 1) (sourceB1463 + difference 1 2) sourceC1463) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1113) := by
    have ha : (tripleCharges (sourceA1463 + difference 2 1) (sourceB1463 + difference 1 2) sourceC1463) = raw22426 := by
      apply Matrix.ext; unfold tripleCharges sourceA1463 sourceB1463 sourceC1463 difference raw22426; decide +kernel
    rw [ha]
    exact (canonical22426 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1463 + difference 3 1) (sourceB1463 + difference 1 3) sourceC1463) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1138) := by
    have ha : (tripleCharges (sourceA1463 + difference 3 1) (sourceB1463 + difference 1 3) sourceC1463) = raw22427 := by
      apply Matrix.ext; unfold tripleCharges sourceA1463 sourceB1463 sourceC1463 difference raw22427; decide +kernel
    rw [ha]
    exact (canonical22427 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1463 + difference 4 1) (sourceB1463 + difference 1 4) sourceC1463) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1121) := by
    have ha : (tripleCharges (sourceA1463 + difference 4 1) (sourceB1463 + difference 1 4) sourceC1463) = raw22428 := by
      apply Matrix.ext; unfold tripleCharges sourceA1463 sourceB1463 sourceC1463 difference raw22428; decide +kernel
    rw [ha]
    exact (canonical22428 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1463 + difference 5 1) (sourceB1463 + difference 1 5) sourceC1463) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1119) := by
    have ha : (tripleCharges (sourceA1463 + difference 5 1) (sourceB1463 + difference 1 5) sourceC1463) = raw20281 := by
      apply Matrix.ext; unfold tripleCharges sourceA1463 sourceB1463 sourceC1463 difference raw20281; decide +kernel
    rw [ha]
    exact (canonical20281 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1463 + sourceB1463) sourceC1463) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA1463 + sourceB1463) sourceC1463) = raw20283 := by
      apply Matrix.ext; unfold doubleCharges sourceA1463 sourceB1463 sourceC1463 raw20283; decide +kernel
    rw [ha]
    exact (canonical20283 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1463 sourceB1463 sourceC1463
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1463, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1464 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1464 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1464 + difference 3 0) (sourceB1464 + difference 0 3) sourceC1464) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 631) := by
    have ha : (tripleCharges (sourceA1464 + difference 3 0) (sourceB1464 + difference 0 3) sourceC1464) = raw22429 := by
      apply Matrix.ext; unfold tripleCharges sourceA1464 sourceB1464 sourceC1464 difference raw22429; decide +kernel
    rw [ha]
    exact (canonical22429 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1464 + difference 3 1) (sourceB1464 + difference 1 3) sourceC1464) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1138) := by
    have ha : (tripleCharges (sourceA1464 + difference 3 1) (sourceB1464 + difference 1 3) sourceC1464) = raw22427 := by
      apply Matrix.ext; unfold tripleCharges sourceA1464 sourceB1464 sourceC1464 difference raw22427; decide +kernel
    rw [ha]
    exact (canonical22427 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1464 + difference 3 2) (sourceB1464 + difference 2 3) sourceC1464) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1151) := by
    have ha : (tripleCharges (sourceA1464 + difference 3 2) (sourceB1464 + difference 2 3) sourceC1464) = raw22430 := by
      apply Matrix.ext; unfold tripleCharges sourceA1464 sourceB1464 sourceC1464 difference raw22430; decide +kernel
    rw [ha]
    exact (canonical22430 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1464 + difference 3 3) (sourceB1464 + difference 3 3) sourceC1464) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1219) := by
    have ha : (tripleCharges (sourceA1464 + difference 3 3) (sourceB1464 + difference 3 3) sourceC1464) = raw22425 := by
      apply Matrix.ext; unfold tripleCharges sourceA1464 sourceB1464 sourceC1464 difference raw22425; decide +kernel
    rw [ha]
    exact (canonical22425 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1464 + difference 3 4) (sourceB1464 + difference 4 3) sourceC1464) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1236) := by
    have ha : (tripleCharges (sourceA1464 + difference 3 4) (sourceB1464 + difference 4 3) sourceC1464) = raw20287 := by
      apply Matrix.ext; unfold tripleCharges sourceA1464 sourceB1464 sourceC1464 difference raw20287; decide +kernel
    rw [ha]
    exact (canonical20287 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1464 + difference 3 5) (sourceB1464 + difference 5 3) sourceC1464) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1241) := by
    have ha : (tripleCharges (sourceA1464 + difference 3 5) (sourceB1464 + difference 5 3) sourceC1464) = raw22431 := by
      apply Matrix.ext; unfold tripleCharges sourceA1464 sourceB1464 sourceC1464 difference raw22431; decide +kernel
    rw [ha]
    exact (canonical22431 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1464 + sourceB1464) sourceC1464) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA1464 + sourceB1464) sourceC1464) = raw20283 := by
      apply Matrix.ext; unfold doubleCharges sourceA1464 sourceB1464 sourceC1464 raw20283; decide +kernel
    rw [ha]
    exact (canonical20283 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1464 sourceB1464 sourceC1464
    (0 : Fin 2) 1 (3 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1464, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1465 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1465 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1465 + difference 0 0) (sourceB1465 + difference 0 0) sourceC1465) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3295) := by
    have ha : (tripleCharges (sourceA1465 + difference 0 0) (sourceB1465 + difference 0 0) sourceC1465) = raw22423 := by
      apply Matrix.ext; unfold tripleCharges sourceA1465 sourceB1465 sourceC1465 difference raw22423; decide +kernel
    rw [ha]
    exact (canonical22423 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1465 + difference 0 1) (sourceB1465 + difference 1 0) sourceC1465) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1611) := by
    have ha : (tripleCharges (sourceA1465 + difference 0 1) (sourceB1465 + difference 1 0) sourceC1465) = raw22432 := by
      apply Matrix.ext; unfold tripleCharges sourceA1465 sourceB1465 sourceC1465 difference raw22432; decide +kernel
    rw [ha]
    exact (canonical22432 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1465 + difference 0 2) (sourceB1465 + difference 2 0) sourceC1465) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1606) := by
    have ha : (tripleCharges (sourceA1465 + difference 0 2) (sourceB1465 + difference 2 0) sourceC1465) = raw22433 := by
      apply Matrix.ext; unfold tripleCharges sourceA1465 sourceB1465 sourceC1465 difference raw22433; decide +kernel
    rw [ha]
    exact (canonical22433 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1465 + difference 0 3) (sourceB1465 + difference 3 0) sourceC1465) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1738) := by
    have ha : (tripleCharges (sourceA1465 + difference 0 3) (sourceB1465 + difference 3 0) sourceC1465) = raw22411 := by
      apply Matrix.ext; unfold tripleCharges sourceA1465 sourceB1465 sourceC1465 difference raw22411; decide +kernel
    rw [ha]
    exact (canonical22411 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1465 + difference 0 4) (sourceB1465 + difference 4 0) sourceC1465) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1608) := by
    have ha : (tripleCharges (sourceA1465 + difference 0 4) (sourceB1465 + difference 4 0) sourceC1465) = raw22434 := by
      apply Matrix.ext; unfold tripleCharges sourceA1465 sourceB1465 sourceC1465 difference raw22434; decide +kernel
    rw [ha]
    exact (canonical22434 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1465 + difference 0 5) (sourceB1465 + difference 5 0) sourceC1465) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1618) := by
    have ha : (tripleCharges (sourceA1465 + difference 0 5) (sourceB1465 + difference 5 0) sourceC1465) = raw22435 := by
      apply Matrix.ext; unfold tripleCharges sourceA1465 sourceB1465 sourceC1465 difference raw22435; decide +kernel
    rw [ha]
    exact (canonical22435 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1465 + sourceB1465) sourceC1465) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4071) := by
    have ha : (doubleCharges (sourceA1465 + sourceB1465) sourceC1465) = raw22329 := by
      apply Matrix.ext; unfold doubleCharges sourceA1465 sourceB1465 sourceC1465 raw22329; decide +kernel
    rw [ha]
    exact (canonical22329 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1465 sourceB1465 sourceC1465
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1465, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1467 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1467 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1467 + difference 0 1) (sourceB1467 + difference 1 0) sourceC1467) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2489) := by
    have ha : (tripleCharges (sourceA1467 + difference 0 1) (sourceB1467 + difference 1 0) sourceC1467) = raw22440 := by
      apply Matrix.ext; unfold tripleCharges sourceA1467 sourceB1467 sourceC1467 difference raw22440; decide +kernel
    rw [ha]
    exact (canonical22440 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1467 + difference 1 1) (sourceB1467 + difference 1 1) sourceC1467) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1220) := by
    have ha : (tripleCharges (sourceA1467 + difference 1 1) (sourceB1467 + difference 1 1) sourceC1467) = raw22441 := by
      apply Matrix.ext; unfold tripleCharges sourceA1467 sourceB1467 sourceC1467 difference raw22441; decide +kernel
    rw [ha]
    exact (canonical22441 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1467 + difference 2 1) (sourceB1467 + difference 1 2) sourceC1467) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1114) := by
    have ha : (tripleCharges (sourceA1467 + difference 2 1) (sourceB1467 + difference 1 2) sourceC1467) = raw22442 := by
      apply Matrix.ext; unfold tripleCharges sourceA1467 sourceB1467 sourceC1467 difference raw22442; decide +kernel
    rw [ha]
    exact (canonical22442 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1467 + difference 3 1) (sourceB1467 + difference 1 3) sourceC1467) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1139) := by
    have ha : (tripleCharges (sourceA1467 + difference 3 1) (sourceB1467 + difference 1 3) sourceC1467) = raw22443 := by
      apply Matrix.ext; unfold tripleCharges sourceA1467 sourceB1467 sourceC1467 difference raw22443; decide +kernel
    rw [ha]
    exact (canonical22443 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1467 + difference 4 1) (sourceB1467 + difference 1 4) sourceC1467) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1120) := by
    have ha : (tripleCharges (sourceA1467 + difference 4 1) (sourceB1467 + difference 1 4) sourceC1467) = raw22444 := by
      apply Matrix.ext; unfold tripleCharges sourceA1467 sourceB1467 sourceC1467 difference raw22444; decide +kernel
    rw [ha]
    exact (canonical22444 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1467 + difference 5 1) (sourceB1467 + difference 1 5) sourceC1467) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1120) := by
    have ha : (tripleCharges (sourceA1467 + difference 5 1) (sourceB1467 + difference 1 5) sourceC1467) = raw22445 := by
      apply Matrix.ext; unfold tripleCharges sourceA1467 sourceB1467 sourceC1467 difference raw22445; decide +kernel
    rw [ha]
    exact (canonical22445 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1467 + sourceB1467) sourceC1467) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA1467 + sourceB1467) sourceC1467) = raw4206 := by
      apply Matrix.ext; unfold doubleCharges sourceA1467 sourceB1467 sourceC1467 raw4206; decide +kernel
    rw [ha]
    exact (canonical4206 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1467 sourceB1467 sourceC1467
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1467, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1468 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1468 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1468 + difference 3 0) (sourceB1468 + difference 0 3) sourceC1468) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 632) := by
    have ha : (tripleCharges (sourceA1468 + difference 3 0) (sourceB1468 + difference 0 3) sourceC1468) = raw22446 := by
      apply Matrix.ext; unfold tripleCharges sourceA1468 sourceB1468 sourceC1468 difference raw22446; decide +kernel
    rw [ha]
    exact (canonical22446 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1468 + difference 3 1) (sourceB1468 + difference 1 3) sourceC1468) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1139) := by
    have ha : (tripleCharges (sourceA1468 + difference 3 1) (sourceB1468 + difference 1 3) sourceC1468) = raw22443 := by
      apply Matrix.ext; unfold tripleCharges sourceA1468 sourceB1468 sourceC1468 difference raw22443; decide +kernel
    rw [ha]
    exact (canonical22443 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1468 + difference 3 2) (sourceB1468 + difference 2 3) sourceC1468) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1152) := by
    have ha : (tripleCharges (sourceA1468 + difference 3 2) (sourceB1468 + difference 2 3) sourceC1468) = raw22447 := by
      apply Matrix.ext; unfold tripleCharges sourceA1468 sourceB1468 sourceC1468 difference raw22447; decide +kernel
    rw [ha]
    exact (canonical22447 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1468 + difference 3 3) (sourceB1468 + difference 3 3) sourceC1468) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1220) := by
    have ha : (tripleCharges (sourceA1468 + difference 3 3) (sourceB1468 + difference 3 3) sourceC1468) = raw22441 := by
      apply Matrix.ext; unfold tripleCharges sourceA1468 sourceB1468 sourceC1468 difference raw22441; decide +kernel
    rw [ha]
    exact (canonical22441 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1468 + difference 3 4) (sourceB1468 + difference 4 3) sourceC1468) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1240) := by
    have ha : (tripleCharges (sourceA1468 + difference 3 4) (sourceB1468 + difference 4 3) sourceC1468) = raw22448 := by
      apply Matrix.ext; unfold tripleCharges sourceA1468 sourceB1468 sourceC1468 difference raw22448; decide +kernel
    rw [ha]
    exact (canonical22448 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1468 + difference 3 5) (sourceB1468 + difference 5 3) sourceC1468) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1240) := by
    have ha : (tripleCharges (sourceA1468 + difference 3 5) (sourceB1468 + difference 5 3) sourceC1468) = raw22449 := by
      apply Matrix.ext; unfold tripleCharges sourceA1468 sourceB1468 sourceC1468 difference raw22449; decide +kernel
    rw [ha]
    exact (canonical22449 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1468 + sourceB1468) sourceC1468) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA1468 + sourceB1468) sourceC1468) = raw4206 := by
      apply Matrix.ext; unfold doubleCharges sourceA1468 sourceB1468 sourceC1468 raw4206; decide +kernel
    rw [ha]
    exact (canonical4206 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1468 sourceB1468 sourceC1468
    (0 : Fin 2) 1 (3 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1468, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1469 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1469 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1469 + difference 0 0) (sourceB1469 + difference 0 0) sourceC1469) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3297) := by
    have ha : (tripleCharges (sourceA1469 + difference 0 0) (sourceB1469 + difference 0 0) sourceC1469) = raw22439 := by
      apply Matrix.ext; unfold tripleCharges sourceA1469 sourceB1469 sourceC1469 difference raw22439; decide +kernel
    rw [ha]
    exact (canonical22439 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1469 + difference 0 1) (sourceB1469 + difference 1 0) sourceC1469) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1626) := by
    have ha : (tripleCharges (sourceA1469 + difference 0 1) (sourceB1469 + difference 1 0) sourceC1469) = raw22450 := by
      apply Matrix.ext; unfold tripleCharges sourceA1469 sourceB1469 sourceC1469 difference raw22450; decide +kernel
    rw [ha]
    exact (canonical22450 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1469 + difference 0 2) (sourceB1469 + difference 2 0) sourceC1469) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1614) := by
    have ha : (tripleCharges (sourceA1469 + difference 0 2) (sourceB1469 + difference 2 0) sourceC1469) = raw22451 := by
      apply Matrix.ext; unfold tripleCharges sourceA1469 sourceB1469 sourceC1469 difference raw22451; decide +kernel
    rw [ha]
    exact (canonical22451 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1469 + difference 0 3) (sourceB1469 + difference 3 0) sourceC1469) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1751) := by
    have ha : (tripleCharges (sourceA1469 + difference 0 3) (sourceB1469 + difference 3 0) sourceC1469) = raw22452 := by
      apply Matrix.ext; unfold tripleCharges sourceA1469 sourceB1469 sourceC1469 difference raw22452; decide +kernel
    rw [ha]
    exact (canonical22452 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1469 + difference 0 4) (sourceB1469 + difference 4 0) sourceC1469) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1618) := by
    have ha : (tripleCharges (sourceA1469 + difference 0 4) (sourceB1469 + difference 4 0) sourceC1469) = raw22435 := by
      apply Matrix.ext; unfold tripleCharges sourceA1469 sourceB1469 sourceC1469 difference raw22435; decide +kernel
    rw [ha]
    exact (canonical22435 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1469 + difference 0 5) (sourceB1469 + difference 5 0) sourceC1469) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1618) := by
    have ha : (tripleCharges (sourceA1469 + difference 0 5) (sourceB1469 + difference 5 0) sourceC1469) = raw22453 := by
      apply Matrix.ext; unfold tripleCharges sourceA1469 sourceB1469 sourceC1469 difference raw22453; decide +kernel
    rw [ha]
    exact (canonical22453 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1469 + sourceB1469) sourceC1469) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4071) := by
    have ha : (doubleCharges (sourceA1469 + sourceB1469) sourceC1469) = raw22329 := by
      apply Matrix.ext; unfold doubleCharges sourceA1469 sourceB1469 sourceC1469 raw22329; decide +kernel
    rw [ha]
    exact (canonical22329 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1469 sourceB1469 sourceC1469
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1469, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1470 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1470 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1470 + difference 1 0) (sourceB1470 + difference 0 1) sourceC1470) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1751) := by
    have ha : (tripleCharges (sourceA1470 + difference 1 0) (sourceB1470 + difference 0 1) sourceC1470) = raw22332 := by
      apply Matrix.ext; unfold tripleCharges sourceA1470 sourceB1470 sourceC1470 difference raw22332; decide +kernel
    rw [ha]
    exact (canonical22332 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1470 + difference 1 1) (sourceB1470 + difference 1 1) sourceC1470) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3297) := by
    have ha : (tripleCharges (sourceA1470 + difference 1 1) (sourceB1470 + difference 1 1) sourceC1470) = raw22439 := by
      apply Matrix.ext; unfold tripleCharges sourceA1470 sourceB1470 sourceC1470 difference raw22439; decide +kernel
    rw [ha]
    exact (canonical22439 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1470 + difference 1 2) (sourceB1470 + difference 2 1) sourceC1470) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3297) := by
    have ha : (tripleCharges (sourceA1470 + difference 1 2) (sourceB1470 + difference 2 1) sourceC1470) = raw22454 := by
      apply Matrix.ext; unfold tripleCharges sourceA1470 sourceB1470 sourceC1470 difference raw22454; decide +kernel
    rw [ha]
    exact (canonical22454 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1470 + difference 1 3) (sourceB1470 + difference 3 1) sourceC1470) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3312) := by
    have ha : (tripleCharges (sourceA1470 + difference 1 3) (sourceB1470 + difference 3 1) sourceC1470) = raw22455 := by
      apply Matrix.ext; unfold tripleCharges sourceA1470 sourceB1470 sourceC1470 difference raw22455; decide +kernel
    rw [ha]
    exact (canonical22455 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1470 + difference 1 4) (sourceB1470 + difference 4 1) sourceC1470) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3301) := by
    have ha : (tripleCharges (sourceA1470 + difference 1 4) (sourceB1470 + difference 4 1) sourceC1470) = raw22326 := by
      apply Matrix.ext; unfold tripleCharges sourceA1470 sourceB1470 sourceC1470 difference raw22326; decide +kernel
    rw [ha]
    exact (canonical22326 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1470 + difference 1 5) (sourceB1470 + difference 5 1) sourceC1470) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3301) := by
    have ha : (tripleCharges (sourceA1470 + difference 1 5) (sourceB1470 + difference 5 1) sourceC1470) = raw22456 := by
      apply Matrix.ext; unfold tripleCharges sourceA1470 sourceB1470 sourceC1470 difference raw22456; decide +kernel
    rw [ha]
    exact (canonical22456 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1470 + sourceB1470) sourceC1470) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4071) := by
    have ha : (doubleCharges (sourceA1470 + sourceB1470) sourceC1470) = raw22329 := by
      apply Matrix.ext; unfold doubleCharges sourceA1470 sourceB1470 sourceC1470 raw22329; decide +kernel
    rw [ha]
    exact (canonical22329 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1470 sourceB1470 sourceC1470
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1470, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1471 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1471 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1471 + difference 0 0) (sourceB1471 + difference 0 0) sourceC1471) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1182) := by
    have ha : (tripleCharges (sourceA1471 + difference 0 0) (sourceB1471 + difference 0 0) sourceC1471) = raw22457 := by
      apply Matrix.ext; unfold tripleCharges sourceA1471 sourceB1471 sourceC1471 difference raw22457; decide +kernel
    rw [ha]
    exact (canonical22457 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1471 + difference 0 1) (sourceB1471 + difference 1 0) sourceC1471) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2608) := by
    have ha : (tripleCharges (sourceA1471 + difference 0 1) (sourceB1471 + difference 1 0) sourceC1471) = raw22458 := by
      apply Matrix.ext; unfold tripleCharges sourceA1471 sourceB1471 sourceC1471 difference raw22458; decide +kernel
    rw [ha]
    exact (canonical22458 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1471 + difference 0 2) (sourceB1471 + difference 2 0) sourceC1471) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2533) := by
    have ha : (tripleCharges (sourceA1471 + difference 0 2) (sourceB1471 + difference 2 0) sourceC1471) = raw22459 := by
      apply Matrix.ext; unfold tripleCharges sourceA1471 sourceB1471 sourceC1471 difference raw22459; decide +kernel
    rw [ha]
    exact (canonical22459 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1471 + difference 0 3) (sourceB1471 + difference 3 0) sourceC1471) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2388) := by
    have ha : (tripleCharges (sourceA1471 + difference 0 3) (sourceB1471 + difference 3 0) sourceC1471) = raw22460 := by
      apply Matrix.ext; unfold tripleCharges sourceA1471 sourceB1471 sourceC1471 difference raw22460; decide +kernel
    rw [ha]
    exact (canonical22460 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1471 + difference 0 4) (sourceB1471 + difference 4 0) sourceC1471) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2673) := by
    have ha : (tripleCharges (sourceA1471 + difference 0 4) (sourceB1471 + difference 4 0) sourceC1471) = raw22461 := by
      apply Matrix.ext; unfold tripleCharges sourceA1471 sourceB1471 sourceC1471 difference raw22461; decide +kernel
    rw [ha]
    exact (canonical22461 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1471 + difference 0 5) (sourceB1471 + difference 5 0) sourceC1471) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2672) := by
    have ha : (tripleCharges (sourceA1471 + difference 0 5) (sourceB1471 + difference 5 0) sourceC1471) = raw22462 := by
      apply Matrix.ext; unfold tripleCharges sourceA1471 sourceB1471 sourceC1471 difference raw22462; decide +kernel
    rw [ha]
    exact (canonical22462 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1471 + sourceB1471) sourceC1471) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4088) := by
    have ha : (doubleCharges (sourceA1471 + sourceB1471) sourceC1471) = raw22463 := by
      apply Matrix.ext; unfold doubleCharges sourceA1471 sourceB1471 sourceC1471 raw22463; decide +kernel
    rw [ha]
    exact (canonical22463 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1471 sourceB1471 sourceC1471
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1471, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources46
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sourceEq1472 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1472 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1472 + difference 0 0) (sourceB1472 + difference 0 0) sourceC1472) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1196) := by
    have ha : (tripleCharges (sourceA1472 + difference 0 0) (sourceB1472 + difference 0 0) sourceC1472) = raw22464 := by
      apply Matrix.ext; unfold tripleCharges sourceA1472 sourceB1472 sourceC1472 difference raw22464; decide +kernel
    rw [ha]
    exact (canonical22464 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1472 + difference 0 1) (sourceB1472 + difference 1 0) sourceC1472) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2609) := by
    have ha : (tripleCharges (sourceA1472 + difference 0 1) (sourceB1472 + difference 1 0) sourceC1472) = raw22465 := by
      apply Matrix.ext; unfold tripleCharges sourceA1472 sourceB1472 sourceC1472 difference raw22465; decide +kernel
    rw [ha]
    exact (canonical22465 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1472 + difference 0 2) (sourceB1472 + difference 2 0) sourceC1472) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2452) := by
    have ha : (tripleCharges (sourceA1472 + difference 0 2) (sourceB1472 + difference 2 0) sourceC1472) = raw22466 := by
      apply Matrix.ext; unfold tripleCharges sourceA1472 sourceB1472 sourceC1472 difference raw22466; decide +kernel
    rw [ha]
    exact (canonical22466 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1472 + difference 0 3) (sourceB1472 + difference 3 0) sourceC1472) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2452) := by
    have ha : (tripleCharges (sourceA1472 + difference 0 3) (sourceB1472 + difference 3 0) sourceC1472) = raw22467 := by
      apply Matrix.ext; unfold tripleCharges sourceA1472 sourceB1472 sourceC1472 difference raw22467; decide +kernel
    rw [ha]
    exact (canonical22467 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1472 + difference 0 4) (sourceB1472 + difference 4 0) sourceC1472) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2695) := by
    have ha : (tripleCharges (sourceA1472 + difference 0 4) (sourceB1472 + difference 4 0) sourceC1472) = raw22468 := by
      apply Matrix.ext; unfold tripleCharges sourceA1472 sourceB1472 sourceC1472 difference raw22468; decide +kernel
    rw [ha]
    exact (canonical22468 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1472 + difference 0 5) (sourceB1472 + difference 5 0) sourceC1472) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2694) := by
    have ha : (tripleCharges (sourceA1472 + difference 0 5) (sourceB1472 + difference 5 0) sourceC1472) = raw22469 := by
      apply Matrix.ext; unfold tripleCharges sourceA1472 sourceB1472 sourceC1472 difference raw22469; decide +kernel
    rw [ha]
    exact (canonical22469 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1472 + sourceB1472) sourceC1472) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4090) := by
    have ha : (doubleCharges (sourceA1472 + sourceB1472) sourceC1472) = raw22470 := by
      apply Matrix.ext; unfold doubleCharges sourceA1472 sourceB1472 sourceC1472 raw22470; decide +kernel
    rw [ha]
    exact (canonical22470 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1472 sourceB1472 sourceC1472
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1472, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1475 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1475 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1475 + difference 0 1) (sourceB1475 + difference 1 0) sourceC1475) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4466) := by
    have ha : (tripleCharges (sourceA1475 + difference 0 1) (sourceB1475 + difference 1 0) sourceC1475) = raw22506 := by
      apply Matrix.ext; unfold tripleCharges sourceA1475 sourceB1475 sourceC1475 difference raw22506; decide +kernel
    rw [ha]
    exact (canonical22506 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1475 + difference 0 2) (sourceB1475 + difference 2 0) sourceC1475) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4466) := by
    have ha : (tripleCharges (sourceA1475 + difference 0 2) (sourceB1475 + difference 2 0) sourceC1475) = raw22507 := by
      apply Matrix.ext; unfold tripleCharges sourceA1475 sourceB1475 sourceC1475 difference raw22507; decide +kernel
    rw [ha]
    exact (canonical22507 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1475 + difference 0 3) (sourceB1475 + difference 3 0) sourceC1475) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4466) := by
    have ha : (tripleCharges (sourceA1475 + difference 0 3) (sourceB1475 + difference 3 0) sourceC1475) = raw22508 := by
      apply Matrix.ext; unfold tripleCharges sourceA1475 sourceB1475 sourceC1475 difference raw22508; decide +kernel
    rw [ha]
    exact (canonical22508 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1475 + difference 0 4) (sourceB1475 + difference 4 0) sourceC1475) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4510) := by
    have ha : (tripleCharges (sourceA1475 + difference 0 4) (sourceB1475 + difference 4 0) sourceC1475) = raw22509 := by
      apply Matrix.ext; unfold tripleCharges sourceA1475 sourceB1475 sourceC1475 difference raw22509; decide +kernel
    rw [ha]
    exact (canonical22509 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1475 + difference 0 5) (sourceB1475 + difference 5 0) sourceC1475) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4511) := by
    have ha : (tripleCharges (sourceA1475 + difference 0 5) (sourceB1475 + difference 5 0) sourceC1475) = raw22510 := by
      apply Matrix.ext; unfold tripleCharges sourceA1475 sourceB1475 sourceC1475 difference raw22510; decide +kernel
    rw [ha]
    exact (canonical22510 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1475 + difference 1 0) (sourceB1475 + difference 0 1) sourceC1475) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4466) := by
    have ha : (tripleCharges (sourceA1475 + difference 1 0) (sourceB1475 + difference 0 1) sourceC1475) = raw22511 := by
      apply Matrix.ext; unfold tripleCharges sourceA1475 sourceB1475 sourceC1475 difference raw22511; decide +kernel
    rw [ha]
    exact (canonical22511 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1475 + difference 1 2) (sourceB1475 + difference 2 1) sourceC1475) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4592) := by
    have ha : (tripleCharges (sourceA1475 + difference 1 2) (sourceB1475 + difference 2 1) sourceC1475) = raw22512 := by
      apply Matrix.ext; unfold tripleCharges sourceA1475 sourceB1475 sourceC1475 difference raw22512; decide +kernel
    rw [ha]
    exact (canonical22512 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1475 + difference 1 3) (sourceB1475 + difference 3 1) sourceC1475) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4592) := by
    have ha : (tripleCharges (sourceA1475 + difference 1 3) (sourceB1475 + difference 3 1) sourceC1475) = raw22513 := by
      apply Matrix.ext; unfold tripleCharges sourceA1475 sourceB1475 sourceC1475 difference raw22513; decide +kernel
    rw [ha]
    exact (canonical22513 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1475 + difference 1 4) (sourceB1475 + difference 4 1) sourceC1475) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4611) := by
    have ha : (tripleCharges (sourceA1475 + difference 1 4) (sourceB1475 + difference 4 1) sourceC1475) = raw22514 := by
      apply Matrix.ext; unfold tripleCharges sourceA1475 sourceB1475 sourceC1475 difference raw22514; decide +kernel
    rw [ha]
    exact (canonical22514 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1475 + difference 1 5) (sourceB1475 + difference 5 1) sourceC1475) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4612) := by
    have ha : (tripleCharges (sourceA1475 + difference 1 5) (sourceB1475 + difference 5 1) sourceC1475) = raw22515 := by
      apply Matrix.ext; unfold tripleCharges sourceA1475 sourceB1475 sourceC1475 difference raw22515; decide +kernel
    rw [ha]
    exact (canonical22515 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1475 + difference 2 0) (sourceB1475 + difference 0 2) sourceC1475) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4466) := by
    have ha : (tripleCharges (sourceA1475 + difference 2 0) (sourceB1475 + difference 0 2) sourceC1475) = raw22516 := by
      apply Matrix.ext; unfold tripleCharges sourceA1475 sourceB1475 sourceC1475 difference raw22516; decide +kernel
    rw [ha]
    exact (canonical22516 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1475 + difference 2 1) (sourceB1475 + difference 1 2) sourceC1475) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4592) := by
    have ha : (tripleCharges (sourceA1475 + difference 2 1) (sourceB1475 + difference 1 2) sourceC1475) = raw22517 := by
      apply Matrix.ext; unfold tripleCharges sourceA1475 sourceB1475 sourceC1475 difference raw22517; decide +kernel
    rw [ha]
    exact (canonical22517 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1475 + difference 2 3) (sourceB1475 + difference 3 2) sourceC1475) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4592) := by
    have ha : (tripleCharges (sourceA1475 + difference 2 3) (sourceB1475 + difference 3 2) sourceC1475) = raw22518 := by
      apply Matrix.ext; unfold tripleCharges sourceA1475 sourceB1475 sourceC1475 difference raw22518; decide +kernel
    rw [ha]
    exact (canonical22518 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1475 + difference 2 4) (sourceB1475 + difference 4 2) sourceC1475) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4611) := by
    have ha : (tripleCharges (sourceA1475 + difference 2 4) (sourceB1475 + difference 4 2) sourceC1475) = raw22519 := by
      apply Matrix.ext; unfold tripleCharges sourceA1475 sourceB1475 sourceC1475 difference raw22519; decide +kernel
    rw [ha]
    exact (canonical22519 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1475 + difference 2 5) (sourceB1475 + difference 5 2) sourceC1475) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4612) := by
    have ha : (tripleCharges (sourceA1475 + difference 2 5) (sourceB1475 + difference 5 2) sourceC1475) = raw22520 := by
      apply Matrix.ext; unfold tripleCharges sourceA1475 sourceB1475 sourceC1475 difference raw22520; decide +kernel
    rw [ha]
    exact (canonical22520 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1475 + difference 3 0) (sourceB1475 + difference 0 3) sourceC1475) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4466) := by
    have ha : (tripleCharges (sourceA1475 + difference 3 0) (sourceB1475 + difference 0 3) sourceC1475) = raw22521 := by
      apply Matrix.ext; unfold tripleCharges sourceA1475 sourceB1475 sourceC1475 difference raw22521; decide +kernel
    rw [ha]
    exact (canonical22521 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1475 + difference 3 1) (sourceB1475 + difference 1 3) sourceC1475) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4592) := by
    have ha : (tripleCharges (sourceA1475 + difference 3 1) (sourceB1475 + difference 1 3) sourceC1475) = raw22522 := by
      apply Matrix.ext; unfold tripleCharges sourceA1475 sourceB1475 sourceC1475 difference raw22522; decide +kernel
    rw [ha]
    exact (canonical22522 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1475 + difference 3 2) (sourceB1475 + difference 2 3) sourceC1475) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4592) := by
    have ha : (tripleCharges (sourceA1475 + difference 3 2) (sourceB1475 + difference 2 3) sourceC1475) = raw22523 := by
      apply Matrix.ext; unfold tripleCharges sourceA1475 sourceB1475 sourceC1475 difference raw22523; decide +kernel
    rw [ha]
    exact (canonical22523 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1475 + difference 3 4) (sourceB1475 + difference 4 3) sourceC1475) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4611) := by
    have ha : (tripleCharges (sourceA1475 + difference 3 4) (sourceB1475 + difference 4 3) sourceC1475) = raw22524 := by
      apply Matrix.ext; unfold tripleCharges sourceA1475 sourceB1475 sourceC1475 difference raw22524; decide +kernel
    rw [ha]
    exact (canonical22524 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1475 + difference 3 5) (sourceB1475 + difference 5 3) sourceC1475) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4612) := by
    have ha : (tripleCharges (sourceA1475 + difference 3 5) (sourceB1475 + difference 5 3) sourceC1475) = raw22525 := by
      apply Matrix.ext; unfold tripleCharges sourceA1475 sourceB1475 sourceC1475 difference raw22525; decide +kernel
    rw [ha]
    exact (canonical22525 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1475 + difference 4 0) (sourceB1475 + difference 0 4) sourceC1475) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4511) := by
    have ha : (tripleCharges (sourceA1475 + difference 4 0) (sourceB1475 + difference 0 4) sourceC1475) = raw22526 := by
      apply Matrix.ext; unfold tripleCharges sourceA1475 sourceB1475 sourceC1475 difference raw22526; decide +kernel
    rw [ha]
    exact (canonical22526 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1475 + difference 4 1) (sourceB1475 + difference 1 4) sourceC1475) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4612) := by
    have ha : (tripleCharges (sourceA1475 + difference 4 1) (sourceB1475 + difference 1 4) sourceC1475) = raw22527 := by
      apply Matrix.ext; unfold tripleCharges sourceA1475 sourceB1475 sourceC1475 difference raw22527; decide +kernel
    rw [ha]
    exact (canonical22527 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1475 + difference 4 2) (sourceB1475 + difference 2 4) sourceC1475) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4612) := by
    have ha : (tripleCharges (sourceA1475 + difference 4 2) (sourceB1475 + difference 2 4) sourceC1475) = raw22528 := by
      apply Matrix.ext; unfold tripleCharges sourceA1475 sourceB1475 sourceC1475 difference raw22528; decide +kernel
    rw [ha]
    exact (canonical22528 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1475 + difference 4 3) (sourceB1475 + difference 3 4) sourceC1475) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4612) := by
    have ha : (tripleCharges (sourceA1475 + difference 4 3) (sourceB1475 + difference 3 4) sourceC1475) = raw22529 := by
      apply Matrix.ext; unfold tripleCharges sourceA1475 sourceB1475 sourceC1475 difference raw22529; decide +kernel
    rw [ha]
    exact (canonical22529 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1475 + difference 4 5) (sourceB1475 + difference 5 4) sourceC1475) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4628) := by
    have ha : (tripleCharges (sourceA1475 + difference 4 5) (sourceB1475 + difference 5 4) sourceC1475) = raw22530 := by
      apply Matrix.ext; unfold tripleCharges sourceA1475 sourceB1475 sourceC1475 difference raw22530; decide +kernel
    rw [ha]
    exact (canonical22530 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1475 + difference 5 0) (sourceB1475 + difference 0 5) sourceC1475) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4510) := by
    have ha : (tripleCharges (sourceA1475 + difference 5 0) (sourceB1475 + difference 0 5) sourceC1475) = raw22531 := by
      apply Matrix.ext; unfold tripleCharges sourceA1475 sourceB1475 sourceC1475 difference raw22531; decide +kernel
    rw [ha]
    exact (canonical22531 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1475 + difference 5 1) (sourceB1475 + difference 1 5) sourceC1475) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4611) := by
    have ha : (tripleCharges (sourceA1475 + difference 5 1) (sourceB1475 + difference 1 5) sourceC1475) = raw22532 := by
      apply Matrix.ext; unfold tripleCharges sourceA1475 sourceB1475 sourceC1475 difference raw22532; decide +kernel
    rw [ha]
    exact (canonical22532 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1475 + difference 5 2) (sourceB1475 + difference 2 5) sourceC1475) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4611) := by
    have ha : (tripleCharges (sourceA1475 + difference 5 2) (sourceB1475 + difference 2 5) sourceC1475) = raw22533 := by
      apply Matrix.ext; unfold tripleCharges sourceA1475 sourceB1475 sourceC1475 difference raw22533; decide +kernel
    rw [ha]
    exact (canonical22533 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1475 + difference 5 3) (sourceB1475 + difference 3 5) sourceC1475) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4611) := by
    have ha : (tripleCharges (sourceA1475 + difference 5 3) (sourceB1475 + difference 3 5) sourceC1475) = raw22534 := by
      apply Matrix.ext; unfold tripleCharges sourceA1475 sourceB1475 sourceC1475 difference raw22534; decide +kernel
    rw [ha]
    exact (canonical22534 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1475 + difference 5 4) (sourceB1475 + difference 4 5) sourceC1475) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4626) := by
    have ha : (tripleCharges (sourceA1475 + difference 5 4) (sourceB1475 + difference 4 5) sourceC1475) = raw22535 := by
      apply Matrix.ext; unfold tripleCharges sourceA1475 sourceB1475 sourceC1475 difference raw22535; decide +kernel
    rw [ha]
    exact (canonical22535 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1475 sourceB1475 sourceC1475
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1475, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic78
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reindexCheck1248 : Integer.Sparse.reindex keyMap MixedData.row1248 = numericRow1248 := by decide +kernel

theorem numericCheck1248 (x : Master → ℝ) : Integer.Sparse.eval numericRow1248 x =
    (1 : ℝ) * reducedSource1248 x := by
  norm_num [numericRow1248, reducedSource1248, Integer.Sparse.eval, Sparse.eval, nodeValue1655, nodeValue1657, nodeValue1660, nodeValue1738, nodeValue2683, nodeValue4071]

theorem reindexCheck1249 : Integer.Sparse.reindex keyMap MixedData.row1249 = numericRow1249 := by decide +kernel

theorem numericCheck1249 (x : Master → ℝ) : Integer.Sparse.eval numericRow1249 x =
    (1 : ℝ) * reducedSource1249 x := by
  norm_num [numericRow1249, reducedSource1249, Integer.Sparse.eval, Sparse.eval, nodeValue1741, nodeValue2683, nodeValue2780, nodeValue3311, nodeValue4071]

theorem reindexCheck1250 : Integer.Sparse.reindex keyMap MixedData.row1250 = numericRow1250 := by decide +kernel

theorem numericCheck1250 (x : Master → ℝ) : Integer.Sparse.eval numericRow1250 x =
    (1 : ℝ) * reducedSource1250 x := by
  norm_num [numericRow1250, reducedSource1250, Integer.Sparse.eval, Sparse.eval, nodeValue1627, nodeValue2397, nodeValue2409, nodeValue2683, nodeValue3301, nodeValue4071]

theorem reindexCheck1251 : Integer.Sparse.reindex keyMap MixedData.row1251 = numericRow1251 := by decide +kernel

theorem numericCheck1251 (x : Master → ℝ) : Integer.Sparse.eval numericRow1251 x =
    (1 : ℝ) * reducedSource1251 x := by
  norm_num [numericRow1251, reducedSource1251, Integer.Sparse.eval, Sparse.eval, nodeValue1738, nodeValue2683, nodeValue3295, nodeValue3301, nodeValue3311, nodeValue4071]

theorem reindexCheck1252 : Integer.Sparse.reindex keyMap MixedData.row1252 = numericRow1252 := by decide +kernel

theorem numericCheck1252 (x : Master → ℝ) : Integer.Sparse.eval numericRow1252 x =
    (1 : ℝ) * reducedSource1252 x := by
  norm_num [numericRow1252, reducedSource1252, Integer.Sparse.eval, Sparse.eval, nodeValue1113, nodeValue1119, nodeValue1121, nodeValue1138, nodeValue1219, nodeValue2488, nodeValue4092]

theorem reindexCheck1253 : Integer.Sparse.reindex keyMap MixedData.row1253 = numericRow1253 := by decide +kernel

theorem numericCheck1253 (x : Master → ℝ) : Integer.Sparse.eval numericRow1253 x =
    (1 : ℝ) * reducedSource1253 x := by
  norm_num [numericRow1253, reducedSource1253, Integer.Sparse.eval, Sparse.eval, nodeValue631, nodeValue1138, nodeValue1151, nodeValue1219, nodeValue1236, nodeValue1241, nodeValue4092]

theorem reindexCheck1254 : Integer.Sparse.reindex keyMap MixedData.row1254 = numericRow1254 := by decide +kernel

theorem numericCheck1254 (x : Master → ℝ) : Integer.Sparse.eval numericRow1254 x =
    (1 : ℝ) * reducedSource1254 x := by
  norm_num [numericRow1254, reducedSource1254, Integer.Sparse.eval, Sparse.eval, nodeValue1606, nodeValue1608, nodeValue1611, nodeValue1618, nodeValue1738, nodeValue3295, nodeValue4071]

theorem reindexCheck1255 : Integer.Sparse.reindex keyMap MixedData.row1255 = numericRow1255 := by decide +kernel

theorem numericCheck1255 (x : Master → ℝ) : Integer.Sparse.eval numericRow1255 x =
    (1 : ℝ) * reducedSource1255 x := by
  norm_num [numericRow1255, reducedSource1255, Integer.Sparse.eval, Sparse.eval, nodeValue1114, nodeValue1120, nodeValue1139, nodeValue1220, nodeValue2489, nodeValue4091]

theorem reindexCheck1256 : Integer.Sparse.reindex keyMap MixedData.row1256 = numericRow1256 := by decide +kernel

theorem numericCheck1256 (x : Master → ℝ) : Integer.Sparse.eval numericRow1256 x =
    (1 : ℝ) * reducedSource1256 x := by
  norm_num [numericRow1256, reducedSource1256, Integer.Sparse.eval, Sparse.eval, nodeValue632, nodeValue1139, nodeValue1152, nodeValue1220, nodeValue1240, nodeValue4091]

theorem reindexCheck1257 : Integer.Sparse.reindex keyMap MixedData.row1257 = numericRow1257 := by decide +kernel

theorem numericCheck1257 (x : Master → ℝ) : Integer.Sparse.eval numericRow1257 x =
    (1 : ℝ) * reducedSource1257 x := by
  norm_num [numericRow1257, reducedSource1257, Integer.Sparse.eval, Sparse.eval, nodeValue1614, nodeValue1618, nodeValue1626, nodeValue1751, nodeValue3297, nodeValue4071]

theorem reindexCheck1258 : Integer.Sparse.reindex keyMap MixedData.row1258 = numericRow1258 := by decide +kernel

theorem numericCheck1258 (x : Master → ℝ) : Integer.Sparse.eval numericRow1258 x =
    (1 : ℝ) * reducedSource1258 x := by
  norm_num [numericRow1258, reducedSource1258, Integer.Sparse.eval, Sparse.eval, nodeValue1751, nodeValue3297, nodeValue3301, nodeValue3312, nodeValue4071]

theorem reindexCheck1259 : Integer.Sparse.reindex keyMap MixedData.row1259 = numericRow1259 := by decide +kernel

theorem numericCheck1259 (x : Master → ℝ) : Integer.Sparse.eval numericRow1259 x =
    (1 : ℝ) * reducedSource1259 x := by
  norm_num [numericRow1259, reducedSource1259, Integer.Sparse.eval, Sparse.eval, nodeValue1182, nodeValue2388, nodeValue2533, nodeValue2608, nodeValue2672, nodeValue2673, nodeValue4088]

theorem reindexCheck1260 : Integer.Sparse.reindex keyMap MixedData.row1260 = numericRow1260 := by decide +kernel

theorem numericCheck1260 (x : Master → ℝ) : Integer.Sparse.eval numericRow1260 x =
    (1 : ℝ) * reducedSource1260 x := by
  norm_num [numericRow1260, reducedSource1260, Integer.Sparse.eval, Sparse.eval, nodeValue1196, nodeValue2452, nodeValue2609, nodeValue2694, nodeValue2695, nodeValue4090]

theorem reindexCheck1263 : Integer.Sparse.reindex keyMap MixedData.row1263 = numericRow1263 := by decide +kernel

theorem numericCheck1263 (x : Master → ℝ) : Integer.Sparse.eval numericRow1263 x =
    (1440 : ℝ) * reducedSource1263 x := by
  norm_num [numericRow1263, reducedSource1263, Integer.Sparse.eval, Sparse.eval, nodeValue4466, nodeValue4510, nodeValue4511, nodeValue4592, nodeValue4611, nodeValue4612, nodeValue4626, nodeValue4628]
  ring

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Rows78
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero1248 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1248 (mixedVector B) = 0 := by
  have h1655 : mixedVector B (Sum.inr 1655) = Sparse.eval nodeValue1655 (mixedVector B) := by
    change mixedMoment B node1655 node1655Labels = _
    exact sound1655 B hB hF
  have h1657 : mixedVector B (Sum.inr 1657) = Sparse.eval nodeValue1657 (mixedVector B) := by
    change mixedMoment B node1657 node1657Labels = _
    exact sound1657 B hB hF
  have h1660 : mixedVector B (Sum.inr 1660) = Sparse.eval nodeValue1660 (mixedVector B) := by
    change mixedMoment B node1660 node1660Labels = _
    exact sound1660 B hB hF
  have h1738 : mixedVector B (Sum.inr 1738) = Sparse.eval nodeValue1738 (mixedVector B) := by
    change mixedMoment B node1738 node1738Labels = _
    exact sound1738 B hB hF
  have h2683 : mixedVector B (Sum.inr 2683) = Sparse.eval nodeValue2683 (mixedVector B) := by
    change mixedMoment B node2683 node2683Labels = _
    exact sound2683 B hB hF
  have h4071 : mixedVector B (Sum.inr 4071) = Sparse.eval nodeValue4071 (mixedVector B) := by
    change mixedMoment B node4071 node4071Labels = _
    exact sound4071 B hB hF
  simpa only [sourceForm1459, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1655, h1657, h1660, h1738, h2683, h4071, reducedSource1248] using sourceEq1459 B hB

theorem rowSound1248 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1248 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1248, numericCheck1248, reducedZero1248 B hB hF, mul_zero]

theorem reducedZero1249 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1249 (mixedVector B) = 0 := by
  have h1741 : mixedVector B (Sum.inr 1741) = Sparse.eval nodeValue1741 (mixedVector B) := by
    change mixedMoment B node1741 node1741Labels = _
    exact sound1741 B hB hF
  have h2683 : mixedVector B (Sum.inr 2683) = Sparse.eval nodeValue2683 (mixedVector B) := by
    change mixedMoment B node2683 node2683Labels = _
    exact sound2683 B hB hF
  have h2780 : mixedVector B (Sum.inr 2780) = Sparse.eval nodeValue2780 (mixedVector B) := by
    change mixedMoment B node2780 node2780Labels = _
    exact sound2780 B hB hF
  have h3311 : mixedVector B (Sum.inr 3311) = Sparse.eval nodeValue3311 (mixedVector B) := by
    change mixedMoment B node3311 node3311Labels = _
    exact sound3311 B hB hF
  have h4071 : mixedVector B (Sum.inr 4071) = Sparse.eval nodeValue4071 (mixedVector B) := by
    change mixedMoment B node4071 node4071Labels = _
    exact sound4071 B hB hF
  simpa only [sourceForm1460, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1741, h2683, h2780, h3311, h4071, reducedSource1249] using sourceEq1460 B hB

theorem rowSound1249 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1249 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1249, numericCheck1249, reducedZero1249 B hB hF, mul_zero]

theorem reducedZero1250 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1250 (mixedVector B) = 0 := by
  have h1627 : mixedVector B (Sum.inr 1627) = Sparse.eval nodeValue1627 (mixedVector B) := by
    change mixedMoment B node1627 node1627Labels = _
    exact sound1627 B hB hF
  have h2397 : mixedVector B (Sum.inr 2397) = Sparse.eval nodeValue2397 (mixedVector B) := by
    change mixedMoment B node2397 node2397Labels = _
    exact sound2397 B hB hF
  have h2409 : mixedVector B (Sum.inr 2409) = Sparse.eval nodeValue2409 (mixedVector B) := by
    change mixedMoment B node2409 node2409Labels = _
    exact sound2409 B hB hF
  have h2683 : mixedVector B (Sum.inr 2683) = Sparse.eval nodeValue2683 (mixedVector B) := by
    change mixedMoment B node2683 node2683Labels = _
    exact sound2683 B hB hF
  have h3301 : mixedVector B (Sum.inr 3301) = Sparse.eval nodeValue3301 (mixedVector B) := by
    change mixedMoment B node3301 node3301Labels = _
    exact sound3301 B hB hF
  have h4071 : mixedVector B (Sum.inr 4071) = Sparse.eval nodeValue4071 (mixedVector B) := by
    change mixedMoment B node4071 node4071Labels = _
    exact sound4071 B hB hF
  simpa only [sourceForm1461, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1627, h2397, h2409, h2683, h3301, h4071, reducedSource1250] using sourceEq1461 B hB

theorem rowSound1250 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1250 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1250, numericCheck1250, reducedZero1250 B hB hF, mul_zero]

theorem reducedZero1251 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1251 (mixedVector B) = 0 := by
  have h1738 : mixedVector B (Sum.inr 1738) = Sparse.eval nodeValue1738 (mixedVector B) := by
    change mixedMoment B node1738 node1738Labels = _
    exact sound1738 B hB hF
  have h2683 : mixedVector B (Sum.inr 2683) = Sparse.eval nodeValue2683 (mixedVector B) := by
    change mixedMoment B node2683 node2683Labels = _
    exact sound2683 B hB hF
  have h3295 : mixedVector B (Sum.inr 3295) = Sparse.eval nodeValue3295 (mixedVector B) := by
    change mixedMoment B node3295 node3295Labels = _
    exact sound3295 B hB hF
  have h3301 : mixedVector B (Sum.inr 3301) = Sparse.eval nodeValue3301 (mixedVector B) := by
    change mixedMoment B node3301 node3301Labels = _
    exact sound3301 B hB hF
  have h3311 : mixedVector B (Sum.inr 3311) = Sparse.eval nodeValue3311 (mixedVector B) := by
    change mixedMoment B node3311 node3311Labels = _
    exact sound3311 B hB hF
  have h4071 : mixedVector B (Sum.inr 4071) = Sparse.eval nodeValue4071 (mixedVector B) := by
    change mixedMoment B node4071 node4071Labels = _
    exact sound4071 B hB hF
  simpa only [sourceForm1462, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1738, h2683, h3295, h3301, h3311, h4071, reducedSource1251] using sourceEq1462 B hB

theorem rowSound1251 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1251 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1251, numericCheck1251, reducedZero1251 B hB hF, mul_zero]

theorem reducedZero1252 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1252 (mixedVector B) = 0 := by
  have h1113 : mixedVector B (Sum.inr 1113) = Sparse.eval nodeValue1113 (mixedVector B) := by
    change mixedMoment B node1113 node1113Labels = _
    exact sound1113 B hB hF
  have h1119 : mixedVector B (Sum.inr 1119) = Sparse.eval nodeValue1119 (mixedVector B) := by
    change mixedMoment B node1119 node1119Labels = _
    exact sound1119 B hB hF
  have h1121 : mixedVector B (Sum.inr 1121) = Sparse.eval nodeValue1121 (mixedVector B) := by
    change mixedMoment B node1121 node1121Labels = _
    exact sound1121 B hB hF
  have h1138 : mixedVector B (Sum.inr 1138) = Sparse.eval nodeValue1138 (mixedVector B) := by
    change mixedMoment B node1138 node1138Labels = _
    exact sound1138 B hB hF
  have h1219 : mixedVector B (Sum.inr 1219) = Sparse.eval nodeValue1219 (mixedVector B) := by
    change mixedMoment B node1219 node1219Labels = _
    exact sound1219 B hB hF
  have h2488 : mixedVector B (Sum.inr 2488) = Sparse.eval nodeValue2488 (mixedVector B) := by
    change mixedMoment B node2488 node2488Labels = _
    exact sound2488 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm1463, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1113, h1119, h1121, h1138, h1219, h2488, h4092, reducedSource1252] using sourceEq1463 B hB

theorem rowSound1252 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1252 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1252, numericCheck1252, reducedZero1252 B hB hF, mul_zero]

theorem reducedZero1253 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1253 (mixedVector B) = 0 := by
  have h631 : mixedVector B (Sum.inr 631) = Sparse.eval nodeValue631 (mixedVector B) := by
    change mixedMoment B node631 node631Labels = _
    exact sound631 B hB hF
  have h1138 : mixedVector B (Sum.inr 1138) = Sparse.eval nodeValue1138 (mixedVector B) := by
    change mixedMoment B node1138 node1138Labels = _
    exact sound1138 B hB hF
  have h1151 : mixedVector B (Sum.inr 1151) = Sparse.eval nodeValue1151 (mixedVector B) := by
    change mixedMoment B node1151 node1151Labels = _
    exact sound1151 B hB hF
  have h1219 : mixedVector B (Sum.inr 1219) = Sparse.eval nodeValue1219 (mixedVector B) := by
    change mixedMoment B node1219 node1219Labels = _
    exact sound1219 B hB hF
  have h1236 : mixedVector B (Sum.inr 1236) = Sparse.eval nodeValue1236 (mixedVector B) := by
    change mixedMoment B node1236 node1236Labels = _
    exact sound1236 B hB hF
  have h1241 : mixedVector B (Sum.inr 1241) = Sparse.eval nodeValue1241 (mixedVector B) := by
    change mixedMoment B node1241 node1241Labels = _
    exact sound1241 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm1464, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h631, h1138, h1151, h1219, h1236, h1241, h4092, reducedSource1253] using sourceEq1464 B hB

theorem rowSound1253 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1253 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1253, numericCheck1253, reducedZero1253 B hB hF, mul_zero]

theorem reducedZero1254 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1254 (mixedVector B) = 0 := by
  have h1606 : mixedVector B (Sum.inr 1606) = Sparse.eval nodeValue1606 (mixedVector B) := by
    change mixedMoment B node1606 node1606Labels = _
    exact sound1606 B hB hF
  have h1608 : mixedVector B (Sum.inr 1608) = Sparse.eval nodeValue1608 (mixedVector B) := by
    change mixedMoment B node1608 node1608Labels = _
    exact sound1608 B hB hF
  have h1611 : mixedVector B (Sum.inr 1611) = Sparse.eval nodeValue1611 (mixedVector B) := by
    change mixedMoment B node1611 node1611Labels = _
    exact sound1611 B hB hF
  have h1618 : mixedVector B (Sum.inr 1618) = Sparse.eval nodeValue1618 (mixedVector B) := by
    change mixedMoment B node1618 node1618Labels = _
    exact sound1618 B hB hF
  have h1738 : mixedVector B (Sum.inr 1738) = Sparse.eval nodeValue1738 (mixedVector B) := by
    change mixedMoment B node1738 node1738Labels = _
    exact sound1738 B hB hF
  have h3295 : mixedVector B (Sum.inr 3295) = Sparse.eval nodeValue3295 (mixedVector B) := by
    change mixedMoment B node3295 node3295Labels = _
    exact sound3295 B hB hF
  have h4071 : mixedVector B (Sum.inr 4071) = Sparse.eval nodeValue4071 (mixedVector B) := by
    change mixedMoment B node4071 node4071Labels = _
    exact sound4071 B hB hF
  simpa only [sourceForm1465, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1606, h1608, h1611, h1618, h1738, h3295, h4071, reducedSource1254] using sourceEq1465 B hB

theorem rowSound1254 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1254 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1254, numericCheck1254, reducedZero1254 B hB hF, mul_zero]

theorem reducedZero1255 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1255 (mixedVector B) = 0 := by
  have h1114 : mixedVector B (Sum.inr 1114) = Sparse.eval nodeValue1114 (mixedVector B) := by
    change mixedMoment B node1114 node1114Labels = _
    exact sound1114 B hB hF
  have h1120 : mixedVector B (Sum.inr 1120) = Sparse.eval nodeValue1120 (mixedVector B) := by
    change mixedMoment B node1120 node1120Labels = _
    exact sound1120 B hB hF
  have h1139 : mixedVector B (Sum.inr 1139) = Sparse.eval nodeValue1139 (mixedVector B) := by
    change mixedMoment B node1139 node1139Labels = _
    exact sound1139 B hB hF
  have h1220 : mixedVector B (Sum.inr 1220) = Sparse.eval nodeValue1220 (mixedVector B) := by
    change mixedMoment B node1220 node1220Labels = _
    exact sound1220 B hB hF
  have h2489 : mixedVector B (Sum.inr 2489) = Sparse.eval nodeValue2489 (mixedVector B) := by
    change mixedMoment B node2489 node2489Labels = _
    exact sound2489 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm1467, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1114, h1120, h1139, h1220, h2489, h4091, reducedSource1255] using sourceEq1467 B hB

theorem rowSound1255 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1255 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1255, numericCheck1255, reducedZero1255 B hB hF, mul_zero]

theorem reducedZero1256 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1256 (mixedVector B) = 0 := by
  have h632 : mixedVector B (Sum.inr 632) = Sparse.eval nodeValue632 (mixedVector B) := by
    change mixedMoment B node632 node632Labels = _
    exact sound632 B hB hF
  have h1139 : mixedVector B (Sum.inr 1139) = Sparse.eval nodeValue1139 (mixedVector B) := by
    change mixedMoment B node1139 node1139Labels = _
    exact sound1139 B hB hF
  have h1152 : mixedVector B (Sum.inr 1152) = Sparse.eval nodeValue1152 (mixedVector B) := by
    change mixedMoment B node1152 node1152Labels = _
    exact sound1152 B hB hF
  have h1220 : mixedVector B (Sum.inr 1220) = Sparse.eval nodeValue1220 (mixedVector B) := by
    change mixedMoment B node1220 node1220Labels = _
    exact sound1220 B hB hF
  have h1240 : mixedVector B (Sum.inr 1240) = Sparse.eval nodeValue1240 (mixedVector B) := by
    change mixedMoment B node1240 node1240Labels = _
    exact sound1240 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm1468, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h632, h1139, h1152, h1220, h1240, h4091, reducedSource1256] using sourceEq1468 B hB

theorem rowSound1256 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1256 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1256, numericCheck1256, reducedZero1256 B hB hF, mul_zero]

theorem reducedZero1257 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1257 (mixedVector B) = 0 := by
  have h1614 : mixedVector B (Sum.inr 1614) = Sparse.eval nodeValue1614 (mixedVector B) := by
    change mixedMoment B node1614 node1614Labels = _
    exact sound1614 B hB hF
  have h1618 : mixedVector B (Sum.inr 1618) = Sparse.eval nodeValue1618 (mixedVector B) := by
    change mixedMoment B node1618 node1618Labels = _
    exact sound1618 B hB hF
  have h1626 : mixedVector B (Sum.inr 1626) = Sparse.eval nodeValue1626 (mixedVector B) := by
    change mixedMoment B node1626 node1626Labels = _
    exact sound1626 B hB hF
  have h1751 : mixedVector B (Sum.inr 1751) = Sparse.eval nodeValue1751 (mixedVector B) := by
    change mixedMoment B node1751 node1751Labels = _
    exact sound1751 B hB hF
  have h3297 : mixedVector B (Sum.inr 3297) = Sparse.eval nodeValue3297 (mixedVector B) := by
    change mixedMoment B node3297 node3297Labels = _
    exact sound3297 B hB hF
  have h4071 : mixedVector B (Sum.inr 4071) = Sparse.eval nodeValue4071 (mixedVector B) := by
    change mixedMoment B node4071 node4071Labels = _
    exact sound4071 B hB hF
  simpa only [sourceForm1469, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1614, h1618, h1626, h1751, h3297, h4071, reducedSource1257] using sourceEq1469 B hB

theorem rowSound1257 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1257 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1257, numericCheck1257, reducedZero1257 B hB hF, mul_zero]

theorem reducedZero1258 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1258 (mixedVector B) = 0 := by
  have h1751 : mixedVector B (Sum.inr 1751) = Sparse.eval nodeValue1751 (mixedVector B) := by
    change mixedMoment B node1751 node1751Labels = _
    exact sound1751 B hB hF
  have h3297 : mixedVector B (Sum.inr 3297) = Sparse.eval nodeValue3297 (mixedVector B) := by
    change mixedMoment B node3297 node3297Labels = _
    exact sound3297 B hB hF
  have h3301 : mixedVector B (Sum.inr 3301) = Sparse.eval nodeValue3301 (mixedVector B) := by
    change mixedMoment B node3301 node3301Labels = _
    exact sound3301 B hB hF
  have h3312 : mixedVector B (Sum.inr 3312) = Sparse.eval nodeValue3312 (mixedVector B) := by
    change mixedMoment B node3312 node3312Labels = _
    exact sound3312 B hB hF
  have h4071 : mixedVector B (Sum.inr 4071) = Sparse.eval nodeValue4071 (mixedVector B) := by
    change mixedMoment B node4071 node4071Labels = _
    exact sound4071 B hB hF
  simpa only [sourceForm1470, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1751, h3297, h3301, h3312, h4071, reducedSource1258] using sourceEq1470 B hB

theorem rowSound1258 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1258 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1258, numericCheck1258, reducedZero1258 B hB hF, mul_zero]

theorem reducedZero1259 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1259 (mixedVector B) = 0 := by
  have h1182 : mixedVector B (Sum.inr 1182) = Sparse.eval nodeValue1182 (mixedVector B) := by
    change mixedMoment B node1182 node1182Labels = _
    exact sound1182 B hB hF
  have h2388 : mixedVector B (Sum.inr 2388) = Sparse.eval nodeValue2388 (mixedVector B) := by
    change mixedMoment B node2388 node2388Labels = _
    exact sound2388 B hB hF
  have h2533 : mixedVector B (Sum.inr 2533) = Sparse.eval nodeValue2533 (mixedVector B) := by
    change mixedMoment B node2533 node2533Labels = _
    exact sound2533 B hB hF
  have h2608 : mixedVector B (Sum.inr 2608) = Sparse.eval nodeValue2608 (mixedVector B) := by
    change mixedMoment B node2608 node2608Labels = _
    exact sound2608 B hB hF
  have h2672 : mixedVector B (Sum.inr 2672) = Sparse.eval nodeValue2672 (mixedVector B) := by
    change mixedMoment B node2672 node2672Labels = _
    exact sound2672 B hB hF
  have h2673 : mixedVector B (Sum.inr 2673) = Sparse.eval nodeValue2673 (mixedVector B) := by
    change mixedMoment B node2673 node2673Labels = _
    exact sound2673 B hB hF
  have h4088 : mixedVector B (Sum.inr 4088) = Sparse.eval nodeValue4088 (mixedVector B) := by
    change mixedMoment B node4088 node4088Labels = _
    exact sound4088 B hB hF
  simpa only [sourceForm1471, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1182, h2388, h2533, h2608, h2672, h2673, h4088, reducedSource1259] using sourceEq1471 B hB

theorem rowSound1259 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1259 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1259, numericCheck1259, reducedZero1259 B hB hF, mul_zero]

theorem reducedZero1260 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1260 (mixedVector B) = 0 := by
  have h1196 : mixedVector B (Sum.inr 1196) = Sparse.eval nodeValue1196 (mixedVector B) := by
    change mixedMoment B node1196 node1196Labels = _
    exact sound1196 B hB hF
  have h2452 : mixedVector B (Sum.inr 2452) = Sparse.eval nodeValue2452 (mixedVector B) := by
    change mixedMoment B node2452 node2452Labels = _
    exact sound2452 B hB hF
  have h2609 : mixedVector B (Sum.inr 2609) = Sparse.eval nodeValue2609 (mixedVector B) := by
    change mixedMoment B node2609 node2609Labels = _
    exact sound2609 B hB hF
  have h2694 : mixedVector B (Sum.inr 2694) = Sparse.eval nodeValue2694 (mixedVector B) := by
    change mixedMoment B node2694 node2694Labels = _
    exact sound2694 B hB hF
  have h2695 : mixedVector B (Sum.inr 2695) = Sparse.eval nodeValue2695 (mixedVector B) := by
    change mixedMoment B node2695 node2695Labels = _
    exact sound2695 B hB hF
  have h4090 : mixedVector B (Sum.inr 4090) = Sparse.eval nodeValue4090 (mixedVector B) := by
    change mixedMoment B node4090 node4090Labels = _
    exact sound4090 B hB hF
  simpa only [sourceForm1472, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1196, h2452, h2609, h2694, h2695, h4090, reducedSource1260] using sourceEq1472 B hB

theorem rowSound1260 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1260 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1260, numericCheck1260, reducedZero1260 B hB hF, mul_zero]

theorem reducedZero1263 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1263 (mixedVector B) = 0 := by
  have h4466 : mixedVector B (Sum.inr 4466) = Sparse.eval nodeValue4466 (mixedVector B) := by
    change mixedMoment B node4466 node4466Labels = _
    exact sound4466 B hB hF
  have h4510 : mixedVector B (Sum.inr 4510) = Sparse.eval nodeValue4510 (mixedVector B) := by
    change mixedMoment B node4510 node4510Labels = _
    exact sound4510 B hB hF
  have h4511 : mixedVector B (Sum.inr 4511) = Sparse.eval nodeValue4511 (mixedVector B) := by
    change mixedMoment B node4511 node4511Labels = _
    exact sound4511 B hB hF
  have h4592 : mixedVector B (Sum.inr 4592) = Sparse.eval nodeValue4592 (mixedVector B) := by
    change mixedMoment B node4592 node4592Labels = _
    exact sound4592 B hB hF
  have h4611 : mixedVector B (Sum.inr 4611) = Sparse.eval nodeValue4611 (mixedVector B) := by
    change mixedMoment B node4611 node4611Labels = _
    exact sound4611 B hB hF
  have h4612 : mixedVector B (Sum.inr 4612) = Sparse.eval nodeValue4612 (mixedVector B) := by
    change mixedMoment B node4612 node4612Labels = _
    exact sound4612 B hB hF
  have h4626 : mixedVector B (Sum.inr 4626) = Sparse.eval nodeValue4626 (mixedVector B) := by
    change mixedMoment B node4626 node4626Labels = _
    exact sound4626 B hB hF
  have h4628 : mixedVector B (Sum.inr 4628) = Sparse.eval nodeValue4628 (mixedVector B) := by
    change mixedMoment B node4628 node4628Labels = _
    exact sound4628 B hB hF
  simpa only [sourceForm1475, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4466, h4510, h4511, h4592, h4611, h4612, h4626, h4628, reducedSource1263] using sourceEq1475 B hB

theorem rowSound1263 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1263 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1263, numericCheck1263, reducedZero1263 B hB hF, mul_zero]

theorem sourceRowsAt1248 : MixedData.sourceRows (1248 : Fin 2425) =
    MixedData.row1248 := by decide +kernel

theorem sourceRowsAt1249 : MixedData.sourceRows (1249 : Fin 2425) =
    MixedData.row1249 := by decide +kernel

theorem sourceRowsAt1250 : MixedData.sourceRows (1250 : Fin 2425) =
    MixedData.row1250 := by decide +kernel

theorem sourceRowsAt1251 : MixedData.sourceRows (1251 : Fin 2425) =
    MixedData.row1251 := by decide +kernel

theorem sourceRowsAt1252 : MixedData.sourceRows (1252 : Fin 2425) =
    MixedData.row1252 := by decide +kernel

theorem sourceRowsAt1253 : MixedData.sourceRows (1253 : Fin 2425) =
    MixedData.row1253 := by decide +kernel

theorem sourceRowsAt1254 : MixedData.sourceRows (1254 : Fin 2425) =
    MixedData.row1254 := by decide +kernel

theorem sourceRowsAt1255 : MixedData.sourceRows (1255 : Fin 2425) =
    MixedData.row1255 := by decide +kernel

theorem sourceRowsAt1256 : MixedData.sourceRows (1256 : Fin 2425) =
    MixedData.row1256 := by decide +kernel

theorem sourceRowsAt1257 : MixedData.sourceRows (1257 : Fin 2425) =
    MixedData.row1257 := by decide +kernel

theorem sourceRowsAt1258 : MixedData.sourceRows (1258 : Fin 2425) =
    MixedData.row1258 := by decide +kernel

theorem sourceRowsAt1259 : MixedData.sourceRows (1259 : Fin 2425) =
    MixedData.row1259 := by decide +kernel

theorem sourceRowsAt1260 : MixedData.sourceRows (1260 : Fin 2425) =
    MixedData.row1260 := by decide +kernel

theorem sourceRowsAt1261 : MixedData.sourceRows (1261 : Fin 2425) =
    MixedData.row1261 := by decide +kernel

theorem sourceRowsAt1262 : MixedData.sourceRows (1262 : Fin 2425) =
    MixedData.row1262 := by decide +kernel

theorem sourceRowsAt1263 : MixedData.sourceRows (1263 : Fin 2425) =
    MixedData.row1263 := by decide +kernel

theorem chunkSound78_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) (k : Fin 2425)
    (hk : k.val / 16 = 78) :
    Integer.Sparse.eval (MixedData.sourceRows k) (numericVector B) = 0 := by
  have heq : k.val = 1248 ∨ k.val = 1249 ∨ k.val = 1250 ∨ k.val = 1251 ∨ k.val = 1252 ∨ k.val = 1253 ∨ k.val = 1254 ∨ k.val = 1255 ∨ k.val = 1256 ∨ k.val = 1257 ∨ k.val = 1258 ∨ k.val = 1259 ∨ k.val = 1260 ∨ k.val = 1261 ∨ k.val = 1262 ∨ k.val = 1263 := by omega
  rcases heq with h1248 | h1249 | h1250 | h1251 | h1252 | h1253 | h1254 | h1255 | h1256 | h1257 | h1258 | h1259 | h1260 | h1261 | h1262 | h1263
  · have he : k = (1248 : Fin 2425) := Fin.ext h1248
    subst k
    rw [sourceRowsAt1248]
    exact rowSound1248 B hB hF
  · have he : k = (1249 : Fin 2425) := Fin.ext h1249
    subst k
    rw [sourceRowsAt1249]
    exact rowSound1249 B hB hF
  · have he : k = (1250 : Fin 2425) := Fin.ext h1250
    subst k
    rw [sourceRowsAt1250]
    exact rowSound1250 B hB hF
  · have he : k = (1251 : Fin 2425) := Fin.ext h1251
    subst k
    rw [sourceRowsAt1251]
    exact rowSound1251 B hB hF
  · have he : k = (1252 : Fin 2425) := Fin.ext h1252
    subst k
    rw [sourceRowsAt1252]
    exact rowSound1252 B hB hF
  · have he : k = (1253 : Fin 2425) := Fin.ext h1253
    subst k
    rw [sourceRowsAt1253]
    exact rowSound1253 B hB hF
  · have he : k = (1254 : Fin 2425) := Fin.ext h1254
    subst k
    rw [sourceRowsAt1254]
    exact rowSound1254 B hB hF
  · have he : k = (1255 : Fin 2425) := Fin.ext h1255
    subst k
    rw [sourceRowsAt1255]
    exact rowSound1255 B hB hF
  · have he : k = (1256 : Fin 2425) := Fin.ext h1256
    subst k
    rw [sourceRowsAt1256]
    exact rowSound1256 B hB hF
  · have he : k = (1257 : Fin 2425) := Fin.ext h1257
    subst k
    rw [sourceRowsAt1257]
    exact rowSound1257 B hB hF
  · have he : k = (1258 : Fin 2425) := Fin.ext h1258
    subst k
    rw [sourceRowsAt1258]
    exact rowSound1258 B hB hF
  · have he : k = (1259 : Fin 2425) := Fin.ext h1259
    subst k
    rw [sourceRowsAt1259]
    exact rowSound1259 B hB hF
  · have he : k = (1260 : Fin 2425) := Fin.ext h1260
    subst k
    rw [sourceRowsAt1260]
    exact rowSound1260 B hB hF
  · have he : k = (1261 : Fin 2425) := Fin.ext h1261
    subst k
    rw [sourceRowsAt1261]
    exact rowSound1261_e B hB hF
  · have he : k = (1262 : Fin 2425) := Fin.ext h1262
    subst k
    rw [sourceRowsAt1262]
    exact rowSound1262_e B hB hF
  · have he : k = (1263 : Fin 2425) := Fin.ext h1263
    subst k
    rw [sourceRowsAt1263]
    exact rowSound1263 B hB hF

end MUB6.Certificate.MixedSourceBridge

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedSourceBridge.chunkSound78_e_oai := @OAI.MUB6.Certificate.MixedSourceBridge.chunkSound78_e_oai
