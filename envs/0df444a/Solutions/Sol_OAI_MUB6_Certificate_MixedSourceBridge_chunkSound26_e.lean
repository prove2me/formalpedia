-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedSourceBridge.chunkSound26_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T04:04:44.027461+00:00
-- url     : https://prove2.me/submissions/9bbbe643-163e-4aab-9065-72ce83dc5983

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E077
import Definitions.Def_OAIQ106E086
import Definitions.Def_OAIQ106E188
import Definitions.Def_OAIQ106E189
import Definitions.Def_OAIQ106E191
import Definitions.Def_OAIQ106E101
import Definitions.Def_OAIQ106E118
import Definitions.Def_OAIQ106E119
import Definitions.Def_OAIQ106E121
import Definitions.Def_OAIQ106E127
import Definitions.Def_OAIQ106E140
import Definitions.Def_OAIQ106E147
import Definitions.Def_OAIQ106E170
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound5485_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound417_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound418_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound419_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound427_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound428_e

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical17
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical2178 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2178 raw2178Labels = mixedMoment B node5152 node5152Labels := by
  calc
    mixedMoment B raw2178 raw2178Labels = mixedMoment B raw2178step0 raw2178step0Labels := by
      have ha : raw2178step0 = (fun i j => raw2178 (permutation32 i) (permutation5 j)) := by apply Matrix.ext; unfold raw2178step0 raw2178; decide +kernel
      have hl : raw2178step0Labels = raw2178Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2178 raw2178Labels permutation32 permutation5
    mixedMoment B raw2178step0 raw2178step0Labels = mixedMoment B raw2178step1 raw2178step1Labels := by
      have ha : raw2178step1 = raw2178step0 := by apply Matrix.ext; unfold raw2178step1 raw2178step0; decide +kernel
      have hl : raw2178step0Labels = labelEmbedding8 ∘ raw2178step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2178step0 raw2178step0Labels raw2178step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5152 node5152Labels := by rfl

theorem canonical2179 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2179 raw2179Labels = mixedMoment B node2931 node2931Labels := by
  calc
    mixedMoment B raw2179 raw2179Labels = mixedMoment B raw2179step0 raw2179step0Labels := by
      have ha : raw2179step0 = (fun i j => raw2179 (permutation33 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2179step0 raw2179; decide +kernel
      have hl : raw2179step0Labels = raw2179Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2179 raw2179Labels permutation33 permutation4
    _ = mixedMoment B node2931 node2931Labels := by rfl

theorem canonical2180 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2180 raw2180Labels = mixedMoment B node3612 node3612Labels := by
  calc
    mixedMoment B raw2180 raw2180Labels = mixedMoment B raw2180step0 raw2180step0Labels := by
      have ha : raw2180step0 = (fun i j => raw2180 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw2180step0 raw2180; decide +kernel
      have hl : raw2180step0Labels = raw2180Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2180 raw2180Labels permutation34 permutation3
    mixedMoment B raw2180step0 raw2180step0Labels = mixedMoment B raw2180step1 raw2180step1Labels := by
      have ha : raw2180step1 = -raw2180step0 := by apply Matrix.ext; change ∀ i j, raw2180step1 i j = -(raw2180step0 i j); unfold raw2180step1 raw2180step0; decide +kernel
      have hl : raw2180step1Labels = raw2180step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2180step1 raw2180step1Labels = mixedMoment B raw2180step2 raw2180step2Labels := by
      have ha : raw2180step2 = raw2180step1 := by apply Matrix.ext; unfold raw2180step2 raw2180step1; decide +kernel
      have hl : raw2180step1Labels = labelEmbedding1 ∘ raw2180step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2180step1 raw2180step1Labels raw2180step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3612 node3612Labels := by rfl

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

theorem canonical2550 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2550 raw2550Labels = mixedMoment B node5448 node5448Labels := by
  calc
    mixedMoment B raw2550 raw2550Labels = mixedMoment B raw2550step0 raw2550step0Labels := by
      have ha : raw2550step0 = (fun i j => raw2550 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2550step0 raw2550; decide +kernel
      have hl : raw2550step0Labels = raw2550Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2550 raw2550Labels permutation32 permutation4
    mixedMoment B raw2550step0 raw2550step0Labels = mixedMoment B raw2550step1 raw2550step1Labels := by
      have ha : raw2550step1 = raw2550step0 := by apply Matrix.ext; unfold raw2550step1 raw2550step0; decide +kernel
      have hl : raw2550step0Labels = labelEmbedding7 ∘ raw2550step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2550step0 raw2550step0Labels raw2550step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5448 node5448Labels := by rfl

theorem canonical2551 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2551 raw2551Labels = mixedMoment B node3885 node3885Labels := by
  calc
    mixedMoment B raw2551 raw2551Labels = mixedMoment B raw2551step0 raw2551step0Labels := by
      have ha : raw2551step0 = (fun i j => raw2551 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2551step0 raw2551; decide +kernel
      have hl : raw2551step0Labels = raw2551Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2551 raw2551Labels permutation32 permutation4
    _ = mixedMoment B node3885 node3885Labels := by rfl

theorem canonical2552 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2552 raw2552Labels = mixedMoment B node3885 node3885Labels := by
  calc
    mixedMoment B raw2552 raw2552Labels = mixedMoment B raw2552step0 raw2552step0Labels := by
      have ha : raw2552step0 = (fun i j => raw2552 (permutation38 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2552step0 raw2552; decide +kernel
      have hl : raw2552step0Labels = raw2552Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2552 raw2552Labels permutation38 permutation6
    mixedMoment B raw2552step0 raw2552step0Labels = mixedMoment B raw2552step1 raw2552step1Labels := by
      have ha : raw2552step1 = -raw2552step0 := by apply Matrix.ext; change ∀ i j, raw2552step1 i j = -(raw2552step0 i j); unfold raw2552step1 raw2552step0; decide +kernel
      have hl : raw2552step1Labels = raw2552step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2552step1 raw2552step1Labels = mixedMoment B raw2552step2 raw2552step2Labels := by
      have ha : raw2552step2 = raw2552step1 := by apply Matrix.ext; unfold raw2552step2 raw2552step1; decide +kernel
      have hl : raw2552step1Labels = labelEmbedding1 ∘ raw2552step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2552step1 raw2552step1Labels raw2552step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3885 node3885Labels := by rfl

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

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical68
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical8770 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8770 raw8770Labels = mixedMoment B node3054 node3054Labels := by
  calc
    mixedMoment B raw8770 raw8770Labels = mixedMoment B raw8770step0 raw8770step0Labels := by
      have hz : ∀ j, raw8770 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8770step0 = (fun i j => raw8770 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8770step0 raw8770; decide +kernel
      have hl : raw8770step0Labels = raw8770Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8770 raw8770Labels permutation346 hz
    mixedMoment B raw8770step0 raw8770step0Labels = mixedMoment B raw8770step1 raw8770step1Labels := by
      have hz : ∀ j, raw8770step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8770step1 = (fun i j => raw8770step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8770step1 raw8770step0; decide +kernel
      have hl : raw8770step1Labels = raw8770step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8770step0 raw8770step0Labels permutation56 hz
    _ = mixedMoment B node3054 node3054Labels := by rfl

theorem canonical8771 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8771 raw8771Labels = mixedMoment B node3813 node3813Labels := by
  calc
    mixedMoment B raw8771 raw8771Labels = mixedMoment B raw8771step0 raw8771step0Labels := by
      have hz : ∀ j, raw8771 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8771step0 = (fun i j => raw8771 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8771step0 raw8771; decide +kernel
      have hl : raw8771step0Labels = raw8771Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8771 raw8771Labels permutation346 hz
    mixedMoment B raw8771step0 raw8771step0Labels = mixedMoment B raw8771step1 raw8771step1Labels := by
      have ha : raw8771step1 = (fun i j => raw8771step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw8771step1 raw8771step0; decide +kernel
      have hl : raw8771step1Labels = raw8771step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8771step0 raw8771step0Labels permutation151 permutation2
    mixedMoment B raw8771step1 raw8771step1Labels = mixedMoment B raw8771step2 raw8771step2Labels := by
      have ha : raw8771step2 = -raw8771step1 := by apply Matrix.ext; change ∀ i j, raw8771step2 i j = -(raw8771step1 i j); unfold raw8771step2 raw8771step1; decide +kernel
      have hl : raw8771step2Labels = raw8771step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3813 node3813Labels := by rfl

theorem canonical8776 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8776 raw8776Labels = mixedMoment B node4092 node4092Labels := by
  calc
    mixedMoment B raw8776 raw8776Labels = mixedMoment B raw8776step0 raw8776step0Labels := by
      have hz : ∀ j, raw8776 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8776step0 = (fun i j => raw8776 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8776step0 raw8776; decide +kernel
      have hl : raw8776step0Labels = raw8776Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8776 raw8776Labels permutation346 hz
    mixedMoment B raw8776step0 raw8776step0Labels = mixedMoment B raw8776step1 raw8776step1Labels := by
      have hz : ∀ j, raw8776step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8776step1 = (fun i j => raw8776step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8776step1 raw8776step0; decide +kernel
      have hl : raw8776step1Labels = raw8776step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8776step0 raw8776step0Labels permutation56 hz
    mixedMoment B raw8776step1 raw8776step1Labels = mixedMoment B raw8776step2 raw8776step2Labels := by
      have ha : raw8776step2 = (fun i j => raw8776step1 (permutation14 i) (permutation0 j)) := by apply Matrix.ext; unfold raw8776step2 raw8776step1; decide +kernel
      have hl : raw8776step2Labels = raw8776step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8776step1 raw8776step1Labels permutation14 permutation0
    _ = mixedMoment B node4092 node4092Labels := by rfl

theorem canonical8782 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8782 raw8782Labels = mixedMoment B node2974 node2974Labels := by
  calc
    mixedMoment B raw8782 raw8782Labels = mixedMoment B raw8782step0 raw8782step0Labels := by
      have ha : raw8782step0 = (fun i j => raw8782 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw8782step0 raw8782; decide +kernel
      have hl : raw8782step0Labels = raw8782Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8782 raw8782Labels permutation158 permutation2
    _ = mixedMoment B node2974 node2974Labels := by rfl

theorem canonical8783 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8783 raw8783Labels = mixedMoment B node2759 node2759Labels := by
  calc
    mixedMoment B raw8783 raw8783Labels = mixedMoment B raw8783step0 raw8783step0Labels := by
      have hz : ∀ j, raw8783 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8783step0 = (fun i j => raw8783 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8783step0 raw8783; decide +kernel
      have hl : raw8783step0Labels = raw8783Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8783 raw8783Labels permutation346 hz
    mixedMoment B raw8783step0 raw8783step0Labels = mixedMoment B raw8783step1 raw8783step1Labels := by
      have ha : raw8783step1 = (fun i j => raw8783step0 (permutation97 i) (permutation4 j)) := by apply Matrix.ext; unfold raw8783step1 raw8783step0; decide +kernel
      have hl : raw8783step1Labels = raw8783step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8783step0 raw8783step0Labels permutation97 permutation4
    _ = mixedMoment B node2759 node2759Labels := by rfl

theorem canonical8784 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8784 raw8784Labels = mixedMoment B node2979 node2979Labels := by
  calc
    mixedMoment B raw8784 raw8784Labels = mixedMoment B raw8784step0 raw8784step0Labels := by
      have hz : ∀ j, raw8784 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8784step0 = (fun i j => raw8784 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8784step0 raw8784; decide +kernel
      have hl : raw8784step0Labels = raw8784Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8784 raw8784Labels permutation346 hz
    _ = mixedMoment B node2979 node2979Labels := by rfl

theorem canonical8785 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8785 raw8785Labels = mixedMoment B node2495 node2495Labels := by
  calc
    mixedMoment B raw8785 raw8785Labels = mixedMoment B raw8785step0 raw8785step0Labels := by
      have hz : ∀ j, raw8785 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8785step0 = (fun i j => raw8785 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8785step0 raw8785; decide +kernel
      have hl : raw8785step0Labels = raw8785Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8785 raw8785Labels permutation346 hz
    mixedMoment B raw8785step0 raw8785step0Labels = mixedMoment B raw8785step1 raw8785step1Labels := by
      have ha : raw8785step1 = (fun i j => raw8785step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw8785step1 raw8785step0; decide +kernel
      have hl : raw8785step1Labels = raw8785step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8785step0 raw8785step0Labels permutation151 permutation2
    mixedMoment B raw8785step1 raw8785step1Labels = mixedMoment B raw8785step2 raw8785step2Labels := by
      have ha : raw8785step2 = -raw8785step1 := by apply Matrix.ext; change ∀ i j, raw8785step2 i j = -(raw8785step1 i j); unfold raw8785step2 raw8785step1; decide +kernel
      have hl : raw8785step2Labels = raw8785step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2495 node2495Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical69
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical8892 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8892 raw8892Labels = mixedMoment B node2751 node2751Labels := by
  calc
    mixedMoment B raw8892 raw8892Labels = mixedMoment B raw8892step0 raw8892step0Labels := by
      have hz : ∀ j, raw8892 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8892step0 = (fun i j => raw8892 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8892step0 raw8892; decide +kernel
      have hl : raw8892step0Labels = raw8892Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8892 raw8892Labels permutation265 hz
    _ = mixedMoment B node2751 node2751Labels := by rfl

theorem canonical8893 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8893 raw8893Labels = mixedMoment B node3846 node3846Labels := by
  calc
    _ = mixedMoment B node3846 node3846Labels := by rfl

theorem canonical8894 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8894 raw8894Labels = mixedMoment B node3881 node3881Labels := by
  calc
    mixedMoment B raw8894 raw8894Labels = mixedMoment B raw8894step0 raw8894step0Labels := by
      have hz : ∀ j, raw8894 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8894step0 = (fun i j => raw8894 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8894step0 raw8894; decide +kernel
      have hl : raw8894step0Labels = raw8894Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8894 raw8894Labels permutation265 hz
    _ = mixedMoment B node3881 node3881Labels := by rfl

theorem canonical8895 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8895 raw8895Labels = mixedMoment B node3881 node3881Labels := by
  calc
    mixedMoment B raw8895 raw8895Labels = mixedMoment B raw8895step0 raw8895step0Labels := by
      have hz : ∀ j, raw8895 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8895step0 = (fun i j => raw8895 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8895step0 raw8895; decide +kernel
      have hl : raw8895step0Labels = raw8895Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8895 raw8895Labels permutation265 hz
    mixedMoment B raw8895step0 raw8895step0Labels = mixedMoment B raw8895step1 raw8895step1Labels := by
      have ha : raw8895step1 = (fun i j => raw8895step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw8895step1 raw8895step0; decide +kernel
      have hl : raw8895step1Labels = raw8895step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8895step0 raw8895step0Labels permutation38 permutation2
    _ = mixedMoment B node3881 node3881Labels := by rfl

theorem canonical8896 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8896 raw8896Labels = mixedMoment B node3902 node3902Labels := by
  calc
    mixedMoment B raw8896 raw8896Labels = mixedMoment B raw8896step0 raw8896step0Labels := by
      have hz : ∀ j, raw8896 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8896step0 = (fun i j => raw8896 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8896step0 raw8896; decide +kernel
      have hl : raw8896step0Labels = raw8896Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8896 raw8896Labels permutation265 hz
    mixedMoment B raw8896step0 raw8896step0Labels = mixedMoment B raw8896step1 raw8896step1Labels := by
      have ha : raw8896step1 = (fun i j => raw8896step0 (permutation44 i) (permutation2 j)) := by apply Matrix.ext; unfold raw8896step1 raw8896step0; decide +kernel
      have hl : raw8896step1Labels = raw8896step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8896step0 raw8896step0Labels permutation44 permutation2
    _ = mixedMoment B node3902 node3902Labels := by rfl

theorem canonical8897 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8897 raw8897Labels = mixedMoment B node3910 node3910Labels := by
  calc
    mixedMoment B raw8897 raw8897Labels = mixedMoment B raw8897step0 raw8897step0Labels := by
      have hz : ∀ j, raw8897 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8897step0 = (fun i j => raw8897 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8897step0 raw8897; decide +kernel
      have hl : raw8897step0Labels = raw8897Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8897 raw8897Labels permutation265 hz
    _ = mixedMoment B node3910 node3910Labels := by rfl

theorem canonical8898 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8898 raw8898Labels = mixedMoment B node4091 node4091Labels := by
  calc
    mixedMoment B raw8898 raw8898Labels = mixedMoment B raw8898step0 raw8898step0Labels := by
      have hz : ∀ j, raw8898 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8898step0 = (fun i j => raw8898 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8898step0 raw8898; decide +kernel
      have hl : raw8898step0Labels = raw8898Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8898 raw8898Labels permutation265 hz
    mixedMoment B raw8898step0 raw8898step0Labels = mixedMoment B raw8898step1 raw8898step1Labels := by
      have ha : raw8898step1 = (fun i j => raw8898step0 (permutation44 i) (permutation0 j)) := by apply Matrix.ext; unfold raw8898step1 raw8898step0; decide +kernel
      have hl : raw8898step1Labels = raw8898step0Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8898step0 raw8898step0Labels permutation44 permutation0
    _ = mixedMoment B node4091 node4091Labels := by rfl

theorem canonical8899 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8899 raw8899Labels = mixedMoment B node1247 node1247Labels := by
  calc
    mixedMoment B raw8899 raw8899Labels = mixedMoment B raw8899step0 raw8899step0Labels := by
      have ha : raw8899step0 = (fun i j => raw8899 (permutation184 i) (permutation2 j)) := by apply Matrix.ext; unfold raw8899step0 raw8899; decide +kernel
      have hl : raw8899step0Labels = raw8899Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8899 raw8899Labels permutation184 permutation2
    _ = mixedMoment B node1247 node1247Labels := by rfl

theorem canonical8900 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8900 raw8900Labels = mixedMoment B node1262 node1262Labels := by
  calc
    mixedMoment B raw8900 raw8900Labels = mixedMoment B raw8900step0 raw8900step0Labels := by
      have hz : ∀ j, raw8900 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8900step0 = (fun i j => raw8900 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8900step0 raw8900; decide +kernel
      have hl : raw8900step0Labels = raw8900Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8900 raw8900Labels permutation265 hz
    mixedMoment B raw8900step0 raw8900step0Labels = mixedMoment B raw8900step1 raw8900step1Labels := by
      have ha : raw8900step1 = (fun i j => raw8900step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw8900step1 raw8900step0; decide +kernel
      have hl : raw8900step1Labels = raw8900step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8900step0 raw8900step0Labels permutation40 permutation2
    _ = mixedMoment B node1262 node1262Labels := by rfl

theorem canonical8901 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8901 raw8901Labels = mixedMoment B node1262 node1262Labels := by
  calc
    mixedMoment B raw8901 raw8901Labels = mixedMoment B raw8901step0 raw8901step0Labels := by
      have hz : ∀ j, raw8901 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8901step0 = (fun i j => raw8901 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8901step0 raw8901; decide +kernel
      have hl : raw8901step0Labels = raw8901Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8901 raw8901Labels permutation265 hz
    mixedMoment B raw8901step0 raw8901step0Labels = mixedMoment B raw8901step1 raw8901step1Labels := by
      have ha : raw8901step1 = (fun i j => raw8901step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw8901step1 raw8901step0; decide +kernel
      have hl : raw8901step1Labels = raw8901step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8901step0 raw8901step0Labels permutation34 permutation2
    _ = mixedMoment B node1262 node1262Labels := by rfl

theorem canonical8902 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8902 raw8902Labels = mixedMoment B node1253 node1253Labels := by
  calc
    mixedMoment B raw8902 raw8902Labels = mixedMoment B raw8902step0 raw8902step0Labels := by
      have hz : ∀ j, raw8902 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8902step0 = (fun i j => raw8902 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8902step0 raw8902; decide +kernel
      have hl : raw8902step0Labels = raw8902Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8902 raw8902Labels permutation265 hz
    _ = mixedMoment B node1253 node1253Labels := by rfl

theorem canonical8903 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8903 raw8903Labels = mixedMoment B node1249 node1249Labels := by
  calc
    mixedMoment B raw8903 raw8903Labels = mixedMoment B raw8903step0 raw8903step0Labels := by
      have hz : ∀ j, raw8903 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8903step0 = (fun i j => raw8903 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8903step0 raw8903; decide +kernel
      have hl : raw8903step0Labels = raw8903Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8903 raw8903Labels permutation265 hz
    _ = mixedMoment B node1249 node1249Labels := by rfl

theorem canonical8904 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8904 raw8904Labels = mixedMoment B node2567 node2567Labels := by
  calc
    mixedMoment B raw8904 raw8904Labels = mixedMoment B raw8904step0 raw8904step0Labels := by
      have ha : raw8904step0 = (fun i j => raw8904 (permutation160 i) (permutation2 j)) := by apply Matrix.ext; unfold raw8904step0 raw8904; decide +kernel
      have hl : raw8904step0Labels = raw8904Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8904 raw8904Labels permutation160 permutation2
    _ = mixedMoment B node2567 node2567Labels := by rfl

theorem canonical8905 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8905 raw8905Labels = mixedMoment B node2567 node2567Labels := by
  calc
    mixedMoment B raw8905 raw8905Labels = mixedMoment B raw8905step0 raw8905step0Labels := by
      have ha : raw8905step0 = (fun i j => raw8905 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw8905step0 raw8905; decide +kernel
      have hl : raw8905step0Labels = raw8905Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8905 raw8905Labels permutation154 permutation2
    _ = mixedMoment B node2567 node2567Labels := by rfl

theorem canonical8906 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8906 raw8906Labels = mixedMoment B node2564 node2564Labels := by
  calc
    _ = mixedMoment B node2564 node2564Labels := by rfl

theorem canonical8907 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8907 raw8907Labels = mixedMoment B node2562 node2562Labels := by
  calc
    _ = mixedMoment B node2562 node2562Labels := by rfl

theorem canonical8908 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8908 raw8908Labels = mixedMoment B node2633 node2633Labels := by
  calc
    mixedMoment B raw8908 raw8908Labels = mixedMoment B raw8908step0 raw8908step0Labels := by
      have hz : ∀ j, raw8908 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8908step0 = (fun i j => raw8908 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8908step0 raw8908; decide +kernel
      have hl : raw8908step0Labels = raw8908Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8908 raw8908Labels permutation265 hz
    mixedMoment B raw8908step0 raw8908step0Labels = mixedMoment B raw8908step1 raw8908step1Labels := by
      have ha : raw8908step1 = (fun i j => raw8908step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw8908step1 raw8908step0; decide +kernel
      have hl : raw8908step1Labels = raw8908step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8908step0 raw8908step0Labels permutation40 permutation2
    _ = mixedMoment B node2633 node2633Labels := by rfl

theorem canonical8909 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8909 raw8909Labels = mixedMoment B node2723 node2723Labels := by
  calc
    mixedMoment B raw8909 raw8909Labels = mixedMoment B raw8909step0 raw8909step0Labels := by
      have hz : ∀ j, raw8909 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8909step0 = (fun i j => raw8909 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8909step0 raw8909; decide +kernel
      have hl : raw8909step0Labels = raw8909Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8909 raw8909Labels permutation265 hz
    mixedMoment B raw8909step0 raw8909step0Labels = mixedMoment B raw8909step1 raw8909step1Labels := by
      have ha : raw8909step1 = (fun i j => raw8909step0 (permutation46 i) (permutation2 j)) := by apply Matrix.ext; unfold raw8909step1 raw8909step0; decide +kernel
      have hl : raw8909step1Labels = raw8909step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8909step0 raw8909step0Labels permutation46 permutation2
    _ = mixedMoment B node2723 node2723Labels := by rfl

theorem canonical8910 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8910 raw8910Labels = mixedMoment B node2764 node2764Labels := by
  calc
    mixedMoment B raw8910 raw8910Labels = mixedMoment B raw8910step0 raw8910step0Labels := by
      have hz : ∀ j, raw8910 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8910step0 = (fun i j => raw8910 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8910step0 raw8910; decide +kernel
      have hl : raw8910step0Labels = raw8910Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8910 raw8910Labels permutation265 hz
    mixedMoment B raw8910step0 raw8910step0Labels = mixedMoment B raw8910step1 raw8910step1Labels := by
      have ha : raw8910step1 = (fun i j => raw8910step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw8910step1 raw8910step0; decide +kernel
      have hl : raw8910step1Labels = raw8910step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8910step0 raw8910step0Labels permutation40 permutation2
    _ = mixedMoment B node2764 node2764Labels := by rfl

theorem canonical8911 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8911 raw8911Labels = mixedMoment B node2622 node2622Labels := by
  calc
    mixedMoment B raw8911 raw8911Labels = mixedMoment B raw8911step0 raw8911step0Labels := by
      have ha : raw8911step0 = (fun i j => raw8911 (permutation184 i) (permutation2 j)) := by apply Matrix.ext; unfold raw8911step0 raw8911; decide +kernel
      have hl : raw8911step0Labels = raw8911Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8911 raw8911Labels permutation184 permutation2
    _ = mixedMoment B node2622 node2622Labels := by rfl

theorem canonical8912 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8912 raw8912Labels = mixedMoment B node2633 node2633Labels := by
  calc
    mixedMoment B raw8912 raw8912Labels = mixedMoment B raw8912step0 raw8912step0Labels := by
      have hz : ∀ j, raw8912 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8912step0 = (fun i j => raw8912 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8912step0 raw8912; decide +kernel
      have hl : raw8912step0Labels = raw8912Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8912 raw8912Labels permutation265 hz
    mixedMoment B raw8912step0 raw8912step0Labels = mixedMoment B raw8912step1 raw8912step1Labels := by
      have ha : raw8912step1 = (fun i j => raw8912step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw8912step1 raw8912step0; decide +kernel
      have hl : raw8912step1Labels = raw8912step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8912step0 raw8912step0Labels permutation34 permutation2
    _ = mixedMoment B node2633 node2633Labels := by rfl

theorem canonical8913 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8913 raw8913Labels = mixedMoment B node2627 node2627Labels := by
  calc
    mixedMoment B raw8913 raw8913Labels = mixedMoment B raw8913step0 raw8913step0Labels := by
      have hz : ∀ j, raw8913 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8913step0 = (fun i j => raw8913 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8913step0 raw8913; decide +kernel
      have hl : raw8913step0Labels = raw8913Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8913 raw8913Labels permutation265 hz
    _ = mixedMoment B node2627 node2627Labels := by rfl

theorem canonical8914 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8914 raw8914Labels = mixedMoment B node2624 node2624Labels := by
  calc
    mixedMoment B raw8914 raw8914Labels = mixedMoment B raw8914step0 raw8914step0Labels := by
      have hz : ∀ j, raw8914 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8914step0 = (fun i j => raw8914 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8914step0 raw8914; decide +kernel
      have hl : raw8914step0Labels = raw8914Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8914 raw8914Labels permutation265 hz
    _ = mixedMoment B node2624 node2624Labels := by rfl

theorem canonical8915 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8915 raw8915Labels = mixedMoment B node2627 node2627Labels := by
  calc
    mixedMoment B raw8915 raw8915Labels = mixedMoment B raw8915step0 raw8915step0Labels := by
      have hz : ∀ j, raw8915 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8915step0 = (fun i j => raw8915 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8915step0 raw8915; decide +kernel
      have hl : raw8915step0Labels = raw8915Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8915 raw8915Labels permutation265 hz
    mixedMoment B raw8915step0 raw8915step0Labels = mixedMoment B raw8915step1 raw8915step1Labels := by
      have ha : raw8915step1 = (fun i j => raw8915step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw8915step1 raw8915step0; decide +kernel
      have hl : raw8915step1Labels = raw8915step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8915step0 raw8915step0Labels permutation38 permutation2
    _ = mixedMoment B node2627 node2627Labels := by rfl

theorem canonical8916 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8916 raw8916Labels = mixedMoment B node2754 node2754Labels := by
  calc
    mixedMoment B raw8916 raw8916Labels = mixedMoment B raw8916step0 raw8916step0Labels := by
      have hz : ∀ j, raw8916 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8916step0 = (fun i j => raw8916 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8916step0 raw8916; decide +kernel
      have hl : raw8916step0Labels = raw8916Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8916 raw8916Labels permutation265 hz
    mixedMoment B raw8916step0 raw8916step0Labels = mixedMoment B raw8916step1 raw8916step1Labels := by
      have ha : raw8916step1 = (fun i j => raw8916step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw8916step1 raw8916step0; decide +kernel
      have hl : raw8916step1Labels = raw8916step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8916step0 raw8916step0Labels permutation33 permutation2
    _ = mixedMoment B node2754 node2754Labels := by rfl

theorem canonical8917 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8917 raw8917Labels = mixedMoment B node5471 node5471Labels := by
  calc
    mixedMoment B raw8917 raw8917Labels = mixedMoment B raw8917step0 raw8917step0Labels := by
      have ha : raw8917step0 = (fun i j => raw8917 (permutation682 i) (permutation2 j)) := by apply Matrix.ext; unfold raw8917step0 raw8917; decide +kernel
      have hl : raw8917step0Labels = raw8917Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8917 raw8917Labels permutation682 permutation2
    mixedMoment B raw8917step0 raw8917step0Labels = mixedMoment B raw8917step1 raw8917step1Labels := by
      have ha : raw8917step1 = -raw8917step0 := by apply Matrix.ext; change ∀ i j, raw8917step1 i j = -(raw8917step0 i j); unfold raw8917step1 raw8917step0; decide +kernel
      have hl : raw8917step1Labels = raw8917step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5471 node5471Labels := by rfl

theorem canonical8918 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8918 raw8918Labels = mixedMoment B node5473 node5473Labels := by
  calc
    mixedMoment B raw8918 raw8918Labels = mixedMoment B raw8918step0 raw8918step0Labels := by
      have hz : ∀ j, raw8918 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8918step0 = (fun i j => raw8918 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8918step0 raw8918; decide +kernel
      have hl : raw8918step0Labels = raw8918Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8918 raw8918Labels permutation265 hz
    mixedMoment B raw8918step0 raw8918step0Labels = mixedMoment B raw8918step1 raw8918step1Labels := by
      have ha : raw8918step1 = (fun i j => raw8918step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw8918step1 raw8918step0; decide +kernel
      have hl : raw8918step1Labels = raw8918step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8918step0 raw8918step0Labels permutation151 permutation2
    mixedMoment B raw8918step1 raw8918step1Labels = mixedMoment B raw8918step2 raw8918step2Labels := by
      have ha : raw8918step2 = -raw8918step1 := by apply Matrix.ext; change ∀ i j, raw8918step2 i j = -(raw8918step1 i j); unfold raw8918step2 raw8918step1; decide +kernel
      have hl : raw8918step2Labels = raw8918step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5473 node5473Labels := by rfl

theorem canonical8919 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8919 raw8919Labels = mixedMoment B node5473 node5473Labels := by
  calc
    mixedMoment B raw8919 raw8919Labels = mixedMoment B raw8919step0 raw8919step0Labels := by
      have hz : ∀ j, raw8919 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8919step0 = (fun i j => raw8919 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8919step0 raw8919; decide +kernel
      have hl : raw8919step0Labels = raw8919Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8919 raw8919Labels permutation265 hz
    mixedMoment B raw8919step0 raw8919step0Labels = mixedMoment B raw8919step1 raw8919step1Labels := by
      have ha : raw8919step1 = (fun i j => raw8919step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw8919step1 raw8919step0; decide +kernel
      have hl : raw8919step1Labels = raw8919step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8919step0 raw8919step0Labels permutation149 permutation2
    mixedMoment B raw8919step1 raw8919step1Labels = mixedMoment B raw8919step2 raw8919step2Labels := by
      have ha : raw8919step2 = -raw8919step1 := by apply Matrix.ext; change ∀ i j, raw8919step2 i j = -(raw8919step1 i j); unfold raw8919step2 raw8919step1; decide +kernel
      have hl : raw8919step2Labels = raw8919step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5473 node5473Labels := by rfl

theorem canonical8920 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8920 raw8920Labels = mixedMoment B node5448 node5448Labels := by
  calc
    mixedMoment B raw8920 raw8920Labels = mixedMoment B raw8920step0 raw8920step0Labels := by
      have hz : ∀ j, raw8920 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8920step0 = (fun i j => raw8920 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8920step0 raw8920; decide +kernel
      have hl : raw8920step0Labels = raw8920Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8920 raw8920Labels permutation265 hz
    mixedMoment B raw8920step0 raw8920step0Labels = mixedMoment B raw8920step1 raw8920step1Labels := by
      have ha : raw8920step1 = (fun i j => raw8920step0 (permutation108 i) (permutation4 j)) := by apply Matrix.ext; unfold raw8920step1 raw8920step0; decide +kernel
      have hl : raw8920step1Labels = raw8920step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8920step0 raw8920step0Labels permutation108 permutation4
    mixedMoment B raw8920step1 raw8920step1Labels = mixedMoment B raw8920step2 raw8920step2Labels := by
      have ha : raw8920step2 = -raw8920step1 := by apply Matrix.ext; change ∀ i j, raw8920step2 i j = -(raw8920step1 i j); unfold raw8920step2 raw8920step1; decide +kernel
      have hl : raw8920step2Labels = raw8920step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw8920step2 raw8920step2Labels = mixedMoment B raw8920step3 raw8920step3Labels := by
      have ha : raw8920step3 = raw8920step2 := by apply Matrix.ext; unfold raw8920step3 raw8920step2; decide +kernel
      have hl : raw8920step2Labels = labelEmbedding7 ∘ raw8920step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8920step2 raw8920step2Labels raw8920step3Labels labelEmbedding7 hl
    _ = mixedMoment B node5448 node5448Labels := by rfl

theorem canonical8921 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8921 raw8921Labels = mixedMoment B node5485 node5485Labels := by
  calc
    mixedMoment B raw8921 raw8921Labels = mixedMoment B raw8921step0 raw8921step0Labels := by
      have hz : ∀ j, raw8921 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8921step0 = (fun i j => raw8921 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8921step0 raw8921; decide +kernel
      have hl : raw8921step0Labels = raw8921Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8921 raw8921Labels permutation265 hz
    mixedMoment B raw8921step0 raw8921step0Labels = mixedMoment B raw8921step1 raw8921step1Labels := by
      have ha : raw8921step1 = (fun i j => raw8921step0 (permutation125 i) (permutation7 j)) := by apply Matrix.ext; unfold raw8921step1 raw8921step0; decide +kernel
      have hl : raw8921step1Labels = raw8921step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8921step0 raw8921step0Labels permutation125 permutation7
    mixedMoment B raw8921step1 raw8921step1Labels = mixedMoment B raw8921step2 raw8921step2Labels := by
      have ha : raw8921step2 = raw8921step1 := by apply Matrix.ext; unfold raw8921step2 raw8921step1; decide +kernel
      have hl : raw8921step1Labels = labelEmbedding10 ∘ raw8921step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8921step1 raw8921step1Labels raw8921step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5485 node5485Labels := by rfl

theorem canonical8922 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8922 raw8922Labels = mixedMoment B node4436 node4436Labels := by
  calc
    mixedMoment B raw8922 raw8922Labels = mixedMoment B raw8922step0 raw8922step0Labels := by
      have ha : raw8922step0 = (fun i j => raw8922 (permutation184 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8922step0 raw8922; decide +kernel
      have hl : raw8922step0Labels = raw8922Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8922 raw8922Labels permutation184 permutation3
    mixedMoment B raw8922step0 raw8922step0Labels = mixedMoment B raw8922step1 raw8922step1Labels := by
      have ha : raw8922step1 = raw8922step0 := by apply Matrix.ext; unfold raw8922step1 raw8922step0; decide +kernel
      have hl : raw8922step0Labels = labelEmbedding6 ∘ raw8922step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8922step0 raw8922step0Labels raw8922step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4436 node4436Labels := by rfl

theorem canonical8923 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8923 raw8923Labels = mixedMoment B node5145 node5145Labels := by
  calc
    mixedMoment B raw8923 raw8923Labels = mixedMoment B raw8923step0 raw8923step0Labels := by
      have ha : raw8923step0 = (fun i j => raw8923 (permutation184 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8923step0 raw8923; decide +kernel
      have hl : raw8923step0Labels = raw8923Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8923 raw8923Labels permutation184 permutation3
    mixedMoment B raw8923step0 raw8923step0Labels = mixedMoment B raw8923step1 raw8923step1Labels := by
      have ha : raw8923step1 = raw8923step0 := by apply Matrix.ext; unfold raw8923step1 raw8923step0; decide +kernel
      have hl : raw8923step0Labels = labelEmbedding6 ∘ raw8923step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8923step0 raw8923step0Labels raw8923step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5145 node5145Labels := by rfl

theorem canonical8924 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8924 raw8924Labels = mixedMoment B node5145 node5145Labels := by
  calc
    mixedMoment B raw8924 raw8924Labels = mixedMoment B raw8924step0 raw8924step0Labels := by
      have ha : raw8924step0 = (fun i j => raw8924 (permutation208 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8924step0 raw8924; decide +kernel
      have hl : raw8924step0Labels = raw8924Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8924 raw8924Labels permutation208 permutation3
    mixedMoment B raw8924step0 raw8924step0Labels = mixedMoment B raw8924step1 raw8924step1Labels := by
      have ha : raw8924step1 = raw8924step0 := by apply Matrix.ext; unfold raw8924step1 raw8924step0; decide +kernel
      have hl : raw8924step0Labels = labelEmbedding6 ∘ raw8924step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8924step0 raw8924step0Labels raw8924step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5145 node5145Labels := by rfl

theorem canonical8925 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8925 raw8925Labels = mixedMoment B node5220 node5220Labels := by
  calc
    mixedMoment B raw8925 raw8925Labels = mixedMoment B raw8925step0 raw8925step0Labels := by
      have ha : raw8925step0 = (fun i j => raw8925 (permutation232 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8925step0 raw8925; decide +kernel
      have hl : raw8925step0Labels = raw8925Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8925 raw8925Labels permutation232 permutation3
    mixedMoment B raw8925step0 raw8925step0Labels = mixedMoment B raw8925step1 raw8925step1Labels := by
      have ha : raw8925step1 = raw8925step0 := by apply Matrix.ext; unfold raw8925step1 raw8925step0; decide +kernel
      have hl : raw8925step0Labels = labelEmbedding6 ∘ raw8925step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8925step0 raw8925step0Labels raw8925step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5220 node5220Labels := by rfl

theorem canonical8926 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8926 raw8926Labels = mixedMoment B node5281 node5281Labels := by
  calc
    mixedMoment B raw8926 raw8926Labels = mixedMoment B raw8926step0 raw8926step0Labels := by
      have ha : raw8926step0 = (fun i j => raw8926 (permutation185 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8926step0 raw8926; decide +kernel
      have hl : raw8926step0Labels = raw8926Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8926 raw8926Labels permutation185 permutation3
    mixedMoment B raw8926step0 raw8926step0Labels = mixedMoment B raw8926step1 raw8926step1Labels := by
      have ha : raw8926step1 = raw8926step0 := by apply Matrix.ext; unfold raw8926step1 raw8926step0; decide +kernel
      have hl : raw8926step0Labels = labelEmbedding6 ∘ raw8926step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8926step0 raw8926step0Labels raw8926step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5281 node5281Labels := by rfl

theorem canonical8927 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8927 raw8927Labels = mixedMoment B node4453 node4453Labels := by
  calc
    mixedMoment B raw8927 raw8927Labels = mixedMoment B raw8927step0 raw8927step0Labels := by
      have hz : ∀ j, raw8927 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8927step0 = (fun i j => raw8927 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8927step0 raw8927; decide +kernel
      have hl : raw8927step0Labels = raw8927Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8927 raw8927Labels permutation265 hz
    mixedMoment B raw8927step0 raw8927step0Labels = mixedMoment B raw8927step1 raw8927step1Labels := by
      have ha : raw8927step1 = (fun i j => raw8927step0 (permutation40 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8927step1 raw8927step0; decide +kernel
      have hl : raw8927step1Labels = raw8927step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8927step0 raw8927step0Labels permutation40 permutation3
    mixedMoment B raw8927step1 raw8927step1Labels = mixedMoment B raw8927step2 raw8927step2Labels := by
      have ha : raw8927step2 = raw8927step1 := by apply Matrix.ext; unfold raw8927step2 raw8927step1; decide +kernel
      have hl : raw8927step1Labels = labelEmbedding6 ∘ raw8927step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8927step1 raw8927step1Labels raw8927step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4453 node4453Labels := by rfl

theorem canonical8928 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8928 raw8928Labels = mixedMoment B node5071 node5071Labels := by
  calc
    mixedMoment B raw8928 raw8928Labels = mixedMoment B raw8928step0 raw8928step0Labels := by
      have ha : raw8928step0 = (fun i j => raw8928 (permutation160 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8928step0 raw8928; decide +kernel
      have hl : raw8928step0Labels = raw8928Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8928 raw8928Labels permutation160 permutation3
    mixedMoment B raw8928step0 raw8928step0Labels = mixedMoment B raw8928step1 raw8928step1Labels := by
      have ha : raw8928step1 = raw8928step0 := by apply Matrix.ext; unfold raw8928step1 raw8928step0; decide +kernel
      have hl : raw8928step0Labels = labelEmbedding6 ∘ raw8928step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8928step0 raw8928step0Labels raw8928step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5071 node5071Labels := by rfl

theorem canonical8929 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8929 raw8929Labels = mixedMoment B node5164 node5164Labels := by
  calc
    mixedMoment B raw8929 raw8929Labels = mixedMoment B raw8929step0 raw8929step0Labels := by
      have hz : ∀ j, raw8929 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8929step0 = (fun i j => raw8929 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8929step0 raw8929; decide +kernel
      have hl : raw8929step0Labels = raw8929Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8929 raw8929Labels permutation265 hz
    mixedMoment B raw8929step0 raw8929step0Labels = mixedMoment B raw8929step1 raw8929step1Labels := by
      have ha : raw8929step1 = (fun i j => raw8929step0 (permutation40 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8929step1 raw8929step0; decide +kernel
      have hl : raw8929step1Labels = raw8929step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8929step0 raw8929step0Labels permutation40 permutation3
    mixedMoment B raw8929step1 raw8929step1Labels = mixedMoment B raw8929step2 raw8929step2Labels := by
      have ha : raw8929step2 = raw8929step1 := by apply Matrix.ext; unfold raw8929step2 raw8929step1; decide +kernel
      have hl : raw8929step1Labels = labelEmbedding6 ∘ raw8929step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8929step1 raw8929step1Labels raw8929step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5164 node5164Labels := by rfl

theorem canonical8930 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8930 raw8930Labels = mixedMoment B node5229 node5229Labels := by
  calc
    mixedMoment B raw8930 raw8930Labels = mixedMoment B raw8930step0 raw8930step0Labels := by
      have hz : ∀ j, raw8930 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8930step0 = (fun i j => raw8930 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8930step0 raw8930; decide +kernel
      have hl : raw8930step0Labels = raw8930Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8930 raw8930Labels permutation265 hz
    mixedMoment B raw8930step0 raw8930step0Labels = mixedMoment B raw8930step1 raw8930step1Labels := by
      have ha : raw8930step1 = (fun i j => raw8930step0 (permutation46 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8930step1 raw8930step0; decide +kernel
      have hl : raw8930step1Labels = raw8930step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8930step0 raw8930step0Labels permutation46 permutation3
    mixedMoment B raw8930step1 raw8930step1Labels = mixedMoment B raw8930step2 raw8930step2Labels := by
      have ha : raw8930step2 = raw8930step1 := by apply Matrix.ext; unfold raw8930step2 raw8930step1; decide +kernel
      have hl : raw8930step1Labels = labelEmbedding6 ∘ raw8930step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8930step1 raw8930step1Labels raw8930step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5229 node5229Labels := by rfl

theorem canonical8931 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8931 raw8931Labels = mixedMoment B node5289 node5289Labels := by
  calc
    mixedMoment B raw8931 raw8931Labels = mixedMoment B raw8931step0 raw8931step0Labels := by
      have hz : ∀ j, raw8931 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8931step0 = (fun i j => raw8931 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8931step0 raw8931; decide +kernel
      have hl : raw8931step0Labels = raw8931Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8931 raw8931Labels permutation265 hz
    mixedMoment B raw8931step0 raw8931step0Labels = mixedMoment B raw8931step1 raw8931step1Labels := by
      have ha : raw8931step1 = (fun i j => raw8931step0 (permutation41 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8931step1 raw8931step0; decide +kernel
      have hl : raw8931step1Labels = raw8931step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8931step0 raw8931step0Labels permutation41 permutation3
    mixedMoment B raw8931step1 raw8931step1Labels = mixedMoment B raw8931step2 raw8931step2Labels := by
      have ha : raw8931step2 = raw8931step1 := by apply Matrix.ext; unfold raw8931step2 raw8931step1; decide +kernel
      have hl : raw8931step1Labels = labelEmbedding6 ∘ raw8931step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8931step1 raw8931step1Labels raw8931step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5289 node5289Labels := by rfl

theorem canonical8932 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8932 raw8932Labels = mixedMoment B node4453 node4453Labels := by
  calc
    mixedMoment B raw8932 raw8932Labels = mixedMoment B raw8932step0 raw8932step0Labels := by
      have hz : ∀ j, raw8932 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8932step0 = (fun i j => raw8932 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8932step0 raw8932; decide +kernel
      have hl : raw8932step0Labels = raw8932Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8932 raw8932Labels permutation265 hz
    mixedMoment B raw8932step0 raw8932step0Labels = mixedMoment B raw8932step1 raw8932step1Labels := by
      have ha : raw8932step1 = (fun i j => raw8932step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8932step1 raw8932step0; decide +kernel
      have hl : raw8932step1Labels = raw8932step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8932step0 raw8932step0Labels permutation34 permutation3
    mixedMoment B raw8932step1 raw8932step1Labels = mixedMoment B raw8932step2 raw8932step2Labels := by
      have ha : raw8932step2 = raw8932step1 := by apply Matrix.ext; unfold raw8932step2 raw8932step1; decide +kernel
      have hl : raw8932step1Labels = labelEmbedding6 ∘ raw8932step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8932step1 raw8932step1Labels raw8932step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4453 node4453Labels := by rfl

theorem canonical8933 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8933 raw8933Labels = mixedMoment B node5071 node5071Labels := by
  calc
    mixedMoment B raw8933 raw8933Labels = mixedMoment B raw8933step0 raw8933step0Labels := by
      have ha : raw8933step0 = (fun i j => raw8933 (permutation154 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8933step0 raw8933; decide +kernel
      have hl : raw8933step0Labels = raw8933Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8933 raw8933Labels permutation154 permutation3
    mixedMoment B raw8933step0 raw8933step0Labels = mixedMoment B raw8933step1 raw8933step1Labels := by
      have ha : raw8933step1 = raw8933step0 := by apply Matrix.ext; unfold raw8933step1 raw8933step0; decide +kernel
      have hl : raw8933step0Labels = labelEmbedding6 ∘ raw8933step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8933step0 raw8933step0Labels raw8933step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5071 node5071Labels := by rfl

theorem canonical8934 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8934 raw8934Labels = mixedMoment B node5164 node5164Labels := by
  calc
    mixedMoment B raw8934 raw8934Labels = mixedMoment B raw8934step0 raw8934step0Labels := by
      have hz : ∀ j, raw8934 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8934step0 = (fun i j => raw8934 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8934step0 raw8934; decide +kernel
      have hl : raw8934step0Labels = raw8934Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8934 raw8934Labels permutation265 hz
    mixedMoment B raw8934step0 raw8934step0Labels = mixedMoment B raw8934step1 raw8934step1Labels := by
      have ha : raw8934step1 = (fun i j => raw8934step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8934step1 raw8934step0; decide +kernel
      have hl : raw8934step1Labels = raw8934step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8934step0 raw8934step0Labels permutation34 permutation3
    mixedMoment B raw8934step1 raw8934step1Labels = mixedMoment B raw8934step2 raw8934step2Labels := by
      have ha : raw8934step2 = raw8934step1 := by apply Matrix.ext; unfold raw8934step2 raw8934step1; decide +kernel
      have hl : raw8934step1Labels = labelEmbedding6 ∘ raw8934step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8934step1 raw8934step1Labels raw8934step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5164 node5164Labels := by rfl

theorem canonical8935 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8935 raw8935Labels = mixedMoment B node5229 node5229Labels := by
  calc
    mixedMoment B raw8935 raw8935Labels = mixedMoment B raw8935step0 raw8935step0Labels := by
      have hz : ∀ j, raw8935 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8935step0 = (fun i j => raw8935 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8935step0 raw8935; decide +kernel
      have hl : raw8935step0Labels = raw8935Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8935 raw8935Labels permutation265 hz
    mixedMoment B raw8935step0 raw8935step0Labels = mixedMoment B raw8935step1 raw8935step1Labels := by
      have ha : raw8935step1 = (fun i j => raw8935step0 (permutation44 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8935step1 raw8935step0; decide +kernel
      have hl : raw8935step1Labels = raw8935step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8935step0 raw8935step0Labels permutation44 permutation3
    mixedMoment B raw8935step1 raw8935step1Labels = mixedMoment B raw8935step2 raw8935step2Labels := by
      have ha : raw8935step2 = raw8935step1 := by apply Matrix.ext; unfold raw8935step2 raw8935step1; decide +kernel
      have hl : raw8935step1Labels = labelEmbedding6 ∘ raw8935step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8935step1 raw8935step1Labels raw8935step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5229 node5229Labels := by rfl

theorem canonical8936 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8936 raw8936Labels = mixedMoment B node5289 node5289Labels := by
  calc
    mixedMoment B raw8936 raw8936Labels = mixedMoment B raw8936step0 raw8936step0Labels := by
      have hz : ∀ j, raw8936 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8936step0 = (fun i j => raw8936 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8936step0 raw8936; decide +kernel
      have hl : raw8936step0Labels = raw8936Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8936 raw8936Labels permutation265 hz
    mixedMoment B raw8936step0 raw8936step0Labels = mixedMoment B raw8936step1 raw8936step1Labels := by
      have ha : raw8936step1 = (fun i j => raw8936step0 (permutation35 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8936step1 raw8936step0; decide +kernel
      have hl : raw8936step1Labels = raw8936step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8936step0 raw8936step0Labels permutation35 permutation3
    mixedMoment B raw8936step1 raw8936step1Labels = mixedMoment B raw8936step2 raw8936step2Labels := by
      have ha : raw8936step2 = raw8936step1 := by apply Matrix.ext; unfold raw8936step2 raw8936step1; decide +kernel
      have hl : raw8936step1Labels = labelEmbedding6 ∘ raw8936step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8936step1 raw8936step1Labels raw8936step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5289 node5289Labels := by rfl

theorem canonical8937 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8937 raw8937Labels = mixedMoment B node4444 node4444Labels := by
  calc
    mixedMoment B raw8937 raw8937Labels = mixedMoment B raw8937step0 raw8937step0Labels := by
      have hz : ∀ j, raw8937 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8937step0 = (fun i j => raw8937 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8937step0 raw8937; decide +kernel
      have hl : raw8937step0Labels = raw8937Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8937 raw8937Labels permutation265 hz
    mixedMoment B raw8937step0 raw8937step0Labels = mixedMoment B raw8937step1 raw8937step1Labels := by
      have ha : raw8937step1 = (fun i j => raw8937step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8937step1 raw8937step0; decide +kernel
      have hl : raw8937step1Labels = raw8937step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8937step0 raw8937step0Labels permutation32 permutation3
    mixedMoment B raw8937step1 raw8937step1Labels = mixedMoment B raw8937step2 raw8937step2Labels := by
      have ha : raw8937step2 = raw8937step1 := by apply Matrix.ext; unfold raw8937step2 raw8937step1; decide +kernel
      have hl : raw8937step1Labels = labelEmbedding6 ∘ raw8937step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8937step1 raw8937step1Labels raw8937step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4444 node4444Labels := by rfl

theorem canonical8938 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8938 raw8938Labels = mixedMoment B node5067 node5067Labels := by
  calc
    mixedMoment B raw8938 raw8938Labels = mixedMoment B raw8938step0 raw8938step0Labels := by
      have ha : raw8938step0 = (fun i j => raw8938 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8938step0 raw8938; decide +kernel
      have hl : raw8938step0Labels = raw8938Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8938 raw8938Labels permutation152 permutation3
    mixedMoment B raw8938step0 raw8938step0Labels = mixedMoment B raw8938step1 raw8938step1Labels := by
      have ha : raw8938step1 = raw8938step0 := by apply Matrix.ext; unfold raw8938step1 raw8938step0; decide +kernel
      have hl : raw8938step0Labels = labelEmbedding6 ∘ raw8938step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8938step0 raw8938step0Labels raw8938step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5067 node5067Labels := by rfl

theorem canonical8939 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8939 raw8939Labels = mixedMoment B node5152 node5152Labels := by
  calc
    mixedMoment B raw8939 raw8939Labels = mixedMoment B raw8939step0 raw8939step0Labels := by
      have hz : ∀ j, raw8939 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8939step0 = (fun i j => raw8939 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8939step0 raw8939; decide +kernel
      have hl : raw8939step0Labels = raw8939Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8939 raw8939Labels permutation265 hz
    mixedMoment B raw8939step0 raw8939step0Labels = mixedMoment B raw8939step1 raw8939step1Labels := by
      have ha : raw8939step1 = (fun i j => raw8939step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8939step1 raw8939step0; decide +kernel
      have hl : raw8939step1Labels = raw8939step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8939step0 raw8939step0Labels permutation32 permutation3
    mixedMoment B raw8939step1 raw8939step1Labels = mixedMoment B raw8939step2 raw8939step2Labels := by
      have ha : raw8939step2 = raw8939step1 := by apply Matrix.ext; unfold raw8939step2 raw8939step1; decide +kernel
      have hl : raw8939step1Labels = labelEmbedding6 ∘ raw8939step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8939step1 raw8939step1Labels raw8939step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5152 node5152Labels := by rfl

theorem canonical8940 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8940 raw8940Labels = mixedMoment B node5152 node5152Labels := by
  calc
    mixedMoment B raw8940 raw8940Labels = mixedMoment B raw8940step0 raw8940step0Labels := by
      have hz : ∀ j, raw8940 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8940step0 = (fun i j => raw8940 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8940step0 raw8940; decide +kernel
      have hl : raw8940step0Labels = raw8940Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8940 raw8940Labels permutation265 hz
    mixedMoment B raw8940step0 raw8940step0Labels = mixedMoment B raw8940step1 raw8940step1Labels := by
      have ha : raw8940step1 = (fun i j => raw8940step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8940step1 raw8940step0; decide +kernel
      have hl : raw8940step1Labels = raw8940step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8940step0 raw8940step0Labels permutation38 permutation3
    mixedMoment B raw8940step1 raw8940step1Labels = mixedMoment B raw8940step2 raw8940step2Labels := by
      have ha : raw8940step2 = raw8940step1 := by apply Matrix.ext; unfold raw8940step2 raw8940step1; decide +kernel
      have hl : raw8940step1Labels = labelEmbedding6 ∘ raw8940step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8940step1 raw8940step1Labels raw8940step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5152 node5152Labels := by rfl

theorem canonical8941 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8941 raw8941Labels = mixedMoment B node5284 node5284Labels := by
  calc
    mixedMoment B raw8941 raw8941Labels = mixedMoment B raw8941step0 raw8941step0Labels := by
      have hz : ∀ j, raw8941 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8941step0 = (fun i j => raw8941 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8941step0 raw8941; decide +kernel
      have hl : raw8941step0Labels = raw8941Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8941 raw8941Labels permutation265 hz
    mixedMoment B raw8941step0 raw8941step0Labels = mixedMoment B raw8941step1 raw8941step1Labels := by
      have ha : raw8941step1 = (fun i j => raw8941step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8941step1 raw8941step0; decide +kernel
      have hl : raw8941step1Labels = raw8941step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8941step0 raw8941step0Labels permutation33 permutation3
    mixedMoment B raw8941step1 raw8941step1Labels = mixedMoment B raw8941step2 raw8941step2Labels := by
      have ha : raw8941step2 = raw8941step1 := by apply Matrix.ext; unfold raw8941step2 raw8941step1; decide +kernel
      have hl : raw8941step1Labels = labelEmbedding6 ∘ raw8941step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8941step1 raw8941step1Labels raw8941step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5284 node5284Labels := by rfl

theorem canonical8942 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8942 raw8942Labels = mixedMoment B node4437 node4437Labels := by
  calc
    mixedMoment B raw8942 raw8942Labels = mixedMoment B raw8942step0 raw8942step0Labels := by
      have hz : ∀ j, raw8942 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8942step0 = (fun i j => raw8942 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8942step0 raw8942; decide +kernel
      have hl : raw8942step0Labels = raw8942Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8942 raw8942Labels permutation265 hz
    mixedMoment B raw8942step0 raw8942step0Labels = mixedMoment B raw8942step1 raw8942step1Labels := by
      have ha : raw8942step1 = (fun i j => raw8942step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8942step1 raw8942step0; decide +kernel
      have hl : raw8942step1Labels = raw8942step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8942step0 raw8942step0Labels permutation32 permutation3
    mixedMoment B raw8942step1 raw8942step1Labels = mixedMoment B raw8942step2 raw8942step2Labels := by
      have ha : raw8942step2 = raw8942step1 := by apply Matrix.ext; unfold raw8942step2 raw8942step1; decide +kernel
      have hl : raw8942step1Labels = labelEmbedding6 ∘ raw8942step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8942step1 raw8942step1Labels raw8942step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4437 node4437Labels := by rfl

theorem canonical8943 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8943 raw8943Labels = mixedMoment B node5064 node5064Labels := by
  calc
    mixedMoment B raw8943 raw8943Labels = mixedMoment B raw8943step0 raw8943step0Labels := by
      have ha : raw8943step0 = (fun i j => raw8943 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8943step0 raw8943; decide +kernel
      have hl : raw8943step0Labels = raw8943Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8943 raw8943Labels permutation152 permutation3
    mixedMoment B raw8943step0 raw8943step0Labels = mixedMoment B raw8943step1 raw8943step1Labels := by
      have ha : raw8943step1 = raw8943step0 := by apply Matrix.ext; unfold raw8943step1 raw8943step0; decide +kernel
      have hl : raw8943step0Labels = labelEmbedding6 ∘ raw8943step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8943step0 raw8943step0Labels raw8943step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5064 node5064Labels := by rfl

theorem canonical8944 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8944 raw8944Labels = mixedMoment B node5147 node5147Labels := by
  calc
    mixedMoment B raw8944 raw8944Labels = mixedMoment B raw8944step0 raw8944step0Labels := by
      have hz : ∀ j, raw8944 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8944step0 = (fun i j => raw8944 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8944step0 raw8944; decide +kernel
      have hl : raw8944step0Labels = raw8944Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8944 raw8944Labels permutation265 hz
    mixedMoment B raw8944step0 raw8944step0Labels = mixedMoment B raw8944step1 raw8944step1Labels := by
      have ha : raw8944step1 = (fun i j => raw8944step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8944step1 raw8944step0; decide +kernel
      have hl : raw8944step1Labels = raw8944step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8944step0 raw8944step0Labels permutation32 permutation3
    mixedMoment B raw8944step1 raw8944step1Labels = mixedMoment B raw8944step2 raw8944step2Labels := by
      have ha : raw8944step2 = raw8944step1 := by apply Matrix.ext; unfold raw8944step2 raw8944step1; decide +kernel
      have hl : raw8944step1Labels = labelEmbedding6 ∘ raw8944step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8944step1 raw8944step1Labels raw8944step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5147 node5147Labels := by rfl

theorem canonical8945 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8945 raw8945Labels = mixedMoment B node5147 node5147Labels := by
  calc
    mixedMoment B raw8945 raw8945Labels = mixedMoment B raw8945step0 raw8945step0Labels := by
      have hz : ∀ j, raw8945 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8945step0 = (fun i j => raw8945 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8945step0 raw8945; decide +kernel
      have hl : raw8945step0Labels = raw8945Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8945 raw8945Labels permutation265 hz
    mixedMoment B raw8945step0 raw8945step0Labels = mixedMoment B raw8945step1 raw8945step1Labels := by
      have ha : raw8945step1 = (fun i j => raw8945step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8945step1 raw8945step0; decide +kernel
      have hl : raw8945step1Labels = raw8945step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8945step0 raw8945step0Labels permutation38 permutation3
    mixedMoment B raw8945step1 raw8945step1Labels = mixedMoment B raw8945step2 raw8945step2Labels := by
      have ha : raw8945step2 = raw8945step1 := by apply Matrix.ext; unfold raw8945step2 raw8945step1; decide +kernel
      have hl : raw8945step1Labels = labelEmbedding6 ∘ raw8945step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8945step1 raw8945step1Labels raw8945step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5147 node5147Labels := by rfl

theorem canonical8946 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8946 raw8946Labels = mixedMoment B node5222 node5222Labels := by
  calc
    mixedMoment B raw8946 raw8946Labels = mixedMoment B raw8946step0 raw8946step0Labels := by
      have hz : ∀ j, raw8946 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8946step0 = (fun i j => raw8946 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8946step0 raw8946; decide +kernel
      have hl : raw8946step0Labels = raw8946Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8946 raw8946Labels permutation265 hz
    mixedMoment B raw8946step0 raw8946step0Labels = mixedMoment B raw8946step1 raw8946step1Labels := by
      have ha : raw8946step1 = (fun i j => raw8946step0 (permutation44 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8946step1 raw8946step0; decide +kernel
      have hl : raw8946step1Labels = raw8946step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8946step0 raw8946step0Labels permutation44 permutation3
    mixedMoment B raw8946step1 raw8946step1Labels = mixedMoment B raw8946step2 raw8946step2Labels := by
      have ha : raw8946step2 = raw8946step1 := by apply Matrix.ext; unfold raw8946step2 raw8946step1; decide +kernel
      have hl : raw8946step1Labels = labelEmbedding6 ∘ raw8946step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8946step1 raw8946step1Labels raw8946step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5222 node5222Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical70
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical9007 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9007 raw9007Labels = mixedMoment B node3078 node3078Labels := by
  calc
    mixedMoment B raw9007 raw9007Labels = mixedMoment B raw9007step0 raw9007step0Labels := by
      have hz : ∀ j, raw9007 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9007step0 = (fun i j => raw9007 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9007step0 raw9007; decide +kernel
      have hl : raw9007step0Labels = raw9007Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9007 raw9007Labels permutation265 hz
    _ = mixedMoment B node3078 node3078Labels := by rfl

theorem canonical9008 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9008 raw9008Labels = mixedMoment B node3953 node3953Labels := by
  calc
    mixedMoment B raw9008 raw9008Labels = mixedMoment B raw9008step0 raw9008step0Labels := by
      have ha : raw9008step0 = (fun i j => raw9008 (permutation682 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9008step0 raw9008; decide +kernel
      have hl : raw9008step0Labels = raw9008Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9008 raw9008Labels permutation682 permutation2
    mixedMoment B raw9008step0 raw9008step0Labels = mixedMoment B raw9008step1 raw9008step1Labels := by
      have ha : raw9008step1 = -raw9008step0 := by apply Matrix.ext; change ∀ i j, raw9008step1 i j = -(raw9008step0 i j); unfold raw9008step1 raw9008step0; decide +kernel
      have hl : raw9008step1Labels = raw9008step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3953 node3953Labels := by rfl

theorem canonical9009 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9009 raw9009Labels = mixedMoment B node3958 node3958Labels := by
  calc
    mixedMoment B raw9009 raw9009Labels = mixedMoment B raw9009step0 raw9009step0Labels := by
      have hz : ∀ j, raw9009 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9009step0 = (fun i j => raw9009 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9009step0 raw9009; decide +kernel
      have hl : raw9009step0Labels = raw9009Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9009 raw9009Labels permutation265 hz
    mixedMoment B raw9009step0 raw9009step0Labels = mixedMoment B raw9009step1 raw9009step1Labels := by
      have ha : raw9009step1 = (fun i j => raw9009step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9009step1 raw9009step0; decide +kernel
      have hl : raw9009step1Labels = raw9009step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9009step0 raw9009step0Labels permutation151 permutation2
    mixedMoment B raw9009step1 raw9009step1Labels = mixedMoment B raw9009step2 raw9009step2Labels := by
      have ha : raw9009step2 = -raw9009step1 := by apply Matrix.ext; change ∀ i j, raw9009step2 i j = -(raw9009step1 i j); unfold raw9009step2 raw9009step1; decide +kernel
      have hl : raw9009step2Labels = raw9009step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3958 node3958Labels := by rfl

theorem canonical9010 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9010 raw9010Labels = mixedMoment B node3958 node3958Labels := by
  calc
    mixedMoment B raw9010 raw9010Labels = mixedMoment B raw9010step0 raw9010step0Labels := by
      have hz : ∀ j, raw9010 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9010step0 = (fun i j => raw9010 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9010step0 raw9010; decide +kernel
      have hl : raw9010step0Labels = raw9010Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9010 raw9010Labels permutation265 hz
    mixedMoment B raw9010step0 raw9010step0Labels = mixedMoment B raw9010step1 raw9010step1Labels := by
      have ha : raw9010step1 = (fun i j => raw9010step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9010step1 raw9010step0; decide +kernel
      have hl : raw9010step1Labels = raw9010step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9010step0 raw9010step0Labels permutation149 permutation2
    mixedMoment B raw9010step1 raw9010step1Labels = mixedMoment B raw9010step2 raw9010step2Labels := by
      have ha : raw9010step2 = -raw9010step1 := by apply Matrix.ext; change ∀ i j, raw9010step2 i j = -(raw9010step1 i j); unfold raw9010step2 raw9010step1; decide +kernel
      have hl : raw9010step2Labels = raw9010step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3958 node3958Labels := by rfl

theorem canonical9011 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9011 raw9011Labels = mixedMoment B node3885 node3885Labels := by
  calc
    mixedMoment B raw9011 raw9011Labels = mixedMoment B raw9011step0 raw9011step0Labels := by
      have hz : ∀ j, raw9011 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9011step0 = (fun i j => raw9011 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9011step0 raw9011; decide +kernel
      have hl : raw9011step0Labels = raw9011Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9011 raw9011Labels permutation265 hz
    mixedMoment B raw9011step0 raw9011step0Labels = mixedMoment B raw9011step1 raw9011step1Labels := by
      have ha : raw9011step1 = (fun i j => raw9011step0 (permutation108 i) (permutation4 j)) := by apply Matrix.ext; unfold raw9011step1 raw9011step0; decide +kernel
      have hl : raw9011step1Labels = raw9011step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9011step0 raw9011step0Labels permutation108 permutation4
    mixedMoment B raw9011step1 raw9011step1Labels = mixedMoment B raw9011step2 raw9011step2Labels := by
      have ha : raw9011step2 = -raw9011step1 := by apply Matrix.ext; change ∀ i j, raw9011step2 i j = -(raw9011step1 i j); unfold raw9011step2 raw9011step1; decide +kernel
      have hl : raw9011step2Labels = raw9011step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3885 node3885Labels := by rfl

theorem canonical9012 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9012 raw9012Labels = mixedMoment B node4010 node4010Labels := by
  calc
    mixedMoment B raw9012 raw9012Labels = mixedMoment B raw9012step0 raw9012step0Labels := by
      have hz : ∀ j, raw9012 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9012step0 = (fun i j => raw9012 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9012step0 raw9012; decide +kernel
      have hl : raw9012step0Labels = raw9012Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9012 raw9012Labels permutation265 hz
    mixedMoment B raw9012step0 raw9012step0Labels = mixedMoment B raw9012step1 raw9012step1Labels := by
      have ha : raw9012step1 = (fun i j => raw9012step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9012step1 raw9012step0; decide +kernel
      have hl : raw9012step1Labels = raw9012step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9012step0 raw9012step0Labels permutation33 permutation2
    _ = mixedMoment B node4010 node4010Labels := by rfl

theorem canonical9013 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9013 raw9013Labels = mixedMoment B node4091 node4091Labels := by
  calc
    mixedMoment B raw9013 raw9013Labels = mixedMoment B raw9013step0 raw9013step0Labels := by
      have hz : ∀ j, raw9013 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9013step0 = (fun i j => raw9013 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9013step0 raw9013; decide +kernel
      have hl : raw9013step0Labels = raw9013Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9013 raw9013Labels permutation265 hz
    mixedMoment B raw9013step0 raw9013step0Labels = mixedMoment B raw9013step1 raw9013step1Labels := by
      have ha : raw9013step1 = (fun i j => raw9013step0 (permutation122 i) (permutation0 j)) := by apply Matrix.ext; unfold raw9013step1 raw9013step0; decide +kernel
      have hl : raw9013step1Labels = raw9013step0Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9013step0 raw9013step0Labels permutation122 permutation0
    mixedMoment B raw9013step1 raw9013step1Labels = mixedMoment B raw9013step2 raw9013step2Labels := by
      have ha : raw9013step2 = -raw9013step1 := by apply Matrix.ext; change ∀ i j, raw9013step2 i j = -(raw9013step1 i j); unfold raw9013step2 raw9013step1; decide +kernel
      have hl : raw9013step2Labels = raw9013step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4091 node4091Labels := by rfl

theorem canonical9014 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9014 raw9014Labels = mixedMoment B node1384 node1384Labels := by
  calc
    mixedMoment B raw9014 raw9014Labels = mixedMoment B raw9014step0 raw9014step0Labels := by
      have ha : raw9014step0 = (fun i j => raw9014 (permutation182 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9014step0 raw9014; decide +kernel
      have hl : raw9014step0Labels = raw9014Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9014 raw9014Labels permutation182 permutation2
    _ = mixedMoment B node1384 node1384Labels := by rfl

theorem canonical9015 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9015 raw9015Labels = mixedMoment B node1407 node1407Labels := by
  calc
    mixedMoment B raw9015 raw9015Labels = mixedMoment B raw9015step0 raw9015step0Labels := by
      have hz : ∀ j, raw9015 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9015step0 = (fun i j => raw9015 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9015step0 raw9015; decide +kernel
      have hl : raw9015step0Labels = raw9015Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9015 raw9015Labels permutation265 hz
    mixedMoment B raw9015step0 raw9015step0Labels = mixedMoment B raw9015step1 raw9015step1Labels := by
      have ha : raw9015step1 = (fun i j => raw9015step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9015step1 raw9015step0; decide +kernel
      have hl : raw9015step1Labels = raw9015step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9015step0 raw9015step0Labels permutation38 permutation2
    _ = mixedMoment B node1407 node1407Labels := by rfl

theorem canonical9016 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9016 raw9016Labels = mixedMoment B node1407 node1407Labels := by
  calc
    mixedMoment B raw9016 raw9016Labels = mixedMoment B raw9016step0 raw9016step0Labels := by
      have hz : ∀ j, raw9016 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9016step0 = (fun i j => raw9016 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9016step0 raw9016; decide +kernel
      have hl : raw9016step0Labels = raw9016Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9016 raw9016Labels permutation265 hz
    _ = mixedMoment B node1407 node1407Labels := by rfl

theorem canonical9017 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9017 raw9017Labels = mixedMoment B node1391 node1391Labels := by
  calc
    mixedMoment B raw9017 raw9017Labels = mixedMoment B raw9017step0 raw9017step0Labels := by
      have hz : ∀ j, raw9017 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9017step0 = (fun i j => raw9017 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9017step0 raw9017; decide +kernel
      have hl : raw9017step0Labels = raw9017Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9017 raw9017Labels permutation265 hz
    mixedMoment B raw9017step0 raw9017step0Labels = mixedMoment B raw9017step1 raw9017step1Labels := by
      have ha : raw9017step1 = (fun i j => raw9017step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9017step1 raw9017step0; decide +kernel
      have hl : raw9017step1Labels = raw9017step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9017step0 raw9017step0Labels permutation33 permutation2
    _ = mixedMoment B node1391 node1391Labels := by rfl

theorem canonical9018 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9018 raw9018Labels = mixedMoment B node1389 node1389Labels := by
  calc
    mixedMoment B raw9018 raw9018Labels = mixedMoment B raw9018step0 raw9018step0Labels := by
      have hz : ∀ j, raw9018 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9018step0 = (fun i j => raw9018 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9018step0 raw9018; decide +kernel
      have hl : raw9018step0Labels = raw9018Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9018 raw9018Labels permutation265 hz
    _ = mixedMoment B node1389 node1389Labels := by rfl

theorem canonical9019 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9019 raw9019Labels = mixedMoment B node2925 node2925Labels := by
  calc
    mixedMoment B raw9019 raw9019Labels = mixedMoment B raw9019step0 raw9019step0Labels := by
      have ha : raw9019step0 = (fun i j => raw9019 (permutation182 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9019step0 raw9019; decide +kernel
      have hl : raw9019step0Labels = raw9019Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9019 raw9019Labels permutation182 permutation2
    _ = mixedMoment B node2925 node2925Labels := by rfl

theorem canonical9020 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9020 raw9020Labels = mixedMoment B node2925 node2925Labels := by
  calc
    mixedMoment B raw9020 raw9020Labels = mixedMoment B raw9020step0 raw9020step0Labels := by
      have ha : raw9020step0 = (fun i j => raw9020 (permutation206 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9020step0 raw9020; decide +kernel
      have hl : raw9020step0Labels = raw9020Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9020 raw9020Labels permutation206 permutation2
    _ = mixedMoment B node2925 node2925Labels := by rfl

theorem canonical9021 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9021 raw9021Labels = mixedMoment B node3068 node3068Labels := by
  calc
    mixedMoment B raw9021 raw9021Labels = mixedMoment B raw9021step0 raw9021step0Labels := by
      have ha : raw9021step0 = (fun i j => raw9021 (permutation184 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9021step0 raw9021; decide +kernel
      have hl : raw9021step0Labels = raw9021Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9021 raw9021Labels permutation184 permutation2
    _ = mixedMoment B node3068 node3068Labels := by rfl

theorem canonical9022 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9022 raw9022Labels = mixedMoment B node3074 node3074Labels := by
  calc
    mixedMoment B raw9022 raw9022Labels = mixedMoment B raw9022step0 raw9022step0Labels := by
      have ha : raw9022step0 = (fun i j => raw9022 (permutation183 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9022step0 raw9022; decide +kernel
      have hl : raw9022step0Labels = raw9022Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9022 raw9022Labels permutation183 permutation2
    _ = mixedMoment B node3074 node3074Labels := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons80
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singleton5152 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5152 node5152Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2931 node2931Labels + mixedMoment B node3612 node3612Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2178 singletonSmall5152
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5152) = raw2178Labels := by decide +kernel
  rw [hl, canonical2178 B hB] at h
  have hc0 : mixedMoment B raw2178 (Fin.cases (0 : Fin 2) singletonSmall5152) =
      mixedMoment B node2931 node2931Labels := by
    have ha : raw2178 = raw2179 := by apply Matrix.ext; unfold raw2178 raw2179; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5152 = raw2179Labels := by decide +kernel
    rw [ha, hj, canonical2179 B hB]
  have hc1 : mixedMoment B raw2178 (Fin.cases (1 : Fin 2) singletonSmall5152) =
      mixedMoment B node3612 node3612Labels := by
    have ha : raw2178 = raw2180 := by apply Matrix.ext; unfold raw2178 raw2180; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5152 = raw2180Labels := by decide +kernel
    rw [ha, hj, canonical2180 B hB]
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons85
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singleton5448 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5448 node5448Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3885 node3885Labels + mixedMoment B node3885 node3885Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2550 singletonSmall5448
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5448) = raw2550Labels := by decide +kernel
  rw [hl, canonical2550 B hB] at h
  have hc0 : mixedMoment B raw2550 (Fin.cases (0 : Fin 2) singletonSmall5448) =
      mixedMoment B node3885 node3885Labels := by
    have ha : raw2550 = raw2551 := by apply Matrix.ext; unfold raw2550 raw2551; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5448 = raw2551Labels := by decide +kernel
    rw [ha, hj, canonical2551 B hB]
  have hc1 : mixedMoment B raw2550 (Fin.cases (1 : Fin 2) singletonSmall5448) =
      mixedMoment B node3885 node3885Labels := by
    have ha : raw2550 = raw2552 := by apply Matrix.ext; unfold raw2550 raw2552; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5448 = raw2552Labels := by decide +kernel
    rw [ha, hj, canonical2552 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

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

theorem zero5471 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node5471 node5471Labels = 0 := by
  exact mixedMoment_alpha B hF node5471 node5471Labels 1 permutation200
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

theorem sound3054 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3054 node3054Labels = Sparse.eval nodeValue3054 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3054) = mixedMoment B node3054 node3054Labels := rfl
  simpa [nodeValue3054, Sparse.eval] using hc.symm

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

theorem sound1247 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1247 node1247Labels = Sparse.eval nodeValue1247 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1247) = mixedMoment B node1247 node1247Labels := rfl
  simpa [nodeValue1247, Sparse.eval] using hc.symm

theorem sound1249 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1249 node1249Labels = Sparse.eval nodeValue1249 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1249) = mixedMoment B node1249 node1249Labels := rfl
  simpa [nodeValue1249, Sparse.eval] using hc.symm

theorem sound1253 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1253 node1253Labels = Sparse.eval nodeValue1253 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1253) = mixedMoment B node1253 node1253Labels := rfl
  simpa [nodeValue1253, Sparse.eval] using hc.symm

theorem sound1262 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1262 node1262Labels = Sparse.eval nodeValue1262 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1262) = mixedMoment B node1262 node1262Labels := rfl
  simpa [nodeValue1262, Sparse.eval] using hc.symm

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

theorem sound1384 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1384 node1384Labels = Sparse.eval nodeValue1384 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1384) = mixedMoment B node1384 node1384Labels := rfl
  simpa [nodeValue1384, Sparse.eval] using hc.symm

theorem sound1389 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1389 node1389Labels = Sparse.eval nodeValue1389 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1389) = mixedMoment B node1389 node1389Labels := rfl
  simpa [nodeValue1389, Sparse.eval] using hc.symm

theorem sound1391 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1391 node1391Labels = Sparse.eval nodeValue1391 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1391) = mixedMoment B node1391 node1391Labels := rfl
  simpa [nodeValue1391, Sparse.eval] using hc.symm

theorem sound1407 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1407 node1407Labels = Sparse.eval nodeValue1407 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1407) = mixedMoment B node1407 node1407Labels := rfl
  simpa [nodeValue1407, Sparse.eval] using hc.symm

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

theorem sound2495 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2495 node2495Labels = Sparse.eval nodeValue2495 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2495) = mixedMoment B node2495 node2495Labels := rfl
  simpa [nodeValue2495, Sparse.eval] using hc.symm

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

theorem sound2562 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2562 node2562Labels = Sparse.eval nodeValue2562 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2562) = mixedMoment B node2562 node2562Labels := rfl
  simpa [nodeValue2562, Sparse.eval] using hc.symm

theorem sound2564 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2564 node2564Labels = Sparse.eval nodeValue2564 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2564) = mixedMoment B node2564 node2564Labels := rfl
  simpa [nodeValue2564, Sparse.eval] using hc.symm

theorem sound2567 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2567 node2567Labels = Sparse.eval nodeValue2567 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2567) = mixedMoment B node2567 node2567Labels := rfl
  simpa [nodeValue2567, Sparse.eval] using hc.symm

theorem sound2622 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2622 node2622Labels = Sparse.eval nodeValue2622 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2622) = mixedMoment B node2622 node2622Labels := rfl
  simpa [nodeValue2622, Sparse.eval] using hc.symm

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

theorem sound2624 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2624 node2624Labels = Sparse.eval nodeValue2624 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2624) = mixedMoment B node2624 node2624Labels := rfl
  simpa [nodeValue2624, Sparse.eval] using hc.symm

theorem sound2627 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2627 node2627Labels = Sparse.eval nodeValue2627 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2627) = mixedMoment B node2627 node2627Labels := rfl
  simpa [nodeValue2627, Sparse.eval] using hc.symm

theorem sound2633 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2633 node2633Labels = Sparse.eval nodeValue2633 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2633) = mixedMoment B node2633 node2633Labels := rfl
  simpa [nodeValue2633, Sparse.eval] using hc.symm

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

theorem sound2751 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2751 node2751Labels = Sparse.eval nodeValue2751 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2751) = mixedMoment B node2751 node2751Labels := rfl
  simpa [nodeValue2751, Sparse.eval] using hc.symm

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

theorem sound2754 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2754 node2754Labels = Sparse.eval nodeValue2754 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2754) = mixedMoment B node2754 node2754Labels := rfl
  simpa [nodeValue2754, Sparse.eval] using hc.symm

theorem sound2759 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2759 node2759Labels = Sparse.eval nodeValue2759 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2759) = mixedMoment B node2759 node2759Labels := rfl
  simpa [nodeValue2759, Sparse.eval] using hc.symm

theorem sound2764 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2764 node2764Labels = Sparse.eval nodeValue2764 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2764) = mixedMoment B node2764 node2764Labels := rfl
  simpa [nodeValue2764, Sparse.eval] using hc.symm

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

theorem sound2925 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2925 node2925Labels = Sparse.eval nodeValue2925 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2925) = mixedMoment B node2925 node2925Labels := rfl
  simpa [nodeValue2925, Sparse.eval] using hc.symm

theorem sound2931 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2931 node2931Labels = Sparse.eval nodeValue2931 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2931) = mixedMoment B node2931 node2931Labels := rfl
  simpa [nodeValue2931, Sparse.eval] using hc.symm

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

theorem sound2974 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2974 node2974Labels = Sparse.eval nodeValue2974 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2974) = mixedMoment B node2974 node2974Labels := rfl
  simpa [nodeValue2974, Sparse.eval] using hc.symm

theorem sound2979 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2979 node2979Labels = Sparse.eval nodeValue2979 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2979) = mixedMoment B node2979 node2979Labels := rfl
  simpa [nodeValue2979, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound47
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound3068 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3068 node3068Labels = Sparse.eval nodeValue3068 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3068) = mixedMoment B node3068 node3068Labels := rfl
  simpa [nodeValue3068, Sparse.eval] using hc.symm

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

theorem sound3074 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3074 node3074Labels = Sparse.eval nodeValue3074 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3074) = mixedMoment B node3074 node3074Labels := rfl
  simpa [nodeValue3074, Sparse.eval] using hc.symm

theorem sound3077 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3077 node3077Labels = Sparse.eval nodeValue3077 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3077) = mixedMoment B node3077 node3077Labels := rfl
  simpa [nodeValue3077, Sparse.eval] using hc.symm

theorem sound3078 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3078 node3078Labels = Sparse.eval nodeValue3078 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3078) = mixedMoment B node3078 node3078Labels := rfl
  simpa [nodeValue3078, Sparse.eval] using hc.symm

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

theorem sound3612 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3612 node3612Labels = Sparse.eval nodeValue3612 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3612) = mixedMoment B node3612 node3612Labels := rfl
  simpa [nodeValue3612, Sparse.eval] using hc.symm

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

theorem sound3813 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3813 node3813Labels = Sparse.eval nodeValue3813 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3813) = mixedMoment B node3813 node3813Labels := rfl
  simpa [nodeValue3813, Sparse.eval] using hc.symm

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

theorem sound3846 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3846 node3846Labels = Sparse.eval nodeValue3846 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3846) = mixedMoment B node3846 node3846Labels := rfl
  simpa [nodeValue3846, Sparse.eval] using hc.symm

theorem sound3881 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3881 node3881Labels = Sparse.eval nodeValue3881 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3881) = mixedMoment B node3881 node3881Labels := rfl
  simpa [nodeValue3881, Sparse.eval] using hc.symm

theorem sound3885 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3885 node3885Labels = Sparse.eval nodeValue3885 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3885) = mixedMoment B node3885 node3885Labels := rfl
  simpa [nodeValue3885, Sparse.eval] using hc.symm

theorem sound3902 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3902 node3902Labels = Sparse.eval nodeValue3902 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3902) = mixedMoment B node3902 node3902Labels := rfl
  simpa [nodeValue3902, Sparse.eval] using hc.symm

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

theorem zero3953 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node3953 node3953Labels = 0 := by
  exact mixedMoment_alpha B hF node3953 node3953Labels 1 permutation200
    (by decide +kernel)

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

theorem sound3910 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3910 node3910Labels = Sparse.eval nodeValue3910 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3910) = mixedMoment B node3910 node3910Labels := rfl
  simpa [nodeValue3910, Sparse.eval] using hc.symm

theorem sound3953 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3953 node3953Labels = Sparse.eval nodeValue3953 (mixedVector B) := by
  simpa only [nodeValue3953, Sparse.eval_nil] using zero3953 B _hB _hF

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

theorem sound4010 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4010 node4010Labels = Sparse.eval nodeValue4010 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4010) = mixedMoment B node4010 node4010Labels := rfl
  simpa [nodeValue4010, Sparse.eval] using hc.symm

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

theorem sound4436 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4436 node4436Labels = Sparse.eval nodeValue4436 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4436) = mixedMoment B node4436 node4436Labels := rfl
  simpa [nodeValue4436, Sparse.eval] using hc.symm

theorem sound4437 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4437 node4437Labels = Sparse.eval nodeValue4437 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4437) = mixedMoment B node4437 node4437Labels := rfl
  simpa [nodeValue4437, Sparse.eval] using hc.symm

theorem sound4444 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4444 node4444Labels = Sparse.eval nodeValue4444 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4444) = mixedMoment B node4444 node4444Labels := rfl
  simpa [nodeValue4444, Sparse.eval] using hc.symm

theorem sound4453 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4453 node4453Labels = Sparse.eval nodeValue4453 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4453) = mixedMoment B node4453 node4453Labels := rfl
  simpa [nodeValue4453, Sparse.eval] using hc.symm

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

theorem sound5064 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5064 node5064Labels = Sparse.eval nodeValue5064 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5064) = mixedMoment B node5064 node5064Labels := rfl
  simpa [nodeValue5064, Sparse.eval] using hc.symm

theorem sound5067 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5067 node5067Labels = Sparse.eval nodeValue5067 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5067) = mixedMoment B node5067 node5067Labels := rfl
  simpa [nodeValue5067, Sparse.eval] using hc.symm

theorem sound5071 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5071 node5071Labels = Sparse.eval nodeValue5071 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5071) = mixedMoment B node5071 node5071Labels := rfl
  simpa [nodeValue5071, Sparse.eval] using hc.symm

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

theorem sound5145 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5145 node5145Labels = Sparse.eval nodeValue5145 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5145) = mixedMoment B node5145 node5145Labels := rfl
  simpa [nodeValue5145, Sparse.eval] using hc.symm

theorem sound5147 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5147 node5147Labels = Sparse.eval nodeValue5147 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5147) = mixedMoment B node5147 node5147Labels := rfl
  simpa [nodeValue5147, Sparse.eval] using hc.symm

theorem sound5152 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5152 node5152Labels = Sparse.eval nodeValue5152 (mixedVector B) := by
  have h := singleton5152 B _hB
  rw [sound2931 B _hB _hF, sound3612 B _hB _hF] at h
  norm_num [nodeValue5152, nodeValue2931, nodeValue3612, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5164 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5164 node5164Labels = Sparse.eval nodeValue5164 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5164) = mixedMoment B node5164 node5164Labels := rfl
  simpa [nodeValue5164, Sparse.eval] using hc.symm

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

theorem sound5220 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5220 node5220Labels = Sparse.eval nodeValue5220 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5220) = mixedMoment B node5220 node5220Labels := rfl
  simpa [nodeValue5220, Sparse.eval] using hc.symm

theorem sound5222 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5222 node5222Labels = Sparse.eval nodeValue5222 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5222) = mixedMoment B node5222 node5222Labels := rfl
  simpa [nodeValue5222, Sparse.eval] using hc.symm

theorem sound5229 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5229 node5229Labels = Sparse.eval nodeValue5229 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5229) = mixedMoment B node5229 node5229Labels := rfl
  simpa [nodeValue5229, Sparse.eval] using hc.symm

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

theorem sound5289 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5289 node5289Labels = Sparse.eval nodeValue5289 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5289) = mixedMoment B node5289 node5289Labels := rfl
  simpa [nodeValue5289, Sparse.eval] using hc.symm

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

theorem sound5448 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5448 node5448Labels = Sparse.eval nodeValue5448 (mixedVector B) := by
  have h := singleton5448 B _hB
  rw [sound3885 B _hB _hF] at h
  norm_num [nodeValue5448, nodeValue3885, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5471 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5471 node5471Labels = Sparse.eval nodeValue5471 (mixedVector B) := by
  simpa only [nodeValue5471, Sparse.eval_nil] using zero5471 B _hB _hF

theorem sound5473 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5473 node5473Labels = Sparse.eval nodeValue5473 (mixedVector B) := by
  have h := singleton5473 B _hB
  rw [sound3958 B _hB _hF, sound3961 B _hB _hF] at h
  norm_num [nodeValue5473, nodeValue3958, nodeValue3961, Sparse.eval] at h ⊢
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources15
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sourceEq498 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm498 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA498 + difference 0 1) (sourceB498 + difference 1 0) sourceC498) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3813) := by
    have ha : (tripleCharges (sourceA498 + difference 0 1) (sourceB498 + difference 1 0) sourceC498) = raw8771 := by
      apply Matrix.ext; unfold tripleCharges sourceA498 sourceB498 sourceC498 difference raw8771; decide +kernel
    rw [ha]
    exact (canonical8771 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA498 + difference 1 1) (sourceB498 + difference 1 1) sourceC498) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3054) := by
    have ha : (tripleCharges (sourceA498 + difference 1 1) (sourceB498 + difference 1 1) sourceC498) = raw8770 := by
      apply Matrix.ext; unfold tripleCharges sourceA498 sourceB498 sourceC498 difference raw8770; decide +kernel
    rw [ha]
    exact (canonical8770 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA498 + difference 2 1) (sourceB498 + difference 1 2) sourceC498) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2974) := by
    have ha : (tripleCharges (sourceA498 + difference 2 1) (sourceB498 + difference 1 2) sourceC498) = raw8782 := by
      apply Matrix.ext; unfold tripleCharges sourceA498 sourceB498 sourceC498 difference raw8782; decide +kernel
    rw [ha]
    exact (canonical8782 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA498 + difference 3 1) (sourceB498 + difference 1 3) sourceC498) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2759) := by
    have ha : (tripleCharges (sourceA498 + difference 3 1) (sourceB498 + difference 1 3) sourceC498) = raw8783 := by
      apply Matrix.ext; unfold tripleCharges sourceA498 sourceB498 sourceC498 difference raw8783; decide +kernel
    rw [ha]
    exact (canonical8783 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA498 + difference 4 1) (sourceB498 + difference 1 4) sourceC498) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2979) := by
    have ha : (tripleCharges (sourceA498 + difference 4 1) (sourceB498 + difference 1 4) sourceC498) = raw8784 := by
      apply Matrix.ext; unfold tripleCharges sourceA498 sourceB498 sourceC498 difference raw8784; decide +kernel
    rw [ha]
    exact (canonical8784 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA498 + difference 5 1) (sourceB498 + difference 1 5) sourceC498) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2495) := by
    have ha : (tripleCharges (sourceA498 + difference 5 1) (sourceB498 + difference 1 5) sourceC498) = raw8785 := by
      apply Matrix.ext; unfold tripleCharges sourceA498 sourceB498 sourceC498 difference raw8785; decide +kernel
    rw [ha]
    exact (canonical8785 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA498 + sourceB498) sourceC498) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA498 + sourceB498) sourceC498) = raw8776 := by
      apply Matrix.ext; unfold doubleCharges sourceA498 sourceB498 sourceC498 raw8776; decide +kernel
    rw [ha]
    exact (canonical8776 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA498 sourceB498 sourceC498
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm498, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq504 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm504 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA504 + difference 0 0) (sourceB504 + difference 0 0) sourceC504) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2751) := by
    have ha : (tripleCharges (sourceA504 + difference 0 0) (sourceB504 + difference 0 0) sourceC504) = raw8892 := by
      apply Matrix.ext; unfold tripleCharges sourceA504 sourceB504 sourceC504 difference raw8892; decide +kernel
    rw [ha]
    exact (canonical8892 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA504 + difference 0 1) (sourceB504 + difference 1 0) sourceC504) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3846) := by
    have ha : (tripleCharges (sourceA504 + difference 0 1) (sourceB504 + difference 1 0) sourceC504) = raw8893 := by
      apply Matrix.ext; unfold tripleCharges sourceA504 sourceB504 sourceC504 difference raw8893; decide +kernel
    rw [ha]
    exact (canonical8893 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA504 + difference 0 2) (sourceB504 + difference 2 0) sourceC504) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3881) := by
    have ha : (tripleCharges (sourceA504 + difference 0 2) (sourceB504 + difference 2 0) sourceC504) = raw8894 := by
      apply Matrix.ext; unfold tripleCharges sourceA504 sourceB504 sourceC504 difference raw8894; decide +kernel
    rw [ha]
    exact (canonical8894 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA504 + difference 0 3) (sourceB504 + difference 3 0) sourceC504) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3881) := by
    have ha : (tripleCharges (sourceA504 + difference 0 3) (sourceB504 + difference 3 0) sourceC504) = raw8895 := by
      apply Matrix.ext; unfold tripleCharges sourceA504 sourceB504 sourceC504 difference raw8895; decide +kernel
    rw [ha]
    exact (canonical8895 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA504 + difference 0 4) (sourceB504 + difference 4 0) sourceC504) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3902) := by
    have ha : (tripleCharges (sourceA504 + difference 0 4) (sourceB504 + difference 4 0) sourceC504) = raw8896 := by
      apply Matrix.ext; unfold tripleCharges sourceA504 sourceB504 sourceC504 difference raw8896; decide +kernel
    rw [ha]
    exact (canonical8896 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA504 + difference 0 5) (sourceB504 + difference 5 0) sourceC504) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3910) := by
    have ha : (tripleCharges (sourceA504 + difference 0 5) (sourceB504 + difference 5 0) sourceC504) = raw8897 := by
      apply Matrix.ext; unfold tripleCharges sourceA504 sourceB504 sourceC504 difference raw8897; decide +kernel
    rw [ha]
    exact (canonical8897 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA504 + sourceB504) sourceC504) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA504 + sourceB504) sourceC504) = raw8898 := by
      apply Matrix.ext; unfold doubleCharges sourceA504 sourceB504 sourceC504 raw8898; decide +kernel
    rw [ha]
    exact (canonical8898 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA504 sourceB504 sourceC504
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm504, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq505 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm505 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA505 + difference 0 0) (sourceB505 + difference 0 0) sourceC505) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2751) := by
    have ha : (tripleCharges (sourceA505 + difference 0 0) (sourceB505 + difference 0 0) sourceC505) = raw8892 := by
      apply Matrix.ext; unfold tripleCharges sourceA505 sourceB505 sourceC505 difference raw8892; decide +kernel
    rw [ha]
    exact (canonical8892 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA505 + difference 1 0) (sourceB505 + difference 0 1) sourceC505) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1247) := by
    have ha : (tripleCharges (sourceA505 + difference 1 0) (sourceB505 + difference 0 1) sourceC505) = raw8899 := by
      apply Matrix.ext; unfold tripleCharges sourceA505 sourceB505 sourceC505 difference raw8899; decide +kernel
    rw [ha]
    exact (canonical8899 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA505 + difference 2 0) (sourceB505 + difference 0 2) sourceC505) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1262) := by
    have ha : (tripleCharges (sourceA505 + difference 2 0) (sourceB505 + difference 0 2) sourceC505) = raw8900 := by
      apply Matrix.ext; unfold tripleCharges sourceA505 sourceB505 sourceC505 difference raw8900; decide +kernel
    rw [ha]
    exact (canonical8900 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA505 + difference 3 0) (sourceB505 + difference 0 3) sourceC505) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1262) := by
    have ha : (tripleCharges (sourceA505 + difference 3 0) (sourceB505 + difference 0 3) sourceC505) = raw8901 := by
      apply Matrix.ext; unfold tripleCharges sourceA505 sourceB505 sourceC505 difference raw8901; decide +kernel
    rw [ha]
    exact (canonical8901 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA505 + difference 4 0) (sourceB505 + difference 0 4) sourceC505) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1253) := by
    have ha : (tripleCharges (sourceA505 + difference 4 0) (sourceB505 + difference 0 4) sourceC505) = raw8902 := by
      apply Matrix.ext; unfold tripleCharges sourceA505 sourceB505 sourceC505 difference raw8902; decide +kernel
    rw [ha]
    exact (canonical8902 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA505 + difference 5 0) (sourceB505 + difference 0 5) sourceC505) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1249) := by
    have ha : (tripleCharges (sourceA505 + difference 5 0) (sourceB505 + difference 0 5) sourceC505) = raw8903 := by
      apply Matrix.ext; unfold tripleCharges sourceA505 sourceB505 sourceC505 difference raw8903; decide +kernel
    rw [ha]
    exact (canonical8903 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA505 + sourceB505) sourceC505) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA505 + sourceB505) sourceC505) = raw8898 := by
      apply Matrix.ext; unfold doubleCharges sourceA505 sourceB505 sourceC505 raw8898; decide +kernel
    rw [ha]
    exact (canonical8898 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA505 sourceB505 sourceC505
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm505, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq506 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm506 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA506 + difference 0 1) (sourceB506 + difference 1 0) sourceC506) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3846) := by
    have ha : (tripleCharges (sourceA506 + difference 0 1) (sourceB506 + difference 1 0) sourceC506) = raw8893 := by
      apply Matrix.ext; unfold tripleCharges sourceA506 sourceB506 sourceC506 difference raw8893; decide +kernel
    rw [ha]
    exact (canonical8893 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA506 + difference 1 1) (sourceB506 + difference 1 1) sourceC506) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2751) := by
    have ha : (tripleCharges (sourceA506 + difference 1 1) (sourceB506 + difference 1 1) sourceC506) = raw8892 := by
      apply Matrix.ext; unfold tripleCharges sourceA506 sourceB506 sourceC506 difference raw8892; decide +kernel
    rw [ha]
    exact (canonical8892 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA506 + difference 2 1) (sourceB506 + difference 1 2) sourceC506) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2567) := by
    have ha : (tripleCharges (sourceA506 + difference 2 1) (sourceB506 + difference 1 2) sourceC506) = raw8904 := by
      apply Matrix.ext; unfold tripleCharges sourceA506 sourceB506 sourceC506 difference raw8904; decide +kernel
    rw [ha]
    exact (canonical8904 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA506 + difference 3 1) (sourceB506 + difference 1 3) sourceC506) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2567) := by
    have ha : (tripleCharges (sourceA506 + difference 3 1) (sourceB506 + difference 1 3) sourceC506) = raw8905 := by
      apply Matrix.ext; unfold tripleCharges sourceA506 sourceB506 sourceC506 difference raw8905; decide +kernel
    rw [ha]
    exact (canonical8905 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA506 + difference 4 1) (sourceB506 + difference 1 4) sourceC506) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2564) := by
    have ha : (tripleCharges (sourceA506 + difference 4 1) (sourceB506 + difference 1 4) sourceC506) = raw8906 := by
      apply Matrix.ext; unfold tripleCharges sourceA506 sourceB506 sourceC506 difference raw8906; decide +kernel
    rw [ha]
    exact (canonical8906 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA506 + difference 5 1) (sourceB506 + difference 1 5) sourceC506) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2562) := by
    have ha : (tripleCharges (sourceA506 + difference 5 1) (sourceB506 + difference 1 5) sourceC506) = raw8907 := by
      apply Matrix.ext; unfold tripleCharges sourceA506 sourceB506 sourceC506 difference raw8907; decide +kernel
    rw [ha]
    exact (canonical8907 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA506 + sourceB506) sourceC506) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA506 + sourceB506) sourceC506) = raw8898 := by
      apply Matrix.ext; unfold doubleCharges sourceA506 sourceB506 sourceC506 raw8898; decide +kernel
    rw [ha]
    exact (canonical8898 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA506 sourceB506 sourceC506
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm506, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq507 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm507 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA507 + difference 2 0) (sourceB507 + difference 0 2) sourceC507) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1262) := by
    have ha : (tripleCharges (sourceA507 + difference 2 0) (sourceB507 + difference 0 2) sourceC507) = raw8900 := by
      apply Matrix.ext; unfold tripleCharges sourceA507 sourceB507 sourceC507 difference raw8900; decide +kernel
    rw [ha]
    exact (canonical8900 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA507 + difference 2 1) (sourceB507 + difference 1 2) sourceC507) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2567) := by
    have ha : (tripleCharges (sourceA507 + difference 2 1) (sourceB507 + difference 1 2) sourceC507) = raw8904 := by
      apply Matrix.ext; unfold tripleCharges sourceA507 sourceB507 sourceC507 difference raw8904; decide +kernel
    rw [ha]
    exact (canonical8904 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA507 + difference 2 2) (sourceB507 + difference 2 2) sourceC507) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2751) := by
    have ha : (tripleCharges (sourceA507 + difference 2 2) (sourceB507 + difference 2 2) sourceC507) = raw8892 := by
      apply Matrix.ext; unfold tripleCharges sourceA507 sourceB507 sourceC507 difference raw8892; decide +kernel
    rw [ha]
    exact (canonical8892 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA507 + difference 2 3) (sourceB507 + difference 3 2) sourceC507) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2633) := by
    have ha : (tripleCharges (sourceA507 + difference 2 3) (sourceB507 + difference 3 2) sourceC507) = raw8908 := by
      apply Matrix.ext; unfold tripleCharges sourceA507 sourceB507 sourceC507 difference raw8908; decide +kernel
    rw [ha]
    exact (canonical8908 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA507 + difference 2 4) (sourceB507 + difference 4 2) sourceC507) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2723) := by
    have ha : (tripleCharges (sourceA507 + difference 2 4) (sourceB507 + difference 4 2) sourceC507) = raw8909 := by
      apply Matrix.ext; unfold tripleCharges sourceA507 sourceB507 sourceC507 difference raw8909; decide +kernel
    rw [ha]
    exact (canonical8909 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA507 + difference 2 5) (sourceB507 + difference 5 2) sourceC507) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2764) := by
    have ha : (tripleCharges (sourceA507 + difference 2 5) (sourceB507 + difference 5 2) sourceC507) = raw8910 := by
      apply Matrix.ext; unfold tripleCharges sourceA507 sourceB507 sourceC507 difference raw8910; decide +kernel
    rw [ha]
    exact (canonical8910 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA507 + sourceB507) sourceC507) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA507 + sourceB507) sourceC507) = raw8898 := by
      apply Matrix.ext; unfold doubleCharges sourceA507 sourceB507 sourceC507 raw8898; decide +kernel
    rw [ha]
    exact (canonical8898 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA507 sourceB507 sourceC507
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm507, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq508 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm508 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA508 + difference 0 2) (sourceB508 + difference 2 0) sourceC508) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3881) := by
    have ha : (tripleCharges (sourceA508 + difference 0 2) (sourceB508 + difference 2 0) sourceC508) = raw8894 := by
      apply Matrix.ext; unfold tripleCharges sourceA508 sourceB508 sourceC508 difference raw8894; decide +kernel
    rw [ha]
    exact (canonical8894 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA508 + difference 1 2) (sourceB508 + difference 2 1) sourceC508) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2622) := by
    have ha : (tripleCharges (sourceA508 + difference 1 2) (sourceB508 + difference 2 1) sourceC508) = raw8911 := by
      apply Matrix.ext; unfold tripleCharges sourceA508 sourceB508 sourceC508 difference raw8911; decide +kernel
    rw [ha]
    exact (canonical8911 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA508 + difference 2 2) (sourceB508 + difference 2 2) sourceC508) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2751) := by
    have ha : (tripleCharges (sourceA508 + difference 2 2) (sourceB508 + difference 2 2) sourceC508) = raw8892 := by
      apply Matrix.ext; unfold tripleCharges sourceA508 sourceB508 sourceC508 difference raw8892; decide +kernel
    rw [ha]
    exact (canonical8892 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA508 + difference 3 2) (sourceB508 + difference 2 3) sourceC508) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2633) := by
    have ha : (tripleCharges (sourceA508 + difference 3 2) (sourceB508 + difference 2 3) sourceC508) = raw8912 := by
      apply Matrix.ext; unfold tripleCharges sourceA508 sourceB508 sourceC508 difference raw8912; decide +kernel
    rw [ha]
    exact (canonical8912 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA508 + difference 4 2) (sourceB508 + difference 2 4) sourceC508) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2627) := by
    have ha : (tripleCharges (sourceA508 + difference 4 2) (sourceB508 + difference 2 4) sourceC508) = raw8913 := by
      apply Matrix.ext; unfold tripleCharges sourceA508 sourceB508 sourceC508 difference raw8913; decide +kernel
    rw [ha]
    exact (canonical8913 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA508 + difference 5 2) (sourceB508 + difference 2 5) sourceC508) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2624) := by
    have ha : (tripleCharges (sourceA508 + difference 5 2) (sourceB508 + difference 2 5) sourceC508) = raw8914 := by
      apply Matrix.ext; unfold tripleCharges sourceA508 sourceB508 sourceC508 difference raw8914; decide +kernel
    rw [ha]
    exact (canonical8914 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA508 + sourceB508) sourceC508) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA508 + sourceB508) sourceC508) = raw8898 := by
      apply Matrix.ext; unfold doubleCharges sourceA508 sourceB508 sourceC508 raw8898; decide +kernel
    rw [ha]
    exact (canonical8898 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA508 sourceB508 sourceC508
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm508, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq509 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm509 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA509 + difference 4 0) (sourceB509 + difference 0 4) sourceC509) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1253) := by
    have ha : (tripleCharges (sourceA509 + difference 4 0) (sourceB509 + difference 0 4) sourceC509) = raw8902 := by
      apply Matrix.ext; unfold tripleCharges sourceA509 sourceB509 sourceC509 difference raw8902; decide +kernel
    rw [ha]
    exact (canonical8902 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA509 + difference 4 1) (sourceB509 + difference 1 4) sourceC509) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2564) := by
    have ha : (tripleCharges (sourceA509 + difference 4 1) (sourceB509 + difference 1 4) sourceC509) = raw8906 := by
      apply Matrix.ext; unfold tripleCharges sourceA509 sourceB509 sourceC509 difference raw8906; decide +kernel
    rw [ha]
    exact (canonical8906 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA509 + difference 4 2) (sourceB509 + difference 2 4) sourceC509) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2627) := by
    have ha : (tripleCharges (sourceA509 + difference 4 2) (sourceB509 + difference 2 4) sourceC509) = raw8913 := by
      apply Matrix.ext; unfold tripleCharges sourceA509 sourceB509 sourceC509 difference raw8913; decide +kernel
    rw [ha]
    exact (canonical8913 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA509 + difference 4 3) (sourceB509 + difference 3 4) sourceC509) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2627) := by
    have ha : (tripleCharges (sourceA509 + difference 4 3) (sourceB509 + difference 3 4) sourceC509) = raw8915 := by
      apply Matrix.ext; unfold tripleCharges sourceA509 sourceB509 sourceC509 difference raw8915; decide +kernel
    rw [ha]
    exact (canonical8915 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA509 + difference 4 4) (sourceB509 + difference 4 4) sourceC509) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2751) := by
    have ha : (tripleCharges (sourceA509 + difference 4 4) (sourceB509 + difference 4 4) sourceC509) = raw8892 := by
      apply Matrix.ext; unfold tripleCharges sourceA509 sourceB509 sourceC509 difference raw8892; decide +kernel
    rw [ha]
    exact (canonical8892 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA509 + difference 4 5) (sourceB509 + difference 5 4) sourceC509) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2754) := by
    have ha : (tripleCharges (sourceA509 + difference 4 5) (sourceB509 + difference 5 4) sourceC509) = raw8916 := by
      apply Matrix.ext; unfold tripleCharges sourceA509 sourceB509 sourceC509 difference raw8916; decide +kernel
    rw [ha]
    exact (canonical8916 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA509 + sourceB509) sourceC509) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA509 + sourceB509) sourceC509) = raw8898 := by
      apply Matrix.ext; unfold doubleCharges sourceA509 sourceB509 sourceC509 raw8898; decide +kernel
    rw [ha]
    exact (canonical8898 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA509 sourceB509 sourceC509
    (0 : Fin 2) 1 (4 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm509, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq510 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm510 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA510 + difference 0 1) (sourceB510 + difference 1 0) sourceC510) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5471) := by
    have ha : (tripleCharges (sourceA510 + difference 0 1) (sourceB510 + difference 1 0) sourceC510) = raw8917 := by
      apply Matrix.ext; unfold tripleCharges sourceA510 sourceB510 sourceC510 difference raw8917; decide +kernel
    rw [ha]
    exact (canonical8917 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA510 + difference 0 2) (sourceB510 + difference 2 0) sourceC510) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5473) := by
    have ha : (tripleCharges (sourceA510 + difference 0 2) (sourceB510 + difference 2 0) sourceC510) = raw8918 := by
      apply Matrix.ext; unfold tripleCharges sourceA510 sourceB510 sourceC510 difference raw8918; decide +kernel
    rw [ha]
    exact (canonical8918 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA510 + difference 0 3) (sourceB510 + difference 3 0) sourceC510) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5473) := by
    have ha : (tripleCharges (sourceA510 + difference 0 3) (sourceB510 + difference 3 0) sourceC510) = raw8919 := by
      apply Matrix.ext; unfold tripleCharges sourceA510 sourceB510 sourceC510 difference raw8919; decide +kernel
    rw [ha]
    exact (canonical8919 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA510 + difference 0 4) (sourceB510 + difference 4 0) sourceC510) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5448) := by
    have ha : (tripleCharges (sourceA510 + difference 0 4) (sourceB510 + difference 4 0) sourceC510) = raw8920 := by
      apply Matrix.ext; unfold tripleCharges sourceA510 sourceB510 sourceC510 difference raw8920; decide +kernel
    rw [ha]
    exact (canonical8920 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA510 + difference 0 5) (sourceB510 + difference 5 0) sourceC510) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5485) := by
    have ha : (tripleCharges (sourceA510 + difference 0 5) (sourceB510 + difference 5 0) sourceC510) = raw8921 := by
      apply Matrix.ext; unfold tripleCharges sourceA510 sourceB510 sourceC510 difference raw8921; decide +kernel
    rw [ha]
    exact (canonical8921 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA510 + difference 1 0) (sourceB510 + difference 0 1) sourceC510) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4436) := by
    have ha : (tripleCharges (sourceA510 + difference 1 0) (sourceB510 + difference 0 1) sourceC510) = raw8922 := by
      apply Matrix.ext; unfold tripleCharges sourceA510 sourceB510 sourceC510 difference raw8922; decide +kernel
    rw [ha]
    exact (canonical8922 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA510 + difference 1 2) (sourceB510 + difference 2 1) sourceC510) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5145) := by
    have ha : (tripleCharges (sourceA510 + difference 1 2) (sourceB510 + difference 2 1) sourceC510) = raw8923 := by
      apply Matrix.ext; unfold tripleCharges sourceA510 sourceB510 sourceC510 difference raw8923; decide +kernel
    rw [ha]
    exact (canonical8923 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA510 + difference 1 3) (sourceB510 + difference 3 1) sourceC510) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5145) := by
    have ha : (tripleCharges (sourceA510 + difference 1 3) (sourceB510 + difference 3 1) sourceC510) = raw8924 := by
      apply Matrix.ext; unfold tripleCharges sourceA510 sourceB510 sourceC510 difference raw8924; decide +kernel
    rw [ha]
    exact (canonical8924 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA510 + difference 1 4) (sourceB510 + difference 4 1) sourceC510) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5220) := by
    have ha : (tripleCharges (sourceA510 + difference 1 4) (sourceB510 + difference 4 1) sourceC510) = raw8925 := by
      apply Matrix.ext; unfold tripleCharges sourceA510 sourceB510 sourceC510 difference raw8925; decide +kernel
    rw [ha]
    exact (canonical8925 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA510 + difference 1 5) (sourceB510 + difference 5 1) sourceC510) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5281) := by
    have ha : (tripleCharges (sourceA510 + difference 1 5) (sourceB510 + difference 5 1) sourceC510) = raw8926 := by
      apply Matrix.ext; unfold tripleCharges sourceA510 sourceB510 sourceC510 difference raw8926; decide +kernel
    rw [ha]
    exact (canonical8926 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA510 + difference 2 0) (sourceB510 + difference 0 2) sourceC510) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4453) := by
    have ha : (tripleCharges (sourceA510 + difference 2 0) (sourceB510 + difference 0 2) sourceC510) = raw8927 := by
      apply Matrix.ext; unfold tripleCharges sourceA510 sourceB510 sourceC510 difference raw8927; decide +kernel
    rw [ha]
    exact (canonical8927 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA510 + difference 2 1) (sourceB510 + difference 1 2) sourceC510) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5071) := by
    have ha : (tripleCharges (sourceA510 + difference 2 1) (sourceB510 + difference 1 2) sourceC510) = raw8928 := by
      apply Matrix.ext; unfold tripleCharges sourceA510 sourceB510 sourceC510 difference raw8928; decide +kernel
    rw [ha]
    exact (canonical8928 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA510 + difference 2 3) (sourceB510 + difference 3 2) sourceC510) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5164) := by
    have ha : (tripleCharges (sourceA510 + difference 2 3) (sourceB510 + difference 3 2) sourceC510) = raw8929 := by
      apply Matrix.ext; unfold tripleCharges sourceA510 sourceB510 sourceC510 difference raw8929; decide +kernel
    rw [ha]
    exact (canonical8929 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA510 + difference 2 4) (sourceB510 + difference 4 2) sourceC510) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5229) := by
    have ha : (tripleCharges (sourceA510 + difference 2 4) (sourceB510 + difference 4 2) sourceC510) = raw8930 := by
      apply Matrix.ext; unfold tripleCharges sourceA510 sourceB510 sourceC510 difference raw8930; decide +kernel
    rw [ha]
    exact (canonical8930 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA510 + difference 2 5) (sourceB510 + difference 5 2) sourceC510) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5289) := by
    have ha : (tripleCharges (sourceA510 + difference 2 5) (sourceB510 + difference 5 2) sourceC510) = raw8931 := by
      apply Matrix.ext; unfold tripleCharges sourceA510 sourceB510 sourceC510 difference raw8931; decide +kernel
    rw [ha]
    exact (canonical8931 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA510 + difference 3 0) (sourceB510 + difference 0 3) sourceC510) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4453) := by
    have ha : (tripleCharges (sourceA510 + difference 3 0) (sourceB510 + difference 0 3) sourceC510) = raw8932 := by
      apply Matrix.ext; unfold tripleCharges sourceA510 sourceB510 sourceC510 difference raw8932; decide +kernel
    rw [ha]
    exact (canonical8932 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA510 + difference 3 1) (sourceB510 + difference 1 3) sourceC510) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5071) := by
    have ha : (tripleCharges (sourceA510 + difference 3 1) (sourceB510 + difference 1 3) sourceC510) = raw8933 := by
      apply Matrix.ext; unfold tripleCharges sourceA510 sourceB510 sourceC510 difference raw8933; decide +kernel
    rw [ha]
    exact (canonical8933 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA510 + difference 3 2) (sourceB510 + difference 2 3) sourceC510) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5164) := by
    have ha : (tripleCharges (sourceA510 + difference 3 2) (sourceB510 + difference 2 3) sourceC510) = raw8934 := by
      apply Matrix.ext; unfold tripleCharges sourceA510 sourceB510 sourceC510 difference raw8934; decide +kernel
    rw [ha]
    exact (canonical8934 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA510 + difference 3 4) (sourceB510 + difference 4 3) sourceC510) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5229) := by
    have ha : (tripleCharges (sourceA510 + difference 3 4) (sourceB510 + difference 4 3) sourceC510) = raw8935 := by
      apply Matrix.ext; unfold tripleCharges sourceA510 sourceB510 sourceC510 difference raw8935; decide +kernel
    rw [ha]
    exact (canonical8935 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA510 + difference 3 5) (sourceB510 + difference 5 3) sourceC510) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5289) := by
    have ha : (tripleCharges (sourceA510 + difference 3 5) (sourceB510 + difference 5 3) sourceC510) = raw8936 := by
      apply Matrix.ext; unfold tripleCharges sourceA510 sourceB510 sourceC510 difference raw8936; decide +kernel
    rw [ha]
    exact (canonical8936 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA510 + difference 4 0) (sourceB510 + difference 0 4) sourceC510) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4444) := by
    have ha : (tripleCharges (sourceA510 + difference 4 0) (sourceB510 + difference 0 4) sourceC510) = raw8937 := by
      apply Matrix.ext; unfold tripleCharges sourceA510 sourceB510 sourceC510 difference raw8937; decide +kernel
    rw [ha]
    exact (canonical8937 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA510 + difference 4 1) (sourceB510 + difference 1 4) sourceC510) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5067) := by
    have ha : (tripleCharges (sourceA510 + difference 4 1) (sourceB510 + difference 1 4) sourceC510) = raw8938 := by
      apply Matrix.ext; unfold tripleCharges sourceA510 sourceB510 sourceC510 difference raw8938; decide +kernel
    rw [ha]
    exact (canonical8938 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA510 + difference 4 2) (sourceB510 + difference 2 4) sourceC510) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5152) := by
    have ha : (tripleCharges (sourceA510 + difference 4 2) (sourceB510 + difference 2 4) sourceC510) = raw8939 := by
      apply Matrix.ext; unfold tripleCharges sourceA510 sourceB510 sourceC510 difference raw8939; decide +kernel
    rw [ha]
    exact (canonical8939 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA510 + difference 4 3) (sourceB510 + difference 3 4) sourceC510) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5152) := by
    have ha : (tripleCharges (sourceA510 + difference 4 3) (sourceB510 + difference 3 4) sourceC510) = raw8940 := by
      apply Matrix.ext; unfold tripleCharges sourceA510 sourceB510 sourceC510 difference raw8940; decide +kernel
    rw [ha]
    exact (canonical8940 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA510 + difference 4 5) (sourceB510 + difference 5 4) sourceC510) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5284) := by
    have ha : (tripleCharges (sourceA510 + difference 4 5) (sourceB510 + difference 5 4) sourceC510) = raw8941 := by
      apply Matrix.ext; unfold tripleCharges sourceA510 sourceB510 sourceC510 difference raw8941; decide +kernel
    rw [ha]
    exact (canonical8941 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA510 + difference 5 0) (sourceB510 + difference 0 5) sourceC510) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4437) := by
    have ha : (tripleCharges (sourceA510 + difference 5 0) (sourceB510 + difference 0 5) sourceC510) = raw8942 := by
      apply Matrix.ext; unfold tripleCharges sourceA510 sourceB510 sourceC510 difference raw8942; decide +kernel
    rw [ha]
    exact (canonical8942 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA510 + difference 5 1) (sourceB510 + difference 1 5) sourceC510) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5064) := by
    have ha : (tripleCharges (sourceA510 + difference 5 1) (sourceB510 + difference 1 5) sourceC510) = raw8943 := by
      apply Matrix.ext; unfold tripleCharges sourceA510 sourceB510 sourceC510 difference raw8943; decide +kernel
    rw [ha]
    exact (canonical8943 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA510 + difference 5 2) (sourceB510 + difference 2 5) sourceC510) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5147) := by
    have ha : (tripleCharges (sourceA510 + difference 5 2) (sourceB510 + difference 2 5) sourceC510) = raw8944 := by
      apply Matrix.ext; unfold tripleCharges sourceA510 sourceB510 sourceC510 difference raw8944; decide +kernel
    rw [ha]
    exact (canonical8944 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA510 + difference 5 3) (sourceB510 + difference 3 5) sourceC510) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5147) := by
    have ha : (tripleCharges (sourceA510 + difference 5 3) (sourceB510 + difference 3 5) sourceC510) = raw8945 := by
      apply Matrix.ext; unfold tripleCharges sourceA510 sourceB510 sourceC510 difference raw8945; decide +kernel
    rw [ha]
    exact (canonical8945 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA510 + difference 5 4) (sourceB510 + difference 4 5) sourceC510) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5222) := by
    have ha : (tripleCharges (sourceA510 + difference 5 4) (sourceB510 + difference 4 5) sourceC510) = raw8946 := by
      apply Matrix.ext; unfold tripleCharges sourceA510 sourceB510 sourceC510 difference raw8946; decide +kernel
    rw [ha]
    exact (canonical8946 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA510 sourceB510 sourceC510
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm510, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources16
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sourceEq513 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm513 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA513 + difference 0 0) (sourceB513 + difference 0 0) sourceC513) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3078) := by
    have ha : (tripleCharges (sourceA513 + difference 0 0) (sourceB513 + difference 0 0) sourceC513) = raw9007 := by
      apply Matrix.ext; unfold tripleCharges sourceA513 sourceB513 sourceC513 difference raw9007; decide +kernel
    rw [ha]
    exact (canonical9007 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA513 + difference 0 1) (sourceB513 + difference 1 0) sourceC513) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3953) := by
    have ha : (tripleCharges (sourceA513 + difference 0 1) (sourceB513 + difference 1 0) sourceC513) = raw9008 := by
      apply Matrix.ext; unfold tripleCharges sourceA513 sourceB513 sourceC513 difference raw9008; decide +kernel
    rw [ha]
    exact (canonical9008 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA513 + difference 0 2) (sourceB513 + difference 2 0) sourceC513) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3958) := by
    have ha : (tripleCharges (sourceA513 + difference 0 2) (sourceB513 + difference 2 0) sourceC513) = raw9009 := by
      apply Matrix.ext; unfold tripleCharges sourceA513 sourceB513 sourceC513 difference raw9009; decide +kernel
    rw [ha]
    exact (canonical9009 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA513 + difference 0 3) (sourceB513 + difference 3 0) sourceC513) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3958) := by
    have ha : (tripleCharges (sourceA513 + difference 0 3) (sourceB513 + difference 3 0) sourceC513) = raw9010 := by
      apply Matrix.ext; unfold tripleCharges sourceA513 sourceB513 sourceC513 difference raw9010; decide +kernel
    rw [ha]
    exact (canonical9010 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA513 + difference 0 4) (sourceB513 + difference 4 0) sourceC513) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3885) := by
    have ha : (tripleCharges (sourceA513 + difference 0 4) (sourceB513 + difference 4 0) sourceC513) = raw9011 := by
      apply Matrix.ext; unfold tripleCharges sourceA513 sourceB513 sourceC513 difference raw9011; decide +kernel
    rw [ha]
    exact (canonical9011 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA513 + difference 0 5) (sourceB513 + difference 5 0) sourceC513) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4010) := by
    have ha : (tripleCharges (sourceA513 + difference 0 5) (sourceB513 + difference 5 0) sourceC513) = raw9012 := by
      apply Matrix.ext; unfold tripleCharges sourceA513 sourceB513 sourceC513 difference raw9012; decide +kernel
    rw [ha]
    exact (canonical9012 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA513 + sourceB513) sourceC513) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA513 + sourceB513) sourceC513) = raw9013 := by
      apply Matrix.ext; unfold doubleCharges sourceA513 sourceB513 sourceC513 raw9013; decide +kernel
    rw [ha]
    exact (canonical9013 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA513 sourceB513 sourceC513
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm513, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq514 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm514 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA514 + difference 0 0) (sourceB514 + difference 0 0) sourceC514) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3078) := by
    have ha : (tripleCharges (sourceA514 + difference 0 0) (sourceB514 + difference 0 0) sourceC514) = raw9007 := by
      apply Matrix.ext; unfold tripleCharges sourceA514 sourceB514 sourceC514 difference raw9007; decide +kernel
    rw [ha]
    exact (canonical9007 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA514 + difference 1 0) (sourceB514 + difference 0 1) sourceC514) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1384) := by
    have ha : (tripleCharges (sourceA514 + difference 1 0) (sourceB514 + difference 0 1) sourceC514) = raw9014 := by
      apply Matrix.ext; unfold tripleCharges sourceA514 sourceB514 sourceC514 difference raw9014; decide +kernel
    rw [ha]
    exact (canonical9014 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA514 + difference 2 0) (sourceB514 + difference 0 2) sourceC514) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1407) := by
    have ha : (tripleCharges (sourceA514 + difference 2 0) (sourceB514 + difference 0 2) sourceC514) = raw9015 := by
      apply Matrix.ext; unfold tripleCharges sourceA514 sourceB514 sourceC514 difference raw9015; decide +kernel
    rw [ha]
    exact (canonical9015 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA514 + difference 3 0) (sourceB514 + difference 0 3) sourceC514) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1407) := by
    have ha : (tripleCharges (sourceA514 + difference 3 0) (sourceB514 + difference 0 3) sourceC514) = raw9016 := by
      apply Matrix.ext; unfold tripleCharges sourceA514 sourceB514 sourceC514 difference raw9016; decide +kernel
    rw [ha]
    exact (canonical9016 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA514 + difference 4 0) (sourceB514 + difference 0 4) sourceC514) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1391) := by
    have ha : (tripleCharges (sourceA514 + difference 4 0) (sourceB514 + difference 0 4) sourceC514) = raw9017 := by
      apply Matrix.ext; unfold tripleCharges sourceA514 sourceB514 sourceC514 difference raw9017; decide +kernel
    rw [ha]
    exact (canonical9017 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA514 + difference 5 0) (sourceB514 + difference 0 5) sourceC514) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1389) := by
    have ha : (tripleCharges (sourceA514 + difference 5 0) (sourceB514 + difference 0 5) sourceC514) = raw9018 := by
      apply Matrix.ext; unfold tripleCharges sourceA514 sourceB514 sourceC514 difference raw9018; decide +kernel
    rw [ha]
    exact (canonical9018 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA514 + sourceB514) sourceC514) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA514 + sourceB514) sourceC514) = raw9013 := by
      apply Matrix.ext; unfold doubleCharges sourceA514 sourceB514 sourceC514 raw9013; decide +kernel
    rw [ha]
    exact (canonical9013 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA514 sourceB514 sourceC514
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm514, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq515 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm515 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA515 + difference 1 0) (sourceB515 + difference 0 1) sourceC515) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1384) := by
    have ha : (tripleCharges (sourceA515 + difference 1 0) (sourceB515 + difference 0 1) sourceC515) = raw9014 := by
      apply Matrix.ext; unfold tripleCharges sourceA515 sourceB515 sourceC515 difference raw9014; decide +kernel
    rw [ha]
    exact (canonical9014 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA515 + difference 1 1) (sourceB515 + difference 1 1) sourceC515) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3078) := by
    have ha : (tripleCharges (sourceA515 + difference 1 1) (sourceB515 + difference 1 1) sourceC515) = raw9007 := by
      apply Matrix.ext; unfold tripleCharges sourceA515 sourceB515 sourceC515 difference raw9007; decide +kernel
    rw [ha]
    exact (canonical9007 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA515 + difference 1 2) (sourceB515 + difference 2 1) sourceC515) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2925) := by
    have ha : (tripleCharges (sourceA515 + difference 1 2) (sourceB515 + difference 2 1) sourceC515) = raw9019 := by
      apply Matrix.ext; unfold tripleCharges sourceA515 sourceB515 sourceC515 difference raw9019; decide +kernel
    rw [ha]
    exact (canonical9019 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA515 + difference 1 3) (sourceB515 + difference 3 1) sourceC515) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2925) := by
    have ha : (tripleCharges (sourceA515 + difference 1 3) (sourceB515 + difference 3 1) sourceC515) = raw9020 := by
      apply Matrix.ext; unfold tripleCharges sourceA515 sourceB515 sourceC515 difference raw9020; decide +kernel
    rw [ha]
    exact (canonical9020 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA515 + difference 1 4) (sourceB515 + difference 4 1) sourceC515) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3068) := by
    have ha : (tripleCharges (sourceA515 + difference 1 4) (sourceB515 + difference 4 1) sourceC515) = raw9021 := by
      apply Matrix.ext; unfold tripleCharges sourceA515 sourceB515 sourceC515 difference raw9021; decide +kernel
    rw [ha]
    exact (canonical9021 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA515 + difference 1 5) (sourceB515 + difference 5 1) sourceC515) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3074) := by
    have ha : (tripleCharges (sourceA515 + difference 1 5) (sourceB515 + difference 5 1) sourceC515) = raw9022 := by
      apply Matrix.ext; unfold tripleCharges sourceA515 sourceB515 sourceC515 difference raw9022; decide +kernel
    rw [ha]
    exact (canonical9022 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA515 + sourceB515) sourceC515) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA515 + sourceB515) sourceC515) = raw9013 := by
      apply Matrix.ext; unfold doubleCharges sourceA515 sourceB515 sourceC515 raw9013; decide +kernel
    rw [ha]
    exact (canonical9013 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA515 sourceB515 sourceC515
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm515, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic26
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reindexCheck416 : Integer.Sparse.reindex keyMap MixedData.row416 = numericRow416 := by decide +kernel

theorem numericCheck416 (x : Master → ℝ) : Integer.Sparse.eval numericRow416 x =
    (1 : ℝ) * reducedSource416 x := by
  norm_num [numericRow416, reducedSource416, Integer.Sparse.eval, Sparse.eval, nodeValue2495, nodeValue2759, nodeValue2974, nodeValue2979, nodeValue3054, nodeValue3813, nodeValue4092]

theorem reindexCheck420 : Integer.Sparse.reindex keyMap MixedData.row420 = numericRow420 := by decide +kernel

theorem numericCheck420 (x : Master → ℝ) : Integer.Sparse.eval numericRow420 x =
    (1 : ℝ) * reducedSource420 x := by
  norm_num [numericRow420, reducedSource420, Integer.Sparse.eval, Sparse.eval, nodeValue2751, nodeValue3846, nodeValue3881, nodeValue3902, nodeValue3910, nodeValue4091]

theorem reindexCheck421 : Integer.Sparse.reindex keyMap MixedData.row421 = numericRow421 := by decide +kernel

theorem numericCheck421 (x : Master → ℝ) : Integer.Sparse.eval numericRow421 x =
    (1 : ℝ) * reducedSource421 x := by
  norm_num [numericRow421, reducedSource421, Integer.Sparse.eval, Sparse.eval, nodeValue1247, nodeValue1249, nodeValue1253, nodeValue1262, nodeValue2751, nodeValue4091]

theorem reindexCheck422 : Integer.Sparse.reindex keyMap MixedData.row422 = numericRow422 := by decide +kernel

theorem numericCheck422 (x : Master → ℝ) : Integer.Sparse.eval numericRow422 x =
    (1 : ℝ) * reducedSource422 x := by
  norm_num [numericRow422, reducedSource422, Integer.Sparse.eval, Sparse.eval, nodeValue2562, nodeValue2564, nodeValue2567, nodeValue2751, nodeValue3846, nodeValue4091]

theorem reindexCheck423 : Integer.Sparse.reindex keyMap MixedData.row423 = numericRow423 := by decide +kernel

theorem numericCheck423 (x : Master → ℝ) : Integer.Sparse.eval numericRow423 x =
    (1 : ℝ) * reducedSource423 x := by
  norm_num [numericRow423, reducedSource423, Integer.Sparse.eval, Sparse.eval, nodeValue1262, nodeValue2567, nodeValue2633, nodeValue2723, nodeValue2751, nodeValue2764, nodeValue4091]

theorem reindexCheck424 : Integer.Sparse.reindex keyMap MixedData.row424 = numericRow424 := by decide +kernel

theorem numericCheck424 (x : Master → ℝ) : Integer.Sparse.eval numericRow424 x =
    (1 : ℝ) * reducedSource424 x := by
  norm_num [numericRow424, reducedSource424, Integer.Sparse.eval, Sparse.eval, nodeValue2622, nodeValue2624, nodeValue2627, nodeValue2633, nodeValue2751, nodeValue3881, nodeValue4091]

theorem reindexCheck425 : Integer.Sparse.reindex keyMap MixedData.row425 = numericRow425 := by decide +kernel

theorem numericCheck425 (x : Master → ℝ) : Integer.Sparse.eval numericRow425 x =
    (1 : ℝ) * reducedSource425 x := by
  norm_num [numericRow425, reducedSource425, Integer.Sparse.eval, Sparse.eval, nodeValue1253, nodeValue2564, nodeValue2627, nodeValue2751, nodeValue2754, nodeValue4091]

theorem reindexCheck426 : Integer.Sparse.reindex keyMap MixedData.row426 = numericRow426 := by decide +kernel

theorem numericCheck426 (x : Master → ℝ) : Integer.Sparse.eval numericRow426 x =
    (17280 : ℝ) * reducedSource426 x := by
  norm_num [numericRow426, reducedSource426, Integer.Sparse.eval, Sparse.eval, nodeValue4436, nodeValue4437, nodeValue4444, nodeValue4453, nodeValue5064, nodeValue5067, nodeValue5071, nodeValue5145, nodeValue5147, nodeValue5152, nodeValue5164, nodeValue5220, nodeValue5222, nodeValue5229, nodeValue5281, nodeValue5284, nodeValue5289, nodeValue5448, nodeValue5471, nodeValue5473, nodeValue5485] <;> ring

theorem reindexCheck429 : Integer.Sparse.reindex keyMap MixedData.row429 = numericRow429 := by decide +kernel

theorem numericCheck429 (x : Master → ℝ) : Integer.Sparse.eval numericRow429 x =
    (1 : ℝ) * reducedSource429 x := by
  norm_num [numericRow429, reducedSource429, Integer.Sparse.eval, Sparse.eval, nodeValue3078, nodeValue3885, nodeValue3953, nodeValue3958, nodeValue4010, nodeValue4091]

theorem reindexCheck430 : Integer.Sparse.reindex keyMap MixedData.row430 = numericRow430 := by decide +kernel

theorem numericCheck430 (x : Master → ℝ) : Integer.Sparse.eval numericRow430 x =
    (1 : ℝ) * reducedSource430 x := by
  norm_num [numericRow430, reducedSource430, Integer.Sparse.eval, Sparse.eval, nodeValue1384, nodeValue1389, nodeValue1391, nodeValue1407, nodeValue3078, nodeValue4091]

theorem reindexCheck431 : Integer.Sparse.reindex keyMap MixedData.row431 = numericRow431 := by decide +kernel

theorem numericCheck431 (x : Master → ℝ) : Integer.Sparse.eval numericRow431 x =
    (1 : ℝ) * reducedSource431 x := by
  norm_num [numericRow431, reducedSource431, Integer.Sparse.eval, Sparse.eval, nodeValue1384, nodeValue2925, nodeValue3068, nodeValue3074, nodeValue3078, nodeValue4091]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Rows26
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero416 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource416 (mixedVector B) = 0 := by
  have h2495 : mixedVector B (Sum.inr 2495) = Sparse.eval nodeValue2495 (mixedVector B) := by
    change mixedMoment B node2495 node2495Labels = _
    exact sound2495 B hB hF
  have h2759 : mixedVector B (Sum.inr 2759) = Sparse.eval nodeValue2759 (mixedVector B) := by
    change mixedMoment B node2759 node2759Labels = _
    exact sound2759 B hB hF
  have h2974 : mixedVector B (Sum.inr 2974) = Sparse.eval nodeValue2974 (mixedVector B) := by
    change mixedMoment B node2974 node2974Labels = _
    exact sound2974 B hB hF
  have h2979 : mixedVector B (Sum.inr 2979) = Sparse.eval nodeValue2979 (mixedVector B) := by
    change mixedMoment B node2979 node2979Labels = _
    exact sound2979 B hB hF
  have h3054 : mixedVector B (Sum.inr 3054) = Sparse.eval nodeValue3054 (mixedVector B) := by
    change mixedMoment B node3054 node3054Labels = _
    exact sound3054 B hB hF
  have h3813 : mixedVector B (Sum.inr 3813) = Sparse.eval nodeValue3813 (mixedVector B) := by
    change mixedMoment B node3813 node3813Labels = _
    exact sound3813 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm498, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2495, h2759, h2974, h2979, h3054, h3813, h4092, reducedSource416] using sourceEq498 B hB

theorem rowSound416 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row416 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck416, numericCheck416, reducedZero416 B hB hF, mul_zero]

theorem reducedZero420 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource420 (mixedVector B) = 0 := by
  have h2751 : mixedVector B (Sum.inr 2751) = Sparse.eval nodeValue2751 (mixedVector B) := by
    change mixedMoment B node2751 node2751Labels = _
    exact sound2751 B hB hF
  have h3846 : mixedVector B (Sum.inr 3846) = Sparse.eval nodeValue3846 (mixedVector B) := by
    change mixedMoment B node3846 node3846Labels = _
    exact sound3846 B hB hF
  have h3881 : mixedVector B (Sum.inr 3881) = Sparse.eval nodeValue3881 (mixedVector B) := by
    change mixedMoment B node3881 node3881Labels = _
    exact sound3881 B hB hF
  have h3902 : mixedVector B (Sum.inr 3902) = Sparse.eval nodeValue3902 (mixedVector B) := by
    change mixedMoment B node3902 node3902Labels = _
    exact sound3902 B hB hF
  have h3910 : mixedVector B (Sum.inr 3910) = Sparse.eval nodeValue3910 (mixedVector B) := by
    change mixedMoment B node3910 node3910Labels = _
    exact sound3910 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm504, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2751, h3846, h3881, h3902, h3910, h4091, reducedSource420] using sourceEq504 B hB

theorem rowSound420 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row420 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck420, numericCheck420, reducedZero420 B hB hF, mul_zero]

theorem reducedZero421 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource421 (mixedVector B) = 0 := by
  have h1247 : mixedVector B (Sum.inr 1247) = Sparse.eval nodeValue1247 (mixedVector B) := by
    change mixedMoment B node1247 node1247Labels = _
    exact sound1247 B hB hF
  have h1249 : mixedVector B (Sum.inr 1249) = Sparse.eval nodeValue1249 (mixedVector B) := by
    change mixedMoment B node1249 node1249Labels = _
    exact sound1249 B hB hF
  have h1253 : mixedVector B (Sum.inr 1253) = Sparse.eval nodeValue1253 (mixedVector B) := by
    change mixedMoment B node1253 node1253Labels = _
    exact sound1253 B hB hF
  have h1262 : mixedVector B (Sum.inr 1262) = Sparse.eval nodeValue1262 (mixedVector B) := by
    change mixedMoment B node1262 node1262Labels = _
    exact sound1262 B hB hF
  have h2751 : mixedVector B (Sum.inr 2751) = Sparse.eval nodeValue2751 (mixedVector B) := by
    change mixedMoment B node2751 node2751Labels = _
    exact sound2751 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm505, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1247, h1249, h1253, h1262, h2751, h4091, reducedSource421] using sourceEq505 B hB

theorem rowSound421 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row421 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck421, numericCheck421, reducedZero421 B hB hF, mul_zero]

theorem reducedZero422 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource422 (mixedVector B) = 0 := by
  have h2562 : mixedVector B (Sum.inr 2562) = Sparse.eval nodeValue2562 (mixedVector B) := by
    change mixedMoment B node2562 node2562Labels = _
    exact sound2562 B hB hF
  have h2564 : mixedVector B (Sum.inr 2564) = Sparse.eval nodeValue2564 (mixedVector B) := by
    change mixedMoment B node2564 node2564Labels = _
    exact sound2564 B hB hF
  have h2567 : mixedVector B (Sum.inr 2567) = Sparse.eval nodeValue2567 (mixedVector B) := by
    change mixedMoment B node2567 node2567Labels = _
    exact sound2567 B hB hF
  have h2751 : mixedVector B (Sum.inr 2751) = Sparse.eval nodeValue2751 (mixedVector B) := by
    change mixedMoment B node2751 node2751Labels = _
    exact sound2751 B hB hF
  have h3846 : mixedVector B (Sum.inr 3846) = Sparse.eval nodeValue3846 (mixedVector B) := by
    change mixedMoment B node3846 node3846Labels = _
    exact sound3846 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm506, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2562, h2564, h2567, h2751, h3846, h4091, reducedSource422] using sourceEq506 B hB

theorem rowSound422 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row422 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck422, numericCheck422, reducedZero422 B hB hF, mul_zero]

theorem reducedZero423 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource423 (mixedVector B) = 0 := by
  have h1262 : mixedVector B (Sum.inr 1262) = Sparse.eval nodeValue1262 (mixedVector B) := by
    change mixedMoment B node1262 node1262Labels = _
    exact sound1262 B hB hF
  have h2567 : mixedVector B (Sum.inr 2567) = Sparse.eval nodeValue2567 (mixedVector B) := by
    change mixedMoment B node2567 node2567Labels = _
    exact sound2567 B hB hF
  have h2633 : mixedVector B (Sum.inr 2633) = Sparse.eval nodeValue2633 (mixedVector B) := by
    change mixedMoment B node2633 node2633Labels = _
    exact sound2633 B hB hF
  have h2723 : mixedVector B (Sum.inr 2723) = Sparse.eval nodeValue2723 (mixedVector B) := by
    change mixedMoment B node2723 node2723Labels = _
    exact sound2723 B hB hF
  have h2751 : mixedVector B (Sum.inr 2751) = Sparse.eval nodeValue2751 (mixedVector B) := by
    change mixedMoment B node2751 node2751Labels = _
    exact sound2751 B hB hF
  have h2764 : mixedVector B (Sum.inr 2764) = Sparse.eval nodeValue2764 (mixedVector B) := by
    change mixedMoment B node2764 node2764Labels = _
    exact sound2764 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm507, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1262, h2567, h2633, h2723, h2751, h2764, h4091, reducedSource423] using sourceEq507 B hB

theorem rowSound423 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row423 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck423, numericCheck423, reducedZero423 B hB hF, mul_zero]

theorem reducedZero424 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource424 (mixedVector B) = 0 := by
  have h2622 : mixedVector B (Sum.inr 2622) = Sparse.eval nodeValue2622 (mixedVector B) := by
    change mixedMoment B node2622 node2622Labels = _
    exact sound2622 B hB hF
  have h2624 : mixedVector B (Sum.inr 2624) = Sparse.eval nodeValue2624 (mixedVector B) := by
    change mixedMoment B node2624 node2624Labels = _
    exact sound2624 B hB hF
  have h2627 : mixedVector B (Sum.inr 2627) = Sparse.eval nodeValue2627 (mixedVector B) := by
    change mixedMoment B node2627 node2627Labels = _
    exact sound2627 B hB hF
  have h2633 : mixedVector B (Sum.inr 2633) = Sparse.eval nodeValue2633 (mixedVector B) := by
    change mixedMoment B node2633 node2633Labels = _
    exact sound2633 B hB hF
  have h2751 : mixedVector B (Sum.inr 2751) = Sparse.eval nodeValue2751 (mixedVector B) := by
    change mixedMoment B node2751 node2751Labels = _
    exact sound2751 B hB hF
  have h3881 : mixedVector B (Sum.inr 3881) = Sparse.eval nodeValue3881 (mixedVector B) := by
    change mixedMoment B node3881 node3881Labels = _
    exact sound3881 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm508, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2622, h2624, h2627, h2633, h2751, h3881, h4091, reducedSource424] using sourceEq508 B hB

theorem rowSound424 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row424 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck424, numericCheck424, reducedZero424 B hB hF, mul_zero]

theorem reducedZero425 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource425 (mixedVector B) = 0 := by
  have h1253 : mixedVector B (Sum.inr 1253) = Sparse.eval nodeValue1253 (mixedVector B) := by
    change mixedMoment B node1253 node1253Labels = _
    exact sound1253 B hB hF
  have h2564 : mixedVector B (Sum.inr 2564) = Sparse.eval nodeValue2564 (mixedVector B) := by
    change mixedMoment B node2564 node2564Labels = _
    exact sound2564 B hB hF
  have h2627 : mixedVector B (Sum.inr 2627) = Sparse.eval nodeValue2627 (mixedVector B) := by
    change mixedMoment B node2627 node2627Labels = _
    exact sound2627 B hB hF
  have h2751 : mixedVector B (Sum.inr 2751) = Sparse.eval nodeValue2751 (mixedVector B) := by
    change mixedMoment B node2751 node2751Labels = _
    exact sound2751 B hB hF
  have h2754 : mixedVector B (Sum.inr 2754) = Sparse.eval nodeValue2754 (mixedVector B) := by
    change mixedMoment B node2754 node2754Labels = _
    exact sound2754 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm509, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1253, h2564, h2627, h2751, h2754, h4091, reducedSource425] using sourceEq509 B hB

theorem rowSound425 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row425 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck425, numericCheck425, reducedZero425 B hB hF, mul_zero]

theorem reducedZero426 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource426 (mixedVector B) = 0 := by
  have h4436 : mixedVector B (Sum.inr 4436) = Sparse.eval nodeValue4436 (mixedVector B) := by
    change mixedMoment B node4436 node4436Labels = _
    exact sound4436 B hB hF
  have h4437 : mixedVector B (Sum.inr 4437) = Sparse.eval nodeValue4437 (mixedVector B) := by
    change mixedMoment B node4437 node4437Labels = _
    exact sound4437 B hB hF
  have h4444 : mixedVector B (Sum.inr 4444) = Sparse.eval nodeValue4444 (mixedVector B) := by
    change mixedMoment B node4444 node4444Labels = _
    exact sound4444 B hB hF
  have h4453 : mixedVector B (Sum.inr 4453) = Sparse.eval nodeValue4453 (mixedVector B) := by
    change mixedMoment B node4453 node4453Labels = _
    exact sound4453 B hB hF
  have h5064 : mixedVector B (Sum.inr 5064) = Sparse.eval nodeValue5064 (mixedVector B) := by
    change mixedMoment B node5064 node5064Labels = _
    exact sound5064 B hB hF
  have h5067 : mixedVector B (Sum.inr 5067) = Sparse.eval nodeValue5067 (mixedVector B) := by
    change mixedMoment B node5067 node5067Labels = _
    exact sound5067 B hB hF
  have h5071 : mixedVector B (Sum.inr 5071) = Sparse.eval nodeValue5071 (mixedVector B) := by
    change mixedMoment B node5071 node5071Labels = _
    exact sound5071 B hB hF
  have h5145 : mixedVector B (Sum.inr 5145) = Sparse.eval nodeValue5145 (mixedVector B) := by
    change mixedMoment B node5145 node5145Labels = _
    exact sound5145 B hB hF
  have h5147 : mixedVector B (Sum.inr 5147) = Sparse.eval nodeValue5147 (mixedVector B) := by
    change mixedMoment B node5147 node5147Labels = _
    exact sound5147 B hB hF
  have h5152 : mixedVector B (Sum.inr 5152) = Sparse.eval nodeValue5152 (mixedVector B) := by
    change mixedMoment B node5152 node5152Labels = _
    exact sound5152 B hB hF
  have h5164 : mixedVector B (Sum.inr 5164) = Sparse.eval nodeValue5164 (mixedVector B) := by
    change mixedMoment B node5164 node5164Labels = _
    exact sound5164 B hB hF
  have h5220 : mixedVector B (Sum.inr 5220) = Sparse.eval nodeValue5220 (mixedVector B) := by
    change mixedMoment B node5220 node5220Labels = _
    exact sound5220 B hB hF
  have h5222 : mixedVector B (Sum.inr 5222) = Sparse.eval nodeValue5222 (mixedVector B) := by
    change mixedMoment B node5222 node5222Labels = _
    exact sound5222 B hB hF
  have h5229 : mixedVector B (Sum.inr 5229) = Sparse.eval nodeValue5229 (mixedVector B) := by
    change mixedMoment B node5229 node5229Labels = _
    exact sound5229 B hB hF
  have h5281 : mixedVector B (Sum.inr 5281) = Sparse.eval nodeValue5281 (mixedVector B) := by
    change mixedMoment B node5281 node5281Labels = _
    exact sound5281 B hB hF
  have h5284 : mixedVector B (Sum.inr 5284) = Sparse.eval nodeValue5284 (mixedVector B) := by
    change mixedMoment B node5284 node5284Labels = _
    exact sound5284 B hB hF
  have h5289 : mixedVector B (Sum.inr 5289) = Sparse.eval nodeValue5289 (mixedVector B) := by
    change mixedMoment B node5289 node5289Labels = _
    exact sound5289 B hB hF
  have h5448 : mixedVector B (Sum.inr 5448) = Sparse.eval nodeValue5448 (mixedVector B) := by
    change mixedMoment B node5448 node5448Labels = _
    exact sound5448 B hB hF
  have h5471 : mixedVector B (Sum.inr 5471) = Sparse.eval nodeValue5471 (mixedVector B) := by
    change mixedMoment B node5471 node5471Labels = _
    exact sound5471 B hB hF
  have h5473 : mixedVector B (Sum.inr 5473) = Sparse.eval nodeValue5473 (mixedVector B) := by
    change mixedMoment B node5473 node5473Labels = _
    exact sound5473 B hB hF
  have h5485 : mixedVector B (Sum.inr 5485) = Sparse.eval nodeValue5485 (mixedVector B) := by
    change mixedMoment B node5485 node5485Labels = _
    exact sound5485_e B hB hF
  simpa only [sourceForm510, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4436, h4437, h4444, h4453, h5064, h5067, h5071, h5145, h5147, h5152, h5164, h5220, h5222, h5229, h5281, h5284, h5289, h5448, h5471, h5473, h5485, reducedSource426] using sourceEq510 B hB

theorem rowSound426 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row426 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck426, numericCheck426, reducedZero426 B hB hF, mul_zero]

theorem reducedZero429 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource429 (mixedVector B) = 0 := by
  have h3078 : mixedVector B (Sum.inr 3078) = Sparse.eval nodeValue3078 (mixedVector B) := by
    change mixedMoment B node3078 node3078Labels = _
    exact sound3078 B hB hF
  have h3885 : mixedVector B (Sum.inr 3885) = Sparse.eval nodeValue3885 (mixedVector B) := by
    change mixedMoment B node3885 node3885Labels = _
    exact sound3885 B hB hF
  have h3953 : mixedVector B (Sum.inr 3953) = Sparse.eval nodeValue3953 (mixedVector B) := by
    change mixedMoment B node3953 node3953Labels = _
    exact sound3953 B hB hF
  have h3958 : mixedVector B (Sum.inr 3958) = Sparse.eval nodeValue3958 (mixedVector B) := by
    change mixedMoment B node3958 node3958Labels = _
    exact sound3958 B hB hF
  have h4010 : mixedVector B (Sum.inr 4010) = Sparse.eval nodeValue4010 (mixedVector B) := by
    change mixedMoment B node4010 node4010Labels = _
    exact sound4010 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm513, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h3078, h3885, h3953, h3958, h4010, h4091, reducedSource429] using sourceEq513 B hB

theorem rowSound429 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row429 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck429, numericCheck429, reducedZero429 B hB hF, mul_zero]

theorem reducedZero430 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource430 (mixedVector B) = 0 := by
  have h1384 : mixedVector B (Sum.inr 1384) = Sparse.eval nodeValue1384 (mixedVector B) := by
    change mixedMoment B node1384 node1384Labels = _
    exact sound1384 B hB hF
  have h1389 : mixedVector B (Sum.inr 1389) = Sparse.eval nodeValue1389 (mixedVector B) := by
    change mixedMoment B node1389 node1389Labels = _
    exact sound1389 B hB hF
  have h1391 : mixedVector B (Sum.inr 1391) = Sparse.eval nodeValue1391 (mixedVector B) := by
    change mixedMoment B node1391 node1391Labels = _
    exact sound1391 B hB hF
  have h1407 : mixedVector B (Sum.inr 1407) = Sparse.eval nodeValue1407 (mixedVector B) := by
    change mixedMoment B node1407 node1407Labels = _
    exact sound1407 B hB hF
  have h3078 : mixedVector B (Sum.inr 3078) = Sparse.eval nodeValue3078 (mixedVector B) := by
    change mixedMoment B node3078 node3078Labels = _
    exact sound3078 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm514, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1384, h1389, h1391, h1407, h3078, h4091, reducedSource430] using sourceEq514 B hB

theorem rowSound430 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row430 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck430, numericCheck430, reducedZero430 B hB hF, mul_zero]

theorem reducedZero431 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource431 (mixedVector B) = 0 := by
  have h1384 : mixedVector B (Sum.inr 1384) = Sparse.eval nodeValue1384 (mixedVector B) := by
    change mixedMoment B node1384 node1384Labels = _
    exact sound1384 B hB hF
  have h2925 : mixedVector B (Sum.inr 2925) = Sparse.eval nodeValue2925 (mixedVector B) := by
    change mixedMoment B node2925 node2925Labels = _
    exact sound2925 B hB hF
  have h3068 : mixedVector B (Sum.inr 3068) = Sparse.eval nodeValue3068 (mixedVector B) := by
    change mixedMoment B node3068 node3068Labels = _
    exact sound3068 B hB hF
  have h3074 : mixedVector B (Sum.inr 3074) = Sparse.eval nodeValue3074 (mixedVector B) := by
    change mixedMoment B node3074 node3074Labels = _
    exact sound3074 B hB hF
  have h3078 : mixedVector B (Sum.inr 3078) = Sparse.eval nodeValue3078 (mixedVector B) := by
    change mixedMoment B node3078 node3078Labels = _
    exact sound3078 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm515, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1384, h2925, h3068, h3074, h3078, h4091, reducedSource431] using sourceEq515 B hB

theorem rowSound431 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row431 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck431, numericCheck431, reducedZero431 B hB hF, mul_zero]

theorem sourceRowsAt416 : MixedData.sourceRows (416 : Fin 2425) =
    MixedData.row416 := by decide +kernel

theorem sourceRowsAt417 : MixedData.sourceRows (417 : Fin 2425) =
    MixedData.row417 := by decide +kernel

theorem sourceRowsAt418 : MixedData.sourceRows (418 : Fin 2425) =
    MixedData.row418 := by decide +kernel

theorem sourceRowsAt419 : MixedData.sourceRows (419 : Fin 2425) =
    MixedData.row419 := by decide +kernel

theorem sourceRowsAt420 : MixedData.sourceRows (420 : Fin 2425) =
    MixedData.row420 := by decide +kernel

theorem sourceRowsAt421 : MixedData.sourceRows (421 : Fin 2425) =
    MixedData.row421 := by decide +kernel

theorem sourceRowsAt422 : MixedData.sourceRows (422 : Fin 2425) =
    MixedData.row422 := by decide +kernel

theorem sourceRowsAt423 : MixedData.sourceRows (423 : Fin 2425) =
    MixedData.row423 := by decide +kernel

theorem sourceRowsAt424 : MixedData.sourceRows (424 : Fin 2425) =
    MixedData.row424 := by decide +kernel

theorem sourceRowsAt425 : MixedData.sourceRows (425 : Fin 2425) =
    MixedData.row425 := by decide +kernel

theorem sourceRowsAt426 : MixedData.sourceRows (426 : Fin 2425) =
    MixedData.row426 := by decide +kernel

theorem sourceRowsAt427 : MixedData.sourceRows (427 : Fin 2425) =
    MixedData.row427 := by decide +kernel

theorem sourceRowsAt428 : MixedData.sourceRows (428 : Fin 2425) =
    MixedData.row428 := by decide +kernel

theorem sourceRowsAt429 : MixedData.sourceRows (429 : Fin 2425) =
    MixedData.row429 := by decide +kernel

theorem sourceRowsAt430 : MixedData.sourceRows (430 : Fin 2425) =
    MixedData.row430 := by decide +kernel

theorem sourceRowsAt431 : MixedData.sourceRows (431 : Fin 2425) =
    MixedData.row431 := by decide +kernel

theorem chunkSound26_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) (k : Fin 2425)
    (hk : k.val / 16 = 26) :
    Integer.Sparse.eval (MixedData.sourceRows k) (numericVector B) = 0 := by
  have heq : k.val = 416 ∨ k.val = 417 ∨ k.val = 418 ∨ k.val = 419 ∨ k.val = 420 ∨ k.val = 421 ∨ k.val = 422 ∨ k.val = 423 ∨ k.val = 424 ∨ k.val = 425 ∨ k.val = 426 ∨ k.val = 427 ∨ k.val = 428 ∨ k.val = 429 ∨ k.val = 430 ∨ k.val = 431 := by omega
  rcases heq with h416 | h417 | h418 | h419 | h420 | h421 | h422 | h423 | h424 | h425 | h426 | h427 | h428 | h429 | h430 | h431
  · have he : k = (416 : Fin 2425) := Fin.ext h416
    subst k
    rw [sourceRowsAt416]
    exact rowSound416 B hB hF
  · have he : k = (417 : Fin 2425) := Fin.ext h417
    subst k
    rw [sourceRowsAt417]
    exact rowSound417_e B hB hF
  · have he : k = (418 : Fin 2425) := Fin.ext h418
    subst k
    rw [sourceRowsAt418]
    exact rowSound418_e B hB hF
  · have he : k = (419 : Fin 2425) := Fin.ext h419
    subst k
    rw [sourceRowsAt419]
    exact rowSound419_e B hB hF
  · have he : k = (420 : Fin 2425) := Fin.ext h420
    subst k
    rw [sourceRowsAt420]
    exact rowSound420 B hB hF
  · have he : k = (421 : Fin 2425) := Fin.ext h421
    subst k
    rw [sourceRowsAt421]
    exact rowSound421 B hB hF
  · have he : k = (422 : Fin 2425) := Fin.ext h422
    subst k
    rw [sourceRowsAt422]
    exact rowSound422 B hB hF
  · have he : k = (423 : Fin 2425) := Fin.ext h423
    subst k
    rw [sourceRowsAt423]
    exact rowSound423 B hB hF
  · have he : k = (424 : Fin 2425) := Fin.ext h424
    subst k
    rw [sourceRowsAt424]
    exact rowSound424 B hB hF
  · have he : k = (425 : Fin 2425) := Fin.ext h425
    subst k
    rw [sourceRowsAt425]
    exact rowSound425 B hB hF
  · have he : k = (426 : Fin 2425) := Fin.ext h426
    subst k
    rw [sourceRowsAt426]
    exact rowSound426 B hB hF
  · have he : k = (427 : Fin 2425) := Fin.ext h427
    subst k
    rw [sourceRowsAt427]
    exact rowSound427_e B hB hF
  · have he : k = (428 : Fin 2425) := Fin.ext h428
    subst k
    rw [sourceRowsAt428]
    exact rowSound428_e B hB hF
  · have he : k = (429 : Fin 2425) := Fin.ext h429
    subst k
    rw [sourceRowsAt429]
    exact rowSound429 B hB hF
  · have he : k = (430 : Fin 2425) := Fin.ext h430
    subst k
    rw [sourceRowsAt430]
    exact rowSound430 B hB hF
  · have he : k = (431 : Fin 2425) := Fin.ext h431
    subst k
    rw [sourceRowsAt431]
    exact rowSound431 B hB hF

end MUB6.Certificate.MixedSourceBridge

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedSourceBridge.chunkSound26_e_oai := @OAI.MUB6.Certificate.MixedSourceBridge.chunkSound26_e_oai
