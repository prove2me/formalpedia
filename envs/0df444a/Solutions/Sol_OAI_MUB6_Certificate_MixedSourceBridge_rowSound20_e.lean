-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedSourceBridge.rowSound20_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-08T22:40:52.836206+00:00
-- url     : https://prove2.me/submissions/af3b11bc-de5f-4edd-9286-6b18f241a71a

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E070
import Definitions.Def_OAIQ106E086
import Definitions.Def_OAIQ106E195
import Definitions.Def_OAIQ106E101
import Definitions.Def_OAIQ106E106
import Definitions.Def_OAIQ106E119
import Definitions.Def_OAIQ106E121
import Definitions.Def_OAIQ106E126
import Definitions.Def_OAIQ106E140
import Definitions.Def_OAIQ106E147
import Definitions.Def_OAIQ106E170
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound5433_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound5434_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound5435_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound5450_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound5490_e
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical19
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical2520 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2520 raw2520Labels = mixedMoment B node5431 node5431Labels := by
  calc
    mixedMoment B raw2520 raw2520Labels = mixedMoment B raw2520step0 raw2520step0Labels := by
      have ha : raw2520step0 = (fun i j => raw2520 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2520step0 raw2520; decide +kernel
      have hl : raw2520step0Labels = raw2520Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2520 raw2520Labels permutation152 permutation4
    mixedMoment B raw2520step0 raw2520step0Labels = mixedMoment B raw2520step1 raw2520step1Labels := by
      have ha : raw2520step1 = raw2520step0 := by apply Matrix.ext; unfold raw2520step1 raw2520step0; decide +kernel
      have hl : raw2520step0Labels = labelEmbedding7 ∘ raw2520step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2520step0 raw2520step0Labels raw2520step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5431 node5431Labels := by rfl

theorem canonical2521 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2521 raw2521Labels = mixedMoment B node3849 node3849Labels := by
  calc
    mixedMoment B raw2521 raw2521Labels = mixedMoment B raw2521step0 raw2521step0Labels := by
      have ha : raw2521step0 = (fun i j => raw2521 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2521step0 raw2521; decide +kernel
      have hl : raw2521step0Labels = raw2521Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2521 raw2521Labels permutation152 permutation4
    _ = mixedMoment B node3849 node3849Labels := by rfl

theorem canonical2522 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2522 raw2522Labels = mixedMoment B node3875 node3875Labels := by
  calc
    mixedMoment B raw2522 raw2522Labels = mixedMoment B raw2522step0 raw2522step0Labels := by
      have ha : raw2522step0 = (fun i j => raw2522 (permutation200 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2522step0 raw2522; decide +kernel
      have hl : raw2522step0Labels = raw2522Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2522 raw2522Labels permutation200 permutation6
    mixedMoment B raw2522step0 raw2522step0Labels = mixedMoment B raw2522step1 raw2522step1Labels := by
      have ha : raw2522step1 = -raw2522step0 := by apply Matrix.ext; change ∀ i j, raw2522step1 i j = -(raw2522step0 i j); unfold raw2522step1 raw2522step0; decide +kernel
      have hl : raw2522step1Labels = raw2522step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2522step1 raw2522step1Labels = mixedMoment B raw2522step2 raw2522step2Labels := by
      have ha : raw2522step2 = raw2522step1 := by apply Matrix.ext; unfold raw2522step2 raw2522step1; decide +kernel
      have hl : raw2522step1Labels = labelEmbedding1 ∘ raw2522step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2522step1 raw2522step1Labels raw2522step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3875 node3875Labels := by rfl

theorem canonical2523 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2523 raw2523Labels = mixedMoment B node5432 node5432Labels := by
  calc
    mixedMoment B raw2523 raw2523Labels = mixedMoment B raw2523step0 raw2523step0Labels := by
      have ha : raw2523step0 = (fun i j => raw2523 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2523step0 raw2523; decide +kernel
      have hl : raw2523step0Labels = raw2523Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2523 raw2523Labels permutation32 permutation4
    mixedMoment B raw2523step0 raw2523step0Labels = mixedMoment B raw2523step1 raw2523step1Labels := by
      have ha : raw2523step1 = raw2523step0 := by apply Matrix.ext; unfold raw2523step1 raw2523step0; decide +kernel
      have hl : raw2523step0Labels = labelEmbedding7 ∘ raw2523step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2523step0 raw2523step0Labels raw2523step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5432 node5432Labels := by rfl

theorem canonical2524 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2524 raw2524Labels = mixedMoment B node3850 node3850Labels := by
  calc
    mixedMoment B raw2524 raw2524Labels = mixedMoment B raw2524step0 raw2524step0Labels := by
      have ha : raw2524step0 = (fun i j => raw2524 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2524step0 raw2524; decide +kernel
      have hl : raw2524step0Labels = raw2524Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2524 raw2524Labels permutation32 permutation4
    _ = mixedMoment B node3850 node3850Labels := by rfl

theorem canonical2525 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2525 raw2525Labels = mixedMoment B node3850 node3850Labels := by
  calc
    mixedMoment B raw2525 raw2525Labels = mixedMoment B raw2525step0 raw2525step0Labels := by
      have ha : raw2525step0 = (fun i j => raw2525 (permutation143 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2525step0 raw2525; decide +kernel
      have hl : raw2525step0Labels = raw2525Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2525 raw2525Labels permutation143 permutation6
    mixedMoment B raw2525step0 raw2525step0Labels = mixedMoment B raw2525step1 raw2525step1Labels := by
      have ha : raw2525step1 = raw2525step0 := by apply Matrix.ext; unfold raw2525step1 raw2525step0; decide +kernel
      have hl : raw2525step0Labels = labelEmbedding1 ∘ raw2525step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2525step0 raw2525step0Labels raw2525step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3850 node3850Labels := by rfl

theorem canonical2538 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2538 raw2538Labels = mixedMoment B node5438 node5438Labels := by
  calc
    mixedMoment B raw2538 raw2538Labels = mixedMoment B raw2538step0 raw2538step0Labels := by
      have ha : raw2538step0 = (fun i j => raw2538 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2538step0 raw2538; decide +kernel
      have hl : raw2538step0Labels = raw2538Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2538 raw2538Labels permutation32 permutation4
    mixedMoment B raw2538step0 raw2538step0Labels = mixedMoment B raw2538step1 raw2538step1Labels := by
      have ha : raw2538step1 = raw2538step0 := by apply Matrix.ext; unfold raw2538step1 raw2538step0; decide +kernel
      have hl : raw2538step0Labels = labelEmbedding7 ∘ raw2538step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2538step0 raw2538step0Labels raw2538step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5438 node5438Labels := by rfl

theorem canonical2539 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2539 raw2539Labels = mixedMoment B node3857 node3857Labels := by
  calc
    mixedMoment B raw2539 raw2539Labels = mixedMoment B raw2539step0 raw2539step0Labels := by
      have ha : raw2539step0 = (fun i j => raw2539 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2539step0 raw2539; decide +kernel
      have hl : raw2539step0Labels = raw2539Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2539 raw2539Labels permutation32 permutation4
    _ = mixedMoment B node3857 node3857Labels := by rfl

theorem canonical2540 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2540 raw2540Labels = mixedMoment B node3876 node3876Labels := by
  calc
    mixedMoment B raw2540 raw2540Labels = mixedMoment B raw2540step0 raw2540step0Labels := by
      have ha : raw2540step0 = (fun i j => raw2540 (permutation38 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2540step0 raw2540; decide +kernel
      have hl : raw2540step0Labels = raw2540Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2540 raw2540Labels permutation38 permutation6
    mixedMoment B raw2540step0 raw2540step0Labels = mixedMoment B raw2540step1 raw2540step1Labels := by
      have ha : raw2540step1 = -raw2540step0 := by apply Matrix.ext; change ∀ i j, raw2540step1 i j = -(raw2540step0 i j); unfold raw2540step1 raw2540step0; decide +kernel
      have hl : raw2540step1Labels = raw2540step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2540step1 raw2540step1Labels = mixedMoment B raw2540step2 raw2540step2Labels := by
      have ha : raw2540step2 = raw2540step1 := by apply Matrix.ext; unfold raw2540step2 raw2540step1; decide +kernel
      have hl : raw2540step1Labels = labelEmbedding1 ∘ raw2540step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2540step1 raw2540step1Labels raw2540step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3876 node3876Labels := by rfl

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

theorem canonical2607 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2607 raw2607Labels = mixedMoment B node5484 node5484Labels := by
  calc
    mixedMoment B raw2607 raw2607Labels = mixedMoment B raw2607step0 raw2607step0Labels := by
      have ha : raw2607step0 = (fun i j => raw2607 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2607step0 raw2607; decide +kernel
      have hl : raw2607step0Labels = raw2607Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2607 raw2607Labels permutation32 permutation4
    mixedMoment B raw2607step0 raw2607step0Labels = mixedMoment B raw2607step1 raw2607step1Labels := by
      have ha : raw2607step1 = raw2607step0 := by apply Matrix.ext; unfold raw2607step1 raw2607step0; decide +kernel
      have hl : raw2607step0Labels = labelEmbedding7 ∘ raw2607step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2607step0 raw2607step0Labels raw2607step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5484 node5484Labels := by rfl

theorem canonical2608 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2608 raw2608Labels = mixedMoment B node3983 node3983Labels := by
  calc
    mixedMoment B raw2608 raw2608Labels = mixedMoment B raw2608step0 raw2608step0Labels := by
      have ha : raw2608step0 = (fun i j => raw2608 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2608step0 raw2608; decide +kernel
      have hl : raw2608step0Labels = raw2608Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2608 raw2608Labels permutation32 permutation4
    _ = mixedMoment B node3983 node3983Labels := by rfl

theorem canonical2609 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2609 raw2609Labels = mixedMoment B node3983 node3983Labels := by
  calc
    mixedMoment B raw2609 raw2609Labels = mixedMoment B raw2609step0 raw2609step0Labels := by
      have ha : raw2609step0 = (fun i j => raw2609 (permutation151 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2609step0 raw2609; decide +kernel
      have hl : raw2609step0Labels = raw2609Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2609 raw2609Labels permutation151 permutation6
    mixedMoment B raw2609step0 raw2609step0Labels = mixedMoment B raw2609step1 raw2609step1Labels := by
      have ha : raw2609step1 = raw2609step0 := by apply Matrix.ext; unfold raw2609step1 raw2609step0; decide +kernel
      have hl : raw2609step0Labels = labelEmbedding1 ∘ raw2609step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2609step0 raw2609step0Labels raw2609step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3983 node3983Labels := by rfl

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

theorem canonical3179 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3179 raw3179Labels = mixedMoment B node5435 node5435Labels := by
  calc
    mixedMoment B raw3179 raw3179Labels = mixedMoment B raw3179step0 raw3179step0Labels := by
      have hz : ∀ j, raw3179 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3179step0 = (fun i j => raw3179 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3179step0 raw3179; decide +kernel
      have hl : raw3179step0Labels = raw3179Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3179 raw3179Labels permutation346 hz
    mixedMoment B raw3179step0 raw3179step0Labels = mixedMoment B raw3179step1 raw3179step1Labels := by
      have ha : raw3179step1 = (fun i j => raw3179step0 (permutation43 i) (permutation2 j)) := by apply Matrix.ext; unfold raw3179step1 raw3179step0; decide +kernel
      have hl : raw3179step1Labels = raw3179step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3179step0 raw3179step0Labels permutation43 permutation2
    mixedMoment B raw3179step1 raw3179step1Labels = mixedMoment B raw3179step2 raw3179step2Labels := by
      have ha : raw3179step2 = -raw3179step1 := by apply Matrix.ext; change ∀ i j, raw3179step2 i j = -(raw3179step1 i j); unfold raw3179step2 raw3179step1; decide +kernel
      have hl : raw3179step2Labels = raw3179step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5435 node5435Labels := by rfl

theorem canonical3180 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3180 raw3180Labels = mixedMoment B node5433 node5433Labels := by
  calc
    mixedMoment B raw3180 raw3180Labels = mixedMoment B raw3180step0 raw3180step0Labels := by
      have ha : raw3180step0 = (fun i j => raw3180 (permutation218 i) (permutation2 j)) := by apply Matrix.ext; unfold raw3180step0 raw3180; decide +kernel
      have hl : raw3180step0Labels = raw3180Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3180 raw3180Labels permutation218 permutation2
    mixedMoment B raw3180step0 raw3180step0Labels = mixedMoment B raw3180step1 raw3180step1Labels := by
      have ha : raw3180step1 = -raw3180step0 := by apply Matrix.ext; change ∀ i j, raw3180step1 i j = -(raw3180step0 i j); unfold raw3180step1 raw3180step0; decide +kernel
      have hl : raw3180step1Labels = raw3180step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5433 node5433Labels := by rfl

theorem canonical3181 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3181 raw3181Labels = mixedMoment B node5454 node5454Labels := by
  calc
    mixedMoment B raw3181 raw3181Labels = mixedMoment B raw3181step0 raw3181step0Labels := by
      have hz : ∀ j, raw3181 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3181step0 = (fun i j => raw3181 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3181step0 raw3181; decide +kernel
      have hl : raw3181step0Labels = raw3181Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3181 raw3181Labels permutation434 hz
    mixedMoment B raw3181step0 raw3181step0Labels = mixedMoment B raw3181step1 raw3181step1Labels := by
      have hz : ∀ j, raw3181step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw3181step1 = (fun i j => raw3181step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw3181step1 raw3181step0; decide +kernel
      have hl : raw3181step1Labels = raw3181step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3181step0 raw3181step0Labels permutation80 hz
    mixedMoment B raw3181step1 raw3181step1Labels = mixedMoment B raw3181step2 raw3181step2Labels := by
      have ha : raw3181step2 = (fun i j => raw3181step1 (permutation12 i) (permutation2 j)) := by apply Matrix.ext; unfold raw3181step2 raw3181step1; decide +kernel
      have hl : raw3181step2Labels = raw3181step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3181step1 raw3181step1Labels permutation12 permutation2
    mixedMoment B raw3181step2 raw3181step2Labels = mixedMoment B raw3181step3 raw3181step3Labels := by
      have ha : raw3181step3 = -raw3181step2 := by apply Matrix.ext; change ∀ i j, raw3181step3 i j = -(raw3181step2 i j); unfold raw3181step3 raw3181step2; decide +kernel
      have hl : raw3181step3Labels = raw3181step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5454 node5454Labels := by rfl

theorem canonical3182 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3182 raw3182Labels = mixedMoment B node5434 node5434Labels := by
  calc
    mixedMoment B raw3182 raw3182Labels = mixedMoment B raw3182step0 raw3182step0Labels := by
      have hz : ∀ j, raw3182 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3182step0 = (fun i j => raw3182 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3182step0 raw3182; decide +kernel
      have hl : raw3182step0Labels = raw3182Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3182 raw3182Labels permutation346 hz
    mixedMoment B raw3182step0 raw3182step0Labels = mixedMoment B raw3182step1 raw3182step1Labels := by
      have ha : raw3182step1 = (fun i j => raw3182step0 (permutation42 i) (permutation2 j)) := by apply Matrix.ext; unfold raw3182step1 raw3182step0; decide +kernel
      have hl : raw3182step1Labels = raw3182step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3182step0 raw3182step0Labels permutation42 permutation2
    mixedMoment B raw3182step1 raw3182step1Labels = mixedMoment B raw3182step2 raw3182step2Labels := by
      have ha : raw3182step2 = -raw3182step1 := by apply Matrix.ext; change ∀ i j, raw3182step2 i j = -(raw3182step1 i j); unfold raw3182step2 raw3182step1; decide +kernel
      have hl : raw3182step2Labels = raw3182step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5434 node5434Labels := by rfl

theorem canonical3183 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3183 raw3183Labels = mixedMoment B node5440 node5440Labels := by
  calc
    mixedMoment B raw3183 raw3183Labels = mixedMoment B raw3183step0 raw3183step0Labels := by
      have hz : ∀ j, raw3183 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3183step0 = (fun i j => raw3183 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3183step0 raw3183; decide +kernel
      have hl : raw3183step0Labels = raw3183Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3183 raw3183Labels permutation346 hz
    mixedMoment B raw3183step0 raw3183step0Labels = mixedMoment B raw3183step1 raw3183step1Labels := by
      have ha : raw3183step1 = (fun i j => raw3183step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw3183step1 raw3183step0; decide +kernel
      have hl : raw3183step1Labels = raw3183step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3183step0 raw3183step0Labels permutation38 permutation2
    mixedMoment B raw3183step1 raw3183step1Labels = mixedMoment B raw3183step2 raw3183step2Labels := by
      have ha : raw3183step2 = -raw3183step1 := by apply Matrix.ext; change ∀ i j, raw3183step2 i j = -(raw3183step1 i j); unfold raw3183step2 raw3183step1; decide +kernel
      have hl : raw3183step2Labels = raw3183step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5440 node5440Labels := by rfl

theorem canonical3184 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3184 raw3184Labels = mixedMoment B node5454 node5454Labels := by
  calc
    mixedMoment B raw3184 raw3184Labels = mixedMoment B raw3184step0 raw3184step0Labels := by
      have hz : ∀ j, raw3184 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3184step0 = (fun i j => raw3184 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3184step0 raw3184; decide +kernel
      have hl : raw3184step0Labels = raw3184Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3184 raw3184Labels permutation346 hz
    mixedMoment B raw3184step0 raw3184step0Labels = mixedMoment B raw3184step1 raw3184step1Labels := by
      have hz : ∀ j, raw3184step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw3184step1 = (fun i j => raw3184step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw3184step1 raw3184step0; decide +kernel
      have hl : raw3184step1Labels = raw3184step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3184step0 raw3184step0Labels permutation56 hz
    mixedMoment B raw3184step1 raw3184step1Labels = mixedMoment B raw3184step2 raw3184step2Labels := by
      have ha : raw3184step2 = (fun i j => raw3184step1 (permutation10 i) (permutation4 j)) := by apply Matrix.ext; unfold raw3184step2 raw3184step1; decide +kernel
      have hl : raw3184step2Labels = raw3184step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3184step1 raw3184step1Labels permutation10 permutation4
    mixedMoment B raw3184step2 raw3184step2Labels = mixedMoment B raw3184step3 raw3184step3Labels := by
      have ha : raw3184step3 = -raw3184step2 := by apply Matrix.ext; change ∀ i j, raw3184step3 i j = -(raw3184step2 i j); unfold raw3184step3 raw3184step2; decide +kernel
      have hl : raw3184step3Labels = raw3184step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw3184step3 raw3184step3Labels = mixedMoment B raw3184step4 raw3184step4Labels := by
      have ha : raw3184step4 = raw3184step3 := by apply Matrix.ext; unfold raw3184step4 raw3184step3; decide +kernel
      have hl : raw3184step3Labels = labelEmbedding7 ∘ raw3184step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3184step3 raw3184step3Labels raw3184step4Labels labelEmbedding7 hl
    _ = mixedMoment B node5454 node5454Labels := by rfl

theorem canonical3185 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3185 raw3185Labels = mixedMoment B node5490 node5490Labels := by
  calc
    mixedMoment B raw3185 raw3185Labels = mixedMoment B raw3185step0 raw3185step0Labels := by
      have hz : ∀ j, raw3185 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw3185step0 = (fun i j => raw3185 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw3185step0 raw3185; decide +kernel
      have hl : raw3185step0Labels = raw3185Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3185 raw3185Labels permutation265 hz
    mixedMoment B raw3185step0 raw3185step0Labels = mixedMoment B raw3185step1 raw3185step1Labels := by
      have ha : raw3185step1 = (fun i j => raw3185step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw3185step1 raw3185step0; decide +kernel
      have hl : raw3185step1Labels = raw3185step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3185step0 raw3185step0Labels permutation32 permutation6
    mixedMoment B raw3185step1 raw3185step1Labels = mixedMoment B raw3185step2 raw3185step2Labels := by
      have ha : raw3185step2 = raw3185step1 := by apply Matrix.ext; unfold raw3185step2 raw3185step1; decide +kernel
      have hl : raw3185step1Labels = labelEmbedding9 ∘ raw3185step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3185step1 raw3185step1Labels raw3185step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5490 node5490Labels := by rfl

theorem canonical3186 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3186 raw3186Labels = mixedMoment B node5495 node5495Labels := by
  calc
    mixedMoment B raw3186 raw3186Labels = mixedMoment B raw3186step0 raw3186step0Labels := by
      have hz : ∀ j, raw3186 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3186step0 = (fun i j => raw3186 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3186step0 raw3186; decide +kernel
      have hl : raw3186step0Labels = raw3186Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3186 raw3186Labels permutation434 hz
    mixedMoment B raw3186step0 raw3186step0Labels = mixedMoment B raw3186step1 raw3186step1Labels := by
      have hz : ∀ j, raw3186step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw3186step1 = (fun i j => raw3186step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw3186step1 raw3186step0; decide +kernel
      have hl : raw3186step1Labels = raw3186step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3186step0 raw3186step0Labels permutation80 hz
    mixedMoment B raw3186step1 raw3186step1Labels = mixedMoment B raw3186step2 raw3186step2Labels := by
      have hz : ∀ j, raw3186step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw3186step2 = (fun i j => raw3186step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw3186step2 raw3186step1; decide +kernel
      have hl : raw3186step2Labels = raw3186step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3186step1 raw3186step1Labels permutation14 hz
    mixedMoment B raw3186step2 raw3186step2Labels = mixedMoment B raw3186step3 raw3186step3Labels := by
      have ha : raw3186step3 = (fun i j => raw3186step2 (permutation2 i) (permutation6 j)) := by apply Matrix.ext; unfold raw3186step3 raw3186step2; decide +kernel
      have hl : raw3186step3Labels = raw3186step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3186step2 raw3186step2Labels permutation2 permutation6
    mixedMoment B raw3186step3 raw3186step3Labels = mixedMoment B raw3186step4 raw3186step4Labels := by
      have ha : raw3186step4 = raw3186step3 := by apply Matrix.ext; unfold raw3186step4 raw3186step3; decide +kernel
      have hl : raw3186step3Labels = labelEmbedding9 ∘ raw3186step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3186step3 raw3186step3Labels raw3186step4Labels labelEmbedding9 hl
    _ = mixedMoment B node5495 node5495Labels := by rfl

theorem canonical3187 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3187 raw3187Labels = mixedMoment B node5492 node5492Labels := by
  calc
    mixedMoment B raw3187 raw3187Labels = mixedMoment B raw3187step0 raw3187step0Labels := by
      have hz : ∀ j, raw3187 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3187step0 = (fun i j => raw3187 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3187step0 raw3187; decide +kernel
      have hl : raw3187step0Labels = raw3187Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3187 raw3187Labels permutation346 hz
    mixedMoment B raw3187step0 raw3187step0Labels = mixedMoment B raw3187step1 raw3187step1Labels := by
      have hz : ∀ j, raw3187step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw3187step1 = (fun i j => raw3187step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw3187step1 raw3187step0; decide +kernel
      have hl : raw3187step1Labels = raw3187step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3187step0 raw3187step0Labels permutation56 hz
    mixedMoment B raw3187step1 raw3187step1Labels = mixedMoment B raw3187step2 raw3187step2Labels := by
      have ha : raw3187step2 = (fun i j => raw3187step1 (permutation25 i) (permutation2 j)) := by apply Matrix.ext; unfold raw3187step2 raw3187step1; decide +kernel
      have hl : raw3187step2Labels = raw3187step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3187step1 raw3187step1Labels permutation25 permutation2
    _ = mixedMoment B node5492 node5492Labels := by rfl

theorem canonical3188 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3188 raw3188Labels = mixedMoment B node5493 node5493Labels := by
  calc
    mixedMoment B raw3188 raw3188Labels = mixedMoment B raw3188step0 raw3188step0Labels := by
      have hz : ∀ j, raw3188 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3188step0 = (fun i j => raw3188 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3188step0 raw3188; decide +kernel
      have hl : raw3188step0Labels = raw3188Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3188 raw3188Labels permutation346 hz
    mixedMoment B raw3188step0 raw3188step0Labels = mixedMoment B raw3188step1 raw3188step1Labels := by
      have hz : ∀ j, raw3188step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw3188step1 = (fun i j => raw3188step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw3188step1 raw3188step0; decide +kernel
      have hl : raw3188step1Labels = raw3188step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3188step0 raw3188step0Labels permutation56 hz
    mixedMoment B raw3188step1 raw3188step1Labels = mixedMoment B raw3188step2 raw3188step2Labels := by
      have ha : raw3188step2 = (fun i j => raw3188step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw3188step2 raw3188step1; decide +kernel
      have hl : raw3188step2Labels = raw3188step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3188step1 raw3188step1Labels permutation8 permutation7
    mixedMoment B raw3188step2 raw3188step2Labels = mixedMoment B raw3188step3 raw3188step3Labels := by
      have ha : raw3188step3 = raw3188step2 := by apply Matrix.ext; unfold raw3188step3 raw3188step2; decide +kernel
      have hl : raw3188step2Labels = labelEmbedding10 ∘ raw3188step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3188step2 raw3188step2Labels raw3188step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5493 node5493Labels := by rfl

theorem canonical3189 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3189 raw3189Labels = mixedMoment B node5433 node5433Labels := by
  calc
    mixedMoment B raw3189 raw3189Labels = mixedMoment B raw3189step0 raw3189step0Labels := by
      have ha : raw3189step0 = (fun i j => raw3189 (permutation164 i) (permutation4 j)) := by apply Matrix.ext; unfold raw3189step0 raw3189; decide +kernel
      have hl : raw3189step0Labels = raw3189Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3189 raw3189Labels permutation164 permutation4
    mixedMoment B raw3189step0 raw3189step0Labels = mixedMoment B raw3189step1 raw3189step1Labels := by
      have ha : raw3189step1 = -raw3189step0 := by apply Matrix.ext; change ∀ i j, raw3189step1 i j = -(raw3189step0 i j); unfold raw3189step1 raw3189step0; decide +kernel
      have hl : raw3189step1Labels = raw3189step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw3189step1 raw3189step1Labels = mixedMoment B raw3189step2 raw3189step2Labels := by
      have ha : raw3189step2 = raw3189step1 := by apply Matrix.ext; unfold raw3189step2 raw3189step1; decide +kernel
      have hl : raw3189step1Labels = labelEmbedding7 ∘ raw3189step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3189step1 raw3189step1Labels raw3189step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5433 node5433Labels := by rfl

theorem canonical3190 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3190 raw3190Labels = mixedMoment B node5431 node5431Labels := by
  calc
    mixedMoment B raw3190 raw3190Labels = mixedMoment B raw3190step0 raw3190step0Labels := by
      have ha : raw3190step0 = (fun i j => raw3190 (permutation329 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3190step0 raw3190; decide +kernel
      have hl : raw3190step0Labels = raw3190Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3190 raw3190Labels permutation329 permutation3
    mixedMoment B raw3190step0 raw3190step0Labels = mixedMoment B raw3190step1 raw3190step1Labels := by
      have ha : raw3190step1 = raw3190step0 := by apply Matrix.ext; unfold raw3190step1 raw3190step0; decide +kernel
      have hl : raw3190step0Labels = labelEmbedding6 ∘ raw3190step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3190step0 raw3190step0Labels raw3190step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5431 node5431Labels := by rfl

theorem canonical3191 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3191 raw3191Labels = mixedMoment B node5490 node5490Labels := by
  calc
    mixedMoment B raw3191 raw3191Labels = mixedMoment B raw3191step0 raw3191step0Labels := by
      have hz : ∀ j, raw3191 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3191step0 = (fun i j => raw3191 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3191step0 raw3191; decide +kernel
      have hl : raw3191step0Labels = raw3191Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3191 raw3191Labels permutation434 hz
    mixedMoment B raw3191step0 raw3191step0Labels = mixedMoment B raw3191step1 raw3191step1Labels := by
      have ha : raw3191step1 = (fun i j => raw3191step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw3191step1 raw3191step0; decide +kernel
      have hl : raw3191step1Labels = raw3191step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3191step0 raw3191step0Labels permutation32 permutation6
    mixedMoment B raw3191step1 raw3191step1Labels = mixedMoment B raw3191step2 raw3191step2Labels := by
      have ha : raw3191step2 = raw3191step1 := by apply Matrix.ext; unfold raw3191step2 raw3191step1; decide +kernel
      have hl : raw3191step1Labels = labelEmbedding9 ∘ raw3191step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3191step1 raw3191step1Labels raw3191step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5490 node5490Labels := by rfl

theorem canonical3192 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3192 raw3192Labels = mixedMoment B node5481 node5481Labels := by
  calc
    mixedMoment B raw3192 raw3192Labels = mixedMoment B raw3192step0 raw3192step0Labels := by
      have ha : raw3192step0 = (fun i j => raw3192 (permutation538 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3192step0 raw3192; decide +kernel
      have hl : raw3192step0Labels = raw3192Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3192 raw3192Labels permutation538 permutation3
    mixedMoment B raw3192step0 raw3192step0Labels = mixedMoment B raw3192step1 raw3192step1Labels := by
      have ha : raw3192step1 = raw3192step0 := by apply Matrix.ext; unfold raw3192step1 raw3192step0; decide +kernel
      have hl : raw3192step0Labels = labelEmbedding6 ∘ raw3192step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3192step0 raw3192step0Labels raw3192step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5481 node5481Labels := by rfl

theorem canonical3193 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3193 raw3193Labels = mixedMoment B node5489 node5489Labels := by
  calc
    mixedMoment B raw3193 raw3193Labels = mixedMoment B raw3193step0 raw3193step0Labels := by
      have ha : raw3193step0 = (fun i j => raw3193 (permutation182 i) (permutation7 j)) := by apply Matrix.ext; unfold raw3193step0 raw3193; decide +kernel
      have hl : raw3193step0Labels = raw3193Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3193 raw3193Labels permutation182 permutation7
    mixedMoment B raw3193step0 raw3193step0Labels = mixedMoment B raw3193step1 raw3193step1Labels := by
      have ha : raw3193step1 = raw3193step0 := by apply Matrix.ext; unfold raw3193step1 raw3193step0; decide +kernel
      have hl : raw3193step0Labels = labelEmbedding10 ∘ raw3193step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3193step0 raw3193step0Labels raw3193step1Labels labelEmbedding10 hl
    _ = mixedMoment B node5489 node5489Labels := by rfl

theorem canonical3194 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3194 raw3194Labels = mixedMoment B node5435 node5435Labels := by
  calc
    mixedMoment B raw3194 raw3194Labels = mixedMoment B raw3194step0 raw3194step0Labels := by
      have hz : ∀ j, raw3194 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3194step0 = (fun i j => raw3194 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3194step0 raw3194; decide +kernel
      have hl : raw3194step0Labels = raw3194Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3194 raw3194Labels permutation346 hz
    mixedMoment B raw3194step0 raw3194step0Labels = mixedMoment B raw3194step1 raw3194step1Labels := by
      have ha : raw3194step1 = (fun i j => raw3194step0 (permutation35 i) (permutation4 j)) := by apply Matrix.ext; unfold raw3194step1 raw3194step0; decide +kernel
      have hl : raw3194step1Labels = raw3194step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3194step0 raw3194step0Labels permutation35 permutation4
    mixedMoment B raw3194step1 raw3194step1Labels = mixedMoment B raw3194step2 raw3194step2Labels := by
      have ha : raw3194step2 = -raw3194step1 := by apply Matrix.ext; change ∀ i j, raw3194step2 i j = -(raw3194step1 i j); unfold raw3194step2 raw3194step1; decide +kernel
      have hl : raw3194step2Labels = raw3194step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw3194step2 raw3194step2Labels = mixedMoment B raw3194step3 raw3194step3Labels := by
      have ha : raw3194step3 = raw3194step2 := by apply Matrix.ext; unfold raw3194step3 raw3194step2; decide +kernel
      have hl : raw3194step2Labels = labelEmbedding7 ∘ raw3194step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3194step2 raw3194step2Labels raw3194step3Labels labelEmbedding7 hl
    _ = mixedMoment B node5435 node5435Labels := by rfl

theorem canonical3195 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3195 raw3195Labels = mixedMoment B node5432 node5432Labels := by
  calc
    mixedMoment B raw3195 raw3195Labels = mixedMoment B raw3195step0 raw3195step0Labels := by
      have hz : ∀ j, raw3195 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3195step0 = (fun i j => raw3195 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3195step0 raw3195; decide +kernel
      have hl : raw3195step0Labels = raw3195Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3195 raw3195Labels permutation346 hz
    mixedMoment B raw3195step0 raw3195step0Labels = mixedMoment B raw3195step1 raw3195step1Labels := by
      have ha : raw3195step1 = (fun i j => raw3195step0 (permutation72 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3195step1 raw3195step0; decide +kernel
      have hl : raw3195step1Labels = raw3195step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3195step0 raw3195step0Labels permutation72 permutation3
    mixedMoment B raw3195step1 raw3195step1Labels = mixedMoment B raw3195step2 raw3195step2Labels := by
      have ha : raw3195step2 = raw3195step1 := by apply Matrix.ext; unfold raw3195step2 raw3195step1; decide +kernel
      have hl : raw3195step1Labels = labelEmbedding6 ∘ raw3195step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3195step1 raw3195step1Labels raw3195step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5432 node5432Labels := by rfl

theorem canonical3196 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3196 raw3196Labels = mixedMoment B node5431 node5431Labels := by
  calc
    mixedMoment B raw3196 raw3196Labels = mixedMoment B raw3196step0 raw3196step0Labels := by
      have ha : raw3196step0 = (fun i j => raw3196 (permutation514 i) (permutation5 j)) := by apply Matrix.ext; unfold raw3196step0 raw3196; decide +kernel
      have hl : raw3196step0Labels = raw3196Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3196 raw3196Labels permutation514 permutation5
    mixedMoment B raw3196step0 raw3196step0Labels = mixedMoment B raw3196step1 raw3196step1Labels := by
      have ha : raw3196step1 = raw3196step0 := by apply Matrix.ext; unfold raw3196step1 raw3196step0; decide +kernel
      have hl : raw3196step0Labels = labelEmbedding8 ∘ raw3196step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3196step0 raw3196step0Labels raw3196step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5431 node5431Labels := by rfl

theorem canonical3197 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3197 raw3197Labels = mixedMoment B node5438 node5438Labels := by
  calc
    mixedMoment B raw3197 raw3197Labels = mixedMoment B raw3197step0 raw3197step0Labels := by
      have hz : ∀ j, raw3197 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3197step0 = (fun i j => raw3197 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3197step0 raw3197; decide +kernel
      have hl : raw3197step0Labels = raw3197Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3197 raw3197Labels permutation346 hz
    mixedMoment B raw3197step0 raw3197step0Labels = mixedMoment B raw3197step1 raw3197step1Labels := by
      have ha : raw3197step1 = (fun i j => raw3197step0 (permutation98 i) (permutation5 j)) := by apply Matrix.ext; unfold raw3197step1 raw3197step0; decide +kernel
      have hl : raw3197step1Labels = raw3197step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3197step0 raw3197step0Labels permutation98 permutation5
    mixedMoment B raw3197step1 raw3197step1Labels = mixedMoment B raw3197step2 raw3197step2Labels := by
      have ha : raw3197step2 = raw3197step1 := by apply Matrix.ext; unfold raw3197step2 raw3197step1; decide +kernel
      have hl : raw3197step1Labels = labelEmbedding8 ∘ raw3197step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3197step1 raw3197step1Labels raw3197step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5438 node5438Labels := by rfl

theorem canonical3198 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3198 raw3198Labels = mixedMoment B node5450 node5450Labels := by
  calc
    mixedMoment B raw3198 raw3198Labels = mixedMoment B raw3198step0 raw3198step0Labels := by
      have hz : ∀ j, raw3198 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3198step0 = (fun i j => raw3198 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3198step0 raw3198; decide +kernel
      have hl : raw3198step0Labels = raw3198Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3198 raw3198Labels permutation346 hz
    mixedMoment B raw3198step0 raw3198step0Labels = mixedMoment B raw3198step1 raw3198step1Labels := by
      have ha : raw3198step1 = (fun i j => raw3198step0 (permutation83 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3198step1 raw3198step0; decide +kernel
      have hl : raw3198step1Labels = raw3198step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3198step0 raw3198step0Labels permutation83 permutation3
    mixedMoment B raw3198step1 raw3198step1Labels = mixedMoment B raw3198step2 raw3198step2Labels := by
      have ha : raw3198step2 = -raw3198step1 := by apply Matrix.ext; change ∀ i j, raw3198step2 i j = -(raw3198step1 i j); unfold raw3198step2 raw3198step1; decide +kernel
      have hl : raw3198step2Labels = raw3198step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw3198step2 raw3198step2Labels = mixedMoment B raw3198step3 raw3198step3Labels := by
      have ha : raw3198step3 = raw3198step2 := by apply Matrix.ext; unfold raw3198step3 raw3198step2; decide +kernel
      have hl : raw3198step2Labels = labelEmbedding6 ∘ raw3198step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3198step2 raw3198step2Labels raw3198step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5450 node5450Labels := by rfl

theorem canonical3199 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3199 raw3199Labels = mixedMoment B node5440 node5440Labels := by
  calc
    mixedMoment B raw3199 raw3199Labels = mixedMoment B raw3199step0 raw3199step0Labels := by
      have hz : ∀ j, raw3199 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3199step0 = (fun i j => raw3199 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3199step0 raw3199; decide +kernel
      have hl : raw3199step0Labels = raw3199Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3199 raw3199Labels permutation346 hz
    mixedMoment B raw3199step0 raw3199step0Labels = mixedMoment B raw3199step1 raw3199step1Labels := by
      have ha : raw3199step1 = (fun i j => raw3199step0 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw3199step1 raw3199step0; decide +kernel
      have hl : raw3199step1Labels = raw3199step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3199step0 raw3199step0Labels permutation32 permutation4
    mixedMoment B raw3199step1 raw3199step1Labels = mixedMoment B raw3199step2 raw3199step2Labels := by
      have ha : raw3199step2 = -raw3199step1 := by apply Matrix.ext; change ∀ i j, raw3199step2 i j = -(raw3199step1 i j); unfold raw3199step2 raw3199step1; decide +kernel
      have hl : raw3199step2Labels = raw3199step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw3199step2 raw3199step2Labels = mixedMoment B raw3199step3 raw3199step3Labels := by
      have ha : raw3199step3 = raw3199step2 := by apply Matrix.ext; unfold raw3199step3 raw3199step2; decide +kernel
      have hl : raw3199step2Labels = labelEmbedding7 ∘ raw3199step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3199step2 raw3199step2Labels raw3199step3Labels labelEmbedding7 hl
    _ = mixedMoment B node5440 node5440Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical25
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical3200 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3200 raw3200Labels = mixedMoment B node5450 node5450Labels := by
  calc
    mixedMoment B raw3200 raw3200Labels = mixedMoment B raw3200step0 raw3200step0Labels := by
      have hz : ∀ j, raw3200 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3200step0 = (fun i j => raw3200 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3200step0 raw3200; decide +kernel
      have hl : raw3200step0Labels = raw3200Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3200 raw3200Labels permutation346 hz
    mixedMoment B raw3200step0 raw3200step0Labels = mixedMoment B raw3200step1 raw3200step1Labels := by
      have ha : raw3200step1 = (fun i j => raw3200step0 (permutation59 i) (permutation5 j)) := by apply Matrix.ext; unfold raw3200step1 raw3200step0; decide +kernel
      have hl : raw3200step1Labels = raw3200step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3200step0 raw3200step0Labels permutation59 permutation5
    mixedMoment B raw3200step1 raw3200step1Labels = mixedMoment B raw3200step2 raw3200step2Labels := by
      have ha : raw3200step2 = -raw3200step1 := by apply Matrix.ext; change ∀ i j, raw3200step2 i j = -(raw3200step1 i j); unfold raw3200step2 raw3200step1; decide +kernel
      have hl : raw3200step2Labels = raw3200step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw3200step2 raw3200step2Labels = mixedMoment B raw3200step3 raw3200step3Labels := by
      have ha : raw3200step3 = raw3200step2 := by apply Matrix.ext; unfold raw3200step3 raw3200step2; decide +kernel
      have hl : raw3200step2Labels = labelEmbedding8 ∘ raw3200step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3200step2 raw3200step2Labels raw3200step3Labels labelEmbedding8 hl
    _ = mixedMoment B node5450 node5450Labels := by rfl

theorem canonical3201 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3201 raw3201Labels = mixedMoment B node5489 node5489Labels := by
  calc
    mixedMoment B raw3201 raw3201Labels = mixedMoment B raw3201step0 raw3201step0Labels := by
      have ha : raw3201step0 = (fun i j => raw3201 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw3201step0 raw3201; decide +kernel
      have hl : raw3201step0Labels = raw3201Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3201 raw3201Labels permutation152 permutation6
    mixedMoment B raw3201step0 raw3201step0Labels = mixedMoment B raw3201step1 raw3201step1Labels := by
      have ha : raw3201step1 = raw3201step0 := by apply Matrix.ext; unfold raw3201step1 raw3201step0; decide +kernel
      have hl : raw3201step0Labels = labelEmbedding9 ∘ raw3201step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3201step0 raw3201step0Labels raw3201step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5489 node5489Labels := by rfl

theorem canonical3202 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3202 raw3202Labels = mixedMoment B node5493 node5493Labels := by
  calc
    mixedMoment B raw3202 raw3202Labels = mixedMoment B raw3202step0 raw3202step0Labels := by
      have hz : ∀ j, raw3202 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3202step0 = (fun i j => raw3202 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3202step0 raw3202; decide +kernel
      have hl : raw3202step0Labels = raw3202Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3202 raw3202Labels permutation434 hz
    mixedMoment B raw3202step0 raw3202step0Labels = mixedMoment B raw3202step1 raw3202step1Labels := by
      have hz : ∀ j, raw3202step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw3202step1 = (fun i j => raw3202step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw3202step1 raw3202step0; decide +kernel
      have hl : raw3202step1Labels = raw3202step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3202step0 raw3202step0Labels permutation80 hz
    mixedMoment B raw3202step1 raw3202step1Labels = mixedMoment B raw3202step2 raw3202step2Labels := by
      have ha : raw3202step2 = (fun i j => raw3202step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw3202step2 raw3202step1; decide +kernel
      have hl : raw3202step2Labels = raw3202step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3202step1 raw3202step1Labels permutation8 permutation6
    mixedMoment B raw3202step2 raw3202step2Labels = mixedMoment B raw3202step3 raw3202step3Labels := by
      have ha : raw3202step3 = raw3202step2 := by apply Matrix.ext; unfold raw3202step3 raw3202step2; decide +kernel
      have hl : raw3202step2Labels = labelEmbedding9 ∘ raw3202step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3202step2 raw3202step2Labels raw3202step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5493 node5493Labels := by rfl

theorem canonical3203 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3203 raw3203Labels = mixedMoment B node5490 node5490Labels := by
  calc
    mixedMoment B raw3203 raw3203Labels = mixedMoment B raw3203step0 raw3203step0Labels := by
      have hz : ∀ j, raw3203 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3203step0 = (fun i j => raw3203 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3203step0 raw3203; decide +kernel
      have hl : raw3203step0Labels = raw3203Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3203 raw3203Labels permutation346 hz
    mixedMoment B raw3203step0 raw3203step0Labels = mixedMoment B raw3203step1 raw3203step1Labels := by
      have ha : raw3203step1 = (fun i j => raw3203step0 (permutation33 i) (permutation6 j)) := by apply Matrix.ext; unfold raw3203step1 raw3203step0; decide +kernel
      have hl : raw3203step1Labels = raw3203step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3203step0 raw3203step0Labels permutation33 permutation6
    mixedMoment B raw3203step1 raw3203step1Labels = mixedMoment B raw3203step2 raw3203step2Labels := by
      have ha : raw3203step2 = raw3203step1 := by apply Matrix.ext; unfold raw3203step2 raw3203step1; decide +kernel
      have hl : raw3203step1Labels = labelEmbedding9 ∘ raw3203step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3203step1 raw3203step1Labels raw3203step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5490 node5490Labels := by rfl

theorem canonical3204 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3204 raw3204Labels = mixedMoment B node5434 node5434Labels := by
  calc
    mixedMoment B raw3204 raw3204Labels = mixedMoment B raw3204step0 raw3204step0Labels := by
      have hz : ∀ j, raw3204 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3204step0 = (fun i j => raw3204 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3204step0 raw3204; decide +kernel
      have hl : raw3204step0Labels = raw3204Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3204 raw3204Labels permutation346 hz
    mixedMoment B raw3204step0 raw3204step0Labels = mixedMoment B raw3204step1 raw3204step1Labels := by
      have ha : raw3204step1 = (fun i j => raw3204step0 (permutation34 i) (permutation4 j)) := by apply Matrix.ext; unfold raw3204step1 raw3204step0; decide +kernel
      have hl : raw3204step1Labels = raw3204step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3204step0 raw3204step0Labels permutation34 permutation4
    mixedMoment B raw3204step1 raw3204step1Labels = mixedMoment B raw3204step2 raw3204step2Labels := by
      have ha : raw3204step2 = -raw3204step1 := by apply Matrix.ext; change ∀ i j, raw3204step2 i j = -(raw3204step1 i j); unfold raw3204step2 raw3204step1; decide +kernel
      have hl : raw3204step2Labels = raw3204step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw3204step2 raw3204step2Labels = mixedMoment B raw3204step3 raw3204step3Labels := by
      have ha : raw3204step3 = raw3204step2 := by apply Matrix.ext; unfold raw3204step3 raw3204step2; decide +kernel
      have hl : raw3204step2Labels = labelEmbedding7 ∘ raw3204step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3204step2 raw3204step2Labels raw3204step3Labels labelEmbedding7 hl
    _ = mixedMoment B node5434 node5434Labels := by rfl

theorem canonical3205 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3205 raw3205Labels = mixedMoment B node5438 node5438Labels := by
  calc
    mixedMoment B raw3205 raw3205Labels = mixedMoment B raw3205step0 raw3205step0Labels := by
      have hz : ∀ j, raw3205 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3205step0 = (fun i j => raw3205 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3205step0 raw3205; decide +kernel
      have hl : raw3205step0Labels = raw3205Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3205 raw3205Labels permutation346 hz
    mixedMoment B raw3205step0 raw3205step0Labels = mixedMoment B raw3205step1 raw3205step1Labels := by
      have ha : raw3205step1 = (fun i j => raw3205step0 (permutation68 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3205step1 raw3205step0; decide +kernel
      have hl : raw3205step1Labels = raw3205step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3205step0 raw3205step0Labels permutation68 permutation3
    mixedMoment B raw3205step1 raw3205step1Labels = mixedMoment B raw3205step2 raw3205step2Labels := by
      have ha : raw3205step2 = raw3205step1 := by apply Matrix.ext; unfold raw3205step2 raw3205step1; decide +kernel
      have hl : raw3205step1Labels = labelEmbedding6 ∘ raw3205step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3205step1 raw3205step1Labels raw3205step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5438 node5438Labels := by rfl

theorem canonical3206 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3206 raw3206Labels = mixedMoment B node5481 node5481Labels := by
  calc
    mixedMoment B raw3206 raw3206Labels = mixedMoment B raw3206step0 raw3206step0Labels := by
      have ha : raw3206step0 = (fun i j => raw3206 (permutation659 i) (permutation5 j)) := by apply Matrix.ext; unfold raw3206step0 raw3206; decide +kernel
      have hl : raw3206step0Labels = raw3206Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3206 raw3206Labels permutation659 permutation5
    mixedMoment B raw3206step0 raw3206step0Labels = mixedMoment B raw3206step1 raw3206step1Labels := by
      have ha : raw3206step1 = raw3206step0 := by apply Matrix.ext; unfold raw3206step1 raw3206step0; decide +kernel
      have hl : raw3206step0Labels = labelEmbedding8 ∘ raw3206step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3206step0 raw3206step0Labels raw3206step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5481 node5481Labels := by rfl

theorem canonical3207 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3207 raw3207Labels = mixedMoment B node5492 node5492Labels := by
  calc
    mixedMoment B raw3207 raw3207Labels = mixedMoment B raw3207step0 raw3207step0Labels := by
      have hz : ∀ j, raw3207 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3207step0 = (fun i j => raw3207 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3207step0 raw3207; decide +kernel
      have hl : raw3207step0Labels = raw3207Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3207 raw3207Labels permutation434 hz
    mixedMoment B raw3207step0 raw3207step0Labels = mixedMoment B raw3207step1 raw3207step1Labels := by
      have hz : ∀ j, raw3207step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw3207step1 = (fun i j => raw3207step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw3207step1 raw3207step0; decide +kernel
      have hl : raw3207step1Labels = raw3207step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3207step0 raw3207step0Labels permutation80 hz
    mixedMoment B raw3207step1 raw3207step1Labels = mixedMoment B raw3207step2 raw3207step2Labels := by
      have ha : raw3207step2 = (fun i j => raw3207step1 (permutation31 i) (permutation4 j)) := by apply Matrix.ext; unfold raw3207step2 raw3207step1; decide +kernel
      have hl : raw3207step2Labels = raw3207step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3207step1 raw3207step1Labels permutation31 permutation4
    mixedMoment B raw3207step2 raw3207step2Labels = mixedMoment B raw3207step3 raw3207step3Labels := by
      have ha : raw3207step3 = raw3207step2 := by apply Matrix.ext; unfold raw3207step3 raw3207step2; decide +kernel
      have hl : raw3207step2Labels = labelEmbedding7 ∘ raw3207step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3207step2 raw3207step2Labels raw3207step3Labels labelEmbedding7 hl
    _ = mixedMoment B node5492 node5492Labels := by rfl

theorem canonical3208 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3208 raw3208Labels = mixedMoment B node5484 node5484Labels := by
  calc
    mixedMoment B raw3208 raw3208Labels = mixedMoment B raw3208step0 raw3208step0Labels := by
      have hz : ∀ j, raw3208 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3208step0 = (fun i j => raw3208 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3208step0 raw3208; decide +kernel
      have hl : raw3208step0Labels = raw3208Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3208 raw3208Labels permutation346 hz
    mixedMoment B raw3208step0 raw3208step0Labels = mixedMoment B raw3208step1 raw3208step1Labels := by
      have ha : raw3208step1 = (fun i j => raw3208step0 (permutation110 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3208step1 raw3208step0; decide +kernel
      have hl : raw3208step1Labels = raw3208step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3208step0 raw3208step0Labels permutation110 permutation3
    mixedMoment B raw3208step1 raw3208step1Labels = mixedMoment B raw3208step2 raw3208step2Labels := by
      have ha : raw3208step2 = raw3208step1 := by apply Matrix.ext; unfold raw3208step2 raw3208step1; decide +kernel
      have hl : raw3208step1Labels = labelEmbedding6 ∘ raw3208step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3208step1 raw3208step1Labels raw3208step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5484 node5484Labels := by rfl

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

theorem singleton5431 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5431 node5431Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3849 node3849Labels + mixedMoment B node3875 node3875Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2520 singletonSmall5431
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5431) = raw2520Labels := by decide +kernel
  rw [hl, canonical2520 B hB] at h
  have hc0 : mixedMoment B raw2520 (Fin.cases (0 : Fin 2) singletonSmall5431) =
      mixedMoment B node3849 node3849Labels := by
    have ha : raw2520 = raw2521 := by apply Matrix.ext; unfold raw2520 raw2521; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5431 = raw2521Labels := by decide +kernel
    rw [ha, hj, canonical2521 B hB]
  have hc1 : mixedMoment B raw2520 (Fin.cases (1 : Fin 2) singletonSmall5431) =
      mixedMoment B node3875 node3875Labels := by
    have ha : raw2520 = raw2522 := by apply Matrix.ext; unfold raw2520 raw2522; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5431 = raw2522Labels := by decide +kernel
    rw [ha, hj, canonical2522 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton5432 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5432 node5432Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3850 node3850Labels + mixedMoment B node3850 node3850Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2523 singletonSmall5432
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5432) = raw2523Labels := by decide +kernel
  rw [hl, canonical2523 B hB] at h
  have hc0 : mixedMoment B raw2523 (Fin.cases (0 : Fin 2) singletonSmall5432) =
      mixedMoment B node3850 node3850Labels := by
    have ha : raw2523 = raw2524 := by apply Matrix.ext; unfold raw2523 raw2524; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5432 = raw2524Labels := by decide +kernel
    rw [ha, hj, canonical2524 B hB]
  have hc1 : mixedMoment B raw2523 (Fin.cases (1 : Fin 2) singletonSmall5432) =
      mixedMoment B node3850 node3850Labels := by
    have ha : raw2523 = raw2525 := by apply Matrix.ext; unfold raw2523 raw2525; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5432 = raw2525Labels := by decide +kernel
    rw [ha, hj, canonical2525 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton5438 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5438 node5438Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3857 node3857Labels + mixedMoment B node3876 node3876Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2538 singletonSmall5438
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5438) = raw2538Labels := by decide +kernel
  rw [hl, canonical2538 B hB] at h
  have hc0 : mixedMoment B raw2538 (Fin.cases (0 : Fin 2) singletonSmall5438) =
      mixedMoment B node3857 node3857Labels := by
    have ha : raw2538 = raw2539 := by apply Matrix.ext; unfold raw2538 raw2539; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5438 = raw2539Labels := by decide +kernel
    rw [ha, hj, canonical2539 B hB]
  have hc1 : mixedMoment B raw2538 (Fin.cases (1 : Fin 2) singletonSmall5438) =
      mixedMoment B node3876 node3876Labels := by
    have ha : raw2538 = raw2540 := by apply Matrix.ext; unfold raw2538 raw2540; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5438 = raw2540Labels := by decide +kernel
    rw [ha, hj, canonical2540 B hB]
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

theorem singleton5484 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5484 node5484Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3983 node3983Labels + mixedMoment B node3983 node3983Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2607 singletonSmall5484
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5484) = raw2607Labels := by decide +kernel
  rw [hl, canonical2607 B hB] at h
  have hc0 : mixedMoment B raw2607 (Fin.cases (0 : Fin 2) singletonSmall5484) =
      mixedMoment B node3983 node3983Labels := by
    have ha : raw2607 = raw2608 := by apply Matrix.ext; unfold raw2607 raw2608; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5484 = raw2608Labels := by decide +kernel
    rw [ha, hj, canonical2608 B hB]
  have hc1 : mixedMoment B raw2607 (Fin.cases (1 : Fin 2) singletonSmall5484) =
      mixedMoment B node3983 node3983Labels := by
    have ha : raw2607 = raw2609 := by apply Matrix.ext; unfold raw2607 raw2609; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5484 = raw2609Labels := by decide +kernel
    rw [ha, hj, canonical2609 B hB]
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

theorem zero5440 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5440 node5440Labels = 0 := by
  exact mixedMoment_order_one B hB node5440 node5440Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero5454 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5454 node5454Labels = 0 := by
  exact mixedMoment_order_one B hB node5454 node5454Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero5481 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node5481 node5481Labels = 0 := by
  exact mixedMoment_alpha B hF node5481 node5481Labels 2 permutation158
    (by decide +kernel)

theorem zero5489 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node5489 node5489Labels = 0 := by
  exact mixedMoment_alpha B hF node5489 node5489Labels 2 permutation152
    (by decide +kernel)

theorem zero5493 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5493 node5493Labels = 0 := by
  exact mixedMoment_order_one B hB node5493 node5493Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero5495 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5495 node5495Labels = 0 := by
  exact mixedMoment_order_one B hB node5495 node5495Labels 1
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

theorem sound3849 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3849 node3849Labels = Sparse.eval nodeValue3849 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3849) = mixedMoment B node3849 node3849Labels := rfl
  simpa [nodeValue3849, Sparse.eval] using hc.symm

theorem sound3850 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3850 node3850Labels = Sparse.eval nodeValue3850 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3850) = mixedMoment B node3850 node3850Labels := rfl
  simpa [nodeValue3850, Sparse.eval] using hc.symm

theorem sound3857 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3857 node3857Labels = Sparse.eval nodeValue3857 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3857) = mixedMoment B node3857 node3857Labels := rfl
  simpa [nodeValue3857, Sparse.eval] using hc.symm

theorem sound3875 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3875 node3875Labels = Sparse.eval nodeValue3875 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3875) = mixedMoment B node3875 node3875Labels := rfl
  simpa [nodeValue3875, Sparse.eval] using hc.symm

theorem sound3876 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3876 node3876Labels = Sparse.eval nodeValue3876 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3876) = mixedMoment B node3876 node3876Labels := rfl
  simpa [nodeValue3876, Sparse.eval] using hc.symm

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

theorem sound3983 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3983 node3983Labels = Sparse.eval nodeValue3983 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3983) = mixedMoment B node3983 node3983Labels := rfl
  simpa [nodeValue3983, Sparse.eval] using hc.symm

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

theorem sound5431 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5431 node5431Labels = Sparse.eval nodeValue5431 (mixedVector B) := by
  have h := singleton5431 B _hB
  rw [sound3849 B _hB _hF, sound3875 B _hB _hF] at h
  norm_num [nodeValue5431, nodeValue3849, nodeValue3875, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5432 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5432 node5432Labels = Sparse.eval nodeValue5432 (mixedVector B) := by
  have h := singleton5432 B _hB
  rw [sound3850 B _hB _hF] at h
  norm_num [nodeValue5432, nodeValue3850, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5438 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5438 node5438Labels = Sparse.eval nodeValue5438 (mixedVector B) := by
  have h := singleton5438 B _hB
  rw [sound3857 B _hB _hF, sound3876 B _hB _hF] at h
  norm_num [nodeValue5438, nodeValue3857, nodeValue3876, Sparse.eval] at h ⊢
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

theorem sound5440 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5440 node5440Labels = Sparse.eval nodeValue5440 (mixedVector B) := by
  simpa only [nodeValue5440, Sparse.eval_nil] using zero5440 B _hB _hF

theorem sound5454 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5454 node5454Labels = Sparse.eval nodeValue5454 (mixedVector B) := by
  simpa only [nodeValue5454, Sparse.eval_nil] using zero5454 B _hB _hF

theorem sound5481 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5481 node5481Labels = Sparse.eval nodeValue5481 (mixedVector B) := by
  simpa only [nodeValue5481, Sparse.eval_nil] using zero5481 B _hB _hF

theorem sound5484 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5484 node5484Labels = Sparse.eval nodeValue5484 (mixedVector B) := by
  have h := singleton5484 B _hB
  rw [sound3983 B _hB _hF] at h
  norm_num [nodeValue5484, nodeValue3983, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5489 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5489 node5489Labels = Sparse.eval nodeValue5489 (mixedVector B) := by
  simpa only [nodeValue5489, Sparse.eval_nil] using zero5489 B _hB _hF

theorem sound5493 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5493 node5493Labels = Sparse.eval nodeValue5493 (mixedVector B) := by
  simpa only [nodeValue5493, Sparse.eval_nil] using zero5493 B _hB _hF

theorem sound5495 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5495 node5495Labels = Sparse.eval nodeValue5495 (mixedVector B) := by
  simpa only [nodeValue5495, Sparse.eval_nil] using zero5495 B _hB _hF

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources0
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sourceEq20 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm20 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA20 + difference 0 1) (sourceB20 + difference 1 0) sourceC20) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5435) := by
    have ha : (tripleCharges (sourceA20 + difference 0 1) (sourceB20 + difference 1 0) sourceC20) = raw3179 := by
      apply Matrix.ext; unfold tripleCharges sourceA20 sourceB20 sourceC20 difference raw3179; decide +kernel
    rw [ha]
    exact (canonical3179 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA20 + difference 0 2) (sourceB20 + difference 2 0) sourceC20) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5433) := by
    have ha : (tripleCharges (sourceA20 + difference 0 2) (sourceB20 + difference 2 0) sourceC20) = raw3180 := by
      apply Matrix.ext; unfold tripleCharges sourceA20 sourceB20 sourceC20 difference raw3180; decide +kernel
    rw [ha]
    exact (canonical3180 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA20 + difference 0 3) (sourceB20 + difference 3 0) sourceC20) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5454) := by
    have ha : (tripleCharges (sourceA20 + difference 0 3) (sourceB20 + difference 3 0) sourceC20) = raw3181 := by
      apply Matrix.ext; unfold tripleCharges sourceA20 sourceB20 sourceC20 difference raw3181; decide +kernel
    rw [ha]
    exact (canonical3181 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA20 + difference 0 4) (sourceB20 + difference 4 0) sourceC20) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5434) := by
    have ha : (tripleCharges (sourceA20 + difference 0 4) (sourceB20 + difference 4 0) sourceC20) = raw3182 := by
      apply Matrix.ext; unfold tripleCharges sourceA20 sourceB20 sourceC20 difference raw3182; decide +kernel
    rw [ha]
    exact (canonical3182 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA20 + difference 0 5) (sourceB20 + difference 5 0) sourceC20) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5440) := by
    have ha : (tripleCharges (sourceA20 + difference 0 5) (sourceB20 + difference 5 0) sourceC20) = raw3183 := by
      apply Matrix.ext; unfold tripleCharges sourceA20 sourceB20 sourceC20 difference raw3183; decide +kernel
    rw [ha]
    exact (canonical3183 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA20 + difference 1 0) (sourceB20 + difference 0 1) sourceC20) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5454) := by
    have ha : (tripleCharges (sourceA20 + difference 1 0) (sourceB20 + difference 0 1) sourceC20) = raw3184 := by
      apply Matrix.ext; unfold tripleCharges sourceA20 sourceB20 sourceC20 difference raw3184; decide +kernel
    rw [ha]
    exact (canonical3184 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA20 + difference 1 2) (sourceB20 + difference 2 1) sourceC20) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5490) := by
    have ha : (tripleCharges (sourceA20 + difference 1 2) (sourceB20 + difference 2 1) sourceC20) = raw3185 := by
      apply Matrix.ext; unfold tripleCharges sourceA20 sourceB20 sourceC20 difference raw3185; decide +kernel
    rw [ha]
    exact (canonical3185 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA20 + difference 1 3) (sourceB20 + difference 3 1) sourceC20) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5495) := by
    have ha : (tripleCharges (sourceA20 + difference 1 3) (sourceB20 + difference 3 1) sourceC20) = raw3186 := by
      apply Matrix.ext; unfold tripleCharges sourceA20 sourceB20 sourceC20 difference raw3186; decide +kernel
    rw [ha]
    exact (canonical3186 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA20 + difference 1 4) (sourceB20 + difference 4 1) sourceC20) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5492) := by
    have ha : (tripleCharges (sourceA20 + difference 1 4) (sourceB20 + difference 4 1) sourceC20) = raw3187 := by
      apply Matrix.ext; unfold tripleCharges sourceA20 sourceB20 sourceC20 difference raw3187; decide +kernel
    rw [ha]
    exact (canonical3187 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA20 + difference 1 5) (sourceB20 + difference 5 1) sourceC20) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5493) := by
    have ha : (tripleCharges (sourceA20 + difference 1 5) (sourceB20 + difference 5 1) sourceC20) = raw3188 := by
      apply Matrix.ext; unfold tripleCharges sourceA20 sourceB20 sourceC20 difference raw3188; decide +kernel
    rw [ha]
    exact (canonical3188 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA20 + difference 2 0) (sourceB20 + difference 0 2) sourceC20) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5433) := by
    have ha : (tripleCharges (sourceA20 + difference 2 0) (sourceB20 + difference 0 2) sourceC20) = raw3189 := by
      apply Matrix.ext; unfold tripleCharges sourceA20 sourceB20 sourceC20 difference raw3189; decide +kernel
    rw [ha]
    exact (canonical3189 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA20 + difference 2 1) (sourceB20 + difference 1 2) sourceC20) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5431) := by
    have ha : (tripleCharges (sourceA20 + difference 2 1) (sourceB20 + difference 1 2) sourceC20) = raw3190 := by
      apply Matrix.ext; unfold tripleCharges sourceA20 sourceB20 sourceC20 difference raw3190; decide +kernel
    rw [ha]
    exact (canonical3190 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA20 + difference 2 3) (sourceB20 + difference 3 2) sourceC20) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5490) := by
    have ha : (tripleCharges (sourceA20 + difference 2 3) (sourceB20 + difference 3 2) sourceC20) = raw3191 := by
      apply Matrix.ext; unfold tripleCharges sourceA20 sourceB20 sourceC20 difference raw3191; decide +kernel
    rw [ha]
    exact (canonical3191 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA20 + difference 2 4) (sourceB20 + difference 4 2) sourceC20) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5481) := by
    have ha : (tripleCharges (sourceA20 + difference 2 4) (sourceB20 + difference 4 2) sourceC20) = raw3192 := by
      apply Matrix.ext; unfold tripleCharges sourceA20 sourceB20 sourceC20 difference raw3192; decide +kernel
    rw [ha]
    exact (canonical3192 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA20 + difference 2 5) (sourceB20 + difference 5 2) sourceC20) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5489) := by
    have ha : (tripleCharges (sourceA20 + difference 2 5) (sourceB20 + difference 5 2) sourceC20) = raw3193 := by
      apply Matrix.ext; unfold tripleCharges sourceA20 sourceB20 sourceC20 difference raw3193; decide +kernel
    rw [ha]
    exact (canonical3193 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA20 + difference 3 0) (sourceB20 + difference 0 3) sourceC20) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5435) := by
    have ha : (tripleCharges (sourceA20 + difference 3 0) (sourceB20 + difference 0 3) sourceC20) = raw3194 := by
      apply Matrix.ext; unfold tripleCharges sourceA20 sourceB20 sourceC20 difference raw3194; decide +kernel
    rw [ha]
    exact (canonical3194 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA20 + difference 3 1) (sourceB20 + difference 1 3) sourceC20) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5432) := by
    have ha : (tripleCharges (sourceA20 + difference 3 1) (sourceB20 + difference 1 3) sourceC20) = raw3195 := by
      apply Matrix.ext; unfold tripleCharges sourceA20 sourceB20 sourceC20 difference raw3195; decide +kernel
    rw [ha]
    exact (canonical3195 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA20 + difference 3 2) (sourceB20 + difference 2 3) sourceC20) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5431) := by
    have ha : (tripleCharges (sourceA20 + difference 3 2) (sourceB20 + difference 2 3) sourceC20) = raw3196 := by
      apply Matrix.ext; unfold tripleCharges sourceA20 sourceB20 sourceC20 difference raw3196; decide +kernel
    rw [ha]
    exact (canonical3196 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA20 + difference 3 4) (sourceB20 + difference 4 3) sourceC20) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5438) := by
    have ha : (tripleCharges (sourceA20 + difference 3 4) (sourceB20 + difference 4 3) sourceC20) = raw3197 := by
      apply Matrix.ext; unfold tripleCharges sourceA20 sourceB20 sourceC20 difference raw3197; decide +kernel
    rw [ha]
    exact (canonical3197 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA20 + difference 3 5) (sourceB20 + difference 5 3) sourceC20) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5450) := by
    have ha : (tripleCharges (sourceA20 + difference 3 5) (sourceB20 + difference 5 3) sourceC20) = raw3198 := by
      apply Matrix.ext; unfold tripleCharges sourceA20 sourceB20 sourceC20 difference raw3198; decide +kernel
    rw [ha]
    exact (canonical3198 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA20 + difference 4 0) (sourceB20 + difference 0 4) sourceC20) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5440) := by
    have ha : (tripleCharges (sourceA20 + difference 4 0) (sourceB20 + difference 0 4) sourceC20) = raw3199 := by
      apply Matrix.ext; unfold tripleCharges sourceA20 sourceB20 sourceC20 difference raw3199; decide +kernel
    rw [ha]
    exact (canonical3199 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA20 + difference 4 1) (sourceB20 + difference 1 4) sourceC20) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5450) := by
    have ha : (tripleCharges (sourceA20 + difference 4 1) (sourceB20 + difference 1 4) sourceC20) = raw3200 := by
      apply Matrix.ext; unfold tripleCharges sourceA20 sourceB20 sourceC20 difference raw3200; decide +kernel
    rw [ha]
    exact (canonical3200 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA20 + difference 4 2) (sourceB20 + difference 2 4) sourceC20) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5489) := by
    have ha : (tripleCharges (sourceA20 + difference 4 2) (sourceB20 + difference 2 4) sourceC20) = raw3201 := by
      apply Matrix.ext; unfold tripleCharges sourceA20 sourceB20 sourceC20 difference raw3201; decide +kernel
    rw [ha]
    exact (canonical3201 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA20 + difference 4 3) (sourceB20 + difference 3 4) sourceC20) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5493) := by
    have ha : (tripleCharges (sourceA20 + difference 4 3) (sourceB20 + difference 3 4) sourceC20) = raw3202 := by
      apply Matrix.ext; unfold tripleCharges sourceA20 sourceB20 sourceC20 difference raw3202; decide +kernel
    rw [ha]
    exact (canonical3202 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA20 + difference 4 5) (sourceB20 + difference 5 4) sourceC20) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5490) := by
    have ha : (tripleCharges (sourceA20 + difference 4 5) (sourceB20 + difference 5 4) sourceC20) = raw3203 := by
      apply Matrix.ext; unfold tripleCharges sourceA20 sourceB20 sourceC20 difference raw3203; decide +kernel
    rw [ha]
    exact (canonical3203 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA20 + difference 5 0) (sourceB20 + difference 0 5) sourceC20) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5434) := by
    have ha : (tripleCharges (sourceA20 + difference 5 0) (sourceB20 + difference 0 5) sourceC20) = raw3204 := by
      apply Matrix.ext; unfold tripleCharges sourceA20 sourceB20 sourceC20 difference raw3204; decide +kernel
    rw [ha]
    exact (canonical3204 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA20 + difference 5 1) (sourceB20 + difference 1 5) sourceC20) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5438) := by
    have ha : (tripleCharges (sourceA20 + difference 5 1) (sourceB20 + difference 1 5) sourceC20) = raw3205 := by
      apply Matrix.ext; unfold tripleCharges sourceA20 sourceB20 sourceC20 difference raw3205; decide +kernel
    rw [ha]
    exact (canonical3205 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA20 + difference 5 2) (sourceB20 + difference 2 5) sourceC20) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5481) := by
    have ha : (tripleCharges (sourceA20 + difference 5 2) (sourceB20 + difference 2 5) sourceC20) = raw3206 := by
      apply Matrix.ext; unfold tripleCharges sourceA20 sourceB20 sourceC20 difference raw3206; decide +kernel
    rw [ha]
    exact (canonical3206 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA20 + difference 5 3) (sourceB20 + difference 3 5) sourceC20) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5492) := by
    have ha : (tripleCharges (sourceA20 + difference 5 3) (sourceB20 + difference 3 5) sourceC20) = raw3207 := by
      apply Matrix.ext; unfold tripleCharges sourceA20 sourceB20 sourceC20 difference raw3207; decide +kernel
    rw [ha]
    exact (canonical3207 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA20 + difference 5 4) (sourceB20 + difference 4 5) sourceC20) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5484) := by
    have ha : (tripleCharges (sourceA20 + difference 5 4) (sourceB20 + difference 4 5) sourceC20) = raw3208 := by
      apply Matrix.ext; unfold tripleCharges sourceA20 sourceB20 sourceC20 difference raw3208; decide +kernel
    rw [ha]
    exact (canonical3208 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA20 sourceB20 sourceC20
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm20, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reindexCheck20 : Integer.Sparse.reindex keyMap MixedData.row20 = numericRow20 := by decide +kernel

theorem numericCheck20 (x : Master → ℝ) : Integer.Sparse.eval numericRow20 x =
    (4320 : ℝ) * reducedSource20 x := by
  norm_num [numericRow20, reducedSource20, Integer.Sparse.eval, Sparse.eval, nodeValue5431, nodeValue5432, nodeValue5433, nodeValue5434, nodeValue5435, nodeValue5438, nodeValue5440, nodeValue5450, nodeValue5454, nodeValue5481, nodeValue5484, nodeValue5489, nodeValue5490, nodeValue5492, nodeValue5493, nodeValue5495]
  ring

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Rows1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero20 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource20 (mixedVector B) = 0 := by
  have h5431 : mixedVector B (Sum.inr 5431) = Sparse.eval nodeValue5431 (mixedVector B) := by
    change mixedMoment B node5431 node5431Labels = _
    exact sound5431 B hB hF
  have h5432 : mixedVector B (Sum.inr 5432) = Sparse.eval nodeValue5432 (mixedVector B) := by
    change mixedMoment B node5432 node5432Labels = _
    exact sound5432 B hB hF
  have h5433 : mixedVector B (Sum.inr 5433) = Sparse.eval nodeValue5433 (mixedVector B) := by
    change mixedMoment B node5433 node5433Labels = _
    exact sound5433_e B hB hF
  have h5434 : mixedVector B (Sum.inr 5434) = Sparse.eval nodeValue5434 (mixedVector B) := by
    change mixedMoment B node5434 node5434Labels = _
    exact sound5434_e B hB hF
  have h5435 : mixedVector B (Sum.inr 5435) = Sparse.eval nodeValue5435 (mixedVector B) := by
    change mixedMoment B node5435 node5435Labels = _
    exact sound5435_e B hB hF
  have h5438 : mixedVector B (Sum.inr 5438) = Sparse.eval nodeValue5438 (mixedVector B) := by
    change mixedMoment B node5438 node5438Labels = _
    exact sound5438 B hB hF
  have h5440 : mixedVector B (Sum.inr 5440) = Sparse.eval nodeValue5440 (mixedVector B) := by
    change mixedMoment B node5440 node5440Labels = _
    exact sound5440 B hB hF
  have h5450 : mixedVector B (Sum.inr 5450) = Sparse.eval nodeValue5450 (mixedVector B) := by
    change mixedMoment B node5450 node5450Labels = _
    exact sound5450_e B hB hF
  have h5454 : mixedVector B (Sum.inr 5454) = Sparse.eval nodeValue5454 (mixedVector B) := by
    change mixedMoment B node5454 node5454Labels = _
    exact sound5454 B hB hF
  have h5481 : mixedVector B (Sum.inr 5481) = Sparse.eval nodeValue5481 (mixedVector B) := by
    change mixedMoment B node5481 node5481Labels = _
    exact sound5481 B hB hF
  have h5484 : mixedVector B (Sum.inr 5484) = Sparse.eval nodeValue5484 (mixedVector B) := by
    change mixedMoment B node5484 node5484Labels = _
    exact sound5484 B hB hF
  have h5489 : mixedVector B (Sum.inr 5489) = Sparse.eval nodeValue5489 (mixedVector B) := by
    change mixedMoment B node5489 node5489Labels = _
    exact sound5489 B hB hF
  have h5490 : mixedVector B (Sum.inr 5490) = Sparse.eval nodeValue5490 (mixedVector B) := by
    change mixedMoment B node5490 node5490Labels = _
    exact sound5490_e B hB hF
  have h5492 : mixedVector B (Sum.inr 5492) = Sparse.eval nodeValue5492 (mixedVector B) := by
    change mixedMoment B node5492 node5492Labels = _
    exact sound5492_e B hB hF
  have h5493 : mixedVector B (Sum.inr 5493) = Sparse.eval nodeValue5493 (mixedVector B) := by
    change mixedMoment B node5493 node5493Labels = _
    exact sound5493 B hB hF
  have h5495 : mixedVector B (Sum.inr 5495) = Sparse.eval nodeValue5495 (mixedVector B) := by
    change mixedMoment B node5495 node5495Labels = _
    exact sound5495 B hB hF
  simpa only [sourceForm20, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h5431, h5432, h5433, h5434, h5435, h5438, h5440, h5450, h5454, h5481, h5484, h5489, h5490, h5492, h5493, h5495, reducedSource20] using sourceEq20 B hB

theorem rowSound20_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row20 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck20, numericCheck20, reducedZero20 B hB hF, mul_zero]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedSourceBridge.rowSound20_e_oai := @OAI.MUB6.Certificate.MixedSourceBridge.rowSound20_e_oai
