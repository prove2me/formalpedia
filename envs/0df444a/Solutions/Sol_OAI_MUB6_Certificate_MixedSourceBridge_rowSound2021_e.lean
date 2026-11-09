-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedSourceBridge.rowSound2021_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-08T22:47:36.726355+00:00
-- url     : https://prove2.me/submissions/1037377e-d436-4f9a-a1b9-1ac207e62b1a

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E070
import Definitions.Def_OAIQ106E086
import Definitions.Def_OAIQ106E087
import Definitions.Def_OAIQ106E091
import Definitions.Def_OAIQ106E092
import Definitions.Def_OAIQ106E093
import Definitions.Def_OAIQ106E094
import Definitions.Def_OAIQ106E195
import Definitions.Def_OAIQ106E105
import Definitions.Def_OAIQ106E107
import Definitions.Def_OAIQ106E108
import Definitions.Def_OAIQ106E118
import Definitions.Def_OAIQ106E119
import Definitions.Def_OAIQ106E121
import Definitions.Def_OAIQ106E126
import Definitions.Def_OAIQ106E140
import Definitions.Def_OAIQ106E147
import Definitions.Def_OAIQ106E170
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound5386_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound5450_e

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical12
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical1554 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1554 raw1554Labels = mixedMoment B node4676 node4676Labels := by
  calc
    mixedMoment B raw1554 raw1554Labels = mixedMoment B raw1554step0 raw1554step0Labels := by
      have ha : raw1554step0 = (fun i j => raw1554 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1554step0 raw1554; decide +kernel
      have hl : raw1554step0Labels = raw1554Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1554 raw1554Labels permutation152 permutation4
    mixedMoment B raw1554step0 raw1554step0Labels = mixedMoment B raw1554step1 raw1554step1Labels := by
      have ha : raw1554step1 = raw1554step0 := by apply Matrix.ext; unfold raw1554step1 raw1554step0; decide +kernel
      have hl : raw1554step0Labels = labelEmbedding7 ∘ raw1554step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1554step0 raw1554step0Labels raw1554step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4676 node4676Labels := by rfl

theorem canonical1555 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1555 raw1555Labels = mixedMoment B node1802 node1802Labels := by
  calc
    mixedMoment B raw1555 raw1555Labels = mixedMoment B raw1555step0 raw1555step0Labels := by
      have ha : raw1555step0 = (fun i j => raw1555 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1555step0 raw1555; decide +kernel
      have hl : raw1555step0Labels = raw1555Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1555 raw1555Labels permutation152 permutation4
    _ = mixedMoment B node1802 node1802Labels := by rfl

theorem canonical1556 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1556 raw1556Labels = mixedMoment B node2141 node2141Labels := by
  calc
    mixedMoment B raw1556 raw1556Labels = mixedMoment B raw1556step0 raw1556step0Labels := by
      have ha : raw1556step0 = (fun i j => raw1556 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1556step0 raw1556; decide +kernel
      have hl : raw1556step0Labels = raw1556Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1556 raw1556Labels permutation152 permutation6
    mixedMoment B raw1556step0 raw1556step0Labels = mixedMoment B raw1556step1 raw1556step1Labels := by
      have ha : raw1556step1 = -raw1556step0 := by apply Matrix.ext; change ∀ i j, raw1556step1 i j = -(raw1556step0 i j); unfold raw1556step1 raw1556step0; decide +kernel
      have hl : raw1556step1Labels = raw1556step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1556step1 raw1556step1Labels = mixedMoment B raw1556step2 raw1556step2Labels := by
      have ha : raw1556step2 = raw1556step1 := by apply Matrix.ext; unfold raw1556step2 raw1556step1; decide +kernel
      have hl : raw1556step1Labels = labelEmbedding1 ∘ raw1556step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1556step1 raw1556step1Labels raw1556step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2141 node2141Labels := by rfl

theorem canonical1560 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1560 raw1560Labels = mixedMoment B node4679 node4679Labels := by
  calc
    mixedMoment B raw1560 raw1560Labels = mixedMoment B raw1560step0 raw1560step0Labels := by
      have ha : raw1560step0 = (fun i j => raw1560 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1560step0 raw1560; decide +kernel
      have hl : raw1560step0Labels = raw1560Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1560 raw1560Labels permutation152 permutation4
    mixedMoment B raw1560step0 raw1560step0Labels = mixedMoment B raw1560step1 raw1560step1Labels := by
      have ha : raw1560step1 = raw1560step0 := by apply Matrix.ext; unfold raw1560step1 raw1560step0; decide +kernel
      have hl : raw1560step0Labels = labelEmbedding7 ∘ raw1560step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1560step0 raw1560step0Labels raw1560step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4679 node4679Labels := by rfl

theorem canonical1561 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1561 raw1561Labels = mixedMoment B node1805 node1805Labels := by
  calc
    mixedMoment B raw1561 raw1561Labels = mixedMoment B raw1561step0 raw1561step0Labels := by
      have ha : raw1561step0 = (fun i j => raw1561 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1561step0 raw1561; decide +kernel
      have hl : raw1561step0Labels = raw1561Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1561 raw1561Labels permutation152 permutation4
    _ = mixedMoment B node1805 node1805Labels := by rfl

theorem canonical1562 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1562 raw1562Labels = mixedMoment B node2150 node2150Labels := by
  calc
    mixedMoment B raw1562 raw1562Labels = mixedMoment B raw1562step0 raw1562step0Labels := by
      have ha : raw1562step0 = (fun i j => raw1562 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1562step0 raw1562; decide +kernel
      have hl : raw1562step0Labels = raw1562Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1562 raw1562Labels permutation152 permutation6
    mixedMoment B raw1562step0 raw1562step0Labels = mixedMoment B raw1562step1 raw1562step1Labels := by
      have ha : raw1562step1 = -raw1562step0 := by apply Matrix.ext; change ∀ i j, raw1562step1 i j = -(raw1562step0 i j); unfold raw1562step1 raw1562step0; decide +kernel
      have hl : raw1562step1Labels = raw1562step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1562step1 raw1562step1Labels = mixedMoment B raw1562step2 raw1562step2Labels := by
      have ha : raw1562step2 = raw1562step1 := by apply Matrix.ext; unfold raw1562step2 raw1562step1; decide +kernel
      have hl : raw1562step1Labels = labelEmbedding1 ∘ raw1562step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1562step1 raw1562step1Labels raw1562step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2150 node2150Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical127
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical16288 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16288 raw16288Labels = mixedMoment B node5450 node5450Labels := by
  calc
    mixedMoment B raw16288 raw16288Labels = mixedMoment B raw16288step0 raw16288step0Labels := by
      have hz : ∀ j, raw16288 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw16288step0 = (fun i j => raw16288 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw16288step0 raw16288; decide +kernel
      have hl : raw16288step0Labels = raw16288Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16288 raw16288Labels permutation434 hz
    mixedMoment B raw16288step0 raw16288step0Labels = mixedMoment B raw16288step1 raw16288step1Labels := by
      have ha : raw16288step1 = (fun i j => raw16288step0 (permutation35 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16288step1 raw16288step0; decide +kernel
      have hl : raw16288step1Labels = raw16288step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16288step0 raw16288step0Labels permutation35 permutation3
    mixedMoment B raw16288step1 raw16288step1Labels = mixedMoment B raw16288step2 raw16288step2Labels := by
      have ha : raw16288step2 = raw16288step1 := by apply Matrix.ext; unfold raw16288step2 raw16288step1; decide +kernel
      have hl : raw16288step1Labels = labelEmbedding6 ∘ raw16288step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16288step1 raw16288step1Labels raw16288step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5450 node5450Labels := by rfl

theorem canonical16292 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16292 raw16292Labels = mixedMoment B node5450 node5450Labels := by
  calc
    mixedMoment B raw16292 raw16292Labels = mixedMoment B raw16292step0 raw16292step0Labels := by
      have hz : ∀ j, raw16292 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16292step0 = (fun i j => raw16292 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16292step0 raw16292; decide +kernel
      have hl : raw16292step0Labels = raw16292Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16292 raw16292Labels permutation346 hz
    mixedMoment B raw16292step0 raw16292step0Labels = mixedMoment B raw16292step1 raw16292step1Labels := by
      have ha : raw16292step1 = (fun i j => raw16292step0 (permutation35 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16292step1 raw16292step0; decide +kernel
      have hl : raw16292step1Labels = raw16292step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16292step0 raw16292step0Labels permutation35 permutation3
    mixedMoment B raw16292step1 raw16292step1Labels = mixedMoment B raw16292step2 raw16292step2Labels := by
      have ha : raw16292step2 = raw16292step1 := by apply Matrix.ext; unfold raw16292step2 raw16292step1; decide +kernel
      have hl : raw16292step1Labels = labelEmbedding6 ∘ raw16292step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16292step1 raw16292step1Labels raw16292step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5450 node5450Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical13
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical1725 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1725 raw1725Labels = mixedMoment B node4798 node4798Labels := by
  calc
    mixedMoment B raw1725 raw1725Labels = mixedMoment B raw1725step0 raw1725step0Labels := by
      have ha : raw1725step0 = (fun i j => raw1725 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1725step0 raw1725; decide +kernel
      have hl : raw1725step0Labels = raw1725Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1725 raw1725Labels permutation152 permutation4
    mixedMoment B raw1725step0 raw1725step0Labels = mixedMoment B raw1725step1 raw1725step1Labels := by
      have ha : raw1725step1 = raw1725step0 := by apply Matrix.ext; unfold raw1725step1 raw1725step0; decide +kernel
      have hl : raw1725step0Labels = labelEmbedding7 ∘ raw1725step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1725step0 raw1725step0Labels raw1725step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4798 node4798Labels := by rfl

theorem canonical1726 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1726 raw1726Labels = mixedMoment B node2016 node2016Labels := by
  calc
    mixedMoment B raw1726 raw1726Labels = mixedMoment B raw1726step0 raw1726step0Labels := by
      have ha : raw1726step0 = (fun i j => raw1726 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1726step0 raw1726; decide +kernel
      have hl : raw1726step0Labels = raw1726Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1726 raw1726Labels permutation152 permutation4
    _ = mixedMoment B node2016 node2016Labels := by rfl

theorem canonical1727 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1727 raw1727Labels = mixedMoment B node2075 node2075Labels := by
  calc
    mixedMoment B raw1727 raw1727Labels = mixedMoment B raw1727step0 raw1727step0Labels := by
      have ha : raw1727step0 = (fun i j => raw1727 (permutation200 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1727step0 raw1727; decide +kernel
      have hl : raw1727step0Labels = raw1727Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1727 raw1727Labels permutation200 permutation6
    mixedMoment B raw1727step0 raw1727step0Labels = mixedMoment B raw1727step1 raw1727step1Labels := by
      have ha : raw1727step1 = -raw1727step0 := by apply Matrix.ext; change ∀ i j, raw1727step1 i j = -(raw1727step0 i j); unfold raw1727step1 raw1727step0; decide +kernel
      have hl : raw1727step1Labels = raw1727step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1727step1 raw1727step1Labels = mixedMoment B raw1727step2 raw1727step2Labels := by
      have ha : raw1727step2 = raw1727step1 := by apply Matrix.ext; unfold raw1727step2 raw1727step1; decide +kernel
      have hl : raw1727step1Labels = labelEmbedding1 ∘ raw1727step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1727step1 raw1727step1Labels raw1727step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2075 node2075Labels := by rfl

theorem canonical1740 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1740 raw1740Labels = mixedMoment B node4805 node4805Labels := by
  calc
    mixedMoment B raw1740 raw1740Labels = mixedMoment B raw1740step0 raw1740step0Labels := by
      have ha : raw1740step0 = (fun i j => raw1740 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1740step0 raw1740; decide +kernel
      have hl : raw1740step0Labels = raw1740Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1740 raw1740Labels permutation152 permutation4
    mixedMoment B raw1740step0 raw1740step0Labels = mixedMoment B raw1740step1 raw1740step1Labels := by
      have ha : raw1740step1 = raw1740step0 := by apply Matrix.ext; unfold raw1740step1 raw1740step0; decide +kernel
      have hl : raw1740step0Labels = labelEmbedding7 ∘ raw1740step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1740step0 raw1740step0Labels raw1740step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4805 node4805Labels := by rfl

theorem canonical1741 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1741 raw1741Labels = mixedMoment B node2023 node2023Labels := by
  calc
    mixedMoment B raw1741 raw1741Labels = mixedMoment B raw1741step0 raw1741step0Labels := by
      have ha : raw1741step0 = (fun i j => raw1741 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1741step0 raw1741; decide +kernel
      have hl : raw1741step0Labels = raw1741Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1741 raw1741Labels permutation152 permutation4
    _ = mixedMoment B node2023 node2023Labels := by rfl

theorem canonical1742 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1742 raw1742Labels = mixedMoment B node2214 node2214Labels := by
  calc
    mixedMoment B raw1742 raw1742Labels = mixedMoment B raw1742step0 raw1742step0Labels := by
      have ha : raw1742step0 = (fun i j => raw1742 (permutation170 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1742step0 raw1742; decide +kernel
      have hl : raw1742step0Labels = raw1742Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1742 raw1742Labels permutation170 permutation6
    mixedMoment B raw1742step0 raw1742step0Labels = mixedMoment B raw1742step1 raw1742step1Labels := by
      have ha : raw1742step1 = -raw1742step0 := by apply Matrix.ext; change ∀ i j, raw1742step1 i j = -(raw1742step0 i j); unfold raw1742step1 raw1742step0; decide +kernel
      have hl : raw1742step1Labels = raw1742step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1742step1 raw1742step1Labels = mixedMoment B raw1742step2 raw1742step2Labels := by
      have ha : raw1742step2 = raw1742step1 := by apply Matrix.ext; unfold raw1742step2 raw1742step1; decide +kernel
      have hl : raw1742step1Labels = labelEmbedding1 ∘ raw1742step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1742step1 raw1742step1Labels raw1742step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2214 node2214Labels := by rfl

theorem canonical1752 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1752 raw1752Labels = mixedMoment B node4826 node4826Labels := by
  calc
    mixedMoment B raw1752 raw1752Labels = mixedMoment B raw1752step0 raw1752step0Labels := by
      have ha : raw1752step0 = (fun i j => raw1752 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1752step0 raw1752; decide +kernel
      have hl : raw1752step0Labels = raw1752Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1752 raw1752Labels permutation152 permutation4
    mixedMoment B raw1752step0 raw1752step0Labels = mixedMoment B raw1752step1 raw1752step1Labels := by
      have ha : raw1752step1 = raw1752step0 := by apply Matrix.ext; unfold raw1752step1 raw1752step0; decide +kernel
      have hl : raw1752step0Labels = labelEmbedding7 ∘ raw1752step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1752step0 raw1752step0Labels raw1752step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4826 node4826Labels := by rfl

theorem canonical1753 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1753 raw1753Labels = mixedMoment B node2046 node2046Labels := by
  calc
    mixedMoment B raw1753 raw1753Labels = mixedMoment B raw1753step0 raw1753step0Labels := by
      have ha : raw1753step0 = (fun i j => raw1753 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1753step0 raw1753; decide +kernel
      have hl : raw1753step0Labels = raw1753Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1753 raw1753Labels permutation152 permutation4
    _ = mixedMoment B node2046 node2046Labels := by rfl

theorem canonical1754 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1754 raw1754Labels = mixedMoment B node2077 node2077Labels := by
  calc
    mixedMoment B raw1754 raw1754Labels = mixedMoment B raw1754step0 raw1754step0Labels := by
      have ha : raw1754step0 = (fun i j => raw1754 (permutation176 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1754step0 raw1754; decide +kernel
      have hl : raw1754step0Labels = raw1754Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1754 raw1754Labels permutation176 permutation6
    mixedMoment B raw1754step0 raw1754step0Labels = mixedMoment B raw1754step1 raw1754step1Labels := by
      have ha : raw1754step1 = -raw1754step0 := by apply Matrix.ext; change ∀ i j, raw1754step1 i j = -(raw1754step0 i j); unfold raw1754step1 raw1754step0; decide +kernel
      have hl : raw1754step1Labels = raw1754step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1754step1 raw1754step1Labels = mixedMoment B raw1754step2 raw1754step2Labels := by
      have ha : raw1754step2 = raw1754step1 := by apply Matrix.ext; unfold raw1754step2 raw1754step1; decide +kernel
      have hl : raw1754step1Labels = labelEmbedding1 ∘ raw1754step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1754step1 raw1754step1Labels raw1754step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2077 node2077Labels := by rfl

theorem canonical1791 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1791 raw1791Labels = mixedMoment B node4865 node4865Labels := by
  calc
    mixedMoment B raw1791 raw1791Labels = mixedMoment B raw1791step0 raw1791step0Labels := by
      have ha : raw1791step0 = (fun i j => raw1791 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1791step0 raw1791; decide +kernel
      have hl : raw1791step0Labels = raw1791Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1791 raw1791Labels permutation32 permutation4
    mixedMoment B raw1791step0 raw1791step0Labels = mixedMoment B raw1791step1 raw1791step1Labels := by
      have ha : raw1791step1 = raw1791step0 := by apply Matrix.ext; unfold raw1791step1 raw1791step0; decide +kernel
      have hl : raw1791step0Labels = labelEmbedding7 ∘ raw1791step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1791step0 raw1791step0Labels raw1791step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4865 node4865Labels := by rfl

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

theorem canonical1792 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1792 raw1792Labels = mixedMoment B node2106 node2106Labels := by
  calc
    mixedMoment B raw1792 raw1792Labels = mixedMoment B raw1792step0 raw1792step0Labels := by
      have ha : raw1792step0 = (fun i j => raw1792 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1792step0 raw1792; decide +kernel
      have hl : raw1792step0Labels = raw1792Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1792 raw1792Labels permutation32 permutation4
    _ = mixedMoment B node2106 node2106Labels := by rfl

theorem canonical1793 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1793 raw1793Labels = mixedMoment B node2242 node2242Labels := by
  calc
    mixedMoment B raw1793 raw1793Labels = mixedMoment B raw1793step0 raw1793step0Labels := by
      have ha : raw1793step0 = (fun i j => raw1793 (permutation40 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1793step0 raw1793; decide +kernel
      have hl : raw1793step0Labels = raw1793Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1793 raw1793Labels permutation40 permutation6
    mixedMoment B raw1793step0 raw1793step0Labels = mixedMoment B raw1793step1 raw1793step1Labels := by
      have ha : raw1793step1 = -raw1793step0 := by apply Matrix.ext; change ∀ i j, raw1793step1 i j = -(raw1793step0 i j); unfold raw1793step1 raw1793step0; decide +kernel
      have hl : raw1793step1Labels = raw1793step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1793step1 raw1793step1Labels = mixedMoment B raw1793step2 raw1793step2Labels := by
      have ha : raw1793step2 = raw1793step1 := by apply Matrix.ext; unfold raw1793step2 raw1793step1; decide +kernel
      have hl : raw1793step1Labels = labelEmbedding1 ∘ raw1793step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1793step1 raw1793step1Labels raw1793step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2242 node2242Labels := by rfl

theorem canonical1794 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1794 raw1794Labels = mixedMoment B node4866 node4866Labels := by
  calc
    mixedMoment B raw1794 raw1794Labels = mixedMoment B raw1794step0 raw1794step0Labels := by
      have ha : raw1794step0 = (fun i j => raw1794 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1794step0 raw1794; decide +kernel
      have hl : raw1794step0Labels = raw1794Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1794 raw1794Labels permutation32 permutation4
    mixedMoment B raw1794step0 raw1794step0Labels = mixedMoment B raw1794step1 raw1794step1Labels := by
      have ha : raw1794step1 = raw1794step0 := by apply Matrix.ext; unfold raw1794step1 raw1794step0; decide +kernel
      have hl : raw1794step0Labels = labelEmbedding7 ∘ raw1794step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1794step0 raw1794step0Labels raw1794step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4866 node4866Labels := by rfl

theorem canonical1795 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1795 raw1795Labels = mixedMoment B node2107 node2107Labels := by
  calc
    mixedMoment B raw1795 raw1795Labels = mixedMoment B raw1795step0 raw1795step0Labels := by
      have ha : raw1795step0 = (fun i j => raw1795 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1795step0 raw1795; decide +kernel
      have hl : raw1795step0Labels = raw1795Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1795 raw1795Labels permutation32 permutation4
    _ = mixedMoment B node2107 node2107Labels := by rfl

theorem canonical1796 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1796 raw1796Labels = mixedMoment B node2260 node2260Labels := by
  calc
    mixedMoment B raw1796 raw1796Labels = mixedMoment B raw1796step0 raw1796step0Labels := by
      have ha : raw1796step0 = (fun i j => raw1796 (permutation38 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1796step0 raw1796; decide +kernel
      have hl : raw1796step0Labels = raw1796Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1796 raw1796Labels permutation38 permutation6
    mixedMoment B raw1796step0 raw1796step0Labels = mixedMoment B raw1796step1 raw1796step1Labels := by
      have ha : raw1796step1 = -raw1796step0 := by apply Matrix.ext; change ∀ i j, raw1796step1 i j = -(raw1796step0 i j); unfold raw1796step1 raw1796step0; decide +kernel
      have hl : raw1796step1Labels = raw1796step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1796step1 raw1796step1Labels = mixedMoment B raw1796step2 raw1796step2Labels := by
      have ha : raw1796step2 = raw1796step1 := by apply Matrix.ext; unfold raw1796step2 raw1796step1; decide +kernel
      have hl : raw1796step1Labels = labelEmbedding1 ∘ raw1796step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1796step1 raw1796step1Labels raw1796step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2260 node2260Labels := by rfl

theorem canonical1818 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1818 raw1818Labels = mixedMoment B node4889 node4889Labels := by
  calc
    mixedMoment B raw1818 raw1818Labels = mixedMoment B raw1818step0 raw1818step0Labels := by
      have ha : raw1818step0 = (fun i j => raw1818 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1818step0 raw1818; decide +kernel
      have hl : raw1818step0Labels = raw1818Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1818 raw1818Labels permutation32 permutation4
    mixedMoment B raw1818step0 raw1818step0Labels = mixedMoment B raw1818step1 raw1818step1Labels := by
      have ha : raw1818step1 = raw1818step0 := by apply Matrix.ext; unfold raw1818step1 raw1818step0; decide +kernel
      have hl : raw1818step0Labels = labelEmbedding7 ∘ raw1818step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1818step0 raw1818step0Labels raw1818step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4889 node4889Labels := by rfl

theorem canonical1819 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1819 raw1819Labels = mixedMoment B node2245 node2245Labels := by
  calc
    mixedMoment B raw1819 raw1819Labels = mixedMoment B raw1819step0 raw1819step0Labels := by
      have ha : raw1819step0 = (fun i j => raw1819 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1819step0 raw1819; decide +kernel
      have hl : raw1819step0Labels = raw1819Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1819 raw1819Labels permutation32 permutation4
    _ = mixedMoment B node2245 node2245Labels := by rfl

theorem canonical1820 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1820 raw1820Labels = mixedMoment B node2277 node2277Labels := by
  calc
    mixedMoment B raw1820 raw1820Labels = mixedMoment B raw1820step0 raw1820step0Labels := by
      have ha : raw1820step0 = (fun i j => raw1820 (permutation50 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1820step0 raw1820; decide +kernel
      have hl : raw1820step0Labels = raw1820Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1820 raw1820Labels permutation50 permutation6
    mixedMoment B raw1820step0 raw1820step0Labels = mixedMoment B raw1820step1 raw1820step1Labels := by
      have ha : raw1820step1 = -raw1820step0 := by apply Matrix.ext; change ∀ i j, raw1820step1 i j = -(raw1820step0 i j); unfold raw1820step1 raw1820step0; decide +kernel
      have hl : raw1820step1Labels = raw1820step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1820step1 raw1820step1Labels = mixedMoment B raw1820step2 raw1820step2Labels := by
      have ha : raw1820step2 = raw1820step1 := by apply Matrix.ext; unfold raw1820step2 raw1820step1; decide +kernel
      have hl : raw1820step1Labels = labelEmbedding1 ∘ raw1820step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1820step1 raw1820step1Labels raw1820step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2277 node2277Labels := by rfl

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

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical243
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical31203 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31203 raw31203Labels = mixedMoment B node4866 node4866Labels := by
  calc
    mixedMoment B raw31203 raw31203Labels = mixedMoment B raw31203step0 raw31203step0Labels := by
      have hz : ∀ j, raw31203 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31203step0 = (fun i j => raw31203 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31203step0 raw31203; decide +kernel
      have hl : raw31203step0Labels = raw31203Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31203 raw31203Labels permutation434 hz
    mixedMoment B raw31203step0 raw31203step0Labels = mixedMoment B raw31203step1 raw31203step1Labels := by
      have ha : raw31203step1 = (fun i j => raw31203step0 (permutation36 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31203step1 raw31203step0; decide +kernel
      have hl : raw31203step1Labels = raw31203step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31203step0 raw31203step0Labels permutation36 permutation3
    mixedMoment B raw31203step1 raw31203step1Labels = mixedMoment B raw31203step2 raw31203step2Labels := by
      have ha : raw31203step2 = raw31203step1 := by apply Matrix.ext; unfold raw31203step2 raw31203step1; decide +kernel
      have hl : raw31203step1Labels = labelEmbedding6 ∘ raw31203step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31203step1 raw31203step1Labels raw31203step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4866 node4866Labels := by rfl

theorem canonical31207 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31207 raw31207Labels = mixedMoment B node4866 node4866Labels := by
  calc
    mixedMoment B raw31207 raw31207Labels = mixedMoment B raw31207step0 raw31207step0Labels := by
      have hz : ∀ j, raw31207 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw31207step0 = (fun i j => raw31207 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw31207step0 raw31207; decide +kernel
      have hl : raw31207step0Labels = raw31207Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31207 raw31207Labels permutation346 hz
    mixedMoment B raw31207step0 raw31207step0Labels = mixedMoment B raw31207step1 raw31207step1Labels := by
      have ha : raw31207step1 = (fun i j => raw31207step0 (permutation36 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31207step1 raw31207step0; decide +kernel
      have hl : raw31207step1Labels = raw31207step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31207step0 raw31207step0Labels permutation36 permutation3
    mixedMoment B raw31207step1 raw31207step1Labels = mixedMoment B raw31207step2 raw31207step2Labels := by
      have ha : raw31207step2 = raw31207step1 := by apply Matrix.ext; unfold raw31207step2 raw31207step1; decide +kernel
      have hl : raw31207step1Labels = labelEmbedding6 ∘ raw31207step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31207step1 raw31207step1Labels raw31207step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4866 node4866Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical262
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical33616 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33616 raw33616Labels = mixedMoment B node4232 node4232Labels := by
  calc
    mixedMoment B raw33616 raw33616Labels = mixedMoment B raw33616step0 raw33616step0Labels := by
      have ha : raw33616step0 = (fun i j => raw33616 (permutation164 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33616step0 raw33616; decide +kernel
      have hl : raw33616step0Labels = raw33616Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33616 raw33616Labels permutation164 permutation3
    mixedMoment B raw33616step0 raw33616step0Labels = mixedMoment B raw33616step1 raw33616step1Labels := by
      have ha : raw33616step1 = raw33616step0 := by apply Matrix.ext; unfold raw33616step1 raw33616step0; decide +kernel
      have hl : raw33616step0Labels = labelEmbedding6 ∘ raw33616step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33616step0 raw33616step0Labels raw33616step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4232 node4232Labels := by rfl

theorem canonical33617 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33617 raw33617Labels = mixedMoment B node4679 node4679Labels := by
  calc
    mixedMoment B raw33617 raw33617Labels = mixedMoment B raw33617step0 raw33617step0Labels := by
      have ha : raw33617step0 = (fun i j => raw33617 (permutation164 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33617step0 raw33617; decide +kernel
      have hl : raw33617step0Labels = raw33617Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33617 raw33617Labels permutation164 permutation3
    mixedMoment B raw33617step0 raw33617step0Labels = mixedMoment B raw33617step1 raw33617step1Labels := by
      have ha : raw33617step1 = raw33617step0 := by apply Matrix.ext; unfold raw33617step1 raw33617step0; decide +kernel
      have hl : raw33617step0Labels = labelEmbedding6 ∘ raw33617step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33617step0 raw33617step0Labels raw33617step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4679 node4679Labels := by rfl

theorem canonical33618 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33618 raw33618Labels = mixedMoment B node4826 node4826Labels := by
  calc
    mixedMoment B raw33618 raw33618Labels = mixedMoment B raw33618step0 raw33618step0Labels := by
      have ha : raw33618step0 = (fun i j => raw33618 (permutation224 i) (permutation5 j)) := by apply Matrix.ext; unfold raw33618step0 raw33618; decide +kernel
      have hl : raw33618step0Labels = raw33618Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33618 raw33618Labels permutation224 permutation5
    mixedMoment B raw33618step0 raw33618step0Labels = mixedMoment B raw33618step1 raw33618step1Labels := by
      have ha : raw33618step1 = -raw33618step0 := by apply Matrix.ext; change ∀ i j, raw33618step1 i j = -(raw33618step0 i j); unfold raw33618step1 raw33618step0; decide +kernel
      have hl : raw33618step1Labels = raw33618step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33618step1 raw33618step1Labels = mixedMoment B raw33618step2 raw33618step2Labels := by
      have ha : raw33618step2 = raw33618step1 := by apply Matrix.ext; unfold raw33618step2 raw33618step1; decide +kernel
      have hl : raw33618step1Labels = labelEmbedding8 ∘ raw33618step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33618step1 raw33618step1Labels raw33618step2Labels labelEmbedding8 hl
    _ = mixedMoment B node4826 node4826Labels := by rfl

theorem canonical33624 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33624 raw33624Labels = mixedMoment B node4865 node4865Labels := by
  calc
    mixedMoment B raw33624 raw33624Labels = mixedMoment B raw33624step0 raw33624step0Labels := by
      have hz : ∀ j, raw33624 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33624step0 = (fun i j => raw33624 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33624step0 raw33624; decide +kernel
      have hl : raw33624step0Labels = raw33624Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33624 raw33624Labels permutation346 hz
    mixedMoment B raw33624step0 raw33624step0Labels = mixedMoment B raw33624step1 raw33624step1Labels := by
      have ha : raw33624step1 = (fun i j => raw33624step0 (permutation35 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33624step1 raw33624step0; decide +kernel
      have hl : raw33624step1Labels = raw33624step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33624step0 raw33624step0Labels permutation35 permutation3
    mixedMoment B raw33624step1 raw33624step1Labels = mixedMoment B raw33624step2 raw33624step2Labels := by
      have ha : raw33624step2 = raw33624step1 := by apply Matrix.ext; unfold raw33624step2 raw33624step1; decide +kernel
      have hl : raw33624step1Labels = labelEmbedding6 ∘ raw33624step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33624step1 raw33624step1Labels raw33624step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4865 node4865Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical270
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical34636 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34636 raw34636Labels = mixedMoment B node5386 node5386Labels := by
  calc
    mixedMoment B raw34636 raw34636Labels = mixedMoment B raw34636step0 raw34636step0Labels := by
      have ha : raw34636step0 = (fun i j => raw34636 (permutation265 i) (permutation2 j)) := by apply Matrix.ext; unfold raw34636step0 raw34636; decide +kernel
      have hl : raw34636step0Labels = raw34636Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34636 raw34636Labels permutation265 permutation2
    _ = mixedMoment B node5386 node5386Labels := by rfl

theorem canonical34637 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34637 raw34637Labels = mixedMoment B node5431 node5431Labels := by
  calc
    mixedMoment B raw34637 raw34637Labels = mixedMoment B raw34637step0 raw34637step0Labels := by
      have ha : raw34637step0 = (fun i j => raw34637 (permutation240 i) (permutation5 j)) := by apply Matrix.ext; unfold raw34637step0 raw34637; decide +kernel
      have hl : raw34637step0Labels = raw34637Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34637 raw34637Labels permutation240 permutation5
    mixedMoment B raw34637step0 raw34637step0Labels = mixedMoment B raw34637step1 raw34637step1Labels := by
      have ha : raw34637step1 = -raw34637step0 := by apply Matrix.ext; change ∀ i j, raw34637step1 i j = -(raw34637step0 i j); unfold raw34637step1 raw34637step0; decide +kernel
      have hl : raw34637step1Labels = raw34637step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34637step1 raw34637step1Labels = mixedMoment B raw34637step2 raw34637step2Labels := by
      have ha : raw34637step2 = raw34637step1 := by apply Matrix.ext; unfold raw34637step2 raw34637step1; decide +kernel
      have hl : raw34637step1Labels = labelEmbedding8 ∘ raw34637step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34637step1 raw34637step1Labels raw34637step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5431 node5431Labels := by rfl

theorem canonical34638 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34638 raw34638Labels = mixedMoment B node5431 node5431Labels := by
  calc
    mixedMoment B raw34638 raw34638Labels = mixedMoment B raw34638step0 raw34638step0Labels := by
      have ha : raw34638step0 = (fun i j => raw34638 (permutation260 i) (permutation5 j)) := by apply Matrix.ext; unfold raw34638step0 raw34638; decide +kernel
      have hl : raw34638step0Labels = raw34638Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34638 raw34638Labels permutation260 permutation5
    mixedMoment B raw34638step0 raw34638step0Labels = mixedMoment B raw34638step1 raw34638step1Labels := by
      have ha : raw34638step1 = -raw34638step0 := by apply Matrix.ext; change ∀ i j, raw34638step1 i j = -(raw34638step0 i j); unfold raw34638step1 raw34638step0; decide +kernel
      have hl : raw34638step1Labels = raw34638step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34638step1 raw34638step1Labels = mixedMoment B raw34638step2 raw34638step2Labels := by
      have ha : raw34638step2 = raw34638step1 := by apply Matrix.ext; unfold raw34638step2 raw34638step1; decide +kernel
      have hl : raw34638step1Labels = labelEmbedding8 ∘ raw34638step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34638step1 raw34638step1Labels raw34638step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5431 node5431Labels := by rfl

theorem canonical34639 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34639 raw34639Labels = mixedMoment B node4252 node4252Labels := by
  calc
    mixedMoment B raw34639 raw34639Labels = mixedMoment B raw34639step0 raw34639step0Labels := by
      have ha : raw34639step0 = (fun i j => raw34639 (permutation243 i) (permutation5 j)) := by apply Matrix.ext; unfold raw34639step0 raw34639; decide +kernel
      have hl : raw34639step0Labels = raw34639Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34639 raw34639Labels permutation243 permutation5
    mixedMoment B raw34639step0 raw34639step0Labels = mixedMoment B raw34639step1 raw34639step1Labels := by
      have ha : raw34639step1 = -raw34639step0 := by apply Matrix.ext; change ∀ i j, raw34639step1 i j = -(raw34639step0 i j); unfold raw34639step1 raw34639step0; decide +kernel
      have hl : raw34639step1Labels = raw34639step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34639step1 raw34639step1Labels = mixedMoment B raw34639step2 raw34639step2Labels := by
      have ha : raw34639step2 = raw34639step1 := by apply Matrix.ext; unfold raw34639step2 raw34639step1; decide +kernel
      have hl : raw34639step1Labels = labelEmbedding8 ∘ raw34639step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34639step1 raw34639step1Labels raw34639step2Labels labelEmbedding8 hl
    _ = mixedMoment B node4252 node4252Labels := by rfl

theorem canonical34640 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34640 raw34640Labels = mixedMoment B node4805 node4805Labels := by
  calc
    mixedMoment B raw34640 raw34640Labels = mixedMoment B raw34640step0 raw34640step0Labels := by
      have ha : raw34640step0 = (fun i j => raw34640 (permutation243 i) (permutation5 j)) := by apply Matrix.ext; unfold raw34640step0 raw34640; decide +kernel
      have hl : raw34640step0Labels = raw34640Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34640 raw34640Labels permutation243 permutation5
    mixedMoment B raw34640step0 raw34640step0Labels = mixedMoment B raw34640step1 raw34640step1Labels := by
      have ha : raw34640step1 = -raw34640step0 := by apply Matrix.ext; change ∀ i j, raw34640step1 i j = -(raw34640step0 i j); unfold raw34640step1 raw34640step0; decide +kernel
      have hl : raw34640step1Labels = raw34640step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34640step1 raw34640step1Labels = mixedMoment B raw34640step2 raw34640step2Labels := by
      have ha : raw34640step2 = raw34640step1 := by apply Matrix.ext; unfold raw34640step2 raw34640step1; decide +kernel
      have hl : raw34640step1Labels = labelEmbedding8 ∘ raw34640step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34640step1 raw34640step1Labels raw34640step2Labels labelEmbedding8 hl
    _ = mixedMoment B node4805 node4805Labels := by rfl

theorem canonical34641 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34641 raw34641Labels = mixedMoment B node4805 node4805Labels := by
  calc
    mixedMoment B raw34641 raw34641Labels = mixedMoment B raw34641step0 raw34641step0Labels := by
      have ha : raw34641step0 = (fun i j => raw34641 (permutation263 i) (permutation5 j)) := by apply Matrix.ext; unfold raw34641step0 raw34641; decide +kernel
      have hl : raw34641step0Labels = raw34641Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34641 raw34641Labels permutation263 permutation5
    mixedMoment B raw34641step0 raw34641step0Labels = mixedMoment B raw34641step1 raw34641step1Labels := by
      have ha : raw34641step1 = -raw34641step0 := by apply Matrix.ext; change ∀ i j, raw34641step1 i j = -(raw34641step0 i j); unfold raw34641step1 raw34641step0; decide +kernel
      have hl : raw34641step1Labels = raw34641step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34641step1 raw34641step1Labels = mixedMoment B raw34641step2 raw34641step2Labels := by
      have ha : raw34641step2 = raw34641step1 := by apply Matrix.ext; unfold raw34641step2 raw34641step1; decide +kernel
      have hl : raw34641step1Labels = labelEmbedding8 ∘ raw34641step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34641step1 raw34641step1Labels raw34641step2Labels labelEmbedding8 hl
    _ = mixedMoment B node4805 node4805Labels := by rfl

theorem canonical34642 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34642 raw34642Labels = mixedMoment B node4230 node4230Labels := by
  calc
    mixedMoment B raw34642 raw34642Labels = mixedMoment B raw34642step0 raw34642step0Labels := by
      have ha : raw34642step0 = (fun i j => raw34642 (permutation169 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34642step0 raw34642; decide +kernel
      have hl : raw34642step0Labels = raw34642Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34642 raw34642Labels permutation169 permutation3
    mixedMoment B raw34642step0 raw34642step0Labels = mixedMoment B raw34642step1 raw34642step1Labels := by
      have ha : raw34642step1 = raw34642step0 := by apply Matrix.ext; unfold raw34642step1 raw34642step0; decide +kernel
      have hl : raw34642step0Labels = labelEmbedding6 ∘ raw34642step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34642step0 raw34642step0Labels raw34642step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4230 node4230Labels := by rfl

theorem canonical34643 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34643 raw34643Labels = mixedMoment B node4676 node4676Labels := by
  calc
    mixedMoment B raw34643 raw34643Labels = mixedMoment B raw34643step0 raw34643step0Labels := by
      have ha : raw34643step0 = (fun i j => raw34643 (permutation169 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34643step0 raw34643; decide +kernel
      have hl : raw34643step0Labels = raw34643Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34643 raw34643Labels permutation169 permutation3
    mixedMoment B raw34643step0 raw34643step0Labels = mixedMoment B raw34643step1 raw34643step1Labels := by
      have ha : raw34643step1 = raw34643step0 := by apply Matrix.ext; unfold raw34643step1 raw34643step0; decide +kernel
      have hl : raw34643step0Labels = labelEmbedding6 ∘ raw34643step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34643step0 raw34643step0Labels raw34643step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4676 node4676Labels := by rfl

theorem canonical34644 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34644 raw34644Labels = mixedMoment B node4865 node4865Labels := by
  calc
    mixedMoment B raw34644 raw34644Labels = mixedMoment B raw34644step0 raw34644step0Labels := by
      have hz : ∀ j, raw34644 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw34644step0 = (fun i j => raw34644 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw34644step0 raw34644; decide +kernel
      have hl : raw34644step0Labels = raw34644Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34644 raw34644Labels permutation434 hz
    mixedMoment B raw34644step0 raw34644step0Labels = mixedMoment B raw34644step1 raw34644step1Labels := by
      have ha : raw34644step1 = (fun i j => raw34644step0 (permutation35 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34644step1 raw34644step0; decide +kernel
      have hl : raw34644step1Labels = raw34644step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34644step0 raw34644step0Labels permutation35 permutation3
    mixedMoment B raw34644step1 raw34644step1Labels = mixedMoment B raw34644step2 raw34644step2Labels := by
      have ha : raw34644step2 = raw34644step1 := by apply Matrix.ext; unfold raw34644step2 raw34644step1; decide +kernel
      have hl : raw34644step1Labels = labelEmbedding6 ∘ raw34644step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34644step1 raw34644step1Labels raw34644step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4865 node4865Labels := by rfl

theorem canonical34645 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34645 raw34645Labels = mixedMoment B node4798 node4798Labels := by
  calc
    mixedMoment B raw34645 raw34645Labels = mixedMoment B raw34645step0 raw34645step0Labels := by
      have ha : raw34645step0 = (fun i j => raw34645 (permutation241 i) (permutation5 j)) := by apply Matrix.ext; unfold raw34645step0 raw34645; decide +kernel
      have hl : raw34645step0Labels = raw34645Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34645 raw34645Labels permutation241 permutation5
    mixedMoment B raw34645step0 raw34645step0Labels = mixedMoment B raw34645step1 raw34645step1Labels := by
      have ha : raw34645step1 = -raw34645step0 := by apply Matrix.ext; change ∀ i j, raw34645step1 i j = -(raw34645step0 i j); unfold raw34645step1 raw34645step0; decide +kernel
      have hl : raw34645step1Labels = raw34645step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34645step1 raw34645step1Labels = mixedMoment B raw34645step2 raw34645step2Labels := by
      have ha : raw34645step2 = raw34645step1 := by apply Matrix.ext; unfold raw34645step2 raw34645step1; decide +kernel
      have hl : raw34645step1Labels = labelEmbedding8 ∘ raw34645step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34645step1 raw34645step1Labels raw34645step2Labels labelEmbedding8 hl
    _ = mixedMoment B node4798 node4798Labels := by rfl

theorem canonical34646 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34646 raw34646Labels = mixedMoment B node4798 node4798Labels := by
  calc
    mixedMoment B raw34646 raw34646Labels = mixedMoment B raw34646step0 raw34646step0Labels := by
      have ha : raw34646step0 = (fun i j => raw34646 (permutation261 i) (permutation5 j)) := by apply Matrix.ext; unfold raw34646step0 raw34646; decide +kernel
      have hl : raw34646step0Labels = raw34646Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34646 raw34646Labels permutation261 permutation5
    mixedMoment B raw34646step0 raw34646step0Labels = mixedMoment B raw34646step1 raw34646step1Labels := by
      have ha : raw34646step1 = -raw34646step0 := by apply Matrix.ext; change ∀ i j, raw34646step1 i j = -(raw34646step0 i j); unfold raw34646step1 raw34646step0; decide +kernel
      have hl : raw34646step1Labels = raw34646step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34646step1 raw34646step1Labels = mixedMoment B raw34646step2 raw34646step2Labels := by
      have ha : raw34646step2 = raw34646step1 := by apply Matrix.ext; unfold raw34646step2 raw34646step1; decide +kernel
      have hl : raw34646step1Labels = labelEmbedding8 ∘ raw34646step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34646step1 raw34646step1Labels raw34646step2Labels labelEmbedding8 hl
    _ = mixedMoment B node4798 node4798Labels := by rfl

theorem canonical34647 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34647 raw34647Labels = mixedMoment B node4230 node4230Labels := by
  calc
    mixedMoment B raw34647 raw34647Labels = mixedMoment B raw34647step0 raw34647step0Labels := by
      have ha : raw34647step0 = (fun i j => raw34647 (permutation168 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34647step0 raw34647; decide +kernel
      have hl : raw34647step0Labels = raw34647Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34647 raw34647Labels permutation168 permutation3
    mixedMoment B raw34647step0 raw34647step0Labels = mixedMoment B raw34647step1 raw34647step1Labels := by
      have ha : raw34647step1 = raw34647step0 := by apply Matrix.ext; unfold raw34647step1 raw34647step0; decide +kernel
      have hl : raw34647step0Labels = labelEmbedding6 ∘ raw34647step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34647step0 raw34647step0Labels raw34647step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4230 node4230Labels := by rfl

theorem canonical34648 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34648 raw34648Labels = mixedMoment B node4676 node4676Labels := by
  calc
    mixedMoment B raw34648 raw34648Labels = mixedMoment B raw34648step0 raw34648step0Labels := by
      have ha : raw34648step0 = (fun i j => raw34648 (permutation168 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34648step0 raw34648; decide +kernel
      have hl : raw34648step0Labels = raw34648Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34648 raw34648Labels permutation168 permutation3
    mixedMoment B raw34648step0 raw34648step0Labels = mixedMoment B raw34648step1 raw34648step1Labels := by
      have ha : raw34648step1 = raw34648step0 := by apply Matrix.ext; unfold raw34648step1 raw34648step0; decide +kernel
      have hl : raw34648step0Labels = labelEmbedding6 ∘ raw34648step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34648step0 raw34648step0Labels raw34648step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4676 node4676Labels := by rfl

theorem canonical34649 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34649 raw34649Labels = mixedMoment B node4798 node4798Labels := by
  calc
    mixedMoment B raw34649 raw34649Labels = mixedMoment B raw34649step0 raw34649step0Labels := by
      have ha : raw34649step0 = (fun i j => raw34649 (permutation240 i) (permutation5 j)) := by apply Matrix.ext; unfold raw34649step0 raw34649; decide +kernel
      have hl : raw34649step0Labels = raw34649Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34649 raw34649Labels permutation240 permutation5
    mixedMoment B raw34649step0 raw34649step0Labels = mixedMoment B raw34649step1 raw34649step1Labels := by
      have ha : raw34649step1 = -raw34649step0 := by apply Matrix.ext; change ∀ i j, raw34649step1 i j = -(raw34649step0 i j); unfold raw34649step1 raw34649step0; decide +kernel
      have hl : raw34649step1Labels = raw34649step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34649step1 raw34649step1Labels = mixedMoment B raw34649step2 raw34649step2Labels := by
      have ha : raw34649step2 = raw34649step1 := by apply Matrix.ext; unfold raw34649step2 raw34649step1; decide +kernel
      have hl : raw34649step1Labels = labelEmbedding8 ∘ raw34649step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34649step1 raw34649step1Labels raw34649step2Labels labelEmbedding8 hl
    _ = mixedMoment B node4798 node4798Labels := by rfl

theorem canonical34650 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34650 raw34650Labels = mixedMoment B node4798 node4798Labels := by
  calc
    mixedMoment B raw34650 raw34650Labels = mixedMoment B raw34650step0 raw34650step0Labels := by
      have ha : raw34650step0 = (fun i j => raw34650 (permutation260 i) (permutation5 j)) := by apply Matrix.ext; unfold raw34650step0 raw34650; decide +kernel
      have hl : raw34650step0Labels = raw34650Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34650 raw34650Labels permutation260 permutation5
    mixedMoment B raw34650step0 raw34650step0Labels = mixedMoment B raw34650step1 raw34650step1Labels := by
      have ha : raw34650step1 = -raw34650step0 := by apply Matrix.ext; change ∀ i j, raw34650step1 i j = -(raw34650step0 i j); unfold raw34650step1 raw34650step0; decide +kernel
      have hl : raw34650step1Labels = raw34650step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34650step1 raw34650step1Labels = mixedMoment B raw34650step2 raw34650step2Labels := by
      have ha : raw34650step2 = raw34650step1 := by apply Matrix.ext; unfold raw34650step2 raw34650step1; decide +kernel
      have hl : raw34650step1Labels = labelEmbedding8 ∘ raw34650step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34650step1 raw34650step1Labels raw34650step2Labels labelEmbedding8 hl
    _ = mixedMoment B node4798 node4798Labels := by rfl

theorem canonical34651 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34651 raw34651Labels = mixedMoment B node4232 node4232Labels := by
  calc
    mixedMoment B raw34651 raw34651Labels = mixedMoment B raw34651step0 raw34651step0Labels := by
      have ha : raw34651step0 = (fun i j => raw34651 (permutation170 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34651step0 raw34651; decide +kernel
      have hl : raw34651step0Labels = raw34651Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34651 raw34651Labels permutation170 permutation3
    mixedMoment B raw34651step0 raw34651step0Labels = mixedMoment B raw34651step1 raw34651step1Labels := by
      have ha : raw34651step1 = raw34651step0 := by apply Matrix.ext; unfold raw34651step1 raw34651step0; decide +kernel
      have hl : raw34651step0Labels = labelEmbedding6 ∘ raw34651step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34651step0 raw34651step0Labels raw34651step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4232 node4232Labels := by rfl

theorem canonical34652 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34652 raw34652Labels = mixedMoment B node4679 node4679Labels := by
  calc
    mixedMoment B raw34652 raw34652Labels = mixedMoment B raw34652step0 raw34652step0Labels := by
      have ha : raw34652step0 = (fun i j => raw34652 (permutation170 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34652step0 raw34652; decide +kernel
      have hl : raw34652step0Labels = raw34652Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34652 raw34652Labels permutation170 permutation3
    mixedMoment B raw34652step0 raw34652step0Labels = mixedMoment B raw34652step1 raw34652step1Labels := by
      have ha : raw34652step1 = raw34652step0 := by apply Matrix.ext; unfold raw34652step1 raw34652step0; decide +kernel
      have hl : raw34652step0Labels = labelEmbedding6 ∘ raw34652step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34652step0 raw34652step0Labels raw34652step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4679 node4679Labels := by rfl

theorem canonical34653 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34653 raw34653Labels = mixedMoment B node4826 node4826Labels := by
  calc
    mixedMoment B raw34653 raw34653Labels = mixedMoment B raw34653step0 raw34653step0Labels := by
      have ha : raw34653step0 = (fun i j => raw34653 (permutation246 i) (permutation5 j)) := by apply Matrix.ext; unfold raw34653step0 raw34653; decide +kernel
      have hl : raw34653step0Labels = raw34653Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34653 raw34653Labels permutation246 permutation5
    mixedMoment B raw34653step0 raw34653step0Labels = mixedMoment B raw34653step1 raw34653step1Labels := by
      have ha : raw34653step1 = -raw34653step0 := by apply Matrix.ext; change ∀ i j, raw34653step1 i j = -(raw34653step0 i j); unfold raw34653step1 raw34653step0; decide +kernel
      have hl : raw34653step1Labels = raw34653step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34653step1 raw34653step1Labels = mixedMoment B raw34653step2 raw34653step2Labels := by
      have ha : raw34653step2 = raw34653step1 := by apply Matrix.ext; unfold raw34653step2 raw34653step1; decide +kernel
      have hl : raw34653step1Labels = labelEmbedding8 ∘ raw34653step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34653step1 raw34653step1Labels raw34653step2Labels labelEmbedding8 hl
    _ = mixedMoment B node4826 node4826Labels := by rfl

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

theorem canonical924 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw924 raw924Labels = mixedMoment B node4230 node4230Labels := by
  calc
    mixedMoment B raw924 raw924Labels = mixedMoment B raw924step0 raw924step0Labels := by
      have ha : raw924step0 = (fun i j => raw924 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw924step0 raw924; decide +kernel
      have hl : raw924step0Labels = raw924Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw924 raw924Labels permutation152 permutation4
    mixedMoment B raw924step0 raw924step0Labels = mixedMoment B raw924step1 raw924step1Labels := by
      have ha : raw924step1 = raw924step0 := by apply Matrix.ext; unfold raw924step1 raw924step0; decide +kernel
      have hl : raw924step0Labels = labelEmbedding7 ∘ raw924step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw924step0 raw924step0Labels raw924step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4230 node4230Labels := by rfl

theorem canonical925 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw925 raw925Labels = mixedMoment B node730 node730Labels := by
  calc
    mixedMoment B raw925 raw925Labels = mixedMoment B raw925step0 raw925step0Labels := by
      have ha : raw925step0 = (fun i j => raw925 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw925step0 raw925; decide +kernel
      have hl : raw925step0Labels = raw925Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw925 raw925Labels permutation152 permutation4
    _ = mixedMoment B node730 node730Labels := by rfl

theorem canonical926 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw926 raw926Labels = mixedMoment B node780 node780Labels := by
  calc
    mixedMoment B raw926 raw926Labels = mixedMoment B raw926step0 raw926step0Labels := by
      have ha : raw926step0 = (fun i j => raw926 (permutation182 i) (permutation6 j)) := by apply Matrix.ext; unfold raw926step0 raw926; decide +kernel
      have hl : raw926step0Labels = raw926Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw926 raw926Labels permutation182 permutation6
    mixedMoment B raw926step0 raw926step0Labels = mixedMoment B raw926step1 raw926step1Labels := by
      have ha : raw926step1 = -raw926step0 := by apply Matrix.ext; change ∀ i j, raw926step1 i j = -(raw926step0 i j); unfold raw926step1 raw926step0; decide +kernel
      have hl : raw926step1Labels = raw926step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw926step1 raw926step1Labels = mixedMoment B raw926step2 raw926step2Labels := by
      have ha : raw926step2 = raw926step1 := by apply Matrix.ext; unfold raw926step2 raw926step1; decide +kernel
      have hl : raw926step1Labels = labelEmbedding1 ∘ raw926step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw926step1 raw926step1Labels raw926step2Labels labelEmbedding1 hl
    _ = mixedMoment B node780 node780Labels := by rfl

theorem canonical930 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw930 raw930Labels = mixedMoment B node4232 node4232Labels := by
  calc
    mixedMoment B raw930 raw930Labels = mixedMoment B raw930step0 raw930step0Labels := by
      have ha : raw930step0 = (fun i j => raw930 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw930step0 raw930; decide +kernel
      have hl : raw930step0Labels = raw930Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw930 raw930Labels permutation152 permutation4
    mixedMoment B raw930step0 raw930step0Labels = mixedMoment B raw930step1 raw930step1Labels := by
      have ha : raw930step1 = raw930step0 := by apply Matrix.ext; unfold raw930step1 raw930step0; decide +kernel
      have hl : raw930step0Labels = labelEmbedding7 ∘ raw930step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw930step0 raw930step0Labels raw930step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4232 node4232Labels := by rfl

theorem canonical931 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw931 raw931Labels = mixedMoment B node732 node732Labels := by
  calc
    mixedMoment B raw931 raw931Labels = mixedMoment B raw931step0 raw931step0Labels := by
      have ha : raw931step0 = (fun i j => raw931 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw931step0 raw931; decide +kernel
      have hl : raw931step0Labels = raw931Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw931 raw931Labels permutation152 permutation4
    _ = mixedMoment B node732 node732Labels := by rfl

theorem canonical932 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw932 raw932Labels = mixedMoment B node798 node798Labels := by
  calc
    mixedMoment B raw932 raw932Labels = mixedMoment B raw932step0 raw932step0Labels := by
      have ha : raw932step0 = (fun i j => raw932 (permutation176 i) (permutation6 j)) := by apply Matrix.ext; unfold raw932step0 raw932; decide +kernel
      have hl : raw932step0Labels = raw932Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw932 raw932Labels permutation176 permutation6
    mixedMoment B raw932step0 raw932step0Labels = mixedMoment B raw932step1 raw932step1Labels := by
      have ha : raw932step1 = -raw932step0 := by apply Matrix.ext; change ∀ i j, raw932step1 i j = -(raw932step0 i j); unfold raw932step1 raw932step0; decide +kernel
      have hl : raw932step1Labels = raw932step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw932step1 raw932step1Labels = mixedMoment B raw932step2 raw932step2Labels := by
      have ha : raw932step2 = raw932step1 := by apply Matrix.ext; unfold raw932step2 raw932step1; decide +kernel
      have hl : raw932step1Labels = labelEmbedding1 ∘ raw932step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw932step1 raw932step1Labels raw932step2Labels labelEmbedding1 hl
    _ = mixedMoment B node798 node798Labels := by rfl

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

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical85
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical10911 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10911 raw10911Labels = mixedMoment B node4866 node4866Labels := by
  calc
    mixedMoment B raw10911 raw10911Labels = mixedMoment B raw10911step0 raw10911step0Labels := by
      have hz : ∀ j, raw10911 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10911step0 = (fun i j => raw10911 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10911step0 raw10911; decide +kernel
      have hl : raw10911step0Labels = raw10911Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10911 raw10911Labels permutation434 hz
    mixedMoment B raw10911step0 raw10911step0Labels = mixedMoment B raw10911step1 raw10911step1Labels := by
      have ha : raw10911step1 = (fun i j => raw10911step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10911step1 raw10911step0; decide +kernel
      have hl : raw10911step1Labels = raw10911step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10911step0 raw10911step0Labels permutation34 permutation3
    mixedMoment B raw10911step1 raw10911step1Labels = mixedMoment B raw10911step2 raw10911step2Labels := by
      have ha : raw10911step2 = raw10911step1 := by apply Matrix.ext; unfold raw10911step2 raw10911step1; decide +kernel
      have hl : raw10911step1Labels = labelEmbedding6 ∘ raw10911step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10911step1 raw10911step1Labels raw10911step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4866 node4866Labels := by rfl

theorem canonical10914 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10914 raw10914Labels = mixedMoment B node4889 node4889Labels := by
  calc
    mixedMoment B raw10914 raw10914Labels = mixedMoment B raw10914step0 raw10914step0Labels := by
      have hz : ∀ j, raw10914 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10914step0 = (fun i j => raw10914 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10914step0 raw10914; decide +kernel
      have hl : raw10914step0Labels = raw10914Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10914 raw10914Labels permutation434 hz
    mixedMoment B raw10914step0 raw10914step0Labels = mixedMoment B raw10914step1 raw10914step1Labels := by
      have ha : raw10914step1 = (fun i j => raw10914step0 (permutation49 i) (permutation5 j)) := by apply Matrix.ext; unfold raw10914step1 raw10914step0; decide +kernel
      have hl : raw10914step1Labels = raw10914step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10914step0 raw10914step0Labels permutation49 permutation5
    mixedMoment B raw10914step1 raw10914step1Labels = mixedMoment B raw10914step2 raw10914step2Labels := by
      have ha : raw10914step2 = -raw10914step1 := by apply Matrix.ext; change ∀ i j, raw10914step2 i j = -(raw10914step1 i j); unfold raw10914step2 raw10914step1; decide +kernel
      have hl : raw10914step2Labels = raw10914step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw10914step2 raw10914step2Labels = mixedMoment B raw10914step3 raw10914step3Labels := by
      have ha : raw10914step3 = raw10914step2 := by apply Matrix.ext; unfold raw10914step3 raw10914step2; decide +kernel
      have hl : raw10914step2Labels = labelEmbedding8 ∘ raw10914step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10914step2 raw10914step2Labels raw10914step3Labels labelEmbedding8 hl
    _ = mixedMoment B node4889 node4889Labels := by rfl

theorem canonical10916 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10916 raw10916Labels = mixedMoment B node4866 node4866Labels := by
  calc
    mixedMoment B raw10916 raw10916Labels = mixedMoment B raw10916step0 raw10916step0Labels := by
      have hz : ∀ j, raw10916 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10916step0 = (fun i j => raw10916 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10916step0 raw10916; decide +kernel
      have hl : raw10916step0Labels = raw10916Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10916 raw10916Labels permutation346 hz
    mixedMoment B raw10916step0 raw10916step0Labels = mixedMoment B raw10916step1 raw10916step1Labels := by
      have ha : raw10916step1 = (fun i j => raw10916step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10916step1 raw10916step0; decide +kernel
      have hl : raw10916step1Labels = raw10916step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10916step0 raw10916step0Labels permutation34 permutation3
    mixedMoment B raw10916step1 raw10916step1Labels = mixedMoment B raw10916step2 raw10916step2Labels := by
      have ha : raw10916step2 = raw10916step1 := by apply Matrix.ext; unfold raw10916step2 raw10916step1; decide +kernel
      have hl : raw10916step1Labels = labelEmbedding6 ∘ raw10916step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10916step1 raw10916step1Labels raw10916step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4866 node4866Labels := by rfl

theorem canonical10919 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10919 raw10919Labels = mixedMoment B node4889 node4889Labels := by
  calc
    mixedMoment B raw10919 raw10919Labels = mixedMoment B raw10919step0 raw10919step0Labels := by
      have hz : ∀ j, raw10919 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10919step0 = (fun i j => raw10919 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10919step0 raw10919; decide +kernel
      have hl : raw10919step0Labels = raw10919Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10919 raw10919Labels permutation346 hz
    mixedMoment B raw10919step0 raw10919step0Labels = mixedMoment B raw10919step1 raw10919step1Labels := by
      have ha : raw10919step1 = (fun i j => raw10919step0 (permutation49 i) (permutation5 j)) := by apply Matrix.ext; unfold raw10919step1 raw10919step0; decide +kernel
      have hl : raw10919step1Labels = raw10919step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10919step0 raw10919step0Labels permutation49 permutation5
    mixedMoment B raw10919step1 raw10919step1Labels = mixedMoment B raw10919step2 raw10919step2Labels := by
      have ha : raw10919step2 = -raw10919step1 := by apply Matrix.ext; change ∀ i j, raw10919step2 i j = -(raw10919step1 i j); unfold raw10919step2 raw10919step1; decide +kernel
      have hl : raw10919step2Labels = raw10919step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw10919step2 raw10919step2Labels = mixedMoment B raw10919step3 raw10919step3Labels := by
      have ha : raw10919step3 = raw10919step2 := by apply Matrix.ext; unfold raw10919step3 raw10919step2; decide +kernel
      have hl : raw10919step2Labels = labelEmbedding8 ∘ raw10919step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10919step2 raw10919step2Labels raw10919step3Labels labelEmbedding8 hl
    _ = mixedMoment B node4889 node4889Labels := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons66
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singleton4230 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4230 node4230Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node730 node730Labels + mixedMoment B node780 node780Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw924 singletonSmall4230
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4230) = raw924Labels := by decide +kernel
  rw [hl, canonical924 B hB] at h
  have hc0 : mixedMoment B raw924 (Fin.cases (0 : Fin 2) singletonSmall4230) =
      mixedMoment B node730 node730Labels := by
    have ha : raw924 = raw925 := by apply Matrix.ext; unfold raw924 raw925; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4230 = raw925Labels := by decide +kernel
    rw [ha, hj, canonical925 B hB]
  have hc1 : mixedMoment B raw924 (Fin.cases (1 : Fin 2) singletonSmall4230) =
      mixedMoment B node780 node780Labels := by
    have ha : raw924 = raw926 := by apply Matrix.ext; unfold raw924 raw926; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4230 = raw926Labels := by decide +kernel
    rw [ha, hj, canonical926 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4232 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4232 node4232Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node732 node732Labels + mixedMoment B node798 node798Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw930 singletonSmall4232
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4232) = raw930Labels := by decide +kernel
  rw [hl, canonical930 B hB] at h
  have hc0 : mixedMoment B raw930 (Fin.cases (0 : Fin 2) singletonSmall4232) =
      mixedMoment B node732 node732Labels := by
    have ha : raw930 = raw931 := by apply Matrix.ext; unfold raw930 raw931; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4232 = raw931Labels := by decide +kernel
    rw [ha, hj, canonical931 B hB]
  have hc1 : mixedMoment B raw930 (Fin.cases (1 : Fin 2) singletonSmall4232) =
      mixedMoment B node798 node798Labels := by
    have ha : raw930 = raw932 := by apply Matrix.ext; unfold raw930 raw932; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4232 = raw932Labels := by decide +kernel
    rw [ha, hj, canonical932 B hB]
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

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons73
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singleton4676 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4676 node4676Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1802 node1802Labels + mixedMoment B node2141 node2141Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1554 singletonSmall4676
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4676) = raw1554Labels := by decide +kernel
  rw [hl, canonical1554 B hB] at h
  have hc0 : mixedMoment B raw1554 (Fin.cases (0 : Fin 2) singletonSmall4676) =
      mixedMoment B node1802 node1802Labels := by
    have ha : raw1554 = raw1555 := by apply Matrix.ext; unfold raw1554 raw1555; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4676 = raw1555Labels := by decide +kernel
    rw [ha, hj, canonical1555 B hB]
  have hc1 : mixedMoment B raw1554 (Fin.cases (1 : Fin 2) singletonSmall4676) =
      mixedMoment B node2141 node2141Labels := by
    have ha : raw1554 = raw1556 := by apply Matrix.ext; unfold raw1554 raw1556; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4676 = raw1556Labels := by decide +kernel
    rw [ha, hj, canonical1556 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4679 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4679 node4679Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1805 node1805Labels + mixedMoment B node2150 node2150Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1560 singletonSmall4679
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4679) = raw1560Labels := by decide +kernel
  rw [hl, canonical1560 B hB] at h
  have hc0 : mixedMoment B raw1560 (Fin.cases (0 : Fin 2) singletonSmall4679) =
      mixedMoment B node1805 node1805Labels := by
    have ha : raw1560 = raw1561 := by apply Matrix.ext; unfold raw1560 raw1561; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4679 = raw1561Labels := by decide +kernel
    rw [ha, hj, canonical1561 B hB]
  have hc1 : mixedMoment B raw1560 (Fin.cases (1 : Fin 2) singletonSmall4679) =
      mixedMoment B node2150 node2150Labels := by
    have ha : raw1560 = raw1562 := by apply Matrix.ext; unfold raw1560 raw1562; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4679 = raw1562Labels := by decide +kernel
    rw [ha, hj, canonical1562 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons74
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singleton4798 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4798 node4798Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2016 node2016Labels + mixedMoment B node2075 node2075Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1725 singletonSmall4798
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4798) = raw1725Labels := by decide +kernel
  rw [hl, canonical1725 B hB] at h
  have hc0 : mixedMoment B raw1725 (Fin.cases (0 : Fin 2) singletonSmall4798) =
      mixedMoment B node2016 node2016Labels := by
    have ha : raw1725 = raw1726 := by apply Matrix.ext; unfold raw1725 raw1726; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4798 = raw1726Labels := by decide +kernel
    rw [ha, hj, canonical1726 B hB]
  have hc1 : mixedMoment B raw1725 (Fin.cases (1 : Fin 2) singletonSmall4798) =
      mixedMoment B node2075 node2075Labels := by
    have ha : raw1725 = raw1727 := by apply Matrix.ext; unfold raw1725 raw1727; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4798 = raw1727Labels := by decide +kernel
    rw [ha, hj, canonical1727 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons75
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singleton4805 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4805 node4805Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2023 node2023Labels + mixedMoment B node2214 node2214Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1740 singletonSmall4805
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4805) = raw1740Labels := by decide +kernel
  rw [hl, canonical1740 B hB] at h
  have hc0 : mixedMoment B raw1740 (Fin.cases (0 : Fin 2) singletonSmall4805) =
      mixedMoment B node2023 node2023Labels := by
    have ha : raw1740 = raw1741 := by apply Matrix.ext; unfold raw1740 raw1741; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4805 = raw1741Labels := by decide +kernel
    rw [ha, hj, canonical1741 B hB]
  have hc1 : mixedMoment B raw1740 (Fin.cases (1 : Fin 2) singletonSmall4805) =
      mixedMoment B node2214 node2214Labels := by
    have ha : raw1740 = raw1742 := by apply Matrix.ext; unfold raw1740 raw1742; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4805 = raw1742Labels := by decide +kernel
    rw [ha, hj, canonical1742 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4826 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4826 node4826Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2046 node2046Labels + mixedMoment B node2077 node2077Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1752 singletonSmall4826
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4826) = raw1752Labels := by decide +kernel
  rw [hl, canonical1752 B hB] at h
  have hc0 : mixedMoment B raw1752 (Fin.cases (0 : Fin 2) singletonSmall4826) =
      mixedMoment B node2046 node2046Labels := by
    have ha : raw1752 = raw1753 := by apply Matrix.ext; unfold raw1752 raw1753; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4826 = raw1753Labels := by decide +kernel
    rw [ha, hj, canonical1753 B hB]
  have hc1 : mixedMoment B raw1752 (Fin.cases (1 : Fin 2) singletonSmall4826) =
      mixedMoment B node2077 node2077Labels := by
    have ha : raw1752 = raw1754 := by apply Matrix.ext; unfold raw1752 raw1754; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4826 = raw1754Labels := by decide +kernel
    rw [ha, hj, canonical1754 B hB]
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

theorem singleton4865 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4865 node4865Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2106 node2106Labels + mixedMoment B node2242 node2242Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1791 singletonSmall4865
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4865) = raw1791Labels := by decide +kernel
  rw [hl, canonical1791 B hB] at h
  have hc0 : mixedMoment B raw1791 (Fin.cases (0 : Fin 2) singletonSmall4865) =
      mixedMoment B node2106 node2106Labels := by
    have ha : raw1791 = raw1792 := by apply Matrix.ext; unfold raw1791 raw1792; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4865 = raw1792Labels := by decide +kernel
    rw [ha, hj, canonical1792 B hB]
  have hc1 : mixedMoment B raw1791 (Fin.cases (1 : Fin 2) singletonSmall4865) =
      mixedMoment B node2242 node2242Labels := by
    have ha : raw1791 = raw1793 := by apply Matrix.ext; unfold raw1791 raw1793; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4865 = raw1793Labels := by decide +kernel
    rw [ha, hj, canonical1793 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4866 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4866 node4866Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2107 node2107Labels + mixedMoment B node2260 node2260Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1794 singletonSmall4866
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4866) = raw1794Labels := by decide +kernel
  rw [hl, canonical1794 B hB] at h
  have hc0 : mixedMoment B raw1794 (Fin.cases (0 : Fin 2) singletonSmall4866) =
      mixedMoment B node2107 node2107Labels := by
    have ha : raw1794 = raw1795 := by apply Matrix.ext; unfold raw1794 raw1795; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4866 = raw1795Labels := by decide +kernel
    rw [ha, hj, canonical1795 B hB]
  have hc1 : mixedMoment B raw1794 (Fin.cases (1 : Fin 2) singletonSmall4866) =
      mixedMoment B node2260 node2260Labels := by
    have ha : raw1794 = raw1796 := by apply Matrix.ext; unfold raw1794 raw1796; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4866 = raw1796Labels := by decide +kernel
    rw [ha, hj, canonical1796 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4889 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4889 node4889Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2245 node2245Labels + mixedMoment B node2277 node2277Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1818 singletonSmall4889
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4889) = raw1818Labels := by decide +kernel
  rw [hl, canonical1818 B hB] at h
  have hc0 : mixedMoment B raw1818 (Fin.cases (0 : Fin 2) singletonSmall4889) =
      mixedMoment B node2245 node2245Labels := by
    have ha : raw1818 = raw1819 := by apply Matrix.ext; unfold raw1818 raw1819; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4889 = raw1819Labels := by decide +kernel
    rw [ha, hj, canonical1819 B hB]
  have hc1 : mixedMoment B raw1818 (Fin.cases (1 : Fin 2) singletonSmall4889) =
      mixedMoment B node2277 node2277Labels := by
    have ha : raw1818 = raw1820 := by apply Matrix.ext; unfold raw1818 raw1820; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4889 = raw1820Labels := by decide +kernel
    rw [ha, hj, canonical1820 B hB]
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

theorem sound730 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node730 node730Labels = Sparse.eval nodeValue730 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 730) = mixedMoment B node730 node730Labels := rfl
  simpa [nodeValue730, Sparse.eval] using hc.symm

theorem sound732 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node732 node732Labels = Sparse.eval nodeValue732 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 732) = mixedMoment B node732 node732Labels := rfl
  simpa [nodeValue732, Sparse.eval] using hc.symm

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

theorem sound780 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node780 node780Labels = Sparse.eval nodeValue780 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 780) = mixedMoment B node780 node780Labels := rfl
  simpa [nodeValue780, Sparse.eval] using hc.symm

theorem sound786 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node786 node786Labels = Sparse.eval nodeValue786 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 786) = mixedMoment B node786 node786Labels := rfl
  simpa [nodeValue786, Sparse.eval] using hc.symm

theorem sound798 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node798 node798Labels = Sparse.eval nodeValue798 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 798) = mixedMoment B node798 node798Labels := rfl
  simpa [nodeValue798, Sparse.eval] using hc.symm

theorem sound822 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node822 node822Labels = Sparse.eval nodeValue822 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 822) = mixedMoment B node822 node822Labels := rfl
  simpa [nodeValue822, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound28
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound1802 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1802 node1802Labels = Sparse.eval nodeValue1802 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1802) = mixedMoment B node1802 node1802Labels := rfl
  simpa [nodeValue1802, Sparse.eval] using hc.symm

theorem sound1805 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1805 node1805Labels = Sparse.eval nodeValue1805 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1805) = mixedMoment B node1805 node1805Labels := rfl
  simpa [nodeValue1805, Sparse.eval] using hc.symm

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

theorem sound2016 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2016 node2016Labels = Sparse.eval nodeValue2016 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2016) = mixedMoment B node2016 node2016Labels := rfl
  simpa [nodeValue2016, Sparse.eval] using hc.symm

theorem sound2023 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2023 node2023Labels = Sparse.eval nodeValue2023 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2023) = mixedMoment B node2023 node2023Labels := rfl
  simpa [nodeValue2023, Sparse.eval] using hc.symm

theorem sound2046 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2046 node2046Labels = Sparse.eval nodeValue2046 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2046) = mixedMoment B node2046 node2046Labels := rfl
  simpa [nodeValue2046, Sparse.eval] using hc.symm

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

theorem sound2075 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2075 node2075Labels = Sparse.eval nodeValue2075 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2075) = mixedMoment B node2075 node2075Labels := rfl
  simpa [nodeValue2075, Sparse.eval] using hc.symm

theorem sound2077 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2077 node2077Labels = Sparse.eval nodeValue2077 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2077) = mixedMoment B node2077 node2077Labels := rfl
  simpa [nodeValue2077, Sparse.eval] using hc.symm

theorem sound2106 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2106 node2106Labels = Sparse.eval nodeValue2106 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2106) = mixedMoment B node2106 node2106Labels := rfl
  simpa [nodeValue2106, Sparse.eval] using hc.symm

theorem sound2107 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2107 node2107Labels = Sparse.eval nodeValue2107 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2107) = mixedMoment B node2107 node2107Labels := rfl
  simpa [nodeValue2107, Sparse.eval] using hc.symm

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

theorem sound2141 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2141 node2141Labels = Sparse.eval nodeValue2141 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2141) = mixedMoment B node2141 node2141Labels := rfl
  simpa [nodeValue2141, Sparse.eval] using hc.symm

theorem sound2150 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2150 node2150Labels = Sparse.eval nodeValue2150 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2150) = mixedMoment B node2150 node2150Labels := rfl
  simpa [nodeValue2150, Sparse.eval] using hc.symm

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

theorem sound2214 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2214 node2214Labels = Sparse.eval nodeValue2214 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2214) = mixedMoment B node2214 node2214Labels := rfl
  simpa [nodeValue2214, Sparse.eval] using hc.symm

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

theorem sound2242 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2242 node2242Labels = Sparse.eval nodeValue2242 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2242) = mixedMoment B node2242 node2242Labels := rfl
  simpa [nodeValue2242, Sparse.eval] using hc.symm

theorem sound2245 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2245 node2245Labels = Sparse.eval nodeValue2245 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2245) = mixedMoment B node2245 node2245Labels := rfl
  simpa [nodeValue2245, Sparse.eval] using hc.symm

theorem sound2260 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2260 node2260Labels = Sparse.eval nodeValue2260 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2260) = mixedMoment B node2260 node2260Labels := rfl
  simpa [nodeValue2260, Sparse.eval] using hc.symm

theorem sound2277 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2277 node2277Labels = Sparse.eval nodeValue2277 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2277) = mixedMoment B node2277 node2277Labels := rfl
  simpa [nodeValue2277, Sparse.eval] using hc.symm

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

theorem sound3875 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3875 node3875Labels = Sparse.eval nodeValue3875 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3875) = mixedMoment B node3875 node3875Labels := rfl
  simpa [nodeValue3875, Sparse.eval] using hc.symm

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

theorem sound4230 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4230 node4230Labels = Sparse.eval nodeValue4230 (mixedVector B) := by
  have h := singleton4230 B _hB
  rw [sound730 B _hB _hF, sound780 B _hB _hF] at h
  norm_num [nodeValue4230, nodeValue730, nodeValue780, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4232 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4232 node4232Labels = Sparse.eval nodeValue4232 (mixedVector B) := by
  have h := singleton4232 B _hB
  rw [sound732 B _hB _hF, sound798 B _hB _hF] at h
  norm_num [nodeValue4232, nodeValue732, nodeValue798, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4252 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4252 node4252Labels = Sparse.eval nodeValue4252 (mixedVector B) := by
  have h := singleton4252 B _hB
  rw [sound786 B _hB _hF, sound822 B _hB _hF] at h
  norm_num [nodeValue4252, nodeValue786, nodeValue822, Sparse.eval] at h ⊢
  linarith only [h]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound73
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound4676 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4676 node4676Labels = Sparse.eval nodeValue4676 (mixedVector B) := by
  have h := singleton4676 B _hB
  rw [sound1802 B _hB _hF, sound2141 B _hB _hF] at h
  norm_num [nodeValue4676, nodeValue1802, nodeValue2141, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4679 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4679 node4679Labels = Sparse.eval nodeValue4679 (mixedVector B) := by
  have h := singleton4679 B _hB
  rw [sound1805 B _hB _hF, sound2150 B _hB _hF] at h
  norm_num [nodeValue4679, nodeValue1805, nodeValue2150, Sparse.eval] at h ⊢
  linarith only [h]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound74
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound4798 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4798 node4798Labels = Sparse.eval nodeValue4798 (mixedVector B) := by
  have h := singleton4798 B _hB
  rw [sound2016 B _hB _hF, sound2075 B _hB _hF] at h
  norm_num [nodeValue4798, nodeValue2016, nodeValue2075, Sparse.eval] at h ⊢
  linarith only [h]

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

theorem sound4805 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4805 node4805Labels = Sparse.eval nodeValue4805 (mixedVector B) := by
  have h := singleton4805 B _hB
  rw [sound2023 B _hB _hF, sound2214 B _hB _hF] at h
  norm_num [nodeValue4805, nodeValue2023, nodeValue2214, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4826 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4826 node4826Labels = Sparse.eval nodeValue4826 (mixedVector B) := by
  have h := singleton4826 B _hB
  rw [sound2046 B _hB _hF, sound2077 B _hB _hF] at h
  norm_num [nodeValue4826, nodeValue2046, nodeValue2077, Sparse.eval] at h ⊢
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

theorem sound4865 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4865 node4865Labels = Sparse.eval nodeValue4865 (mixedVector B) := by
  have h := singleton4865 B _hB
  rw [sound2106 B _hB _hF, sound2242 B _hB _hF] at h
  norm_num [nodeValue4865, nodeValue2106, nodeValue2242, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4866 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4866 node4866Labels = Sparse.eval nodeValue4866 (mixedVector B) := by
  have h := singleton4866 B _hB
  rw [sound2107 B _hB _hF, sound2260 B _hB _hF] at h
  norm_num [nodeValue4866, nodeValue2107, nodeValue2260, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4889 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4889 node4889Labels = Sparse.eval nodeValue4889 (mixedVector B) := by
  have h := singleton4889 B _hB
  rw [sound2245 B _hB _hF, sound2277 B _hB _hF] at h
  norm_num [nodeValue4889, nodeValue2245, nodeValue2277, Sparse.eval] at h ⊢
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

theorem sound5431 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5431 node5431Labels = Sparse.eval nodeValue5431 (mixedVector B) := by
  have h := singleton5431 B _hB
  rw [sound3849 B _hB _hF, sound3875 B _hB _hF] at h
  norm_num [nodeValue5431, nodeValue3849, nodeValue3875, Sparse.eval] at h ⊢
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources78
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sourceEq2510 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2510 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2510 + difference 0 1) (sourceB2510 + difference 1 0) sourceC2510) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5386) := by
    have ha : (tripleCharges (sourceA2510 + difference 0 1) (sourceB2510 + difference 1 0) sourceC2510) = raw34636 := by
      apply Matrix.ext; unfold tripleCharges sourceA2510 sourceB2510 sourceC2510 difference raw34636; decide +kernel
    rw [ha]
    exact (canonical34636 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2510 + difference 0 2) (sourceB2510 + difference 2 0) sourceC2510) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5450) := by
    have ha : (tripleCharges (sourceA2510 + difference 0 2) (sourceB2510 + difference 2 0) sourceC2510) = raw16292 := by
      apply Matrix.ext; unfold tripleCharges sourceA2510 sourceB2510 sourceC2510 difference raw16292; decide +kernel
    rw [ha]
    exact (canonical16292 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2510 + difference 0 3) (sourceB2510 + difference 3 0) sourceC2510) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5450) := by
    have ha : (tripleCharges (sourceA2510 + difference 0 3) (sourceB2510 + difference 3 0) sourceC2510) = raw16288 := by
      apply Matrix.ext; unfold tripleCharges sourceA2510 sourceB2510 sourceC2510 difference raw16288; decide +kernel
    rw [ha]
    exact (canonical16288 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2510 + difference 0 4) (sourceB2510 + difference 4 0) sourceC2510) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5431) := by
    have ha : (tripleCharges (sourceA2510 + difference 0 4) (sourceB2510 + difference 4 0) sourceC2510) = raw34637 := by
      apply Matrix.ext; unfold tripleCharges sourceA2510 sourceB2510 sourceC2510 difference raw34637; decide +kernel
    rw [ha]
    exact (canonical34637 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2510 + difference 0 5) (sourceB2510 + difference 5 0) sourceC2510) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5431) := by
    have ha : (tripleCharges (sourceA2510 + difference 0 5) (sourceB2510 + difference 5 0) sourceC2510) = raw34638 := by
      apply Matrix.ext; unfold tripleCharges sourceA2510 sourceB2510 sourceC2510 difference raw34638; decide +kernel
    rw [ha]
    exact (canonical34638 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2510 + difference 1 0) (sourceB2510 + difference 0 1) sourceC2510) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4252) := by
    have ha : (tripleCharges (sourceA2510 + difference 1 0) (sourceB2510 + difference 0 1) sourceC2510) = raw34639 := by
      apply Matrix.ext; unfold tripleCharges sourceA2510 sourceB2510 sourceC2510 difference raw34639; decide +kernel
    rw [ha]
    exact (canonical34639 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2510 + difference 1 2) (sourceB2510 + difference 2 1) sourceC2510) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4889) := by
    have ha : (tripleCharges (sourceA2510 + difference 1 2) (sourceB2510 + difference 2 1) sourceC2510) = raw10919 := by
      apply Matrix.ext; unfold tripleCharges sourceA2510 sourceB2510 sourceC2510 difference raw10919; decide +kernel
    rw [ha]
    exact (canonical10919 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2510 + difference 1 3) (sourceB2510 + difference 3 1) sourceC2510) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4889) := by
    have ha : (tripleCharges (sourceA2510 + difference 1 3) (sourceB2510 + difference 3 1) sourceC2510) = raw10914 := by
      apply Matrix.ext; unfold tripleCharges sourceA2510 sourceB2510 sourceC2510 difference raw10914; decide +kernel
    rw [ha]
    exact (canonical10914 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2510 + difference 1 4) (sourceB2510 + difference 4 1) sourceC2510) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4805) := by
    have ha : (tripleCharges (sourceA2510 + difference 1 4) (sourceB2510 + difference 4 1) sourceC2510) = raw34640 := by
      apply Matrix.ext; unfold tripleCharges sourceA2510 sourceB2510 sourceC2510 difference raw34640; decide +kernel
    rw [ha]
    exact (canonical34640 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2510 + difference 1 5) (sourceB2510 + difference 5 1) sourceC2510) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4805) := by
    have ha : (tripleCharges (sourceA2510 + difference 1 5) (sourceB2510 + difference 5 1) sourceC2510) = raw34641 := by
      apply Matrix.ext; unfold tripleCharges sourceA2510 sourceB2510 sourceC2510 difference raw34641; decide +kernel
    rw [ha]
    exact (canonical34641 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2510 + difference 2 0) (sourceB2510 + difference 0 2) sourceC2510) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4230) := by
    have ha : (tripleCharges (sourceA2510 + difference 2 0) (sourceB2510 + difference 0 2) sourceC2510) = raw34642 := by
      apply Matrix.ext; unfold tripleCharges sourceA2510 sourceB2510 sourceC2510 difference raw34642; decide +kernel
    rw [ha]
    exact (canonical34642 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2510 + difference 2 1) (sourceB2510 + difference 1 2) sourceC2510) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4676) := by
    have ha : (tripleCharges (sourceA2510 + difference 2 1) (sourceB2510 + difference 1 2) sourceC2510) = raw34643 := by
      apply Matrix.ext; unfold tripleCharges sourceA2510 sourceB2510 sourceC2510 difference raw34643; decide +kernel
    rw [ha]
    exact (canonical34643 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2510 + difference 2 3) (sourceB2510 + difference 3 2) sourceC2510) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4865) := by
    have ha : (tripleCharges (sourceA2510 + difference 2 3) (sourceB2510 + difference 3 2) sourceC2510) = raw34644 := by
      apply Matrix.ext; unfold tripleCharges sourceA2510 sourceB2510 sourceC2510 difference raw34644; decide +kernel
    rw [ha]
    exact (canonical34644 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2510 + difference 2 4) (sourceB2510 + difference 4 2) sourceC2510) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4798) := by
    have ha : (tripleCharges (sourceA2510 + difference 2 4) (sourceB2510 + difference 4 2) sourceC2510) = raw34645 := by
      apply Matrix.ext; unfold tripleCharges sourceA2510 sourceB2510 sourceC2510 difference raw34645; decide +kernel
    rw [ha]
    exact (canonical34645 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2510 + difference 2 5) (sourceB2510 + difference 5 2) sourceC2510) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4798) := by
    have ha : (tripleCharges (sourceA2510 + difference 2 5) (sourceB2510 + difference 5 2) sourceC2510) = raw34646 := by
      apply Matrix.ext; unfold tripleCharges sourceA2510 sourceB2510 sourceC2510 difference raw34646; decide +kernel
    rw [ha]
    exact (canonical34646 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2510 + difference 3 0) (sourceB2510 + difference 0 3) sourceC2510) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4230) := by
    have ha : (tripleCharges (sourceA2510 + difference 3 0) (sourceB2510 + difference 0 3) sourceC2510) = raw34647 := by
      apply Matrix.ext; unfold tripleCharges sourceA2510 sourceB2510 sourceC2510 difference raw34647; decide +kernel
    rw [ha]
    exact (canonical34647 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2510 + difference 3 1) (sourceB2510 + difference 1 3) sourceC2510) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4676) := by
    have ha : (tripleCharges (sourceA2510 + difference 3 1) (sourceB2510 + difference 1 3) sourceC2510) = raw34648 := by
      apply Matrix.ext; unfold tripleCharges sourceA2510 sourceB2510 sourceC2510 difference raw34648; decide +kernel
    rw [ha]
    exact (canonical34648 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2510 + difference 3 2) (sourceB2510 + difference 2 3) sourceC2510) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4865) := by
    have ha : (tripleCharges (sourceA2510 + difference 3 2) (sourceB2510 + difference 2 3) sourceC2510) = raw33624 := by
      apply Matrix.ext; unfold tripleCharges sourceA2510 sourceB2510 sourceC2510 difference raw33624; decide +kernel
    rw [ha]
    exact (canonical33624 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2510 + difference 3 4) (sourceB2510 + difference 4 3) sourceC2510) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4798) := by
    have ha : (tripleCharges (sourceA2510 + difference 3 4) (sourceB2510 + difference 4 3) sourceC2510) = raw34649 := by
      apply Matrix.ext; unfold tripleCharges sourceA2510 sourceB2510 sourceC2510 difference raw34649; decide +kernel
    rw [ha]
    exact (canonical34649 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2510 + difference 3 5) (sourceB2510 + difference 5 3) sourceC2510) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4798) := by
    have ha : (tripleCharges (sourceA2510 + difference 3 5) (sourceB2510 + difference 5 3) sourceC2510) = raw34650 := by
      apply Matrix.ext; unfold tripleCharges sourceA2510 sourceB2510 sourceC2510 difference raw34650; decide +kernel
    rw [ha]
    exact (canonical34650 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2510 + difference 4 0) (sourceB2510 + difference 0 4) sourceC2510) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4232) := by
    have ha : (tripleCharges (sourceA2510 + difference 4 0) (sourceB2510 + difference 0 4) sourceC2510) = raw34651 := by
      apply Matrix.ext; unfold tripleCharges sourceA2510 sourceB2510 sourceC2510 difference raw34651; decide +kernel
    rw [ha]
    exact (canonical34651 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2510 + difference 4 1) (sourceB2510 + difference 1 4) sourceC2510) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4679) := by
    have ha : (tripleCharges (sourceA2510 + difference 4 1) (sourceB2510 + difference 1 4) sourceC2510) = raw34652 := by
      apply Matrix.ext; unfold tripleCharges sourceA2510 sourceB2510 sourceC2510 difference raw34652; decide +kernel
    rw [ha]
    exact (canonical34652 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2510 + difference 4 2) (sourceB2510 + difference 2 4) sourceC2510) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4866) := by
    have ha : (tripleCharges (sourceA2510 + difference 4 2) (sourceB2510 + difference 2 4) sourceC2510) = raw31207 := by
      apply Matrix.ext; unfold tripleCharges sourceA2510 sourceB2510 sourceC2510 difference raw31207; decide +kernel
    rw [ha]
    exact (canonical31207 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2510 + difference 4 3) (sourceB2510 + difference 3 4) sourceC2510) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4866) := by
    have ha : (tripleCharges (sourceA2510 + difference 4 3) (sourceB2510 + difference 3 4) sourceC2510) = raw31203 := by
      apply Matrix.ext; unfold tripleCharges sourceA2510 sourceB2510 sourceC2510 difference raw31203; decide +kernel
    rw [ha]
    exact (canonical31203 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2510 + difference 4 5) (sourceB2510 + difference 5 4) sourceC2510) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4826) := by
    have ha : (tripleCharges (sourceA2510 + difference 4 5) (sourceB2510 + difference 5 4) sourceC2510) = raw34653 := by
      apply Matrix.ext; unfold tripleCharges sourceA2510 sourceB2510 sourceC2510 difference raw34653; decide +kernel
    rw [ha]
    exact (canonical34653 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2510 + difference 5 0) (sourceB2510 + difference 0 5) sourceC2510) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4232) := by
    have ha : (tripleCharges (sourceA2510 + difference 5 0) (sourceB2510 + difference 0 5) sourceC2510) = raw33616 := by
      apply Matrix.ext; unfold tripleCharges sourceA2510 sourceB2510 sourceC2510 difference raw33616; decide +kernel
    rw [ha]
    exact (canonical33616 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2510 + difference 5 1) (sourceB2510 + difference 1 5) sourceC2510) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4679) := by
    have ha : (tripleCharges (sourceA2510 + difference 5 1) (sourceB2510 + difference 1 5) sourceC2510) = raw33617 := by
      apply Matrix.ext; unfold tripleCharges sourceA2510 sourceB2510 sourceC2510 difference raw33617; decide +kernel
    rw [ha]
    exact (canonical33617 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2510 + difference 5 2) (sourceB2510 + difference 2 5) sourceC2510) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4866) := by
    have ha : (tripleCharges (sourceA2510 + difference 5 2) (sourceB2510 + difference 2 5) sourceC2510) = raw10916 := by
      apply Matrix.ext; unfold tripleCharges sourceA2510 sourceB2510 sourceC2510 difference raw10916; decide +kernel
    rw [ha]
    exact (canonical10916 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2510 + difference 5 3) (sourceB2510 + difference 3 5) sourceC2510) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4866) := by
    have ha : (tripleCharges (sourceA2510 + difference 5 3) (sourceB2510 + difference 3 5) sourceC2510) = raw10911 := by
      apply Matrix.ext; unfold tripleCharges sourceA2510 sourceB2510 sourceC2510 difference raw10911; decide +kernel
    rw [ha]
    exact (canonical10911 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2510 + difference 5 4) (sourceB2510 + difference 4 5) sourceC2510) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4826) := by
    have ha : (tripleCharges (sourceA2510 + difference 5 4) (sourceB2510 + difference 4 5) sourceC2510) = raw33618 := by
      apply Matrix.ext; unfold tripleCharges sourceA2510 sourceB2510 sourceC2510 difference raw33618; decide +kernel
    rw [ha]
    exact (canonical33618 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2510 sourceB2510 sourceC2510
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2510, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic126
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reindexCheck2021 : Integer.Sparse.reindex keyMap MixedData.row2021 = numericRow2021 := by decide +kernel

theorem numericCheck2021 (x : Master → ℝ) : Integer.Sparse.eval numericRow2021 x =
    (17280 : ℝ) * reducedSource2021 x := by
  norm_num [numericRow2021, reducedSource2021, Integer.Sparse.eval, Sparse.eval, nodeValue4230, nodeValue4232, nodeValue4252, nodeValue4676, nodeValue4679, nodeValue4798, nodeValue4805, nodeValue4826, nodeValue4865, nodeValue4866, nodeValue4889, nodeValue5386, nodeValue5431, nodeValue5450]
  ring

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Rows126
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero2021 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource2021 (mixedVector B) = 0 := by
  have h4230 : mixedVector B (Sum.inr 4230) = Sparse.eval nodeValue4230 (mixedVector B) := by
    change mixedMoment B node4230 node4230Labels = _
    exact sound4230 B hB hF
  have h4232 : mixedVector B (Sum.inr 4232) = Sparse.eval nodeValue4232 (mixedVector B) := by
    change mixedMoment B node4232 node4232Labels = _
    exact sound4232 B hB hF
  have h4252 : mixedVector B (Sum.inr 4252) = Sparse.eval nodeValue4252 (mixedVector B) := by
    change mixedMoment B node4252 node4252Labels = _
    exact sound4252 B hB hF
  have h4676 : mixedVector B (Sum.inr 4676) = Sparse.eval nodeValue4676 (mixedVector B) := by
    change mixedMoment B node4676 node4676Labels = _
    exact sound4676 B hB hF
  have h4679 : mixedVector B (Sum.inr 4679) = Sparse.eval nodeValue4679 (mixedVector B) := by
    change mixedMoment B node4679 node4679Labels = _
    exact sound4679 B hB hF
  have h4798 : mixedVector B (Sum.inr 4798) = Sparse.eval nodeValue4798 (mixedVector B) := by
    change mixedMoment B node4798 node4798Labels = _
    exact sound4798 B hB hF
  have h4805 : mixedVector B (Sum.inr 4805) = Sparse.eval nodeValue4805 (mixedVector B) := by
    change mixedMoment B node4805 node4805Labels = _
    exact sound4805 B hB hF
  have h4826 : mixedVector B (Sum.inr 4826) = Sparse.eval nodeValue4826 (mixedVector B) := by
    change mixedMoment B node4826 node4826Labels = _
    exact sound4826 B hB hF
  have h4865 : mixedVector B (Sum.inr 4865) = Sparse.eval nodeValue4865 (mixedVector B) := by
    change mixedMoment B node4865 node4865Labels = _
    exact sound4865 B hB hF
  have h4866 : mixedVector B (Sum.inr 4866) = Sparse.eval nodeValue4866 (mixedVector B) := by
    change mixedMoment B node4866 node4866Labels = _
    exact sound4866 B hB hF
  have h4889 : mixedVector B (Sum.inr 4889) = Sparse.eval nodeValue4889 (mixedVector B) := by
    change mixedMoment B node4889 node4889Labels = _
    exact sound4889 B hB hF
  have h5386 : mixedVector B (Sum.inr 5386) = Sparse.eval nodeValue5386 (mixedVector B) := by
    change mixedMoment B node5386 node5386Labels = _
    exact sound5386_e B hB hF
  have h5431 : mixedVector B (Sum.inr 5431) = Sparse.eval nodeValue5431 (mixedVector B) := by
    change mixedMoment B node5431 node5431Labels = _
    exact sound5431 B hB hF
  have h5450 : mixedVector B (Sum.inr 5450) = Sparse.eval nodeValue5450 (mixedVector B) := by
    change mixedMoment B node5450 node5450Labels = _
    exact sound5450_e B hB hF
  simpa only [sourceForm2510, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4230, h4232, h4252, h4676, h4679, h4798, h4805, h4826, h4865, h4866, h4889, h5386, h5431, h5450, reducedSource2021] using sourceEq2510 B hB

theorem rowSound2021_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row2021 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck2021, numericCheck2021, reducedZero2021 B hB hF, mul_zero]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedSourceBridge.rowSound2021_e_oai := @OAI.MUB6.Certificate.MixedSourceBridge.rowSound2021_e_oai
