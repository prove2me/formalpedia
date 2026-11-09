-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedSourceBridge.rowSound2060_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-08T22:54:42.970368+00:00
-- url     : https://prove2.me/submissions/ec613e09-0912-42ec-a504-6be6579811bb

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E070
import Definitions.Def_OAIQ106E086
import Definitions.Def_OAIQ106E091
import Definitions.Def_OAIQ106E092
import Definitions.Def_OAIQ106E093
import Definitions.Def_OAIQ106E094
import Definitions.Def_OAIQ106E095
import Definitions.Def_OAIQ106E192
import Definitions.Def_OAIQ106E100
import Definitions.Def_OAIQ106E194
import Definitions.Def_OAIQ106E195
import Definitions.Def_OAIQ106E107
import Definitions.Def_OAIQ106E108
import Definitions.Def_OAIQ106E119
import Definitions.Def_OAIQ106E121
import Definitions.Def_OAIQ106E126
import Definitions.Def_OAIQ106E140
import Definitions.Def_OAIQ106E147
import Definitions.Def_OAIQ106E170
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound5172_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound5386_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound5388_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound5417_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound5435_e
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

theorem canonical1557 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1557 raw1557Labels = mixedMoment B node4678 node4678Labels := by
  calc
    mixedMoment B raw1557 raw1557Labels = mixedMoment B raw1557step0 raw1557step0Labels := by
      have ha : raw1557step0 = (fun i j => raw1557 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1557step0 raw1557; decide +kernel
      have hl : raw1557step0Labels = raw1557Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1557 raw1557Labels permutation32 permutation4
    mixedMoment B raw1557step0 raw1557step0Labels = mixedMoment B raw1557step1 raw1557step1Labels := by
      have ha : raw1557step1 = raw1557step0 := by apply Matrix.ext; unfold raw1557step1 raw1557step0; decide +kernel
      have hl : raw1557step0Labels = labelEmbedding7 ∘ raw1557step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1557step0 raw1557step0Labels raw1557step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4678 node4678Labels := by rfl

theorem canonical1558 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1558 raw1558Labels = mixedMoment B node1804 node1804Labels := by
  calc
    mixedMoment B raw1558 raw1558Labels = mixedMoment B raw1558step0 raw1558step0Labels := by
      have ha : raw1558step0 = (fun i j => raw1558 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1558step0 raw1558; decide +kernel
      have hl : raw1558step0Labels = raw1558Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1558 raw1558Labels permutation32 permutation4
    _ = mixedMoment B node1804 node1804Labels := by rfl

theorem canonical1559 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1559 raw1559Labels = mixedMoment B node2143 node2143Labels := by
  calc
    mixedMoment B raw1559 raw1559Labels = mixedMoment B raw1559step0 raw1559step0Labels := by
      have ha : raw1559step0 = (fun i j => raw1559 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1559step0 raw1559; decide +kernel
      have hl : raw1559step0Labels = raw1559Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1559 raw1559Labels permutation32 permutation6
    mixedMoment B raw1559step0 raw1559step0Labels = mixedMoment B raw1559step1 raw1559step1Labels := by
      have ha : raw1559step1 = -raw1559step0 := by apply Matrix.ext; change ∀ i j, raw1559step1 i j = -(raw1559step0 i j); unfold raw1559step1 raw1559step0; decide +kernel
      have hl : raw1559step1Labels = raw1559step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1559step1 raw1559step1Labels = mixedMoment B raw1559step2 raw1559step2Labels := by
      have ha : raw1559step2 = raw1559step1 := by apply Matrix.ext; unfold raw1559step2 raw1559step1; decide +kernel
      have hl : raw1559step1Labels = labelEmbedding1 ∘ raw1559step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1559step1 raw1559step1Labels raw1559step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2143 node2143Labels := by rfl

theorem canonical1566 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1566 raw1566Labels = mixedMoment B node4684 node4684Labels := by
  calc
    mixedMoment B raw1566 raw1566Labels = mixedMoment B raw1566step0 raw1566step0Labels := by
      have ha : raw1566step0 = (fun i j => raw1566 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1566step0 raw1566; decide +kernel
      have hl : raw1566step0Labels = raw1566Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1566 raw1566Labels permutation32 permutation4
    mixedMoment B raw1566step0 raw1566step0Labels = mixedMoment B raw1566step1 raw1566step1Labels := by
      have ha : raw1566step1 = raw1566step0 := by apply Matrix.ext; unfold raw1566step1 raw1566step0; decide +kernel
      have hl : raw1566step0Labels = labelEmbedding7 ∘ raw1566step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1566step0 raw1566step0Labels raw1566step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4684 node4684Labels := by rfl

theorem canonical1567 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1567 raw1567Labels = mixedMoment B node1810 node1810Labels := by
  calc
    mixedMoment B raw1567 raw1567Labels = mixedMoment B raw1567step0 raw1567step0Labels := by
      have ha : raw1567step0 = (fun i j => raw1567 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1567step0 raw1567; decide +kernel
      have hl : raw1567step0Labels = raw1567Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1567 raw1567Labels permutation32 permutation4
    _ = mixedMoment B node1810 node1810Labels := by rfl

theorem canonical1568 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1568 raw1568Labels = mixedMoment B node2152 node2152Labels := by
  calc
    mixedMoment B raw1568 raw1568Labels = mixedMoment B raw1568step0 raw1568step0Labels := by
      have ha : raw1568step0 = (fun i j => raw1568 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1568step0 raw1568; decide +kernel
      have hl : raw1568step0Labels = raw1568Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1568 raw1568Labels permutation32 permutation6
    mixedMoment B raw1568step0 raw1568step0Labels = mixedMoment B raw1568step1 raw1568step1Labels := by
      have ha : raw1568step1 = -raw1568step0 := by apply Matrix.ext; change ∀ i j, raw1568step1 i j = -(raw1568step0 i j); unfold raw1568step1 raw1568step0; decide +kernel
      have hl : raw1568step1Labels = raw1568step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1568step1 raw1568step1Labels = mixedMoment B raw1568step2 raw1568step2Labels := by
      have ha : raw1568step2 = raw1568step1 := by apply Matrix.ext; unfold raw1568step2 raw1568step1; decide +kernel
      have hl : raw1568step1Labels = labelEmbedding1 ∘ raw1568step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1568step1 raw1568step1Labels raw1568step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2152 node2152Labels := by rfl

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

theorem canonical1698 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1698 raw1698Labels = mixedMoment B node4766 node4766Labels := by
  calc
    mixedMoment B raw1698 raw1698Labels = mixedMoment B raw1698step0 raw1698step0Labels := by
      have ha : raw1698step0 = (fun i j => raw1698 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1698step0 raw1698; decide +kernel
      have hl : raw1698step0Labels = raw1698Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1698 raw1698Labels permutation152 permutation4
    mixedMoment B raw1698step0 raw1698step0Labels = mixedMoment B raw1698step1 raw1698step1Labels := by
      have ha : raw1698step1 = raw1698step0 := by apply Matrix.ext; unfold raw1698step1 raw1698step0; decide +kernel
      have hl : raw1698step0Labels = labelEmbedding7 ∘ raw1698step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1698step0 raw1698step0Labels raw1698step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4766 node4766Labels := by rfl

theorem canonical1699 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1699 raw1699Labels = mixedMoment B node1966 node1966Labels := by
  calc
    mixedMoment B raw1699 raw1699Labels = mixedMoment B raw1699step0 raw1699step0Labels := by
      have ha : raw1699step0 = (fun i j => raw1699 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1699step0 raw1699; decide +kernel
      have hl : raw1699step0Labels = raw1699Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1699 raw1699Labels permutation152 permutation4
    _ = mixedMoment B node1966 node1966Labels := by rfl

theorem canonical1700 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1700 raw1700Labels = mixedMoment B node2177 node2177Labels := by
  calc
    mixedMoment B raw1700 raw1700Labels = mixedMoment B raw1700step0 raw1700step0Labels := by
      have ha : raw1700step0 = (fun i j => raw1700 (permutation154 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1700step0 raw1700; decide +kernel
      have hl : raw1700step0Labels = raw1700Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1700 raw1700Labels permutation154 permutation6
    mixedMoment B raw1700step0 raw1700step0Labels = mixedMoment B raw1700step1 raw1700step1Labels := by
      have ha : raw1700step1 = -raw1700step0 := by apply Matrix.ext; change ∀ i j, raw1700step1 i j = -(raw1700step0 i j); unfold raw1700step1 raw1700step0; decide +kernel
      have hl : raw1700step1Labels = raw1700step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1700step1 raw1700step1Labels = mixedMoment B raw1700step2 raw1700step2Labels := by
      have ha : raw1700step2 = raw1700step1 := by apply Matrix.ext; unfold raw1700step2 raw1700step1; decide +kernel
      have hl : raw1700step1Labels = labelEmbedding1 ∘ raw1700step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1700step1 raw1700step1Labels raw1700step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2177 node2177Labels := by rfl

theorem canonical1707 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1707 raw1707Labels = mixedMoment B node4770 node4770Labels := by
  calc
    mixedMoment B raw1707 raw1707Labels = mixedMoment B raw1707step0 raw1707step0Labels := by
      have ha : raw1707step0 = (fun i j => raw1707 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1707step0 raw1707; decide +kernel
      have hl : raw1707step0Labels = raw1707Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1707 raw1707Labels permutation32 permutation4
    mixedMoment B raw1707step0 raw1707step0Labels = mixedMoment B raw1707step1 raw1707step1Labels := by
      have ha : raw1707step1 = raw1707step0 := by apply Matrix.ext; unfold raw1707step1 raw1707step0; decide +kernel
      have hl : raw1707step0Labels = labelEmbedding7 ∘ raw1707step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1707step0 raw1707step0Labels raw1707step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4770 node4770Labels := by rfl

theorem canonical1708 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1708 raw1708Labels = mixedMoment B node1970 node1970Labels := by
  calc
    mixedMoment B raw1708 raw1708Labels = mixedMoment B raw1708step0 raw1708step0Labels := by
      have ha : raw1708step0 = (fun i j => raw1708 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1708step0 raw1708; decide +kernel
      have hl : raw1708step0Labels = raw1708Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1708 raw1708Labels permutation32 permutation4
    _ = mixedMoment B node1970 node1970Labels := by rfl

theorem canonical1709 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1709 raw1709Labels = mixedMoment B node2186 node2186Labels := by
  calc
    mixedMoment B raw1709 raw1709Labels = mixedMoment B raw1709step0 raw1709step0Labels := by
      have ha : raw1709step0 = (fun i j => raw1709 (permutation33 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1709step0 raw1709; decide +kernel
      have hl : raw1709step0Labels = raw1709Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1709 raw1709Labels permutation33 permutation6
    mixedMoment B raw1709step0 raw1709step0Labels = mixedMoment B raw1709step1 raw1709step1Labels := by
      have ha : raw1709step1 = -raw1709step0 := by apply Matrix.ext; change ∀ i j, raw1709step1 i j = -(raw1709step0 i j); unfold raw1709step1 raw1709step0; decide +kernel
      have hl : raw1709step1Labels = raw1709step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1709step1 raw1709step1Labels = mixedMoment B raw1709step2 raw1709step2Labels := by
      have ha : raw1709step2 = raw1709step1 := by apply Matrix.ext; unfold raw1709step2 raw1709step1; decide +kernel
      have hl : raw1709step1Labels = labelEmbedding1 ∘ raw1709step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1709step1 raw1709step1Labels raw1709step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2186 node2186Labels := by rfl

theorem canonical1746 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1746 raw1746Labels = mixedMoment B node4810 node4810Labels := by
  calc
    mixedMoment B raw1746 raw1746Labels = mixedMoment B raw1746step0 raw1746step0Labels := by
      have ha : raw1746step0 = (fun i j => raw1746 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1746step0 raw1746; decide +kernel
      have hl : raw1746step0Labels = raw1746Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1746 raw1746Labels permutation32 permutation4
    mixedMoment B raw1746step0 raw1746step0Labels = mixedMoment B raw1746step1 raw1746step1Labels := by
      have ha : raw1746step1 = raw1746step0 := by apply Matrix.ext; unfold raw1746step1 raw1746step0; decide +kernel
      have hl : raw1746step0Labels = labelEmbedding7 ∘ raw1746step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1746step0 raw1746step0Labels raw1746step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4810 node4810Labels := by rfl

theorem canonical1747 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1747 raw1747Labels = mixedMoment B node2028 node2028Labels := by
  calc
    mixedMoment B raw1747 raw1747Labels = mixedMoment B raw1747step0 raw1747step0Labels := by
      have ha : raw1747step0 = (fun i j => raw1747 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1747step0 raw1747; decide +kernel
      have hl : raw1747step0Labels = raw1747Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1747 raw1747Labels permutation32 permutation4
    _ = mixedMoment B node2028 node2028Labels := by rfl

theorem canonical1748 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1748 raw1748Labels = mixedMoment B node2215 node2215Labels := by
  calc
    mixedMoment B raw1748 raw1748Labels = mixedMoment B raw1748step0 raw1748step0Labels := by
      have ha : raw1748step0 = (fun i j => raw1748 (permutation34 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1748step0 raw1748; decide +kernel
      have hl : raw1748step0Labels = raw1748Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1748 raw1748Labels permutation34 permutation6
    mixedMoment B raw1748step0 raw1748step0Labels = mixedMoment B raw1748step1 raw1748step1Labels := by
      have ha : raw1748step1 = -raw1748step0 := by apply Matrix.ext; change ∀ i j, raw1748step1 i j = -(raw1748step0 i j); unfold raw1748step1 raw1748step0; decide +kernel
      have hl : raw1748step1Labels = raw1748step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1748step1 raw1748step1Labels = mixedMoment B raw1748step2 raw1748step2Labels := by
      have ha : raw1748step2 = raw1748step1 := by apply Matrix.ext; unfold raw1748step2 raw1748step1; decide +kernel
      have hl : raw1748step1Labels = labelEmbedding1 ∘ raw1748step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1748step1 raw1748step1Labels raw1748step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2215 node2215Labels := by rfl

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

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical142
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical18182 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18182 raw18182Labels = mixedMoment B node5435 node5435Labels := by
  calc
    mixedMoment B raw18182 raw18182Labels = mixedMoment B raw18182step0 raw18182step0Labels := by
      have hz : ∀ j, raw18182 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18182step0 = (fun i j => raw18182 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18182step0 raw18182; decide +kernel
      have hl : raw18182step0Labels = raw18182Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18182 raw18182Labels permutation346 hz
    mixedMoment B raw18182step0 raw18182step0Labels = mixedMoment B raw18182step1 raw18182step1Labels := by
      have ha : raw18182step1 = (fun i j => raw18182step0 (permutation56 i) (permutation2 j)) := by apply Matrix.ext; unfold raw18182step1 raw18182step0; decide +kernel
      have hl : raw18182step1Labels = raw18182step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18182step0 raw18182step0Labels permutation56 permutation2
    _ = mixedMoment B node5435 node5435Labels := by rfl

theorem canonical18193 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18193 raw18193Labels = mixedMoment B node5378 node5378Labels := by
  calc
    mixedMoment B raw18193 raw18193Labels = mixedMoment B raw18193step0 raw18193step0Labels := by
      have ha : raw18193step0 = (fun i j => raw18193 (permutation160 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18193step0 raw18193; decide +kernel
      have hl : raw18193step0Labels = raw18193Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18193 raw18193Labels permutation160 permutation3
    mixedMoment B raw18193step0 raw18193step0Labels = mixedMoment B raw18193step1 raw18193step1Labels := by
      have ha : raw18193step1 = raw18193step0 := by apply Matrix.ext; unfold raw18193step1 raw18193step0; decide +kernel
      have hl : raw18193step0Labels = labelEmbedding6 ∘ raw18193step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18193step0 raw18193step0Labels raw18193step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5378 node5378Labels := by rfl

theorem canonical18197 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18197 raw18197Labels = mixedMoment B node4865 node4865Labels := by
  calc
    mixedMoment B raw18197 raw18197Labels = mixedMoment B raw18197step0 raw18197step0Labels := by
      have hz : ∀ j, raw18197 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18197step0 = (fun i j => raw18197 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18197step0 raw18197; decide +kernel
      have hl : raw18197step0Labels = raw18197Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18197 raw18197Labels permutation346 hz
    mixedMoment B raw18197step0 raw18197step0Labels = mixedMoment B raw18197step1 raw18197step1Labels := by
      have ha : raw18197step1 = (fun i j => raw18197step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18197step1 raw18197step0; decide +kernel
      have hl : raw18197step1Labels = raw18197step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18197step0 raw18197step0Labels permutation32 permutation3
    mixedMoment B raw18197step1 raw18197step1Labels = mixedMoment B raw18197step2 raw18197step2Labels := by
      have ha : raw18197step2 = raw18197step1 := by apply Matrix.ext; unfold raw18197step2 raw18197step1; decide +kernel
      have hl : raw18197step1Labels = labelEmbedding6 ∘ raw18197step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18197step1 raw18197step1Labels raw18197step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4865 node4865Labels := by rfl

theorem canonical18199 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18199 raw18199Labels = mixedMoment B node5400 node5400Labels := by
  calc
    mixedMoment B raw18199 raw18199Labels = mixedMoment B raw18199step0 raw18199step0Labels := by
      have ha : raw18199step0 = (fun i j => raw18199 (permutation176 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18199step0 raw18199; decide +kernel
      have hl : raw18199step0Labels = raw18199Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18199 raw18199Labels permutation176 permutation3
    mixedMoment B raw18199step0 raw18199step0Labels = mixedMoment B raw18199step1 raw18199step1Labels := by
      have ha : raw18199step1 = raw18199step0 := by apply Matrix.ext; unfold raw18199step1 raw18199step0; decide +kernel
      have hl : raw18199step0Labels = labelEmbedding6 ∘ raw18199step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18199step0 raw18199step0Labels raw18199step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5400 node5400Labels := by rfl

theorem canonical18200 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18200 raw18200Labels = mixedMoment B node5432 node5432Labels := by
  calc
    mixedMoment B raw18200 raw18200Labels = mixedMoment B raw18200step0 raw18200step0Labels := by
      have hz : ∀ j, raw18200 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18200step0 = (fun i j => raw18200 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18200step0 raw18200; decide +kernel
      have hl : raw18200step0Labels = raw18200Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18200 raw18200Labels permutation346 hz
    mixedMoment B raw18200step0 raw18200step0Labels = mixedMoment B raw18200step1 raw18200step1Labels := by
      have ha : raw18200step1 = (fun i j => raw18200step0 (permutation145 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18200step1 raw18200step0; decide +kernel
      have hl : raw18200step1Labels = raw18200step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18200step0 raw18200step0Labels permutation145 permutation3
    mixedMoment B raw18200step1 raw18200step1Labels = mixedMoment B raw18200step2 raw18200step2Labels := by
      have ha : raw18200step2 = -raw18200step1 := by apply Matrix.ext; change ∀ i j, raw18200step2 i j = -(raw18200step1 i j); unfold raw18200step2 raw18200step1; decide +kernel
      have hl : raw18200step2Labels = raw18200step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18200step2 raw18200step2Labels = mixedMoment B raw18200step3 raw18200step3Labels := by
      have ha : raw18200step3 = raw18200step2 := by apply Matrix.ext; unfold raw18200step3 raw18200step2; decide +kernel
      have hl : raw18200step2Labels = labelEmbedding6 ∘ raw18200step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18200step2 raw18200step2Labels raw18200step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5432 node5432Labels := by rfl

theorem canonical18201 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18201 raw18201Labels = mixedMoment B node5450 node5450Labels := by
  calc
    mixedMoment B raw18201 raw18201Labels = mixedMoment B raw18201step0 raw18201step0Labels := by
      have hz : ∀ j, raw18201 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18201step0 = (fun i j => raw18201 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18201step0 raw18201; decide +kernel
      have hl : raw18201step0Labels = raw18201Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18201 raw18201Labels permutation346 hz
    mixedMoment B raw18201step0 raw18201step0Labels = mixedMoment B raw18201step1 raw18201step1Labels := by
      have ha : raw18201step1 = (fun i j => raw18201step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18201step1 raw18201step0; decide +kernel
      have hl : raw18201step1Labels = raw18201step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18201step0 raw18201step0Labels permutation32 permutation3
    mixedMoment B raw18201step1 raw18201step1Labels = mixedMoment B raw18201step2 raw18201step2Labels := by
      have ha : raw18201step2 = raw18201step1 := by apply Matrix.ext; unfold raw18201step2 raw18201step1; decide +kernel
      have hl : raw18201step1Labels = labelEmbedding6 ∘ raw18201step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18201step1 raw18201step1Labels raw18201step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5450 node5450Labels := by rfl

theorem canonical18203 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18203 raw18203Labels = mixedMoment B node5355 node5355Labels := by
  calc
    mixedMoment B raw18203 raw18203Labels = mixedMoment B raw18203step0 raw18203step0Labels := by
      have hz : ∀ j, raw18203 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18203step0 = (fun i j => raw18203 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18203step0 raw18203; decide +kernel
      have hl : raw18203step0Labels = raw18203Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18203 raw18203Labels permutation346 hz
    mixedMoment B raw18203step0 raw18203step0Labels = mixedMoment B raw18203step1 raw18203step1Labels := by
      have ha : raw18203step1 = (fun i j => raw18203step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18203step1 raw18203step0; decide +kernel
      have hl : raw18203step1Labels = raw18203step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18203step0 raw18203step0Labels permutation151 permutation3
    mixedMoment B raw18203step1 raw18203step1Labels = mixedMoment B raw18203step2 raw18203step2Labels := by
      have ha : raw18203step2 = -raw18203step1 := by apply Matrix.ext; change ∀ i j, raw18203step2 i j = -(raw18203step1 i j); unfold raw18203step2 raw18203step1; decide +kernel
      have hl : raw18203step2Labels = raw18203step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18203step2 raw18203step2Labels = mixedMoment B raw18203step3 raw18203step3Labels := by
      have ha : raw18203step3 = raw18203step2 := by apply Matrix.ext; unfold raw18203step3 raw18203step2; decide +kernel
      have hl : raw18203step2Labels = labelEmbedding6 ∘ raw18203step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18203step2 raw18203step2Labels raw18203step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5355 node5355Labels := by rfl

theorem canonical18208 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18208 raw18208Labels = mixedMoment B node4810 node4810Labels := by
  calc
    mixedMoment B raw18208 raw18208Labels = mixedMoment B raw18208step0 raw18208step0Labels := by
      have hz : ∀ j, raw18208 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18208step0 = (fun i j => raw18208 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18208step0 raw18208; decide +kernel
      have hl : raw18208step0Labels = raw18208Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18208 raw18208Labels permutation346 hz
    mixedMoment B raw18208step0 raw18208step0Labels = mixedMoment B raw18208step1 raw18208step1Labels := by
      have ha : raw18208step1 = (fun i j => raw18208step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18208step1 raw18208step0; decide +kernel
      have hl : raw18208step1Labels = raw18208step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18208step0 raw18208step0Labels permutation151 permutation3
    mixedMoment B raw18208step1 raw18208step1Labels = mixedMoment B raw18208step2 raw18208step2Labels := by
      have ha : raw18208step2 = -raw18208step1 := by apply Matrix.ext; change ∀ i j, raw18208step2 i j = -(raw18208step1 i j); unfold raw18208step2 raw18208step1; decide +kernel
      have hl : raw18208step2Labels = raw18208step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18208step2 raw18208step2Labels = mixedMoment B raw18208step3 raw18208step3Labels := by
      have ha : raw18208step3 = raw18208step2 := by apply Matrix.ext; unfold raw18208step3 raw18208step2; decide +kernel
      have hl : raw18208step2Labels = labelEmbedding6 ∘ raw18208step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18208step2 raw18208step2Labels raw18208step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4810 node4810Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical144
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical18485 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18485 raw18485Labels = mixedMoment B node5440 node5440Labels := by
  calc
    mixedMoment B raw18485 raw18485Labels = mixedMoment B raw18485step0 raw18485step0Labels := by
      have hz : ∀ j, raw18485 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18485step0 = (fun i j => raw18485 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18485step0 raw18485; decide +kernel
      have hl : raw18485step0Labels = raw18485Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18485 raw18485Labels permutation346 hz
    mixedMoment B raw18485step0 raw18485step0Labels = mixedMoment B raw18485step1 raw18485step1Labels := by
      have ha : raw18485step1 = (fun i j => raw18485step0 (permutation60 i) (permutation2 j)) := by apply Matrix.ext; unfold raw18485step1 raw18485step0; decide +kernel
      have hl : raw18485step1Labels = raw18485step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18485step0 raw18485step0Labels permutation60 permutation2
    _ = mixedMoment B node5440 node5440Labels := by rfl

theorem canonical18494 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18494 raw18494Labels = mixedMoment B node5386 node5386Labels := by
  calc
    mixedMoment B raw18494 raw18494Labels = mixedMoment B raw18494step0 raw18494step0Labels := by
      have ha : raw18494step0 = (fun i j => raw18494 (permutation269 i) (permutation2 j)) := by apply Matrix.ext; unfold raw18494step0 raw18494; decide +kernel
      have hl : raw18494step0Labels = raw18494Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18494 raw18494Labels permutation269 permutation2
    _ = mixedMoment B node5386 node5386Labels := by rfl

theorem canonical18498 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18498 raw18498Labels = mixedMoment B node5388 node5388Labels := by
  calc
    mixedMoment B raw18498 raw18498Labels = mixedMoment B raw18498step0 raw18498step0Labels := by
      have hz : ∀ j, raw18498 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18498step0 = (fun i j => raw18498 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18498step0 raw18498; decide +kernel
      have hl : raw18498step0Labels = raw18498Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18498 raw18498Labels permutation346 hz
    mixedMoment B raw18498step0 raw18498step0Labels = mixedMoment B raw18498step1 raw18498step1Labels := by
      have ha : raw18498step1 = (fun i j => raw18498step0 (permutation61 i) (permutation2 j)) := by apply Matrix.ext; unfold raw18498step1 raw18498step0; decide +kernel
      have hl : raw18498step1Labels = raw18498step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18498step0 raw18498step0Labels permutation61 permutation2
    _ = mixedMoment B node5388 node5388Labels := by rfl

theorem canonical18503 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18503 raw18503Labels = mixedMoment B node5388 node5388Labels := by
  calc
    mixedMoment B raw18503 raw18503Labels = mixedMoment B raw18503step0 raw18503step0Labels := by
      have hz : ∀ j, raw18503 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18503step0 = (fun i j => raw18503 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18503step0 raw18503; decide +kernel
      have hl : raw18503step0Labels = raw18503Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18503 raw18503Labels permutation346 hz
    mixedMoment B raw18503step0 raw18503step0Labels = mixedMoment B raw18503step1 raw18503step1Labels := by
      have ha : raw18503step1 = (fun i j => raw18503step0 (permutation60 i) (permutation2 j)) := by apply Matrix.ext; unfold raw18503step1 raw18503step0; decide +kernel
      have hl : raw18503step1Labels = raw18503step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18503step0 raw18503step0Labels permutation60 permutation2
    _ = mixedMoment B node5388 node5388Labels := by rfl

theorem canonical18506 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18506 raw18506Labels = mixedMoment B node5432 node5432Labels := by
  calc
    mixedMoment B raw18506 raw18506Labels = mixedMoment B raw18506step0 raw18506step0Labels := by
      have hz : ∀ j, raw18506 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18506step0 = (fun i j => raw18506 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18506step0 raw18506; decide +kernel
      have hl : raw18506step0Labels = raw18506Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18506 raw18506Labels permutation346 hz
    mixedMoment B raw18506step0 raw18506step0Labels = mixedMoment B raw18506step1 raw18506step1Labels := by
      have ha : raw18506step1 = (fun i j => raw18506step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18506step1 raw18506step0; decide +kernel
      have hl : raw18506step1Labels = raw18506step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18506step0 raw18506step0Labels permutation151 permutation3
    mixedMoment B raw18506step1 raw18506step1Labels = mixedMoment B raw18506step2 raw18506step2Labels := by
      have ha : raw18506step2 = -raw18506step1 := by apply Matrix.ext; change ∀ i j, raw18506step2 i j = -(raw18506step1 i j); unfold raw18506step2 raw18506step1; decide +kernel
      have hl : raw18506step2Labels = raw18506step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18506step2 raw18506step2Labels = mixedMoment B raw18506step3 raw18506step3Labels := by
      have ha : raw18506step3 = raw18506step2 := by apply Matrix.ext; unfold raw18506step3 raw18506step2; decide +kernel
      have hl : raw18506step2Labels = labelEmbedding6 ∘ raw18506step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18506step2 raw18506step2Labels raw18506step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5432 node5432Labels := by rfl

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

theorem canonical1953 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1953 raw1953Labels = mixedMoment B node4971 node4971Labels := by
  calc
    mixedMoment B raw1953 raw1953Labels = mixedMoment B raw1953step0 raw1953step0Labels := by
      have ha : raw1953step0 = (fun i j => raw1953 (permutation152 i) (permutation5 j)) := by apply Matrix.ext; unfold raw1953step0 raw1953; decide +kernel
      have hl : raw1953step0Labels = raw1953Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1953 raw1953Labels permutation152 permutation5
    mixedMoment B raw1953step0 raw1953step0Labels = mixedMoment B raw1953step1 raw1953step1Labels := by
      have ha : raw1953step1 = raw1953step0 := by apply Matrix.ext; unfold raw1953step1 raw1953step0; decide +kernel
      have hl : raw1953step0Labels = labelEmbedding8 ∘ raw1953step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1953step0 raw1953step0Labels raw1953step1Labels labelEmbedding8 hl
    _ = mixedMoment B node4971 node4971Labels := by rfl

theorem canonical1954 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1954 raw1954Labels = mixedMoment B node2807 node2807Labels := by
  calc
    mixedMoment B raw1954 raw1954Labels = mixedMoment B raw1954step0 raw1954step0Labels := by
      have ha : raw1954step0 = (fun i j => raw1954 (permutation160 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1954step0 raw1954; decide +kernel
      have hl : raw1954step0Labels = raw1954Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1954 raw1954Labels permutation160 permutation4
    _ = mixedMoment B node2807 node2807Labels := by rfl

theorem canonical1955 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1955 raw1955Labels = mixedMoment B node3590 node3590Labels := by
  calc
    mixedMoment B raw1955 raw1955Labels = mixedMoment B raw1955step0 raw1955step0Labels := by
      have ha : raw1955step0 = (fun i j => raw1955 (permutation156 i) (permutation3 j)) := by apply Matrix.ext; unfold raw1955step0 raw1955; decide +kernel
      have hl : raw1955step0Labels = raw1955Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1955 raw1955Labels permutation156 permutation3
    mixedMoment B raw1955step0 raw1955step0Labels = mixedMoment B raw1955step1 raw1955step1Labels := by
      have ha : raw1955step1 = -raw1955step0 := by apply Matrix.ext; change ∀ i j, raw1955step1 i j = -(raw1955step0 i j); unfold raw1955step1 raw1955step0; decide +kernel
      have hl : raw1955step1Labels = raw1955step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1955step1 raw1955step1Labels = mixedMoment B raw1955step2 raw1955step2Labels := by
      have ha : raw1955step2 = raw1955step1 := by apply Matrix.ext; unfold raw1955step2 raw1955step1; decide +kernel
      have hl : raw1955step1Labels = labelEmbedding1 ∘ raw1955step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1955step1 raw1955step1Labels raw1955step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3590 node3590Labels := by rfl

theorem canonical1965 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1965 raw1965Labels = mixedMoment B node4977 node4977Labels := by
  calc
    mixedMoment B raw1965 raw1965Labels = mixedMoment B raw1965step0 raw1965step0Labels := by
      have ha : raw1965step0 = (fun i j => raw1965 (permutation32 i) (permutation5 j)) := by apply Matrix.ext; unfold raw1965step0 raw1965; decide +kernel
      have hl : raw1965step0Labels = raw1965Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1965 raw1965Labels permutation32 permutation5
    mixedMoment B raw1965step0 raw1965step0Labels = mixedMoment B raw1965step1 raw1965step1Labels := by
      have ha : raw1965step1 = raw1965step0 := by apply Matrix.ext; unfold raw1965step1 raw1965step0; decide +kernel
      have hl : raw1965step0Labels = labelEmbedding8 ∘ raw1965step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1965step0 raw1965step0Labels raw1965step1Labels labelEmbedding8 hl
    _ = mixedMoment B node4977 node4977Labels := by rfl

theorem canonical1966 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1966 raw1966Labels = mixedMoment B node2813 node2813Labels := by
  calc
    mixedMoment B raw1966 raw1966Labels = mixedMoment B raw1966step0 raw1966step0Labels := by
      have ha : raw1966step0 = (fun i j => raw1966 (permutation33 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1966step0 raw1966; decide +kernel
      have hl : raw1966step0Labels = raw1966Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1966 raw1966Labels permutation33 permutation4
    _ = mixedMoment B node2813 node2813Labels := by rfl

theorem canonical1967 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1967 raw1967Labels = mixedMoment B node3595 node3595Labels := by
  calc
    mixedMoment B raw1967 raw1967Labels = mixedMoment B raw1967step0 raw1967step0Labels := by
      have ha : raw1967step0 = (fun i j => raw1967 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw1967step0 raw1967; decide +kernel
      have hl : raw1967step0Labels = raw1967Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1967 raw1967Labels permutation34 permutation3
    mixedMoment B raw1967step0 raw1967step0Labels = mixedMoment B raw1967step1 raw1967step1Labels := by
      have ha : raw1967step1 = -raw1967step0 := by apply Matrix.ext; change ∀ i j, raw1967step1 i j = -(raw1967step0 i j); unfold raw1967step1 raw1967step0; decide +kernel
      have hl : raw1967step1Labels = raw1967step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1967step1 raw1967step1Labels = mixedMoment B raw1967step2 raw1967step2Labels := by
      have ha : raw1967step2 = raw1967step1 := by apply Matrix.ext; unfold raw1967step2 raw1967step1; decide +kernel
      have hl : raw1967step1Labels = labelEmbedding1 ∘ raw1967step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1967step1 raw1967step1Labels raw1967step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3595 node3595Labels := by rfl

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

theorem canonical2373 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2373 raw2373Labels = mixedMoment B node5336 node5336Labels := by
  calc
    mixedMoment B raw2373 raw2373Labels = mixedMoment B raw2373step0 raw2373step0Labels := by
      have ha : raw2373step0 = (fun i j => raw2373 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2373step0 raw2373; decide +kernel
      have hl : raw2373step0Labels = raw2373Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2373 raw2373Labels permutation152 permutation4
    mixedMoment B raw2373step0 raw2373step0Labels = mixedMoment B raw2373step1 raw2373step1Labels := by
      have ha : raw2373step1 = raw2373step0 := by apply Matrix.ext; unfold raw2373step1 raw2373step0; decide +kernel
      have hl : raw2373step0Labels = labelEmbedding7 ∘ raw2373step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2373step0 raw2373step0Labels raw2373step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5336 node5336Labels := by rfl

theorem canonical2374 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2374 raw2374Labels = mixedMoment B node3671 node3671Labels := by
  calc
    mixedMoment B raw2374 raw2374Labels = mixedMoment B raw2374step0 raw2374step0Labels := by
      have ha : raw2374step0 = (fun i j => raw2374 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2374step0 raw2374; decide +kernel
      have hl : raw2374step0Labels = raw2374Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2374 raw2374Labels permutation152 permutation4
    _ = mixedMoment B node3671 node3671Labels := by rfl

theorem canonical2375 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2375 raw2375Labels = mixedMoment B node3754 node3754Labels := by
  calc
    mixedMoment B raw2375 raw2375Labels = mixedMoment B raw2375step0 raw2375step0Labels := by
      have ha : raw2375step0 = (fun i j => raw2375 (permutation154 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2375step0 raw2375; decide +kernel
      have hl : raw2375step0Labels = raw2375Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2375 raw2375Labels permutation154 permutation6
    mixedMoment B raw2375step0 raw2375step0Labels = mixedMoment B raw2375step1 raw2375step1Labels := by
      have ha : raw2375step1 = -raw2375step0 := by apply Matrix.ext; change ∀ i j, raw2375step1 i j = -(raw2375step0 i j); unfold raw2375step1 raw2375step0; decide +kernel
      have hl : raw2375step1Labels = raw2375step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2375step1 raw2375step1Labels = mixedMoment B raw2375step2 raw2375step2Labels := by
      have ha : raw2375step2 = raw2375step1 := by apply Matrix.ext; unfold raw2375step2 raw2375step1; decide +kernel
      have hl : raw2375step1Labels = labelEmbedding1 ∘ raw2375step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2375step1 raw2375step1Labels raw2375step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3754 node3754Labels := by rfl

theorem canonical2400 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2400 raw2400Labels = mixedMoment B node5355 node5355Labels := by
  calc
    mixedMoment B raw2400 raw2400Labels = mixedMoment B raw2400step0 raw2400step0Labels := by
      have ha : raw2400step0 = (fun i j => raw2400 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2400step0 raw2400; decide +kernel
      have hl : raw2400step0Labels = raw2400Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2400 raw2400Labels permutation32 permutation4
    mixedMoment B raw2400step0 raw2400step0Labels = mixedMoment B raw2400step1 raw2400step1Labels := by
      have ha : raw2400step1 = raw2400step0 := by apply Matrix.ext; unfold raw2400step1 raw2400step0; decide +kernel
      have hl : raw2400step0Labels = labelEmbedding7 ∘ raw2400step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2400step0 raw2400step0Labels raw2400step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5355 node5355Labels := by rfl

theorem canonical2401 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2401 raw2401Labels = mixedMoment B node3693 node3693Labels := by
  calc
    mixedMoment B raw2401 raw2401Labels = mixedMoment B raw2401step0 raw2401step0Labels := by
      have ha : raw2401step0 = (fun i j => raw2401 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2401step0 raw2401; decide +kernel
      have hl : raw2401step0Labels = raw2401Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2401 raw2401Labels permutation32 permutation4
    _ = mixedMoment B node3693 node3693Labels := by rfl

theorem canonical2402 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2402 raw2402Labels = mixedMoment B node3770 node3770Labels := by
  calc
    mixedMoment B raw2402 raw2402Labels = mixedMoment B raw2402step0 raw2402step0Labels := by
      have ha : raw2402step0 = (fun i j => raw2402 (permutation34 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2402step0 raw2402; decide +kernel
      have hl : raw2402step0Labels = raw2402Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2402 raw2402Labels permutation34 permutation6
    mixedMoment B raw2402step0 raw2402step0Labels = mixedMoment B raw2402step1 raw2402step1Labels := by
      have ha : raw2402step1 = -raw2402step0 := by apply Matrix.ext; change ∀ i j, raw2402step1 i j = -(raw2402step0 i j); unfold raw2402step1 raw2402step0; decide +kernel
      have hl : raw2402step1Labels = raw2402step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2402step1 raw2402step1Labels = mixedMoment B raw2402step2 raw2402step2Labels := by
      have ha : raw2402step2 = raw2402step1 := by apply Matrix.ext; unfold raw2402step2 raw2402step1; decide +kernel
      have hl : raw2402step1Labels = labelEmbedding1 ∘ raw2402step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2402step1 raw2402step1Labels raw2402step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3770 node3770Labels := by rfl

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

theorem canonical2472 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2472 raw2472Labels = mixedMoment B node5400 node5400Labels := by
  calc
    mixedMoment B raw2472 raw2472Labels = mixedMoment B raw2472step0 raw2472step0Labels := by
      have ha : raw2472step0 = (fun i j => raw2472 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2472step0 raw2472; decide +kernel
      have hl : raw2472step0Labels = raw2472Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2472 raw2472Labels permutation152 permutation4
    mixedMoment B raw2472step0 raw2472step0Labels = mixedMoment B raw2472step1 raw2472step1Labels := by
      have ha : raw2472step1 = raw2472step0 := by apply Matrix.ext; unfold raw2472step1 raw2472step0; decide +kernel
      have hl : raw2472step0Labels = labelEmbedding7 ∘ raw2472step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2472step0 raw2472step0Labels raw2472step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5400 node5400Labels := by rfl

theorem canonical2473 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2473 raw2473Labels = mixedMoment B node3786 node3786Labels := by
  calc
    mixedMoment B raw2473 raw2473Labels = mixedMoment B raw2473step0 raw2473step0Labels := by
      have ha : raw2473step0 = (fun i j => raw2473 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2473step0 raw2473; decide +kernel
      have hl : raw2473step0Labels = raw2473Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2473 raw2473Labels permutation152 permutation4
    _ = mixedMoment B node3786 node3786Labels := by rfl

theorem canonical2474 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2474 raw2474Labels = mixedMoment B node3799 node3799Labels := by
  calc
    mixedMoment B raw2474 raw2474Labels = mixedMoment B raw2474step0 raw2474step0Labels := by
      have ha : raw2474step0 = (fun i j => raw2474 (permutation160 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2474step0 raw2474; decide +kernel
      have hl : raw2474step0Labels = raw2474Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2474 raw2474Labels permutation160 permutation6
    mixedMoment B raw2474step0 raw2474step0Labels = mixedMoment B raw2474step1 raw2474step1Labels := by
      have ha : raw2474step1 = -raw2474step0 := by apply Matrix.ext; change ∀ i j, raw2474step1 i j = -(raw2474step0 i j); unfold raw2474step1 raw2474step0; decide +kernel
      have hl : raw2474step1Labels = raw2474step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2474step1 raw2474step1Labels = mixedMoment B raw2474step2 raw2474step2Labels := by
      have ha : raw2474step2 = raw2474step1 := by apply Matrix.ext; unfold raw2474step2 raw2474step1; decide +kernel
      have hl : raw2474step1Labels = labelEmbedding1 ∘ raw2474step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2474step1 raw2474step1Labels raw2474step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3799 node3799Labels := by rfl

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

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical263
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical33723 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33723 raw33723Labels = mixedMoment B node4676 node4676Labels := by
  calc
    mixedMoment B raw33723 raw33723Labels = mixedMoment B raw33723step0 raw33723step0Labels := by
      have ha : raw33723step0 = (fun i j => raw33723 (permutation160 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33723step0 raw33723; decide +kernel
      have hl : raw33723step0Labels = raw33723Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33723 raw33723Labels permutation160 permutation3
    mixedMoment B raw33723step0 raw33723step0Labels = mixedMoment B raw33723step1 raw33723step1Labels := by
      have ha : raw33723step1 = raw33723step0 := by apply Matrix.ext; unfold raw33723step1 raw33723step0; decide +kernel
      have hl : raw33723step0Labels = labelEmbedding6 ∘ raw33723step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33723step0 raw33723step0Labels raw33723step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4676 node4676Labels := by rfl

theorem canonical33726 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33726 raw33726Labels = mixedMoment B node4684 node4684Labels := by
  calc
    mixedMoment B raw33726 raw33726Labels = mixedMoment B raw33726step0 raw33726step0Labels := by
      have hz : ∀ j, raw33726 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33726step0 = (fun i j => raw33726 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33726step0 raw33726; decide +kernel
      have hl : raw33726step0Labels = raw33726Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33726 raw33726Labels permutation346 hz
    mixedMoment B raw33726step0 raw33726step0Labels = mixedMoment B raw33726step1 raw33726step1Labels := by
      have ha : raw33726step1 = (fun i j => raw33726step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33726step1 raw33726step0; decide +kernel
      have hl : raw33726step1Labels = raw33726step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33726step0 raw33726step0Labels permutation34 permutation3
    mixedMoment B raw33726step1 raw33726step1Labels = mixedMoment B raw33726step2 raw33726step2Labels := by
      have ha : raw33726step2 = raw33726step1 := by apply Matrix.ext; unfold raw33726step2 raw33726step1; decide +kernel
      have hl : raw33726step1Labels = labelEmbedding6 ∘ raw33726step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33726step1 raw33726step1Labels raw33726step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4684 node4684Labels := by rfl

theorem canonical33730 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33730 raw33730Labels = mixedMoment B node4684 node4684Labels := by
  calc
    mixedMoment B raw33730 raw33730Labels = mixedMoment B raw33730step0 raw33730step0Labels := by
      have hz : ∀ j, raw33730 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33730step0 = (fun i j => raw33730 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33730step0 raw33730; decide +kernel
      have hl : raw33730step0Labels = raw33730Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33730 raw33730Labels permutation346 hz
    mixedMoment B raw33730step0 raw33730step0Labels = mixedMoment B raw33730step1 raw33730step1Labels := by
      have ha : raw33730step1 = (fun i j => raw33730step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33730step1 raw33730step0; decide +kernel
      have hl : raw33730step1Labels = raw33730step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33730step0 raw33730step0Labels permutation32 permutation3
    mixedMoment B raw33730step1 raw33730step1Labels = mixedMoment B raw33730step2 raw33730step2Labels := by
      have ha : raw33730step2 = raw33730step1 := by apply Matrix.ext; unfold raw33730step2 raw33730step1; decide +kernel
      have hl : raw33730step1Labels = labelEmbedding6 ∘ raw33730step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33730step1 raw33730step1Labels raw33730step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4684 node4684Labels := by rfl

theorem canonical33733 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33733 raw33733Labels = mixedMoment B node4678 node4678Labels := by
  calc
    mixedMoment B raw33733 raw33733Labels = mixedMoment B raw33733step0 raw33733step0Labels := by
      have hz : ∀ j, raw33733 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33733step0 = (fun i j => raw33733 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33733step0 raw33733; decide +kernel
      have hl : raw33733step0Labels = raw33733Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33733 raw33733Labels permutation346 hz
    mixedMoment B raw33733step0 raw33733step0Labels = mixedMoment B raw33733step1 raw33733step1Labels := by
      have ha : raw33733step1 = (fun i j => raw33733step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33733step1 raw33733step0; decide +kernel
      have hl : raw33733step1Labels = raw33733step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33733step0 raw33733step0Labels permutation32 permutation3
    mixedMoment B raw33733step1 raw33733step1Labels = mixedMoment B raw33733step2 raw33733step2Labels := by
      have ha : raw33733step2 = raw33733step1 := by apply Matrix.ext; unfold raw33733step2 raw33733step1; decide +kernel
      have hl : raw33733step1Labels = labelEmbedding6 ∘ raw33733step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33733step1 raw33733step1Labels raw33733step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4678 node4678Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical277
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical35559 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35559 raw35559Labels = mixedMoment B node5172 node5172Labels := by
  calc
    mixedMoment B raw35559 raw35559Labels = mixedMoment B raw35559step0 raw35559step0Labels := by
      have hz : ∀ j, raw35559 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35559step0 = (fun i j => raw35559 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35559step0 raw35559; decide +kernel
      have hl : raw35559step0Labels = raw35559Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35559 raw35559Labels permutation346 hz
    mixedMoment B raw35559step0 raw35559step0Labels = mixedMoment B raw35559step1 raw35559step1Labels := by
      have ha : raw35559step1 = (fun i j => raw35559step0 (permutation56 i) (permutation2 j)) := by apply Matrix.ext; unfold raw35559step1 raw35559step0; decide +kernel
      have hl : raw35559step1Labels = raw35559step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35559step0 raw35559step0Labels permutation56 permutation2
    _ = mixedMoment B node5172 node5172Labels := by rfl

theorem canonical35560 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35560 raw35560Labels = mixedMoment B node5417 node5417Labels := by
  calc
    mixedMoment B raw35560 raw35560Labels = mixedMoment B raw35560step0 raw35560step0Labels := by
      have ha : raw35560step0 = (fun i j => raw35560 (permutation265 i) (permutation2 j)) := by apply Matrix.ext; unfold raw35560step0 raw35560; decide +kernel
      have hl : raw35560step0Labels = raw35560Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35560 raw35560Labels permutation265 permutation2
    _ = mixedMoment B node5417 node5417Labels := by rfl

theorem canonical35561 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35561 raw35561Labels = mixedMoment B node5435 node5435Labels := by
  calc
    mixedMoment B raw35561 raw35561Labels = mixedMoment B raw35561step0 raw35561step0Labels := by
      have hz : ∀ j, raw35561 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35561step0 = (fun i j => raw35561 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35561step0 raw35561; decide +kernel
      have hl : raw35561step0Labels = raw35561Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35561 raw35561Labels permutation346 hz
    mixedMoment B raw35561step0 raw35561step0Labels = mixedMoment B raw35561step1 raw35561step1Labels := by
      have ha : raw35561step1 = (fun i j => raw35561step0 (permutation58 i) (permutation2 j)) := by apply Matrix.ext; unfold raw35561step1 raw35561step0; decide +kernel
      have hl : raw35561step1Labels = raw35561step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35561step0 raw35561step0Labels permutation58 permutation2
    _ = mixedMoment B node5435 node5435Labels := by rfl

theorem canonical35562 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35562 raw35562Labels = mixedMoment B node4971 node4971Labels := by
  calc
    mixedMoment B raw35562 raw35562Labels = mixedMoment B raw35562step0 raw35562step0Labels := by
      have ha : raw35562step0 = (fun i j => raw35562 (permutation265 i) (permutation2 j)) := by apply Matrix.ext; unfold raw35562step0 raw35562; decide +kernel
      have hl : raw35562step0Labels = raw35562Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35562 raw35562Labels permutation265 permutation2
    _ = mixedMoment B node4971 node4971Labels := by rfl

theorem canonical35563 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35563 raw35563Labels = mixedMoment B node5378 node5378Labels := by
  calc
    mixedMoment B raw35563 raw35563Labels = mixedMoment B raw35563step0 raw35563step0Labels := by
      have ha : raw35563step0 = (fun i j => raw35563 (permutation166 i) (permutation3 j)) := by apply Matrix.ext; unfold raw35563step0 raw35563; decide +kernel
      have hl : raw35563step0Labels = raw35563Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35563 raw35563Labels permutation166 permutation3
    mixedMoment B raw35563step0 raw35563step0Labels = mixedMoment B raw35563step1 raw35563step1Labels := by
      have ha : raw35563step1 = raw35563step0 := by apply Matrix.ext; unfold raw35563step1 raw35563step0; decide +kernel
      have hl : raw35563step0Labels = labelEmbedding6 ∘ raw35563step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35563step0 raw35563step0Labels raw35563step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5378 node5378Labels := by rfl

theorem canonical35564 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35564 raw35564Labels = mixedMoment B node4977 node4977Labels := by
  calc
    mixedMoment B raw35564 raw35564Labels = mixedMoment B raw35564step0 raw35564step0Labels := by
      have hz : ∀ j, raw35564 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35564step0 = (fun i j => raw35564 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35564step0 raw35564; decide +kernel
      have hl : raw35564step0Labels = raw35564Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35564 raw35564Labels permutation346 hz
    mixedMoment B raw35564step0 raw35564step0Labels = mixedMoment B raw35564step1 raw35564step1Labels := by
      have ha : raw35564step1 = (fun i j => raw35564step0 (permutation59 i) (permutation2 j)) := by apply Matrix.ext; unfold raw35564step1 raw35564step0; decide +kernel
      have hl : raw35564step1Labels = raw35564step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35564step0 raw35564step0Labels permutation59 permutation2
    _ = mixedMoment B node4977 node4977Labels := by rfl

theorem canonical35565 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35565 raw35565Labels = mixedMoment B node5336 node5336Labels := by
  calc
    mixedMoment B raw35565 raw35565Labels = mixedMoment B raw35565step0 raw35565step0Labels := by
      have ha : raw35565step0 = (fun i j => raw35565 (permutation664 i) (permutation3 j)) := by apply Matrix.ext; unfold raw35565step0 raw35565; decide +kernel
      have hl : raw35565step0Labels = raw35565Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35565 raw35565Labels permutation664 permutation3
    mixedMoment B raw35565step0 raw35565step0Labels = mixedMoment B raw35565step1 raw35565step1Labels := by
      have ha : raw35565step1 = -raw35565step0 := by apply Matrix.ext; change ∀ i j, raw35565step1 i j = -(raw35565step0 i j); unfold raw35565step1 raw35565step0; decide +kernel
      have hl : raw35565step1Labels = raw35565step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35565step1 raw35565step1Labels = mixedMoment B raw35565step2 raw35565step2Labels := by
      have ha : raw35565step2 = raw35565step1 := by apply Matrix.ext; unfold raw35565step2 raw35565step1; decide +kernel
      have hl : raw35565step1Labels = labelEmbedding6 ∘ raw35565step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35565step1 raw35565step1Labels raw35565step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5336 node5336Labels := by rfl

theorem canonical35566 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35566 raw35566Labels = mixedMoment B node5355 node5355Labels := by
  calc
    mixedMoment B raw35566 raw35566Labels = mixedMoment B raw35566step0 raw35566step0Labels := by
      have hz : ∀ j, raw35566 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35566step0 = (fun i j => raw35566 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35566step0 raw35566; decide +kernel
      have hl : raw35566step0Labels = raw35566Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35566 raw35566Labels permutation346 hz
    mixedMoment B raw35566step0 raw35566step0Labels = mixedMoment B raw35566step1 raw35566step1Labels := by
      have ha : raw35566step1 = (fun i j => raw35566step0 (permutation145 i) (permutation3 j)) := by apply Matrix.ext; unfold raw35566step1 raw35566step0; decide +kernel
      have hl : raw35566step1Labels = raw35566step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35566step0 raw35566step0Labels permutation145 permutation3
    mixedMoment B raw35566step1 raw35566step1Labels = mixedMoment B raw35566step2 raw35566step2Labels := by
      have ha : raw35566step2 = -raw35566step1 := by apply Matrix.ext; change ∀ i j, raw35566step2 i j = -(raw35566step1 i j); unfold raw35566step2 raw35566step1; decide +kernel
      have hl : raw35566step2Labels = raw35566step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35566step2 raw35566step2Labels = mixedMoment B raw35566step3 raw35566step3Labels := by
      have ha : raw35566step3 = raw35566step2 := by apply Matrix.ext; unfold raw35566step3 raw35566step2; decide +kernel
      have hl : raw35566step2Labels = labelEmbedding6 ∘ raw35566step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35566step2 raw35566step2Labels raw35566step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5355 node5355Labels := by rfl

theorem canonical35567 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35567 raw35567Labels = mixedMoment B node4977 node4977Labels := by
  calc
    mixedMoment B raw35567 raw35567Labels = mixedMoment B raw35567step0 raw35567step0Labels := by
      have hz : ∀ j, raw35567 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35567step0 = (fun i j => raw35567 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35567step0 raw35567; decide +kernel
      have hl : raw35567step0Labels = raw35567Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35567 raw35567Labels permutation346 hz
    mixedMoment B raw35567step0 raw35567step0Labels = mixedMoment B raw35567step1 raw35567step1Labels := by
      have ha : raw35567step1 = (fun i j => raw35567step0 (permutation57 i) (permutation2 j)) := by apply Matrix.ext; unfold raw35567step1 raw35567step0; decide +kernel
      have hl : raw35567step1Labels = raw35567step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35567step0 raw35567step0Labels permutation57 permutation2
    _ = mixedMoment B node4977 node4977Labels := by rfl

theorem canonical35568 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35568 raw35568Labels = mixedMoment B node5336 node5336Labels := by
  calc
    mixedMoment B raw35568 raw35568Labels = mixedMoment B raw35568step0 raw35568step0Labels := by
      have ha : raw35568step0 = (fun i j => raw35568 (permutation688 i) (permutation3 j)) := by apply Matrix.ext; unfold raw35568step0 raw35568; decide +kernel
      have hl : raw35568step0Labels = raw35568Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35568 raw35568Labels permutation688 permutation3
    mixedMoment B raw35568step0 raw35568step0Labels = mixedMoment B raw35568step1 raw35568step1Labels := by
      have ha : raw35568step1 = -raw35568step0 := by apply Matrix.ext; change ∀ i j, raw35568step1 i j = -(raw35568step0 i j); unfold raw35568step1 raw35568step0; decide +kernel
      have hl : raw35568step1Labels = raw35568step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35568step1 raw35568step1Labels = mixedMoment B raw35568step2 raw35568step2Labels := by
      have ha : raw35568step2 = raw35568step1 := by apply Matrix.ext; unfold raw35568step2 raw35568step1; decide +kernel
      have hl : raw35568step1Labels = labelEmbedding6 ∘ raw35568step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35568step1 raw35568step1Labels raw35568step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5336 node5336Labels := by rfl

theorem canonical35569 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35569 raw35569Labels = mixedMoment B node4770 node4770Labels := by
  calc
    mixedMoment B raw35569 raw35569Labels = mixedMoment B raw35569step0 raw35569step0Labels := by
      have hz : ∀ j, raw35569 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35569step0 = (fun i j => raw35569 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35569step0 raw35569; decide +kernel
      have hl : raw35569step0Labels = raw35569Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35569 raw35569Labels permutation346 hz
    mixedMoment B raw35569step0 raw35569step0Labels = mixedMoment B raw35569step1 raw35569step1Labels := by
      have ha : raw35569step1 = (fun i j => raw35569step0 (permutation144 i) (permutation3 j)) := by apply Matrix.ext; unfold raw35569step1 raw35569step0; decide +kernel
      have hl : raw35569step1Labels = raw35569step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35569step0 raw35569step0Labels permutation144 permutation3
    mixedMoment B raw35569step1 raw35569step1Labels = mixedMoment B raw35569step2 raw35569step2Labels := by
      have ha : raw35569step2 = -raw35569step1 := by apply Matrix.ext; change ∀ i j, raw35569step2 i j = -(raw35569step1 i j); unfold raw35569step2 raw35569step1; decide +kernel
      have hl : raw35569step2Labels = raw35569step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35569step2 raw35569step2Labels = mixedMoment B raw35569step3 raw35569step3Labels := by
      have ha : raw35569step3 = raw35569step2 := by apply Matrix.ext; unfold raw35569step3 raw35569step2; decide +kernel
      have hl : raw35569step2Labels = labelEmbedding6 ∘ raw35569step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35569step2 raw35569step2Labels raw35569step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4770 node4770Labels := by rfl

theorem canonical35570 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35570 raw35570Labels = mixedMoment B node4766 node4766Labels := by
  calc
    mixedMoment B raw35570 raw35570Labels = mixedMoment B raw35570step0 raw35570step0Labels := by
      have ha : raw35570step0 = (fun i j => raw35570 (permutation664 i) (permutation3 j)) := by apply Matrix.ext; unfold raw35570step0 raw35570; decide +kernel
      have hl : raw35570step0Labels = raw35570Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35570 raw35570Labels permutation664 permutation3
    mixedMoment B raw35570step0 raw35570step0Labels = mixedMoment B raw35570step1 raw35570step1Labels := by
      have ha : raw35570step1 = -raw35570step0 := by apply Matrix.ext; change ∀ i j, raw35570step1 i j = -(raw35570step0 i j); unfold raw35570step1 raw35570step0; decide +kernel
      have hl : raw35570step1Labels = raw35570step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35570step1 raw35570step1Labels = mixedMoment B raw35570step2 raw35570step2Labels := by
      have ha : raw35570step2 = raw35570step1 := by apply Matrix.ext; unfold raw35570step2 raw35570step1; decide +kernel
      have hl : raw35570step1Labels = labelEmbedding6 ∘ raw35570step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35570step1 raw35570step1Labels raw35570step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4766 node4766Labels := by rfl

theorem canonical35571 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35571 raw35571Labels = mixedMoment B node4810 node4810Labels := by
  calc
    mixedMoment B raw35571 raw35571Labels = mixedMoment B raw35571step0 raw35571step0Labels := by
      have hz : ∀ j, raw35571 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35571step0 = (fun i j => raw35571 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35571step0 raw35571; decide +kernel
      have hl : raw35571step0Labels = raw35571Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35571 raw35571Labels permutation346 hz
    mixedMoment B raw35571step0 raw35571step0Labels = mixedMoment B raw35571step1 raw35571step1Labels := by
      have ha : raw35571step1 = (fun i j => raw35571step0 (permutation145 i) (permutation3 j)) := by apply Matrix.ext; unfold raw35571step1 raw35571step0; decide +kernel
      have hl : raw35571step1Labels = raw35571step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35571step0 raw35571step0Labels permutation145 permutation3
    mixedMoment B raw35571step1 raw35571step1Labels = mixedMoment B raw35571step2 raw35571step2Labels := by
      have ha : raw35571step2 = -raw35571step1 := by apply Matrix.ext; change ∀ i j, raw35571step2 i j = -(raw35571step1 i j); unfold raw35571step2 raw35571step1; decide +kernel
      have hl : raw35571step2Labels = raw35571step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35571step2 raw35571step2Labels = mixedMoment B raw35571step3 raw35571step3Labels := by
      have ha : raw35571step3 = raw35571step2 := by apply Matrix.ext; unfold raw35571step3 raw35571step2; decide +kernel
      have hl : raw35571step2Labels = labelEmbedding6 ∘ raw35571step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35571step2 raw35571step2Labels raw35571step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4810 node4810Labels := by rfl

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

theorem singleton4678 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4678 node4678Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1804 node1804Labels + mixedMoment B node2143 node2143Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1557 singletonSmall4678
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4678) = raw1557Labels := by decide +kernel
  rw [hl, canonical1557 B hB] at h
  have hc0 : mixedMoment B raw1557 (Fin.cases (0 : Fin 2) singletonSmall4678) =
      mixedMoment B node1804 node1804Labels := by
    have ha : raw1557 = raw1558 := by apply Matrix.ext; unfold raw1557 raw1558; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4678 = raw1558Labels := by decide +kernel
    rw [ha, hj, canonical1558 B hB]
  have hc1 : mixedMoment B raw1557 (Fin.cases (1 : Fin 2) singletonSmall4678) =
      mixedMoment B node2143 node2143Labels := by
    have ha : raw1557 = raw1559 := by apply Matrix.ext; unfold raw1557 raw1559; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4678 = raw1559Labels := by decide +kernel
    rw [ha, hj, canonical1559 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4684 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4684 node4684Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1810 node1810Labels + mixedMoment B node2152 node2152Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1566 singletonSmall4684
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4684) = raw1566Labels := by decide +kernel
  rw [hl, canonical1566 B hB] at h
  have hc0 : mixedMoment B raw1566 (Fin.cases (0 : Fin 2) singletonSmall4684) =
      mixedMoment B node1810 node1810Labels := by
    have ha : raw1566 = raw1567 := by apply Matrix.ext; unfold raw1566 raw1567; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4684 = raw1567Labels := by decide +kernel
    rw [ha, hj, canonical1567 B hB]
  have hc1 : mixedMoment B raw1566 (Fin.cases (1 : Fin 2) singletonSmall4684) =
      mixedMoment B node2152 node2152Labels := by
    have ha : raw1566 = raw1568 := by apply Matrix.ext; unfold raw1566 raw1568; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4684 = raw1568Labels := by decide +kernel
    rw [ha, hj, canonical1568 B hB]
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

theorem singleton4766 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4766 node4766Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1966 node1966Labels + mixedMoment B node2177 node2177Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1698 singletonSmall4766
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4766) = raw1698Labels := by decide +kernel
  rw [hl, canonical1698 B hB] at h
  have hc0 : mixedMoment B raw1698 (Fin.cases (0 : Fin 2) singletonSmall4766) =
      mixedMoment B node1966 node1966Labels := by
    have ha : raw1698 = raw1699 := by apply Matrix.ext; unfold raw1698 raw1699; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4766 = raw1699Labels := by decide +kernel
    rw [ha, hj, canonical1699 B hB]
  have hc1 : mixedMoment B raw1698 (Fin.cases (1 : Fin 2) singletonSmall4766) =
      mixedMoment B node2177 node2177Labels := by
    have ha : raw1698 = raw1700 := by apply Matrix.ext; unfold raw1698 raw1700; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4766 = raw1700Labels := by decide +kernel
    rw [ha, hj, canonical1700 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4770 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4770 node4770Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1970 node1970Labels + mixedMoment B node2186 node2186Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1707 singletonSmall4770
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4770) = raw1707Labels := by decide +kernel
  rw [hl, canonical1707 B hB] at h
  have hc0 : mixedMoment B raw1707 (Fin.cases (0 : Fin 2) singletonSmall4770) =
      mixedMoment B node1970 node1970Labels := by
    have ha : raw1707 = raw1708 := by apply Matrix.ext; unfold raw1707 raw1708; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4770 = raw1708Labels := by decide +kernel
    rw [ha, hj, canonical1708 B hB]
  have hc1 : mixedMoment B raw1707 (Fin.cases (1 : Fin 2) singletonSmall4770) =
      mixedMoment B node2186 node2186Labels := by
    have ha : raw1707 = raw1709 := by apply Matrix.ext; unfold raw1707 raw1709; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4770 = raw1709Labels := by decide +kernel
    rw [ha, hj, canonical1709 B hB]
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

theorem singleton4810 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4810 node4810Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2028 node2028Labels + mixedMoment B node2215 node2215Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1746 singletonSmall4810
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4810) = raw1746Labels := by decide +kernel
  rw [hl, canonical1746 B hB] at h
  have hc0 : mixedMoment B raw1746 (Fin.cases (0 : Fin 2) singletonSmall4810) =
      mixedMoment B node2028 node2028Labels := by
    have ha : raw1746 = raw1747 := by apply Matrix.ext; unfold raw1746 raw1747; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4810 = raw1747Labels := by decide +kernel
    rw [ha, hj, canonical1747 B hB]
  have hc1 : mixedMoment B raw1746 (Fin.cases (1 : Fin 2) singletonSmall4810) =
      mixedMoment B node2215 node2215Labels := by
    have ha : raw1746 = raw1748 := by apply Matrix.ext; unfold raw1746 raw1748; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4810 = raw1748Labels := by decide +kernel
    rw [ha, hj, canonical1748 B hB]
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

theorem singleton4971 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4971 node4971Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2807 node2807Labels + mixedMoment B node3590 node3590Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1953 singletonSmall4971
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4971) = raw1953Labels := by decide +kernel
  rw [hl, canonical1953 B hB] at h
  have hc0 : mixedMoment B raw1953 (Fin.cases (0 : Fin 2) singletonSmall4971) =
      mixedMoment B node2807 node2807Labels := by
    have ha : raw1953 = raw1954 := by apply Matrix.ext; unfold raw1953 raw1954; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4971 = raw1954Labels := by decide +kernel
    rw [ha, hj, canonical1954 B hB]
  have hc1 : mixedMoment B raw1953 (Fin.cases (1 : Fin 2) singletonSmall4971) =
      mixedMoment B node3590 node3590Labels := by
    have ha : raw1953 = raw1955 := by apply Matrix.ext; unfold raw1953 raw1955; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4971 = raw1955Labels := by decide +kernel
    rw [ha, hj, canonical1955 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4977 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4977 node4977Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2813 node2813Labels + mixedMoment B node3595 node3595Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1965 singletonSmall4977
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4977) = raw1965Labels := by decide +kernel
  rw [hl, canonical1965 B hB] at h
  have hc0 : mixedMoment B raw1965 (Fin.cases (0 : Fin 2) singletonSmall4977) =
      mixedMoment B node2813 node2813Labels := by
    have ha : raw1965 = raw1966 := by apply Matrix.ext; unfold raw1965 raw1966; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4977 = raw1966Labels := by decide +kernel
    rw [ha, hj, canonical1966 B hB]
  have hc1 : mixedMoment B raw1965 (Fin.cases (1 : Fin 2) singletonSmall4977) =
      mixedMoment B node3595 node3595Labels := by
    have ha : raw1965 = raw1967 := by apply Matrix.ext; unfold raw1965 raw1967; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4977 = raw1967Labels := by decide +kernel
    rw [ha, hj, canonical1967 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons83
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singleton5336 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5336 node5336Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3671 node3671Labels + mixedMoment B node3754 node3754Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2373 singletonSmall5336
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5336) = raw2373Labels := by decide +kernel
  rw [hl, canonical2373 B hB] at h
  have hc0 : mixedMoment B raw2373 (Fin.cases (0 : Fin 2) singletonSmall5336) =
      mixedMoment B node3671 node3671Labels := by
    have ha : raw2373 = raw2374 := by apply Matrix.ext; unfold raw2373 raw2374; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5336 = raw2374Labels := by decide +kernel
    rw [ha, hj, canonical2374 B hB]
  have hc1 : mixedMoment B raw2373 (Fin.cases (1 : Fin 2) singletonSmall5336) =
      mixedMoment B node3754 node3754Labels := by
    have ha : raw2373 = raw2375 := by apply Matrix.ext; unfold raw2373 raw2375; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5336 = raw2375Labels := by decide +kernel
    rw [ha, hj, canonical2375 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton5355 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5355 node5355Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3693 node3693Labels + mixedMoment B node3770 node3770Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2400 singletonSmall5355
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5355) = raw2400Labels := by decide +kernel
  rw [hl, canonical2400 B hB] at h
  have hc0 : mixedMoment B raw2400 (Fin.cases (0 : Fin 2) singletonSmall5355) =
      mixedMoment B node3693 node3693Labels := by
    have ha : raw2400 = raw2401 := by apply Matrix.ext; unfold raw2400 raw2401; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5355 = raw2401Labels := by decide +kernel
    rw [ha, hj, canonical2401 B hB]
  have hc1 : mixedMoment B raw2400 (Fin.cases (1 : Fin 2) singletonSmall5355) =
      mixedMoment B node3770 node3770Labels := by
    have ha : raw2400 = raw2402 := by apply Matrix.ext; unfold raw2400 raw2402; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5355 = raw2402Labels := by decide +kernel
    rw [ha, hj, canonical2402 B hB]
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

theorem singleton5400 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5400 node5400Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3786 node3786Labels + mixedMoment B node3799 node3799Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2472 singletonSmall5400
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5400) = raw2472Labels := by decide +kernel
  rw [hl, canonical2472 B hB] at h
  have hc0 : mixedMoment B raw2472 (Fin.cases (0 : Fin 2) singletonSmall5400) =
      mixedMoment B node3786 node3786Labels := by
    have ha : raw2472 = raw2473 := by apply Matrix.ext; unfold raw2472 raw2473; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5400 = raw2473Labels := by decide +kernel
    rw [ha, hj, canonical2473 B hB]
  have hc1 : mixedMoment B raw2472 (Fin.cases (1 : Fin 2) singletonSmall5400) =
      mixedMoment B node3799 node3799Labels := by
    have ha : raw2472 = raw2474 := by apply Matrix.ext; unfold raw2472 raw2474; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5400 = raw2474Labels := by decide +kernel
    rw [ha, hj, canonical2474 B hB]
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

theorem sound1804 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1804 node1804Labels = Sparse.eval nodeValue1804 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1804) = mixedMoment B node1804 node1804Labels := rfl
  simpa [nodeValue1804, Sparse.eval] using hc.symm

theorem sound1810 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1810 node1810Labels = Sparse.eval nodeValue1810 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1810) = mixedMoment B node1810 node1810Labels := rfl
  simpa [nodeValue1810, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound30
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound1966 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1966 node1966Labels = Sparse.eval nodeValue1966 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1966) = mixedMoment B node1966 node1966Labels := rfl
  simpa [nodeValue1966, Sparse.eval] using hc.symm

theorem sound1970 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1970 node1970Labels = Sparse.eval nodeValue1970 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1970) = mixedMoment B node1970 node1970Labels := rfl
  simpa [nodeValue1970, Sparse.eval] using hc.symm

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

theorem sound2028 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2028 node2028Labels = Sparse.eval nodeValue2028 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2028) = mixedMoment B node2028 node2028Labels := rfl
  simpa [nodeValue2028, Sparse.eval] using hc.symm

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

theorem sound2106 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2106 node2106Labels = Sparse.eval nodeValue2106 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2106) = mixedMoment B node2106 node2106Labels := rfl
  simpa [nodeValue2106, Sparse.eval] using hc.symm

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

theorem sound2143 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2143 node2143Labels = Sparse.eval nodeValue2143 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2143) = mixedMoment B node2143 node2143Labels := rfl
  simpa [nodeValue2143, Sparse.eval] using hc.symm

theorem sound2152 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2152 node2152Labels = Sparse.eval nodeValue2152 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2152) = mixedMoment B node2152 node2152Labels := rfl
  simpa [nodeValue2152, Sparse.eval] using hc.symm

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

theorem sound2177 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2177 node2177Labels = Sparse.eval nodeValue2177 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2177) = mixedMoment B node2177 node2177Labels := rfl
  simpa [nodeValue2177, Sparse.eval] using hc.symm

theorem sound2186 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2186 node2186Labels = Sparse.eval nodeValue2186 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2186) = mixedMoment B node2186 node2186Labels := rfl
  simpa [nodeValue2186, Sparse.eval] using hc.symm

theorem sound2215 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2215 node2215Labels = Sparse.eval nodeValue2215 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2215) = mixedMoment B node2215 node2215Labels := rfl
  simpa [nodeValue2215, Sparse.eval] using hc.symm

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

theorem sound2807 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2807 node2807Labels = Sparse.eval nodeValue2807 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2807) = mixedMoment B node2807 node2807Labels := rfl
  simpa [nodeValue2807, Sparse.eval] using hc.symm

theorem sound2813 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2813 node2813Labels = Sparse.eval nodeValue2813 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2813) = mixedMoment B node2813 node2813Labels := rfl
  simpa [nodeValue2813, Sparse.eval] using hc.symm

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

theorem sound3590 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3590 node3590Labels = Sparse.eval nodeValue3590 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3590) = mixedMoment B node3590 node3590Labels := rfl
  simpa [nodeValue3590, Sparse.eval] using hc.symm

theorem sound3595 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3595 node3595Labels = Sparse.eval nodeValue3595 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3595) = mixedMoment B node3595 node3595Labels := rfl
  simpa [nodeValue3595, Sparse.eval] using hc.symm

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

theorem sound3671 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3671 node3671Labels = Sparse.eval nodeValue3671 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3671) = mixedMoment B node3671 node3671Labels := rfl
  simpa [nodeValue3671, Sparse.eval] using hc.symm

theorem sound3693 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3693 node3693Labels = Sparse.eval nodeValue3693 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3693) = mixedMoment B node3693 node3693Labels := rfl
  simpa [nodeValue3693, Sparse.eval] using hc.symm

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

theorem sound3719 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3719 node3719Labels = Sparse.eval nodeValue3719 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3719) = mixedMoment B node3719 node3719Labels := rfl
  simpa [nodeValue3719, Sparse.eval] using hc.symm

theorem sound3754 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3754 node3754Labels = Sparse.eval nodeValue3754 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3754) = mixedMoment B node3754 node3754Labels := rfl
  simpa [nodeValue3754, Sparse.eval] using hc.symm

theorem sound3770 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3770 node3770Labels = Sparse.eval nodeValue3770 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3770) = mixedMoment B node3770 node3770Labels := rfl
  simpa [nodeValue3770, Sparse.eval] using hc.symm

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

theorem sound3786 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3786 node3786Labels = Sparse.eval nodeValue3786 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3786) = mixedMoment B node3786 node3786Labels := rfl
  simpa [nodeValue3786, Sparse.eval] using hc.symm

theorem sound3795 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3795 node3795Labels = Sparse.eval nodeValue3795 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3795) = mixedMoment B node3795 node3795Labels := rfl
  simpa [nodeValue3795, Sparse.eval] using hc.symm

theorem sound3799 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3799 node3799Labels = Sparse.eval nodeValue3799 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3799) = mixedMoment B node3799 node3799Labels := rfl
  simpa [nodeValue3799, Sparse.eval] using hc.symm

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

theorem sound4678 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4678 node4678Labels = Sparse.eval nodeValue4678 (mixedVector B) := by
  have h := singleton4678 B _hB
  rw [sound1804 B _hB _hF, sound2143 B _hB _hF] at h
  norm_num [nodeValue4678, nodeValue1804, nodeValue2143, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4684 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4684 node4684Labels = Sparse.eval nodeValue4684 (mixedVector B) := by
  have h := singleton4684 B _hB
  rw [sound1810 B _hB _hF, sound2152 B _hB _hF] at h
  norm_num [nodeValue4684, nodeValue1810, nodeValue2152, Sparse.eval] at h ⊢
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

theorem sound4766 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4766 node4766Labels = Sparse.eval nodeValue4766 (mixedVector B) := by
  have h := singleton4766 B _hB
  rw [sound1966 B _hB _hF, sound2177 B _hB _hF] at h
  norm_num [nodeValue4766, nodeValue1966, nodeValue2177, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4770 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4770 node4770Labels = Sparse.eval nodeValue4770 (mixedVector B) := by
  have h := singleton4770 B _hB
  rw [sound1970 B _hB _hF, sound2186 B _hB _hF] at h
  norm_num [nodeValue4770, nodeValue1970, nodeValue2186, Sparse.eval] at h ⊢
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

theorem sound4810 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4810 node4810Labels = Sparse.eval nodeValue4810 (mixedVector B) := by
  have h := singleton4810 B _hB
  rw [sound2028 B _hB _hF, sound2215 B _hB _hF] at h
  norm_num [nodeValue4810, nodeValue2028, nodeValue2215, Sparse.eval] at h ⊢
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

theorem sound4971 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4971 node4971Labels = Sparse.eval nodeValue4971 (mixedVector B) := by
  have h := singleton4971 B _hB
  rw [sound2807 B _hB _hF, sound3590 B _hB _hF] at h
  norm_num [nodeValue4971, nodeValue2807, nodeValue3590, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4977 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4977 node4977Labels = Sparse.eval nodeValue4977 (mixedVector B) := by
  have h := singleton4977 B _hB
  rw [sound2813 B _hB _hF, sound3595 B _hB _hF] at h
  norm_num [nodeValue4977, nodeValue2813, nodeValue3595, Sparse.eval] at h ⊢
  linarith only [h]

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

theorem sound5336 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5336 node5336Labels = Sparse.eval nodeValue5336 (mixedVector B) := by
  have h := singleton5336 B _hB
  rw [sound3671 B _hB _hF, sound3754 B _hB _hF] at h
  norm_num [nodeValue5336, nodeValue3671, nodeValue3754, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5355 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5355 node5355Labels = Sparse.eval nodeValue5355 (mixedVector B) := by
  have h := singleton5355 B _hB
  rw [sound3693 B _hB _hF, sound3770 B _hB _hF] at h
  norm_num [nodeValue5355, nodeValue3693, nodeValue3770, Sparse.eval] at h ⊢
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

theorem sound5378 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5378 node5378Labels = Sparse.eval nodeValue5378 (mixedVector B) := by
  have h := singleton5378 B _hB
  rw [sound3719 B _hB _hF, sound3795 B _hB _hF] at h
  norm_num [nodeValue5378, nodeValue3719, nodeValue3795, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5400 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5400 node5400Labels = Sparse.eval nodeValue5400 (mixedVector B) := by
  have h := singleton5400 B _hB
  rw [sound3786 B _hB _hF, sound3799 B _hB _hF] at h
  norm_num [nodeValue5400, nodeValue3786, nodeValue3799, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5432 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5432 node5432Labels = Sparse.eval nodeValue5432 (mixedVector B) := by
  have h := singleton5432 B _hB
  rw [sound3850 B _hB _hF] at h
  norm_num [nodeValue5432, nodeValue3850, Sparse.eval] at h ⊢
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources80
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sourceEq2573 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2573 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2573 + difference 0 1) (sourceB2573 + difference 1 0) sourceC2573) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5172) := by
    have ha : (tripleCharges (sourceA2573 + difference 0 1) (sourceB2573 + difference 1 0) sourceC2573) = raw35559 := by
      apply Matrix.ext; unfold tripleCharges sourceA2573 sourceB2573 sourceC2573 difference raw35559; decide +kernel
    rw [ha]
    exact (canonical35559 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2573 + difference 0 2) (sourceB2573 + difference 2 0) sourceC2573) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5417) := by
    have ha : (tripleCharges (sourceA2573 + difference 0 2) (sourceB2573 + difference 2 0) sourceC2573) = raw35560 := by
      apply Matrix.ext; unfold tripleCharges sourceA2573 sourceB2573 sourceC2573 difference raw35560; decide +kernel
    rw [ha]
    exact (canonical35560 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2573 + difference 0 3) (sourceB2573 + difference 3 0) sourceC2573) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5435) := by
    have ha : (tripleCharges (sourceA2573 + difference 0 3) (sourceB2573 + difference 3 0) sourceC2573) = raw18182 := by
      apply Matrix.ext; unfold tripleCharges sourceA2573 sourceB2573 sourceC2573 difference raw18182; decide +kernel
    rw [ha]
    exact (canonical18182 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2573 + difference 0 4) (sourceB2573 + difference 4 0) sourceC2573) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5435) := by
    have ha : (tripleCharges (sourceA2573 + difference 0 4) (sourceB2573 + difference 4 0) sourceC2573) = raw35561 := by
      apply Matrix.ext; unfold tripleCharges sourceA2573 sourceB2573 sourceC2573 difference raw35561; decide +kernel
    rw [ha]
    exact (canonical35561 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2573 + difference 0 5) (sourceB2573 + difference 5 0) sourceC2573) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5440) := by
    have ha : (tripleCharges (sourceA2573 + difference 0 5) (sourceB2573 + difference 5 0) sourceC2573) = raw18485 := by
      apply Matrix.ext; unfold tripleCharges sourceA2573 sourceB2573 sourceC2573 difference raw18485; decide +kernel
    rw [ha]
    exact (canonical18485 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2573 + difference 1 0) (sourceB2573 + difference 0 1) sourceC2573) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4865) := by
    have ha : (tripleCharges (sourceA2573 + difference 1 0) (sourceB2573 + difference 0 1) sourceC2573) = raw18197 := by
      apply Matrix.ext; unfold tripleCharges sourceA2573 sourceB2573 sourceC2573 difference raw18197; decide +kernel
    rw [ha]
    exact (canonical18197 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2573 + difference 1 2) (sourceB2573 + difference 2 1) sourceC2573) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5400) := by
    have ha : (tripleCharges (sourceA2573 + difference 1 2) (sourceB2573 + difference 2 1) sourceC2573) = raw18199 := by
      apply Matrix.ext; unfold tripleCharges sourceA2573 sourceB2573 sourceC2573 difference raw18199; decide +kernel
    rw [ha]
    exact (canonical18199 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2573 + difference 1 3) (sourceB2573 + difference 3 1) sourceC2573) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5432) := by
    have ha : (tripleCharges (sourceA2573 + difference 1 3) (sourceB2573 + difference 3 1) sourceC2573) = raw18506 := by
      apply Matrix.ext; unfold tripleCharges sourceA2573 sourceB2573 sourceC2573 difference raw18506; decide +kernel
    rw [ha]
    exact (canonical18506 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2573 + difference 1 4) (sourceB2573 + difference 4 1) sourceC2573) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5432) := by
    have ha : (tripleCharges (sourceA2573 + difference 1 4) (sourceB2573 + difference 4 1) sourceC2573) = raw18200 := by
      apply Matrix.ext; unfold tripleCharges sourceA2573 sourceB2573 sourceC2573 difference raw18200; decide +kernel
    rw [ha]
    exact (canonical18200 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2573 + difference 1 5) (sourceB2573 + difference 5 1) sourceC2573) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5450) := by
    have ha : (tripleCharges (sourceA2573 + difference 1 5) (sourceB2573 + difference 5 1) sourceC2573) = raw18201 := by
      apply Matrix.ext; unfold tripleCharges sourceA2573 sourceB2573 sourceC2573 difference raw18201; decide +kernel
    rw [ha]
    exact (canonical18201 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2573 + difference 2 0) (sourceB2573 + difference 0 2) sourceC2573) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4676) := by
    have ha : (tripleCharges (sourceA2573 + difference 2 0) (sourceB2573 + difference 0 2) sourceC2573) = raw33723 := by
      apply Matrix.ext; unfold tripleCharges sourceA2573 sourceB2573 sourceC2573 difference raw33723; decide +kernel
    rw [ha]
    exact (canonical33723 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2573 + difference 2 1) (sourceB2573 + difference 1 2) sourceC2573) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4971) := by
    have ha : (tripleCharges (sourceA2573 + difference 2 1) (sourceB2573 + difference 1 2) sourceC2573) = raw35562 := by
      apply Matrix.ext; unfold tripleCharges sourceA2573 sourceB2573 sourceC2573 difference raw35562; decide +kernel
    rw [ha]
    exact (canonical35562 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2573 + difference 2 3) (sourceB2573 + difference 3 2) sourceC2573) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5378) := by
    have ha : (tripleCharges (sourceA2573 + difference 2 3) (sourceB2573 + difference 3 2) sourceC2573) = raw18193 := by
      apply Matrix.ext; unfold tripleCharges sourceA2573 sourceB2573 sourceC2573 difference raw18193; decide +kernel
    rw [ha]
    exact (canonical18193 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2573 + difference 2 4) (sourceB2573 + difference 4 2) sourceC2573) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5378) := by
    have ha : (tripleCharges (sourceA2573 + difference 2 4) (sourceB2573 + difference 4 2) sourceC2573) = raw35563 := by
      apply Matrix.ext; unfold tripleCharges sourceA2573 sourceB2573 sourceC2573 difference raw35563; decide +kernel
    rw [ha]
    exact (canonical35563 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2573 + difference 2 5) (sourceB2573 + difference 5 2) sourceC2573) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5386) := by
    have ha : (tripleCharges (sourceA2573 + difference 2 5) (sourceB2573 + difference 5 2) sourceC2573) = raw18494 := by
      apply Matrix.ext; unfold tripleCharges sourceA2573 sourceB2573 sourceC2573 difference raw18494; decide +kernel
    rw [ha]
    exact (canonical18494 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2573 + difference 3 0) (sourceB2573 + difference 0 3) sourceC2573) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4684) := by
    have ha : (tripleCharges (sourceA2573 + difference 3 0) (sourceB2573 + difference 0 3) sourceC2573) = raw33726 := by
      apply Matrix.ext; unfold tripleCharges sourceA2573 sourceB2573 sourceC2573 difference raw33726; decide +kernel
    rw [ha]
    exact (canonical33726 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2573 + difference 3 1) (sourceB2573 + difference 1 3) sourceC2573) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4977) := by
    have ha : (tripleCharges (sourceA2573 + difference 3 1) (sourceB2573 + difference 1 3) sourceC2573) = raw35564 := by
      apply Matrix.ext; unfold tripleCharges sourceA2573 sourceB2573 sourceC2573 difference raw35564; decide +kernel
    rw [ha]
    exact (canonical35564 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2573 + difference 3 2) (sourceB2573 + difference 2 3) sourceC2573) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5336) := by
    have ha : (tripleCharges (sourceA2573 + difference 3 2) (sourceB2573 + difference 2 3) sourceC2573) = raw35565 := by
      apply Matrix.ext; unfold tripleCharges sourceA2573 sourceB2573 sourceC2573 difference raw35565; decide +kernel
    rw [ha]
    exact (canonical35565 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2573 + difference 3 4) (sourceB2573 + difference 4 3) sourceC2573) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5355) := by
    have ha : (tripleCharges (sourceA2573 + difference 3 4) (sourceB2573 + difference 4 3) sourceC2573) = raw35566 := by
      apply Matrix.ext; unfold tripleCharges sourceA2573 sourceB2573 sourceC2573 difference raw35566; decide +kernel
    rw [ha]
    exact (canonical35566 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2573 + difference 3 5) (sourceB2573 + difference 5 3) sourceC2573) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5388) := by
    have ha : (tripleCharges (sourceA2573 + difference 3 5) (sourceB2573 + difference 5 3) sourceC2573) = raw18498 := by
      apply Matrix.ext; unfold tripleCharges sourceA2573 sourceB2573 sourceC2573 difference raw18498; decide +kernel
    rw [ha]
    exact (canonical18498 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2573 + difference 4 0) (sourceB2573 + difference 0 4) sourceC2573) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4684) := by
    have ha : (tripleCharges (sourceA2573 + difference 4 0) (sourceB2573 + difference 0 4) sourceC2573) = raw33730 := by
      apply Matrix.ext; unfold tripleCharges sourceA2573 sourceB2573 sourceC2573 difference raw33730; decide +kernel
    rw [ha]
    exact (canonical33730 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2573 + difference 4 1) (sourceB2573 + difference 1 4) sourceC2573) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4977) := by
    have ha : (tripleCharges (sourceA2573 + difference 4 1) (sourceB2573 + difference 1 4) sourceC2573) = raw35567 := by
      apply Matrix.ext; unfold tripleCharges sourceA2573 sourceB2573 sourceC2573 difference raw35567; decide +kernel
    rw [ha]
    exact (canonical35567 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2573 + difference 4 2) (sourceB2573 + difference 2 4) sourceC2573) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5336) := by
    have ha : (tripleCharges (sourceA2573 + difference 4 2) (sourceB2573 + difference 2 4) sourceC2573) = raw35568 := by
      apply Matrix.ext; unfold tripleCharges sourceA2573 sourceB2573 sourceC2573 difference raw35568; decide +kernel
    rw [ha]
    exact (canonical35568 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2573 + difference 4 3) (sourceB2573 + difference 3 4) sourceC2573) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5355) := by
    have ha : (tripleCharges (sourceA2573 + difference 4 3) (sourceB2573 + difference 3 4) sourceC2573) = raw18203 := by
      apply Matrix.ext; unfold tripleCharges sourceA2573 sourceB2573 sourceC2573 difference raw18203; decide +kernel
    rw [ha]
    exact (canonical18203 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2573 + difference 4 5) (sourceB2573 + difference 5 4) sourceC2573) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5388) := by
    have ha : (tripleCharges (sourceA2573 + difference 4 5) (sourceB2573 + difference 5 4) sourceC2573) = raw18503 := by
      apply Matrix.ext; unfold tripleCharges sourceA2573 sourceB2573 sourceC2573 difference raw18503; decide +kernel
    rw [ha]
    exact (canonical18503 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2573 + difference 5 0) (sourceB2573 + difference 0 5) sourceC2573) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4678) := by
    have ha : (tripleCharges (sourceA2573 + difference 5 0) (sourceB2573 + difference 0 5) sourceC2573) = raw33733 := by
      apply Matrix.ext; unfold tripleCharges sourceA2573 sourceB2573 sourceC2573 difference raw33733; decide +kernel
    rw [ha]
    exact (canonical33733 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2573 + difference 5 1) (sourceB2573 + difference 1 5) sourceC2573) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4770) := by
    have ha : (tripleCharges (sourceA2573 + difference 5 1) (sourceB2573 + difference 1 5) sourceC2573) = raw35569 := by
      apply Matrix.ext; unfold tripleCharges sourceA2573 sourceB2573 sourceC2573 difference raw35569; decide +kernel
    rw [ha]
    exact (canonical35569 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2573 + difference 5 2) (sourceB2573 + difference 2 5) sourceC2573) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4766) := by
    have ha : (tripleCharges (sourceA2573 + difference 5 2) (sourceB2573 + difference 2 5) sourceC2573) = raw35570 := by
      apply Matrix.ext; unfold tripleCharges sourceA2573 sourceB2573 sourceC2573 difference raw35570; decide +kernel
    rw [ha]
    exact (canonical35570 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2573 + difference 5 3) (sourceB2573 + difference 3 5) sourceC2573) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4810) := by
    have ha : (tripleCharges (sourceA2573 + difference 5 3) (sourceB2573 + difference 3 5) sourceC2573) = raw18208 := by
      apply Matrix.ext; unfold tripleCharges sourceA2573 sourceB2573 sourceC2573 difference raw18208; decide +kernel
    rw [ha]
    exact (canonical18208 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2573 + difference 5 4) (sourceB2573 + difference 4 5) sourceC2573) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4810) := by
    have ha : (tripleCharges (sourceA2573 + difference 5 4) (sourceB2573 + difference 4 5) sourceC2573) = raw35571 := by
      apply Matrix.ext; unfold tripleCharges sourceA2573 sourceB2573 sourceC2573 difference raw35571; decide +kernel
    rw [ha]
    exact (canonical35571 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2573 sourceB2573 sourceC2573
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2573, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic128
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reindexCheck2060 : Integer.Sparse.reindex keyMap MixedData.row2060 = numericRow2060 := by decide +kernel

theorem numericCheck2060 (x : Master → ℝ) : Integer.Sparse.eval numericRow2060 x =
    (5184 : ℝ) * reducedSource2060 x := by
  norm_num [numericRow2060, reducedSource2060, Integer.Sparse.eval, Sparse.eval, nodeValue4676, nodeValue4678, nodeValue4684, nodeValue4766, nodeValue4770, nodeValue4810, nodeValue4865, nodeValue4971, nodeValue4977, nodeValue5172, nodeValue5336, nodeValue5355, nodeValue5378, nodeValue5386, nodeValue5388, nodeValue5400, nodeValue5417, nodeValue5432, nodeValue5435, nodeValue5440, nodeValue5450]
  ring

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Rows128
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero2060 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource2060 (mixedVector B) = 0 := by
  have h4676 : mixedVector B (Sum.inr 4676) = Sparse.eval nodeValue4676 (mixedVector B) := by
    change mixedMoment B node4676 node4676Labels = _
    exact sound4676 B hB hF
  have h4678 : mixedVector B (Sum.inr 4678) = Sparse.eval nodeValue4678 (mixedVector B) := by
    change mixedMoment B node4678 node4678Labels = _
    exact sound4678 B hB hF
  have h4684 : mixedVector B (Sum.inr 4684) = Sparse.eval nodeValue4684 (mixedVector B) := by
    change mixedMoment B node4684 node4684Labels = _
    exact sound4684 B hB hF
  have h4766 : mixedVector B (Sum.inr 4766) = Sparse.eval nodeValue4766 (mixedVector B) := by
    change mixedMoment B node4766 node4766Labels = _
    exact sound4766 B hB hF
  have h4770 : mixedVector B (Sum.inr 4770) = Sparse.eval nodeValue4770 (mixedVector B) := by
    change mixedMoment B node4770 node4770Labels = _
    exact sound4770 B hB hF
  have h4810 : mixedVector B (Sum.inr 4810) = Sparse.eval nodeValue4810 (mixedVector B) := by
    change mixedMoment B node4810 node4810Labels = _
    exact sound4810 B hB hF
  have h4865 : mixedVector B (Sum.inr 4865) = Sparse.eval nodeValue4865 (mixedVector B) := by
    change mixedMoment B node4865 node4865Labels = _
    exact sound4865 B hB hF
  have h4971 : mixedVector B (Sum.inr 4971) = Sparse.eval nodeValue4971 (mixedVector B) := by
    change mixedMoment B node4971 node4971Labels = _
    exact sound4971 B hB hF
  have h4977 : mixedVector B (Sum.inr 4977) = Sparse.eval nodeValue4977 (mixedVector B) := by
    change mixedMoment B node4977 node4977Labels = _
    exact sound4977 B hB hF
  have h5172 : mixedVector B (Sum.inr 5172) = Sparse.eval nodeValue5172 (mixedVector B) := by
    change mixedMoment B node5172 node5172Labels = _
    exact sound5172_e B hB hF
  have h5336 : mixedVector B (Sum.inr 5336) = Sparse.eval nodeValue5336 (mixedVector B) := by
    change mixedMoment B node5336 node5336Labels = _
    exact sound5336 B hB hF
  have h5355 : mixedVector B (Sum.inr 5355) = Sparse.eval nodeValue5355 (mixedVector B) := by
    change mixedMoment B node5355 node5355Labels = _
    exact sound5355 B hB hF
  have h5378 : mixedVector B (Sum.inr 5378) = Sparse.eval nodeValue5378 (mixedVector B) := by
    change mixedMoment B node5378 node5378Labels = _
    exact sound5378 B hB hF
  have h5386 : mixedVector B (Sum.inr 5386) = Sparse.eval nodeValue5386 (mixedVector B) := by
    change mixedMoment B node5386 node5386Labels = _
    exact sound5386_e B hB hF
  have h5388 : mixedVector B (Sum.inr 5388) = Sparse.eval nodeValue5388 (mixedVector B) := by
    change mixedMoment B node5388 node5388Labels = _
    exact sound5388_e B hB hF
  have h5400 : mixedVector B (Sum.inr 5400) = Sparse.eval nodeValue5400 (mixedVector B) := by
    change mixedMoment B node5400 node5400Labels = _
    exact sound5400 B hB hF
  have h5417 : mixedVector B (Sum.inr 5417) = Sparse.eval nodeValue5417 (mixedVector B) := by
    change mixedMoment B node5417 node5417Labels = _
    exact sound5417_e B hB hF
  have h5432 : mixedVector B (Sum.inr 5432) = Sparse.eval nodeValue5432 (mixedVector B) := by
    change mixedMoment B node5432 node5432Labels = _
    exact sound5432 B hB hF
  have h5435 : mixedVector B (Sum.inr 5435) = Sparse.eval nodeValue5435 (mixedVector B) := by
    change mixedMoment B node5435 node5435Labels = _
    exact sound5435_e B hB hF
  have h5440 : mixedVector B (Sum.inr 5440) = Sparse.eval nodeValue5440 (mixedVector B) := by
    change mixedMoment B node5440 node5440Labels = _
    exact sound5440 B hB hF
  have h5450 : mixedVector B (Sum.inr 5450) = Sparse.eval nodeValue5450 (mixedVector B) := by
    change mixedMoment B node5450 node5450Labels = _
    exact sound5450_e B hB hF
  simpa only [sourceForm2573, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4676, h4678, h4684, h4766, h4770, h4810, h4865, h4971, h4977, h5172, h5336, h5355, h5378, h5386, h5388, h5400, h5417, h5432, h5435, h5440, h5450, reducedSource2060] using sourceEq2573 B hB

theorem rowSound2060_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row2060 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck2060, numericCheck2060, reducedZero2060 B hB hF, mul_zero]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedSourceBridge.rowSound2060_e_oai := @OAI.MUB6.Certificate.MixedSourceBridge.rowSound2060_e_oai
