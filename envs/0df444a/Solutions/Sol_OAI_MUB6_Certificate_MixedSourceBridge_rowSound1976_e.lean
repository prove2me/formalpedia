-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedSourceBridge.rowSound1976_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-08T22:31:39.229449+00:00
-- url     : https://prove2.me/submissions/d4405e40-47ec-4b5a-be65-1b9596c64bca

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E070
import Definitions.Def_OAIQ106E086
import Definitions.Def_OAIQ106E091
import Definitions.Def_OAIQ106E092
import Definitions.Def_OAIQ106E093
import Definitions.Def_OAIQ106E094
import Definitions.Def_OAIQ106E194
import Definitions.Def_OAIQ106E195
import Definitions.Def_OAIQ106E107
import Definitions.Def_OAIQ106E118
import Definitions.Def_OAIQ106E119
import Definitions.Def_OAIQ106E121
import Definitions.Def_OAIQ106E126
import Definitions.Def_OAIQ106E140
import Definitions.Def_OAIQ106E147
import Definitions.Def_OAIQ106E170
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound5387_e
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

theorem canonical1617 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1617 raw1617Labels = mixedMoment B node4720 node4720Labels := by
  calc
    mixedMoment B raw1617 raw1617Labels = mixedMoment B raw1617step0 raw1617step0Labels := by
      have ha : raw1617step0 = (fun i j => raw1617 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1617step0 raw1617; decide +kernel
      have hl : raw1617step0Labels = raw1617Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1617 raw1617Labels permutation152 permutation4
    mixedMoment B raw1617step0 raw1617step0Labels = mixedMoment B raw1617step1 raw1617step1Labels := by
      have ha : raw1617step1 = raw1617step0 := by apply Matrix.ext; unfold raw1617step1 raw1617step0; decide +kernel
      have hl : raw1617step0Labels = labelEmbedding7 ∘ raw1617step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1617step0 raw1617step0Labels raw1617step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4720 node4720Labels := by rfl

theorem canonical1618 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1618 raw1618Labels = mixedMoment B node1874 node1874Labels := by
  calc
    mixedMoment B raw1618 raw1618Labels = mixedMoment B raw1618step0 raw1618step0Labels := by
      have ha : raw1618step0 = (fun i j => raw1618 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1618step0 raw1618; decide +kernel
      have hl : raw1618step0Labels = raw1618Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1618 raw1618Labels permutation152 permutation4
    _ = mixedMoment B node1874 node1874Labels := by rfl

theorem canonical1619 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1619 raw1619Labels = mixedMoment B node1896 node1896Labels := by
  calc
    mixedMoment B raw1619 raw1619Labels = mixedMoment B raw1619step0 raw1619step0Labels := by
      have ha : raw1619step0 = (fun i j => raw1619 (permutation160 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1619step0 raw1619; decide +kernel
      have hl : raw1619step0Labels = raw1619Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1619 raw1619Labels permutation160 permutation6
    mixedMoment B raw1619step0 raw1619step0Labels = mixedMoment B raw1619step1 raw1619step1Labels := by
      have ha : raw1619step1 = -raw1619step0 := by apply Matrix.ext; change ∀ i j, raw1619step1 i j = -(raw1619step0 i j); unfold raw1619step1 raw1619step0; decide +kernel
      have hl : raw1619step1Labels = raw1619step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1619step1 raw1619step1Labels = mixedMoment B raw1619step2 raw1619step2Labels := by
      have ha : raw1619step2 = raw1619step1 := by apply Matrix.ext; unfold raw1619step2 raw1619step1; decide +kernel
      have hl : raw1619step1Labels = labelEmbedding1 ∘ raw1619step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1619step1 raw1619step1Labels raw1619step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1896 node1896Labels := by rfl

theorem canonical1623 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1623 raw1623Labels = mixedMoment B node4722 node4722Labels := by
  calc
    mixedMoment B raw1623 raw1623Labels = mixedMoment B raw1623step0 raw1623step0Labels := by
      have ha : raw1623step0 = (fun i j => raw1623 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1623step0 raw1623; decide +kernel
      have hl : raw1623step0Labels = raw1623Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1623 raw1623Labels permutation152 permutation4
    mixedMoment B raw1623step0 raw1623step0Labels = mixedMoment B raw1623step1 raw1623step1Labels := by
      have ha : raw1623step1 = raw1623step0 := by apply Matrix.ext; unfold raw1623step1 raw1623step0; decide +kernel
      have hl : raw1623step0Labels = labelEmbedding7 ∘ raw1623step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1623step0 raw1623step0Labels raw1623step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4722 node4722Labels := by rfl

theorem canonical1624 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1624 raw1624Labels = mixedMoment B node1876 node1876Labels := by
  calc
    mixedMoment B raw1624 raw1624Labels = mixedMoment B raw1624step0 raw1624step0Labels := by
      have ha : raw1624step0 = (fun i j => raw1624 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1624step0 raw1624; decide +kernel
      have hl : raw1624step0Labels = raw1624Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1624 raw1624Labels permutation152 permutation4
    _ = mixedMoment B node1876 node1876Labels := by rfl

theorem canonical1625 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1625 raw1625Labels = mixedMoment B node1906 node1906Labels := by
  calc
    mixedMoment B raw1625 raw1625Labels = mixedMoment B raw1625step0 raw1625step0Labels := by
      have ha : raw1625step0 = (fun i j => raw1625 (permutation158 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1625step0 raw1625; decide +kernel
      have hl : raw1625step0Labels = raw1625Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1625 raw1625Labels permutation158 permutation6
    mixedMoment B raw1625step0 raw1625step0Labels = mixedMoment B raw1625step1 raw1625step1Labels := by
      have ha : raw1625step1 = -raw1625step0 := by apply Matrix.ext; change ∀ i j, raw1625step1 i j = -(raw1625step0 i j); unfold raw1625step1 raw1625step0; decide +kernel
      have hl : raw1625step1Labels = raw1625step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1625step1 raw1625step1Labels = mixedMoment B raw1625step2 raw1625step2Labels := by
      have ha : raw1625step2 = raw1625step1 := by apply Matrix.ext; unfold raw1625step2 raw1625step1; decide +kernel
      have hl : raw1625step1Labels = labelEmbedding1 ∘ raw1625step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1625step1 raw1625step1Labels raw1625step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1906 node1906Labels := by rfl

theorem canonical1647 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1647 raw1647Labels = mixedMoment B node4731 node4731Labels := by
  calc
    mixedMoment B raw1647 raw1647Labels = mixedMoment B raw1647step0 raw1647step0Labels := by
      have ha : raw1647step0 = (fun i j => raw1647 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1647step0 raw1647; decide +kernel
      have hl : raw1647step0Labels = raw1647Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1647 raw1647Labels permutation152 permutation4
    mixedMoment B raw1647step0 raw1647step0Labels = mixedMoment B raw1647step1 raw1647step1Labels := by
      have ha : raw1647step1 = raw1647step0 := by apply Matrix.ext; unfold raw1647step1 raw1647step0; decide +kernel
      have hl : raw1647step0Labels = labelEmbedding7 ∘ raw1647step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1647step0 raw1647step0Labels raw1647step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4731 node4731Labels := by rfl

theorem canonical1648 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1648 raw1648Labels = mixedMoment B node1900 node1900Labels := by
  calc
    mixedMoment B raw1648 raw1648Labels = mixedMoment B raw1648step0 raw1648step0Labels := by
      have ha : raw1648step0 = (fun i j => raw1648 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1648step0 raw1648; decide +kernel
      have hl : raw1648step0Labels = raw1648Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1648 raw1648Labels permutation152 permutation4
    _ = mixedMoment B node1900 node1900Labels := by rfl

theorem canonical1649 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1649 raw1649Labels = mixedMoment B node1921 node1921Labels := by
  calc
    mixedMoment B raw1649 raw1649Labels = mixedMoment B raw1649step0 raw1649step0Labels := by
      have ha : raw1649step0 = (fun i j => raw1649 (permutation164 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1649step0 raw1649; decide +kernel
      have hl : raw1649step0Labels = raw1649Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1649 raw1649Labels permutation164 permutation6
    mixedMoment B raw1649step0 raw1649step0Labels = mixedMoment B raw1649step1 raw1649step1Labels := by
      have ha : raw1649step1 = -raw1649step0 := by apply Matrix.ext; change ∀ i j, raw1649step1 i j = -(raw1649step0 i j); unfold raw1649step1 raw1649step0; decide +kernel
      have hl : raw1649step1Labels = raw1649step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1649step1 raw1649step1Labels = mixedMoment B raw1649step2 raw1649step2Labels := by
      have ha : raw1649step2 = raw1649step1 := by apply Matrix.ext; unfold raw1649step2 raw1649step1; decide +kernel
      have hl : raw1649step1Labels = labelEmbedding1 ∘ raw1649step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1649step1 raw1649step1Labels raw1649step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1921 node1921Labels := by rfl

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

theorem canonical1728 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1728 raw1728Labels = mixedMoment B node4800 node4800Labels := by
  calc
    mixedMoment B raw1728 raw1728Labels = mixedMoment B raw1728step0 raw1728step0Labels := by
      have ha : raw1728step0 = (fun i j => raw1728 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1728step0 raw1728; decide +kernel
      have hl : raw1728step0Labels = raw1728Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1728 raw1728Labels permutation32 permutation4
    mixedMoment B raw1728step0 raw1728step0Labels = mixedMoment B raw1728step1 raw1728step1Labels := by
      have ha : raw1728step1 = raw1728step0 := by apply Matrix.ext; unfold raw1728step1 raw1728step0; decide +kernel
      have hl : raw1728step0Labels = labelEmbedding7 ∘ raw1728step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1728step0 raw1728step0Labels raw1728step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4800 node4800Labels := by rfl

theorem canonical1729 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1729 raw1729Labels = mixedMoment B node2018 node2018Labels := by
  calc
    mixedMoment B raw1729 raw1729Labels = mixedMoment B raw1729step0 raw1729step0Labels := by
      have ha : raw1729step0 = (fun i j => raw1729 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1729step0 raw1729; decide +kernel
      have hl : raw1729step0Labels = raw1729Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1729 raw1729Labels permutation32 permutation4
    _ = mixedMoment B node2018 node2018Labels := by rfl

theorem canonical1730 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1730 raw1730Labels = mixedMoment B node2018 node2018Labels := by
  calc
    mixedMoment B raw1730 raw1730Labels = mixedMoment B raw1730step0 raw1730step0Labels := by
      have ha : raw1730step0 = (fun i j => raw1730 (permutation143 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1730step0 raw1730; decide +kernel
      have hl : raw1730step0Labels = raw1730Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1730 raw1730Labels permutation143 permutation6
    mixedMoment B raw1730step0 raw1730step0Labels = mixedMoment B raw1730step1 raw1730step1Labels := by
      have ha : raw1730step1 = raw1730step0 := by apply Matrix.ext; unfold raw1730step1 raw1730step0; decide +kernel
      have hl : raw1730step0Labels = labelEmbedding1 ∘ raw1730step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1730step0 raw1730step0Labels raw1730step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2018 node2018Labels := by rfl

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

theorem canonical1758 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1758 raw1758Labels = mixedMoment B node4828 node4828Labels := by
  calc
    mixedMoment B raw1758 raw1758Labels = mixedMoment B raw1758step0 raw1758step0Labels := by
      have ha : raw1758step0 = (fun i j => raw1758 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1758step0 raw1758; decide +kernel
      have hl : raw1758step0Labels = raw1758Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1758 raw1758Labels permutation32 permutation4
    mixedMoment B raw1758step0 raw1758step0Labels = mixedMoment B raw1758step1 raw1758step1Labels := by
      have ha : raw1758step1 = raw1758step0 := by apply Matrix.ext; unfold raw1758step1 raw1758step0; decide +kernel
      have hl : raw1758step0Labels = labelEmbedding7 ∘ raw1758step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1758step0 raw1758step0Labels raw1758step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4828 node4828Labels := by rfl

theorem canonical1759 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1759 raw1759Labels = mixedMoment B node2048 node2048Labels := by
  calc
    mixedMoment B raw1759 raw1759Labels = mixedMoment B raw1759step0 raw1759step0Labels := by
      have ha : raw1759step0 = (fun i j => raw1759 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1759step0 raw1759; decide +kernel
      have hl : raw1759step0Labels = raw1759Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1759 raw1759Labels permutation32 permutation4
    _ = mixedMoment B node2048 node2048Labels := by rfl

theorem canonical1760 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1760 raw1760Labels = mixedMoment B node2082 node2082Labels := by
  calc
    mixedMoment B raw1760 raw1760Labels = mixedMoment B raw1760step0 raw1760step0Labels := by
      have ha : raw1760step0 = (fun i j => raw1760 (permutation38 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1760step0 raw1760; decide +kernel
      have hl : raw1760step0Labels = raw1760Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1760 raw1760Labels permutation38 permutation6
    mixedMoment B raw1760step0 raw1760step0Labels = mixedMoment B raw1760step1 raw1760step1Labels := by
      have ha : raw1760step1 = -raw1760step0 := by apply Matrix.ext; change ∀ i j, raw1760step1 i j = -(raw1760step0 i j); unfold raw1760step1 raw1760step0; decide +kernel
      have hl : raw1760step1Labels = raw1760step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1760step1 raw1760step1Labels = mixedMoment B raw1760step2 raw1760step2Labels := by
      have ha : raw1760step2 = raw1760step1 := by apply Matrix.ext; unfold raw1760step2 raw1760step1; decide +kernel
      have hl : raw1760step1Labels = labelEmbedding1 ∘ raw1760step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1760step1 raw1760step1Labels raw1760step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2082 node2082Labels := by rfl

theorem canonical1788 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1788 raw1788Labels = mixedMoment B node4864 node4864Labels := by
  calc
    mixedMoment B raw1788 raw1788Labels = mixedMoment B raw1788step0 raw1788step0Labels := by
      have ha : raw1788step0 = (fun i j => raw1788 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1788step0 raw1788; decide +kernel
      have hl : raw1788step0Labels = raw1788Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1788 raw1788Labels permutation152 permutation4
    mixedMoment B raw1788step0 raw1788step0Labels = mixedMoment B raw1788step1 raw1788step1Labels := by
      have ha : raw1788step1 = raw1788step0 := by apply Matrix.ext; unfold raw1788step1 raw1788step0; decide +kernel
      have hl : raw1788step0Labels = labelEmbedding7 ∘ raw1788step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1788step0 raw1788step0Labels raw1788step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4864 node4864Labels := by rfl

theorem canonical1789 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1789 raw1789Labels = mixedMoment B node2105 node2105Labels := by
  calc
    mixedMoment B raw1789 raw1789Labels = mixedMoment B raw1789step0 raw1789step0Labels := by
      have ha : raw1789step0 = (fun i j => raw1789 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1789step0 raw1789; decide +kernel
      have hl : raw1789step0Labels = raw1789Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1789 raw1789Labels permutation152 permutation4
    _ = mixedMoment B node2105 node2105Labels := by rfl

theorem canonical1790 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1790 raw1790Labels = mixedMoment B node2241 node2241Labels := by
  calc
    mixedMoment B raw1790 raw1790Labels = mixedMoment B raw1790step0 raw1790step0Labels := by
      have ha : raw1790step0 = (fun i j => raw1790 (permutation182 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1790step0 raw1790; decide +kernel
      have hl : raw1790step0Labels = raw1790Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1790 raw1790Labels permutation182 permutation6
    mixedMoment B raw1790step0 raw1790step0Labels = mixedMoment B raw1790step1 raw1790step1Labels := by
      have ha : raw1790step1 = -raw1790step0 := by apply Matrix.ext; change ∀ i j, raw1790step1 i j = -(raw1790step0 i j); unfold raw1790step1 raw1790step0; decide +kernel
      have hl : raw1790step1Labels = raw1790step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1790step1 raw1790step1Labels = mixedMoment B raw1790step2 raw1790step2Labels := by
      have ha : raw1790step2 = raw1790step1 := by apply Matrix.ext; unfold raw1790step2 raw1790step1; decide +kernel
      have hl : raw1790step1Labels = labelEmbedding1 ∘ raw1790step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1790step1 raw1790step1Labels raw1790step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2241 node2241Labels := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical142
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical18187 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18187 raw18187Labels = mixedMoment B node4810 node4810Labels := by
  calc
    mixedMoment B raw18187 raw18187Labels = mixedMoment B raw18187step0 raw18187step0Labels := by
      have hz : ∀ j, raw18187 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18187step0 = (fun i j => raw18187 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18187step0 raw18187; decide +kernel
      have hl : raw18187step0Labels = raw18187Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18187 raw18187Labels permutation346 hz
    mixedMoment B raw18187step0 raw18187step0Labels = mixedMoment B raw18187step1 raw18187step1Labels := by
      have ha : raw18187step1 = (fun i j => raw18187step0 (permutation40 i) (permutation5 j)) := by apply Matrix.ext; unfold raw18187step1 raw18187step0; decide +kernel
      have hl : raw18187step1Labels = raw18187step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18187step0 raw18187step0Labels permutation40 permutation5
    mixedMoment B raw18187step1 raw18187step1Labels = mixedMoment B raw18187step2 raw18187step2Labels := by
      have ha : raw18187step2 = -raw18187step1 := by apply Matrix.ext; change ∀ i j, raw18187step2 i j = -(raw18187step1 i j); unfold raw18187step2 raw18187step1; decide +kernel
      have hl : raw18187step2Labels = raw18187step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18187step2 raw18187step2Labels = mixedMoment B raw18187step3 raw18187step3Labels := by
      have ha : raw18187step3 = raw18187step2 := by apply Matrix.ext; unfold raw18187step3 raw18187step2; decide +kernel
      have hl : raw18187step2Labels = labelEmbedding8 ∘ raw18187step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18187step2 raw18187step2Labels raw18187step3Labels labelEmbedding8 hl
    _ = mixedMoment B node4810 node4810Labels := by rfl

theorem canonical18192 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18192 raw18192Labels = mixedMoment B node4798 node4798Labels := by
  calc
    mixedMoment B raw18192 raw18192Labels = mixedMoment B raw18192step0 raw18192step0Labels := by
      have ha : raw18192step0 = (fun i j => raw18192 (permutation212 i) (permutation5 j)) := by apply Matrix.ext; unfold raw18192step0 raw18192; decide +kernel
      have hl : raw18192step0Labels = raw18192Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18192 raw18192Labels permutation212 permutation5
    mixedMoment B raw18192step0 raw18192step0Labels = mixedMoment B raw18192step1 raw18192step1Labels := by
      have ha : raw18192step1 = -raw18192step0 := by apply Matrix.ext; change ∀ i j, raw18192step1 i j = -(raw18192step0 i j); unfold raw18192step1 raw18192step0; decide +kernel
      have hl : raw18192step1Labels = raw18192step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18192step1 raw18192step1Labels = mixedMoment B raw18192step2 raw18192step2Labels := by
      have ha : raw18192step2 = raw18192step1 := by apply Matrix.ext; unfold raw18192step2 raw18192step1; decide +kernel
      have hl : raw18192step1Labels = labelEmbedding8 ∘ raw18192step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18192step1 raw18192step1Labels raw18192step2Labels labelEmbedding8 hl
    _ = mixedMoment B node4798 node4798Labels := by rfl

theorem canonical18198 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18198 raw18198Labels = mixedMoment B node5387 node5387Labels := by
  calc
    mixedMoment B raw18198 raw18198Labels = mixedMoment B raw18198step0 raw18198step0Labels := by
      have hz : ∀ j, raw18198 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18198step0 = (fun i j => raw18198 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18198step0 raw18198; decide +kernel
      have hl : raw18198step0Labels = raw18198Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18198 raw18198Labels permutation346 hz
    mixedMoment B raw18198step0 raw18198step0Labels = mixedMoment B raw18198step1 raw18198step1Labels := by
      have ha : raw18198step1 = (fun i j => raw18198step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18198step1 raw18198step0; decide +kernel
      have hl : raw18198step1Labels = raw18198step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18198step0 raw18198step0Labels permutation32 permutation3
    mixedMoment B raw18198step1 raw18198step1Labels = mixedMoment B raw18198step2 raw18198step2Labels := by
      have ha : raw18198step2 = raw18198step1 := by apply Matrix.ext; unfold raw18198step2 raw18198step1; decide +kernel
      have hl : raw18198step1Labels = labelEmbedding6 ∘ raw18198step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18198step1 raw18198step1Labels raw18198step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5387 node5387Labels := by rfl

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

theorem canonical18202 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18202 raw18202Labels = mixedMoment B node4828 node4828Labels := by
  calc
    mixedMoment B raw18202 raw18202Labels = mixedMoment B raw18202step0 raw18202step0Labels := by
      have hz : ∀ j, raw18202 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18202step0 = (fun i j => raw18202 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18202step0 raw18202; decide +kernel
      have hl : raw18202step0Labels = raw18202Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18202 raw18202Labels permutation346 hz
    mixedMoment B raw18202step0 raw18202step0Labels = mixedMoment B raw18202step1 raw18202step1Labels := by
      have ha : raw18202step1 = (fun i j => raw18202step0 (permutation38 i) (permutation5 j)) := by apply Matrix.ext; unfold raw18202step1 raw18202step0; decide +kernel
      have hl : raw18202step1Labels = raw18202step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18202step0 raw18202step0Labels permutation38 permutation5
    mixedMoment B raw18202step1 raw18202step1Labels = mixedMoment B raw18202step2 raw18202step2Labels := by
      have ha : raw18202step2 = -raw18202step1 := by apply Matrix.ext; change ∀ i j, raw18202step2 i j = -(raw18202step1 i j); unfold raw18202step2 raw18202step1; decide +kernel
      have hl : raw18202step2Labels = raw18202step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18202step2 raw18202step2Labels = mixedMoment B raw18202step3 raw18202step3Labels := by
      have ha : raw18202step3 = raw18202step2 := by apply Matrix.ext; unfold raw18202step3 raw18202step2; decide +kernel
      have hl : raw18202step2Labels = labelEmbedding8 ∘ raw18202step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18202step2 raw18202step2Labels raw18202step3Labels labelEmbedding8 hl
    _ = mixedMoment B node4828 node4828Labels := by rfl

theorem canonical18207 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18207 raw18207Labels = mixedMoment B node4800 node4800Labels := by
  calc
    mixedMoment B raw18207 raw18207Labels = mixedMoment B raw18207step0 raw18207step0Labels := by
      have hz : ∀ j, raw18207 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18207step0 = (fun i j => raw18207 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18207step0 raw18207; decide +kernel
      have hl : raw18207step0Labels = raw18207Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18207 raw18207Labels permutation346 hz
    mixedMoment B raw18207step0 raw18207step0Labels = mixedMoment B raw18207step1 raw18207step1Labels := by
      have ha : raw18207step1 = (fun i j => raw18207step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18207step1 raw18207step0; decide +kernel
      have hl : raw18207step1Labels = raw18207step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18207step0 raw18207step0Labels permutation151 permutation3
    mixedMoment B raw18207step1 raw18207step1Labels = mixedMoment B raw18207step2 raw18207step2Labels := by
      have ha : raw18207step2 = -raw18207step1 := by apply Matrix.ext; change ∀ i j, raw18207step2 i j = -(raw18207step1 i j); unfold raw18207step2 raw18207step1; decide +kernel
      have hl : raw18207step2Labels = raw18207step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18207step2 raw18207step2Labels = mixedMoment B raw18207step3 raw18207step3Labels := by
      have ha : raw18207step3 = raw18207step2 := by apply Matrix.ext; unfold raw18207step3 raw18207step2; decide +kernel
      have hl : raw18207step2Labels = labelEmbedding6 ∘ raw18207step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18207step2 raw18207step2Labels raw18207step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4800 node4800Labels := by rfl

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

theorem canonical18489 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18489 raw18489Labels = mixedMoment B node4889 node4889Labels := by
  calc
    mixedMoment B raw18489 raw18489Labels = mixedMoment B raw18489step0 raw18489step0Labels := by
      have hz : ∀ j, raw18489 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18489step0 = (fun i j => raw18489 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18489step0 raw18489; decide +kernel
      have hl : raw18489step0Labels = raw18489Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18489 raw18489Labels permutation346 hz
    mixedMoment B raw18489step0 raw18489step0Labels = mixedMoment B raw18489step1 raw18489step1Labels := by
      have ha : raw18489step1 = (fun i j => raw18489step0 (permutation41 i) (permutation5 j)) := by apply Matrix.ext; unfold raw18489step1 raw18489step0; decide +kernel
      have hl : raw18489step1Labels = raw18489step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18489step0 raw18489step0Labels permutation41 permutation5
    mixedMoment B raw18489step1 raw18489step1Labels = mixedMoment B raw18489step2 raw18489step2Labels := by
      have ha : raw18489step2 = -raw18489step1 := by apply Matrix.ext; change ∀ i j, raw18489step2 i j = -(raw18489step1 i j); unfold raw18489step2 raw18489step1; decide +kernel
      have hl : raw18489step2Labels = raw18489step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18489step2 raw18489step2Labels = mixedMoment B raw18489step3 raw18489step3Labels := by
      have ha : raw18489step3 = raw18489step2 := by apply Matrix.ext; unfold raw18489step3 raw18489step2; decide +kernel
      have hl : raw18489step2Labels = labelEmbedding8 ∘ raw18489step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18489step2 raw18489step2Labels raw18489step3Labels labelEmbedding8 hl
    _ = mixedMoment B node4889 node4889Labels := by rfl

theorem canonical18493 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18493 raw18493Labels = mixedMoment B node4864 node4864Labels := by
  calc
    mixedMoment B raw18493 raw18493Labels = mixedMoment B raw18493step0 raw18493step0Labels := by
      have ha : raw18493step0 = (fun i j => raw18493 (permutation160 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18493step0 raw18493; decide +kernel
      have hl : raw18493step0Labels = raw18493Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18493 raw18493Labels permutation160 permutation3
    mixedMoment B raw18493step0 raw18493step0Labels = mixedMoment B raw18493step1 raw18493step1Labels := by
      have ha : raw18493step1 = raw18493step0 := by apply Matrix.ext; unfold raw18493step1 raw18493step0; decide +kernel
      have hl : raw18493step0Labels = labelEmbedding6 ∘ raw18493step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18493step0 raw18493step0Labels raw18493step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4864 node4864Labels := by rfl

theorem canonical18497 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18497 raw18497Labels = mixedMoment B node4866 node4866Labels := by
  calc
    mixedMoment B raw18497 raw18497Labels = mixedMoment B raw18497step0 raw18497step0Labels := by
      have hz : ∀ j, raw18497 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18497step0 = (fun i j => raw18497 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18497step0 raw18497; decide +kernel
      have hl : raw18497step0Labels = raw18497Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18497 raw18497Labels permutation346 hz
    mixedMoment B raw18497step0 raw18497step0Labels = mixedMoment B raw18497step1 raw18497step1Labels := by
      have ha : raw18497step1 = (fun i j => raw18497step0 (permutation35 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18497step1 raw18497step0; decide +kernel
      have hl : raw18497step1Labels = raw18497step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18497step0 raw18497step0Labels permutation35 permutation3
    mixedMoment B raw18497step1 raw18497step1Labels = mixedMoment B raw18497step2 raw18497step2Labels := by
      have ha : raw18497step2 = raw18497step1 := by apply Matrix.ext; unfold raw18497step2 raw18497step1; decide +kernel
      have hl : raw18497step1Labels = labelEmbedding6 ∘ raw18497step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18497step1 raw18497step1Labels raw18497step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4866 node4866Labels := by rfl

theorem canonical18502 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18502 raw18502Labels = mixedMoment B node4866 node4866Labels := by
  calc
    mixedMoment B raw18502 raw18502Labels = mixedMoment B raw18502step0 raw18502step0Labels := by
      have hz : ∀ j, raw18502 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18502step0 = (fun i j => raw18502 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18502step0 raw18502; decide +kernel
      have hl : raw18502step0Labels = raw18502Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18502 raw18502Labels permutation346 hz
    mixedMoment B raw18502step0 raw18502step0Labels = mixedMoment B raw18502step1 raw18502step1Labels := by
      have ha : raw18502step1 = (fun i j => raw18502step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18502step1 raw18502step0; decide +kernel
      have hl : raw18502step1Labels = raw18502step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18502step0 raw18502step0Labels permutation33 permutation3
    mixedMoment B raw18502step1 raw18502step1Labels = mixedMoment B raw18502step2 raw18502step2Labels := by
      have ha : raw18502step2 = raw18502step1 := by apply Matrix.ext; unfold raw18502step2 raw18502step1; decide +kernel
      have hl : raw18502step1Labels = labelEmbedding6 ∘ raw18502step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18502step1 raw18502step1Labels raw18502step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4866 node4866Labels := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical19
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

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

theorem canonical33719 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33719 raw33719Labels = mixedMoment B node4255 node4255Labels := by
  calc
    mixedMoment B raw33719 raw33719Labels = mixedMoment B raw33719step0 raw33719step0Labels := by
      have hz : ∀ j, raw33719 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33719step0 = (fun i j => raw33719 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33719step0 raw33719; decide +kernel
      have hl : raw33719step0Labels = raw33719Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33719 raw33719Labels permutation346 hz
    mixedMoment B raw33719step0 raw33719step0Labels = mixedMoment B raw33719step1 raw33719step1Labels := by
      have ha : raw33719step1 = (fun i j => raw33719step0 (permutation40 i) (permutation5 j)) := by apply Matrix.ext; unfold raw33719step1 raw33719step0; decide +kernel
      have hl : raw33719step1Labels = raw33719step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33719step0 raw33719step0Labels permutation40 permutation5
    mixedMoment B raw33719step1 raw33719step1Labels = mixedMoment B raw33719step2 raw33719step2Labels := by
      have ha : raw33719step2 = -raw33719step1 := by apply Matrix.ext; change ∀ i j, raw33719step2 i j = -(raw33719step1 i j); unfold raw33719step2 raw33719step1; decide +kernel
      have hl : raw33719step2Labels = raw33719step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33719step2 raw33719step2Labels = mixedMoment B raw33719step3 raw33719step3Labels := by
      have ha : raw33719step3 = raw33719step2 := by apply Matrix.ext; unfold raw33719step3 raw33719step2; decide +kernel
      have hl : raw33719step2Labels = labelEmbedding8 ∘ raw33719step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33719step2 raw33719step2Labels raw33719step3Labels labelEmbedding8 hl
    _ = mixedMoment B node4255 node4255Labels := by rfl

theorem canonical33720 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33720 raw33720Labels = mixedMoment B node4731 node4731Labels := by
  calc
    mixedMoment B raw33720 raw33720Labels = mixedMoment B raw33720step0 raw33720step0Labels := by
      have ha : raw33720step0 = (fun i j => raw33720 (permutation184 i) (permutation5 j)) := by apply Matrix.ext; unfold raw33720step0 raw33720; decide +kernel
      have hl : raw33720step0Labels = raw33720Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33720 raw33720Labels permutation184 permutation5
    mixedMoment B raw33720step0 raw33720step0Labels = mixedMoment B raw33720step1 raw33720step1Labels := by
      have ha : raw33720step1 = -raw33720step0 := by apply Matrix.ext; change ∀ i j, raw33720step1 i j = -(raw33720step0 i j); unfold raw33720step1 raw33720step0; decide +kernel
      have hl : raw33720step1Labels = raw33720step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33720step1 raw33720step1Labels = mixedMoment B raw33720step2 raw33720step2Labels := by
      have ha : raw33720step2 = raw33720step1 := by apply Matrix.ext; unfold raw33720step2 raw33720step1; decide +kernel
      have hl : raw33720step1Labels = labelEmbedding8 ∘ raw33720step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33720step1 raw33720step1Labels raw33720step2Labels labelEmbedding8 hl
    _ = mixedMoment B node4731 node4731Labels := by rfl

theorem canonical33721 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33721 raw33721Labels = mixedMoment B node4810 node4810Labels := by
  calc
    mixedMoment B raw33721 raw33721Labels = mixedMoment B raw33721step0 raw33721step0Labels := by
      have hz : ∀ j, raw33721 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33721step0 = (fun i j => raw33721 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33721step0 raw33721; decide +kernel
      have hl : raw33721step0Labels = raw33721Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33721 raw33721Labels permutation346 hz
    mixedMoment B raw33721step0 raw33721step0Labels = mixedMoment B raw33721step1 raw33721step1Labels := by
      have ha : raw33721step1 = (fun i j => raw33721step0 (permutation46 i) (permutation5 j)) := by apply Matrix.ext; unfold raw33721step1 raw33721step0; decide +kernel
      have hl : raw33721step1Labels = raw33721step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33721step0 raw33721step0Labels permutation46 permutation5
    mixedMoment B raw33721step1 raw33721step1Labels = mixedMoment B raw33721step2 raw33721step2Labels := by
      have ha : raw33721step2 = -raw33721step1 := by apply Matrix.ext; change ∀ i j, raw33721step2 i j = -(raw33721step1 i j); unfold raw33721step2 raw33721step1; decide +kernel
      have hl : raw33721step2Labels = raw33721step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33721step2 raw33721step2Labels = mixedMoment B raw33721step3 raw33721step3Labels := by
      have ha : raw33721step3 = raw33721step2 := by apply Matrix.ext; unfold raw33721step3 raw33721step2; decide +kernel
      have hl : raw33721step2Labels = labelEmbedding8 ∘ raw33721step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33721step2 raw33721step2Labels raw33721step3Labels labelEmbedding8 hl
    _ = mixedMoment B node4810 node4810Labels := by rfl

theorem canonical33722 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33722 raw33722Labels = mixedMoment B node4230 node4230Labels := by
  calc
    mixedMoment B raw33722 raw33722Labels = mixedMoment B raw33722step0 raw33722step0Labels := by
      have ha : raw33722step0 = (fun i j => raw33722 (permutation160 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33722step0 raw33722; decide +kernel
      have hl : raw33722step0Labels = raw33722Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33722 raw33722Labels permutation160 permutation3
    mixedMoment B raw33722step0 raw33722step0Labels = mixedMoment B raw33722step1 raw33722step1Labels := by
      have ha : raw33722step1 = raw33722step0 := by apply Matrix.ext; unfold raw33722step1 raw33722step0; decide +kernel
      have hl : raw33722step0Labels = labelEmbedding6 ∘ raw33722step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33722step0 raw33722step0Labels raw33722step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4230 node4230Labels := by rfl

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

theorem canonical33724 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33724 raw33724Labels = mixedMoment B node4798 node4798Labels := by
  calc
    mixedMoment B raw33724 raw33724Labels = mixedMoment B raw33724step0 raw33724step0Labels := by
      have ha : raw33724step0 = (fun i j => raw33724 (permutation234 i) (permutation5 j)) := by apply Matrix.ext; unfold raw33724step0 raw33724; decide +kernel
      have hl : raw33724step0Labels = raw33724Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33724 raw33724Labels permutation234 permutation5
    mixedMoment B raw33724step0 raw33724step0Labels = mixedMoment B raw33724step1 raw33724step1Labels := by
      have ha : raw33724step1 = -raw33724step0 := by apply Matrix.ext; change ∀ i j, raw33724step1 i j = -(raw33724step0 i j); unfold raw33724step1 raw33724step0; decide +kernel
      have hl : raw33724step1Labels = raw33724step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33724step1 raw33724step1Labels = mixedMoment B raw33724step2 raw33724step2Labels := by
      have ha : raw33724step2 = raw33724step1 := by apply Matrix.ext; unfold raw33724step2 raw33724step1; decide +kernel
      have hl : raw33724step1Labels = labelEmbedding8 ∘ raw33724step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33724step1 raw33724step1Labels raw33724step2Labels labelEmbedding8 hl
    _ = mixedMoment B node4798 node4798Labels := by rfl

theorem canonical33725 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33725 raw33725Labels = mixedMoment B node4234 node4234Labels := by
  calc
    mixedMoment B raw33725 raw33725Labels = mixedMoment B raw33725step0 raw33725step0Labels := by
      have hz : ∀ j, raw33725 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33725step0 = (fun i j => raw33725 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33725step0 raw33725; decide +kernel
      have hl : raw33725step0Labels = raw33725Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33725 raw33725Labels permutation346 hz
    mixedMoment B raw33725step0 raw33725step0Labels = mixedMoment B raw33725step1 raw33725step1Labels := by
      have ha : raw33725step1 = (fun i j => raw33725step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33725step1 raw33725step0; decide +kernel
      have hl : raw33725step1Labels = raw33725step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33725step0 raw33725step0Labels permutation34 permutation3
    mixedMoment B raw33725step1 raw33725step1Labels = mixedMoment B raw33725step2 raw33725step2Labels := by
      have ha : raw33725step2 = raw33725step1 := by apply Matrix.ext; unfold raw33725step2 raw33725step1; decide +kernel
      have hl : raw33725step1Labels = labelEmbedding6 ∘ raw33725step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33725step1 raw33725step1Labels raw33725step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4234 node4234Labels := by rfl

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

theorem canonical33727 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33727 raw33727Labels = mixedMoment B node4722 node4722Labels := by
  calc
    mixedMoment B raw33727 raw33727Labels = mixedMoment B raw33727step0 raw33727step0Labels := by
      have ha : raw33727step0 = (fun i j => raw33727 (permutation178 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33727step0 raw33727; decide +kernel
      have hl : raw33727step0Labels = raw33727Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33727 raw33727Labels permutation178 permutation3
    mixedMoment B raw33727step0 raw33727step0Labels = mixedMoment B raw33727step1 raw33727step1Labels := by
      have ha : raw33727step1 = raw33727step0 := by apply Matrix.ext; unfold raw33727step1 raw33727step0; decide +kernel
      have hl : raw33727step0Labels = labelEmbedding6 ∘ raw33727step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33727step0 raw33727step0Labels raw33727step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4722 node4722Labels := by rfl

theorem canonical33728 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33728 raw33728Labels = mixedMoment B node4828 node4828Labels := by
  calc
    mixedMoment B raw33728 raw33728Labels = mixedMoment B raw33728step0 raw33728step0Labels := by
      have hz : ∀ j, raw33728 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33728step0 = (fun i j => raw33728 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33728step0 raw33728; decide +kernel
      have hl : raw33728step0Labels = raw33728Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33728 raw33728Labels permutation346 hz
    mixedMoment B raw33728step0 raw33728step0Labels = mixedMoment B raw33728step1 raw33728step1Labels := by
      have ha : raw33728step1 = (fun i j => raw33728step0 (permutation44 i) (permutation5 j)) := by apply Matrix.ext; unfold raw33728step1 raw33728step0; decide +kernel
      have hl : raw33728step1Labels = raw33728step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33728step0 raw33728step0Labels permutation44 permutation5
    mixedMoment B raw33728step1 raw33728step1Labels = mixedMoment B raw33728step2 raw33728step2Labels := by
      have ha : raw33728step2 = -raw33728step1 := by apply Matrix.ext; change ∀ i j, raw33728step2 i j = -(raw33728step1 i j); unfold raw33728step2 raw33728step1; decide +kernel
      have hl : raw33728step2Labels = raw33728step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33728step2 raw33728step2Labels = mixedMoment B raw33728step3 raw33728step3Labels := by
      have ha : raw33728step3 = raw33728step2 := by apply Matrix.ext; unfold raw33728step3 raw33728step2; decide +kernel
      have hl : raw33728step2Labels = labelEmbedding8 ∘ raw33728step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33728step2 raw33728step2Labels raw33728step3Labels labelEmbedding8 hl
    _ = mixedMoment B node4828 node4828Labels := by rfl

theorem canonical33729 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33729 raw33729Labels = mixedMoment B node4234 node4234Labels := by
  calc
    mixedMoment B raw33729 raw33729Labels = mixedMoment B raw33729step0 raw33729step0Labels := by
      have hz : ∀ j, raw33729 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33729step0 = (fun i j => raw33729 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33729step0 raw33729; decide +kernel
      have hl : raw33729step0Labels = raw33729Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33729 raw33729Labels permutation346 hz
    mixedMoment B raw33729step0 raw33729step0Labels = mixedMoment B raw33729step1 raw33729step1Labels := by
      have ha : raw33729step1 = (fun i j => raw33729step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33729step1 raw33729step0; decide +kernel
      have hl : raw33729step1Labels = raw33729step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33729step0 raw33729step0Labels permutation32 permutation3
    mixedMoment B raw33729step1 raw33729step1Labels = mixedMoment B raw33729step2 raw33729step2Labels := by
      have ha : raw33729step2 = raw33729step1 := by apply Matrix.ext; unfold raw33729step2 raw33729step1; decide +kernel
      have hl : raw33729step1Labels = labelEmbedding6 ∘ raw33729step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33729step1 raw33729step1Labels raw33729step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4234 node4234Labels := by rfl

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

theorem canonical33731 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33731 raw33731Labels = mixedMoment B node4722 node4722Labels := by
  calc
    mixedMoment B raw33731 raw33731Labels = mixedMoment B raw33731step0 raw33731step0Labels := by
      have ha : raw33731step0 = (fun i j => raw33731 (permutation176 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33731step0 raw33731; decide +kernel
      have hl : raw33731step0Labels = raw33731Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33731 raw33731Labels permutation176 permutation3
    mixedMoment B raw33731step0 raw33731step0Labels = mixedMoment B raw33731step1 raw33731step1Labels := by
      have ha : raw33731step1 = raw33731step0 := by apply Matrix.ext; unfold raw33731step1 raw33731step0; decide +kernel
      have hl : raw33731step0Labels = labelEmbedding6 ∘ raw33731step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33731step0 raw33731step0Labels raw33731step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4722 node4722Labels := by rfl

theorem canonical33732 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33732 raw33732Labels = mixedMoment B node4231 node4231Labels := by
  calc
    mixedMoment B raw33732 raw33732Labels = mixedMoment B raw33732step0 raw33732step0Labels := by
      have hz : ∀ j, raw33732 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33732step0 = (fun i j => raw33732 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33732step0 raw33732; decide +kernel
      have hl : raw33732step0Labels = raw33732Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33732 raw33732Labels permutation346 hz
    mixedMoment B raw33732step0 raw33732step0Labels = mixedMoment B raw33732step1 raw33732step1Labels := by
      have ha : raw33732step1 = (fun i j => raw33732step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33732step1 raw33732step0; decide +kernel
      have hl : raw33732step1Labels = raw33732step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33732step0 raw33732step0Labels permutation32 permutation3
    mixedMoment B raw33732step1 raw33732step1Labels = mixedMoment B raw33732step2 raw33732step2Labels := by
      have ha : raw33732step2 = raw33732step1 := by apply Matrix.ext; unfold raw33732step2 raw33732step1; decide +kernel
      have hl : raw33732step1Labels = labelEmbedding6 ∘ raw33732step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33732step1 raw33732step1Labels raw33732step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4231 node4231Labels := by rfl

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

theorem canonical33734 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33734 raw33734Labels = mixedMoment B node4720 node4720Labels := by
  calc
    mixedMoment B raw33734 raw33734Labels = mixedMoment B raw33734step0 raw33734step0Labels := by
      have ha : raw33734step0 = (fun i j => raw33734 (permutation176 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33734step0 raw33734; decide +kernel
      have hl : raw33734step0Labels = raw33734Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33734 raw33734Labels permutation176 permutation3
    mixedMoment B raw33734step0 raw33734step0Labels = mixedMoment B raw33734step1 raw33734step1Labels := by
      have ha : raw33734step1 = raw33734step0 := by apply Matrix.ext; unfold raw33734step1 raw33734step0; decide +kernel
      have hl : raw33734step0Labels = labelEmbedding6 ∘ raw33734step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33734step0 raw33734step0Labels raw33734step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4720 node4720Labels := by rfl

theorem canonical33735 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33735 raw33735Labels = mixedMoment B node4800 node4800Labels := by
  calc
    mixedMoment B raw33735 raw33735Labels = mixedMoment B raw33735step0 raw33735step0Labels := by
      have hz : ∀ j, raw33735 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33735step0 = (fun i j => raw33735 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33735step0 raw33735; decide +kernel
      have hl : raw33735step0Labels = raw33735Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33735 raw33735Labels permutation346 hz
    mixedMoment B raw33735step0 raw33735step0Labels = mixedMoment B raw33735step1 raw33735step1Labels := by
      have ha : raw33735step1 = (fun i j => raw33735step0 (permutation145 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33735step1 raw33735step0; decide +kernel
      have hl : raw33735step1Labels = raw33735step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33735step0 raw33735step0Labels permutation145 permutation3
    mixedMoment B raw33735step1 raw33735step1Labels = mixedMoment B raw33735step2 raw33735step2Labels := by
      have ha : raw33735step2 = -raw33735step1 := by apply Matrix.ext; change ∀ i j, raw33735step2 i j = -(raw33735step1 i j); unfold raw33735step2 raw33735step1; decide +kernel
      have hl : raw33735step2Labels = raw33735step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33735step2 raw33735step2Labels = mixedMoment B raw33735step3 raw33735step3Labels := by
      have ha : raw33735step3 = raw33735step2 := by apply Matrix.ext; unfold raw33735step3 raw33735step2; decide +kernel
      have hl : raw33735step2Labels = labelEmbedding6 ∘ raw33735step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33735step2 raw33735step2Labels raw33735step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4800 node4800Labels := by rfl

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

theorem canonical927 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw927 raw927Labels = mixedMoment B node4231 node4231Labels := by
  calc
    mixedMoment B raw927 raw927Labels = mixedMoment B raw927step0 raw927step0Labels := by
      have ha : raw927step0 = (fun i j => raw927 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw927step0 raw927; decide +kernel
      have hl : raw927step0Labels = raw927Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw927 raw927Labels permutation32 permutation4
    mixedMoment B raw927step0 raw927step0Labels = mixedMoment B raw927step1 raw927step1Labels := by
      have ha : raw927step1 = raw927step0 := by apply Matrix.ext; unfold raw927step1 raw927step0; decide +kernel
      have hl : raw927step0Labels = labelEmbedding7 ∘ raw927step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw927step0 raw927step0Labels raw927step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4231 node4231Labels := by rfl

theorem canonical928 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw928 raw928Labels = mixedMoment B node731 node731Labels := by
  calc
    mixedMoment B raw928 raw928Labels = mixedMoment B raw928step0 raw928step0Labels := by
      have ha : raw928step0 = (fun i j => raw928 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw928step0 raw928; decide +kernel
      have hl : raw928step0Labels = raw928Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw928 raw928Labels permutation32 permutation4
    _ = mixedMoment B node731 node731Labels := by rfl

theorem canonical929 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw929 raw929Labels = mixedMoment B node781 node781Labels := by
  calc
    mixedMoment B raw929 raw929Labels = mixedMoment B raw929step0 raw929step0Labels := by
      have ha : raw929step0 = (fun i j => raw929 (permutation40 i) (permutation6 j)) := by apply Matrix.ext; unfold raw929step0 raw929; decide +kernel
      have hl : raw929step0Labels = raw929Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw929 raw929Labels permutation40 permutation6
    mixedMoment B raw929step0 raw929step0Labels = mixedMoment B raw929step1 raw929step1Labels := by
      have ha : raw929step1 = -raw929step0 := by apply Matrix.ext; change ∀ i j, raw929step1 i j = -(raw929step0 i j); unfold raw929step1 raw929step0; decide +kernel
      have hl : raw929step1Labels = raw929step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw929step1 raw929step1Labels = mixedMoment B raw929step2 raw929step2Labels := by
      have ha : raw929step2 = raw929step1 := by apply Matrix.ext; unfold raw929step2 raw929step1; decide +kernel
      have hl : raw929step1Labels = labelEmbedding1 ∘ raw929step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw929step1 raw929step1Labels raw929step2Labels labelEmbedding1 hl
    _ = mixedMoment B node781 node781Labels := by rfl

theorem canonical936 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw936 raw936Labels = mixedMoment B node4234 node4234Labels := by
  calc
    mixedMoment B raw936 raw936Labels = mixedMoment B raw936step0 raw936step0Labels := by
      have ha : raw936step0 = (fun i j => raw936 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw936step0 raw936; decide +kernel
      have hl : raw936step0Labels = raw936Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw936 raw936Labels permutation32 permutation4
    mixedMoment B raw936step0 raw936step0Labels = mixedMoment B raw936step1 raw936step1Labels := by
      have ha : raw936step1 = raw936step0 := by apply Matrix.ext; unfold raw936step1 raw936step0; decide +kernel
      have hl : raw936step0Labels = labelEmbedding7 ∘ raw936step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw936step0 raw936step0Labels raw936step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4234 node4234Labels := by rfl

theorem canonical937 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw937 raw937Labels = mixedMoment B node734 node734Labels := by
  calc
    mixedMoment B raw937 raw937Labels = mixedMoment B raw937step0 raw937step0Labels := by
      have ha : raw937step0 = (fun i j => raw937 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw937step0 raw937; decide +kernel
      have hl : raw937step0Labels = raw937Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw937 raw937Labels permutation32 permutation4
    _ = mixedMoment B node734 node734Labels := by rfl

theorem canonical938 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw938 raw938Labels = mixedMoment B node800 node800Labels := by
  calc
    mixedMoment B raw938 raw938Labels = mixedMoment B raw938step0 raw938step0Labels := by
      have ha : raw938step0 = (fun i j => raw938 (permutation38 i) (permutation6 j)) := by apply Matrix.ext; unfold raw938step0 raw938; decide +kernel
      have hl : raw938step0Labels = raw938Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw938 raw938Labels permutation38 permutation6
    mixedMoment B raw938step0 raw938step0Labels = mixedMoment B raw938step1 raw938step1Labels := by
      have ha : raw938step1 = -raw938step0 := by apply Matrix.ext; change ∀ i j, raw938step1 i j = -(raw938step0 i j); unfold raw938step1 raw938step0; decide +kernel
      have hl : raw938step1Labels = raw938step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw938step1 raw938step1Labels = mixedMoment B raw938step2 raw938step2Labels := by
      have ha : raw938step2 = raw938step1 := by apply Matrix.ext; unfold raw938step2 raw938step1; decide +kernel
      have hl : raw938step1Labels = labelEmbedding1 ∘ raw938step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw938step1 raw938step1Labels raw938step2Labels labelEmbedding1 hl
    _ = mixedMoment B node800 node800Labels := by rfl

theorem canonical981 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw981 raw981Labels = mixedMoment B node4255 node4255Labels := by
  calc
    mixedMoment B raw981 raw981Labels = mixedMoment B raw981step0 raw981step0Labels := by
      have ha : raw981step0 = (fun i j => raw981 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw981step0 raw981; decide +kernel
      have hl : raw981step0Labels = raw981Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw981 raw981Labels permutation32 permutation4
    mixedMoment B raw981step0 raw981step0Labels = mixedMoment B raw981step1 raw981step1Labels := by
      have ha : raw981step1 = raw981step0 := by apply Matrix.ext; unfold raw981step1 raw981step0; decide +kernel
      have hl : raw981step0Labels = labelEmbedding7 ∘ raw981step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw981step0 raw981step0Labels raw981step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4255 node4255Labels := by rfl

theorem canonical982 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw982 raw982Labels = mixedMoment B node789 node789Labels := by
  calc
    mixedMoment B raw982 raw982Labels = mixedMoment B raw982step0 raw982step0Labels := by
      have ha : raw982step0 = (fun i j => raw982 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw982step0 raw982; decide +kernel
      have hl : raw982step0Labels = raw982Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw982 raw982Labels permutation32 permutation4
    _ = mixedMoment B node789 node789Labels := by rfl

theorem canonical983 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw983 raw983Labels = mixedMoment B node823 node823Labels := by
  calc
    mixedMoment B raw983 raw983Labels = mixedMoment B raw983step0 raw983step0Labels := by
      have ha : raw983step0 = (fun i j => raw983 (permutation44 i) (permutation6 j)) := by apply Matrix.ext; unfold raw983step0 raw983; decide +kernel
      have hl : raw983step0Labels = raw983Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw983 raw983Labels permutation44 permutation6
    mixedMoment B raw983step0 raw983step0Labels = mixedMoment B raw983step1 raw983step1Labels := by
      have ha : raw983step1 = -raw983step0 := by apply Matrix.ext; change ∀ i j, raw983step1 i j = -(raw983step0 i j); unfold raw983step1 raw983step0; decide +kernel
      have hl : raw983step1Labels = raw983step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw983step1 raw983step1Labels = mixedMoment B raw983step2 raw983step2Labels := by
      have ha : raw983step2 = raw983step1 := by apply Matrix.ext; unfold raw983step2 raw983step1; decide +kernel
      have hl : raw983step1Labels = labelEmbedding1 ∘ raw983step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw983step1 raw983step1Labels raw983step2Labels labelEmbedding1 hl
    _ = mixedMoment B node823 node823Labels := by rfl

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

theorem singleton4231 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4231 node4231Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node731 node731Labels + mixedMoment B node781 node781Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw927 singletonSmall4231
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4231) = raw927Labels := by decide +kernel
  rw [hl, canonical927 B hB] at h
  have hc0 : mixedMoment B raw927 (Fin.cases (0 : Fin 2) singletonSmall4231) =
      mixedMoment B node731 node731Labels := by
    have ha : raw927 = raw928 := by apply Matrix.ext; unfold raw927 raw928; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4231 = raw928Labels := by decide +kernel
    rw [ha, hj, canonical928 B hB]
  have hc1 : mixedMoment B raw927 (Fin.cases (1 : Fin 2) singletonSmall4231) =
      mixedMoment B node781 node781Labels := by
    have ha : raw927 = raw929 := by apply Matrix.ext; unfold raw927 raw929; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4231 = raw929Labels := by decide +kernel
    rw [ha, hj, canonical929 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4234 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4234 node4234Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node734 node734Labels + mixedMoment B node800 node800Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw936 singletonSmall4234
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4234) = raw936Labels := by decide +kernel
  rw [hl, canonical936 B hB] at h
  have hc0 : mixedMoment B raw936 (Fin.cases (0 : Fin 2) singletonSmall4234) =
      mixedMoment B node734 node734Labels := by
    have ha : raw936 = raw937 := by apply Matrix.ext; unfold raw936 raw937; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4234 = raw937Labels := by decide +kernel
    rw [ha, hj, canonical937 B hB]
  have hc1 : mixedMoment B raw936 (Fin.cases (1 : Fin 2) singletonSmall4234) =
      mixedMoment B node800 node800Labels := by
    have ha : raw936 = raw938 := by apply Matrix.ext; unfold raw936 raw938; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4234 = raw938Labels := by decide +kernel
    rw [ha, hj, canonical938 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4255 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4255 node4255Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node789 node789Labels + mixedMoment B node823 node823Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw981 singletonSmall4255
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4255) = raw981Labels := by decide +kernel
  rw [hl, canonical981 B hB] at h
  have hc0 : mixedMoment B raw981 (Fin.cases (0 : Fin 2) singletonSmall4255) =
      mixedMoment B node789 node789Labels := by
    have ha : raw981 = raw982 := by apply Matrix.ext; unfold raw981 raw982; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4255 = raw982Labels := by decide +kernel
    rw [ha, hj, canonical982 B hB]
  have hc1 : mixedMoment B raw981 (Fin.cases (1 : Fin 2) singletonSmall4255) =
      mixedMoment B node823 node823Labels := by
    have ha : raw981 = raw983 := by apply Matrix.ext; unfold raw981 raw983; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4255 = raw983Labels := by decide +kernel
    rw [ha, hj, canonical983 B hB]
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

theorem singleton4720 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4720 node4720Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1874 node1874Labels + mixedMoment B node1896 node1896Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1617 singletonSmall4720
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4720) = raw1617Labels := by decide +kernel
  rw [hl, canonical1617 B hB] at h
  have hc0 : mixedMoment B raw1617 (Fin.cases (0 : Fin 2) singletonSmall4720) =
      mixedMoment B node1874 node1874Labels := by
    have ha : raw1617 = raw1618 := by apply Matrix.ext; unfold raw1617 raw1618; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4720 = raw1618Labels := by decide +kernel
    rw [ha, hj, canonical1618 B hB]
  have hc1 : mixedMoment B raw1617 (Fin.cases (1 : Fin 2) singletonSmall4720) =
      mixedMoment B node1896 node1896Labels := by
    have ha : raw1617 = raw1619 := by apply Matrix.ext; unfold raw1617 raw1619; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4720 = raw1619Labels := by decide +kernel
    rw [ha, hj, canonical1619 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4722 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4722 node4722Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1876 node1876Labels + mixedMoment B node1906 node1906Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1623 singletonSmall4722
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4722) = raw1623Labels := by decide +kernel
  rw [hl, canonical1623 B hB] at h
  have hc0 : mixedMoment B raw1623 (Fin.cases (0 : Fin 2) singletonSmall4722) =
      mixedMoment B node1876 node1876Labels := by
    have ha : raw1623 = raw1624 := by apply Matrix.ext; unfold raw1623 raw1624; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4722 = raw1624Labels := by decide +kernel
    rw [ha, hj, canonical1624 B hB]
  have hc1 : mixedMoment B raw1623 (Fin.cases (1 : Fin 2) singletonSmall4722) =
      mixedMoment B node1906 node1906Labels := by
    have ha : raw1623 = raw1625 := by apply Matrix.ext; unfold raw1623 raw1625; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4722 = raw1625Labels := by decide +kernel
    rw [ha, hj, canonical1625 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4731 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4731 node4731Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1900 node1900Labels + mixedMoment B node1921 node1921Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1647 singletonSmall4731
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4731) = raw1647Labels := by decide +kernel
  rw [hl, canonical1647 B hB] at h
  have hc0 : mixedMoment B raw1647 (Fin.cases (0 : Fin 2) singletonSmall4731) =
      mixedMoment B node1900 node1900Labels := by
    have ha : raw1647 = raw1648 := by apply Matrix.ext; unfold raw1647 raw1648; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4731 = raw1648Labels := by decide +kernel
    rw [ha, hj, canonical1648 B hB]
  have hc1 : mixedMoment B raw1647 (Fin.cases (1 : Fin 2) singletonSmall4731) =
      mixedMoment B node1921 node1921Labels := by
    have ha : raw1647 = raw1649 := by apply Matrix.ext; unfold raw1647 raw1649; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4731 = raw1649Labels := by decide +kernel
    rw [ha, hj, canonical1649 B hB]
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

theorem singleton4800 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4800 node4800Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2018 node2018Labels + mixedMoment B node2018 node2018Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1728 singletonSmall4800
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4800) = raw1728Labels := by decide +kernel
  rw [hl, canonical1728 B hB] at h
  have hc0 : mixedMoment B raw1728 (Fin.cases (0 : Fin 2) singletonSmall4800) =
      mixedMoment B node2018 node2018Labels := by
    have ha : raw1728 = raw1729 := by apply Matrix.ext; unfold raw1728 raw1729; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4800 = raw1729Labels := by decide +kernel
    rw [ha, hj, canonical1729 B hB]
  have hc1 : mixedMoment B raw1728 (Fin.cases (1 : Fin 2) singletonSmall4800) =
      mixedMoment B node2018 node2018Labels := by
    have ha : raw1728 = raw1730 := by apply Matrix.ext; unfold raw1728 raw1730; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4800 = raw1730Labels := by decide +kernel
    rw [ha, hj, canonical1730 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

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

theorem singleton4828 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4828 node4828Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2048 node2048Labels + mixedMoment B node2082 node2082Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1758 singletonSmall4828
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4828) = raw1758Labels := by decide +kernel
  rw [hl, canonical1758 B hB] at h
  have hc0 : mixedMoment B raw1758 (Fin.cases (0 : Fin 2) singletonSmall4828) =
      mixedMoment B node2048 node2048Labels := by
    have ha : raw1758 = raw1759 := by apply Matrix.ext; unfold raw1758 raw1759; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4828 = raw1759Labels := by decide +kernel
    rw [ha, hj, canonical1759 B hB]
  have hc1 : mixedMoment B raw1758 (Fin.cases (1 : Fin 2) singletonSmall4828) =
      mixedMoment B node2082 node2082Labels := by
    have ha : raw1758 = raw1760 := by apply Matrix.ext; unfold raw1758 raw1760; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4828 = raw1760Labels := by decide +kernel
    rw [ha, hj, canonical1760 B hB]
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

theorem singleton4864 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4864 node4864Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2105 node2105Labels + mixedMoment B node2241 node2241Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1788 singletonSmall4864
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4864) = raw1788Labels := by decide +kernel
  rw [hl, canonical1788 B hB] at h
  have hc0 : mixedMoment B raw1788 (Fin.cases (0 : Fin 2) singletonSmall4864) =
      mixedMoment B node2105 node2105Labels := by
    have ha : raw1788 = raw1789 := by apply Matrix.ext; unfold raw1788 raw1789; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4864 = raw1789Labels := by decide +kernel
    rw [ha, hj, canonical1789 B hB]
  have hc1 : mixedMoment B raw1788 (Fin.cases (1 : Fin 2) singletonSmall4864) =
      mixedMoment B node2241 node2241Labels := by
    have ha : raw1788 = raw1790 := by apply Matrix.ext; unfold raw1788 raw1790; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4864 = raw1790Labels := by decide +kernel
    rw [ha, hj, canonical1790 B hB]
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

theorem sound731 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node731 node731Labels = Sparse.eval nodeValue731 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 731) = mixedMoment B node731 node731Labels := rfl
  simpa [nodeValue731, Sparse.eval] using hc.symm

theorem sound734 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node734 node734Labels = Sparse.eval nodeValue734 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 734) = mixedMoment B node734 node734Labels := rfl
  simpa [nodeValue734, Sparse.eval] using hc.symm

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

theorem sound781 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node781 node781Labels = Sparse.eval nodeValue781 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 781) = mixedMoment B node781 node781Labels := rfl
  simpa [nodeValue781, Sparse.eval] using hc.symm

theorem sound789 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node789 node789Labels = Sparse.eval nodeValue789 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 789) = mixedMoment B node789 node789Labels := rfl
  simpa [nodeValue789, Sparse.eval] using hc.symm

theorem sound800 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node800 node800Labels = Sparse.eval nodeValue800 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 800) = mixedMoment B node800 node800Labels := rfl
  simpa [nodeValue800, Sparse.eval] using hc.symm

theorem sound823 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node823 node823Labels = Sparse.eval nodeValue823 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 823) = mixedMoment B node823 node823Labels := rfl
  simpa [nodeValue823, Sparse.eval] using hc.symm

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound29
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound1874 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1874 node1874Labels = Sparse.eval nodeValue1874 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1874) = mixedMoment B node1874 node1874Labels := rfl
  simpa [nodeValue1874, Sparse.eval] using hc.symm

theorem sound1876 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1876 node1876Labels = Sparse.eval nodeValue1876 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1876) = mixedMoment B node1876 node1876Labels := rfl
  simpa [nodeValue1876, Sparse.eval] using hc.symm

theorem sound1896 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1896 node1896Labels = Sparse.eval nodeValue1896 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1896) = mixedMoment B node1896 node1896Labels := rfl
  simpa [nodeValue1896, Sparse.eval] using hc.symm

theorem sound1900 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1900 node1900Labels = Sparse.eval nodeValue1900 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1900) = mixedMoment B node1900 node1900Labels := rfl
  simpa [nodeValue1900, Sparse.eval] using hc.symm

theorem sound1906 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1906 node1906Labels = Sparse.eval nodeValue1906 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1906) = mixedMoment B node1906 node1906Labels := rfl
  simpa [nodeValue1906, Sparse.eval] using hc.symm

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

theorem sound1921 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1921 node1921Labels = Sparse.eval nodeValue1921 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1921) = mixedMoment B node1921 node1921Labels := rfl
  simpa [nodeValue1921, Sparse.eval] using hc.symm

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

theorem sound2018 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2018 node2018Labels = Sparse.eval nodeValue2018 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2018) = mixedMoment B node2018 node2018Labels := rfl
  simpa [nodeValue2018, Sparse.eval] using hc.symm

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

theorem sound2048 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2048 node2048Labels = Sparse.eval nodeValue2048 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2048) = mixedMoment B node2048 node2048Labels := rfl
  simpa [nodeValue2048, Sparse.eval] using hc.symm

theorem sound2075 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2075 node2075Labels = Sparse.eval nodeValue2075 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2075) = mixedMoment B node2075 node2075Labels := rfl
  simpa [nodeValue2075, Sparse.eval] using hc.symm

theorem sound2082 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2082 node2082Labels = Sparse.eval nodeValue2082 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2082) = mixedMoment B node2082 node2082Labels := rfl
  simpa [nodeValue2082, Sparse.eval] using hc.symm

theorem sound2105 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2105 node2105Labels = Sparse.eval nodeValue2105 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2105) = mixedMoment B node2105 node2105Labels := rfl
  simpa [nodeValue2105, Sparse.eval] using hc.symm

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

theorem sound2241 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2241 node2241Labels = Sparse.eval nodeValue2241 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2241) = mixedMoment B node2241 node2241Labels := rfl
  simpa [nodeValue2241, Sparse.eval] using hc.symm

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

theorem sound4231 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4231 node4231Labels = Sparse.eval nodeValue4231 (mixedVector B) := by
  have h := singleton4231 B _hB
  rw [sound731 B _hB _hF, sound781 B _hB _hF] at h
  norm_num [nodeValue4231, nodeValue731, nodeValue781, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4234 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4234 node4234Labels = Sparse.eval nodeValue4234 (mixedVector B) := by
  have h := singleton4234 B _hB
  rw [sound734 B _hB _hF, sound800 B _hB _hF] at h
  norm_num [nodeValue4234, nodeValue734, nodeValue800, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4255 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4255 node4255Labels = Sparse.eval nodeValue4255 (mixedVector B) := by
  have h := singleton4255 B _hB
  rw [sound789 B _hB _hF, sound823 B _hB _hF] at h
  norm_num [nodeValue4255, nodeValue789, nodeValue823, Sparse.eval] at h ⊢
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

theorem sound4720 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4720 node4720Labels = Sparse.eval nodeValue4720 (mixedVector B) := by
  have h := singleton4720 B _hB
  rw [sound1874 B _hB _hF, sound1896 B _hB _hF] at h
  norm_num [nodeValue4720, nodeValue1874, nodeValue1896, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4722 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4722 node4722Labels = Sparse.eval nodeValue4722 (mixedVector B) := by
  have h := singleton4722 B _hB
  rw [sound1876 B _hB _hF, sound1906 B _hB _hF] at h
  norm_num [nodeValue4722, nodeValue1876, nodeValue1906, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4731 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4731 node4731Labels = Sparse.eval nodeValue4731 (mixedVector B) := by
  have h := singleton4731 B _hB
  rw [sound1900 B _hB _hF, sound1921 B _hB _hF] at h
  norm_num [nodeValue4731, nodeValue1900, nodeValue1921, Sparse.eval] at h ⊢
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

theorem sound4800 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4800 node4800Labels = Sparse.eval nodeValue4800 (mixedVector B) := by
  have h := singleton4800 B _hB
  rw [sound2018 B _hB _hF] at h
  norm_num [nodeValue4800, nodeValue2018, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4810 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4810 node4810Labels = Sparse.eval nodeValue4810 (mixedVector B) := by
  have h := singleton4810 B _hB
  rw [sound2028 B _hB _hF, sound2215 B _hB _hF] at h
  norm_num [nodeValue4810, nodeValue2028, nodeValue2215, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4828 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4828 node4828Labels = Sparse.eval nodeValue4828 (mixedVector B) := by
  have h := singleton4828 B _hB
  rw [sound2048 B _hB _hF, sound2082 B _hB _hF] at h
  norm_num [nodeValue4828, nodeValue2048, nodeValue2082, Sparse.eval] at h ⊢
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

theorem sound4864 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4864 node4864Labels = Sparse.eval nodeValue4864 (mixedVector B) := by
  have h := singleton4864 B _hB
  rw [sound2105 B _hB _hF, sound2241 B _hB _hF] at h
  norm_num [nodeValue4864, nodeValue2105, nodeValue2241, Sparse.eval] at h ⊢
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources76
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sourceEq2456 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2456 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2456 + difference 0 1) (sourceB2456 + difference 1 0) sourceC2456) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5387) := by
    have ha : (tripleCharges (sourceA2456 + difference 0 1) (sourceB2456 + difference 1 0) sourceC2456) = raw18198 := by
      apply Matrix.ext; unfold tripleCharges sourceA2456 sourceB2456 sourceC2456 difference raw18198; decide +kernel
    rw [ha]
    exact (canonical18198 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2456 + difference 0 2) (sourceB2456 + difference 2 0) sourceC2456) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5400) := by
    have ha : (tripleCharges (sourceA2456 + difference 0 2) (sourceB2456 + difference 2 0) sourceC2456) = raw18199 := by
      apply Matrix.ext; unfold tripleCharges sourceA2456 sourceB2456 sourceC2456 difference raw18199; decide +kernel
    rw [ha]
    exact (canonical18199 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2456 + difference 0 3) (sourceB2456 + difference 3 0) sourceC2456) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5432) := by
    have ha : (tripleCharges (sourceA2456 + difference 0 3) (sourceB2456 + difference 3 0) sourceC2456) = raw18506 := by
      apply Matrix.ext; unfold tripleCharges sourceA2456 sourceB2456 sourceC2456 difference raw18506; decide +kernel
    rw [ha]
    exact (canonical18506 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2456 + difference 0 4) (sourceB2456 + difference 4 0) sourceC2456) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5432) := by
    have ha : (tripleCharges (sourceA2456 + difference 0 4) (sourceB2456 + difference 4 0) sourceC2456) = raw18200 := by
      apply Matrix.ext; unfold tripleCharges sourceA2456 sourceB2456 sourceC2456 difference raw18200; decide +kernel
    rw [ha]
    exact (canonical18200 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2456 + difference 0 5) (sourceB2456 + difference 5 0) sourceC2456) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5450) := by
    have ha : (tripleCharges (sourceA2456 + difference 0 5) (sourceB2456 + difference 5 0) sourceC2456) = raw18201 := by
      apply Matrix.ext; unfold tripleCharges sourceA2456 sourceB2456 sourceC2456 difference raw18201; decide +kernel
    rw [ha]
    exact (canonical18201 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2456 + difference 1 0) (sourceB2456 + difference 0 1) sourceC2456) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4255) := by
    have ha : (tripleCharges (sourceA2456 + difference 1 0) (sourceB2456 + difference 0 1) sourceC2456) = raw33719 := by
      apply Matrix.ext; unfold tripleCharges sourceA2456 sourceB2456 sourceC2456 difference raw33719; decide +kernel
    rw [ha]
    exact (canonical33719 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2456 + difference 1 2) (sourceB2456 + difference 2 1) sourceC2456) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4731) := by
    have ha : (tripleCharges (sourceA2456 + difference 1 2) (sourceB2456 + difference 2 1) sourceC2456) = raw33720 := by
      apply Matrix.ext; unfold tripleCharges sourceA2456 sourceB2456 sourceC2456 difference raw33720; decide +kernel
    rw [ha]
    exact (canonical33720 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2456 + difference 1 3) (sourceB2456 + difference 3 1) sourceC2456) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4810) := by
    have ha : (tripleCharges (sourceA2456 + difference 1 3) (sourceB2456 + difference 3 1) sourceC2456) = raw18187 := by
      apply Matrix.ext; unfold tripleCharges sourceA2456 sourceB2456 sourceC2456 difference raw18187; decide +kernel
    rw [ha]
    exact (canonical18187 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2456 + difference 1 4) (sourceB2456 + difference 4 1) sourceC2456) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4810) := by
    have ha : (tripleCharges (sourceA2456 + difference 1 4) (sourceB2456 + difference 4 1) sourceC2456) = raw33721 := by
      apply Matrix.ext; unfold tripleCharges sourceA2456 sourceB2456 sourceC2456 difference raw33721; decide +kernel
    rw [ha]
    exact (canonical33721 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2456 + difference 1 5) (sourceB2456 + difference 5 1) sourceC2456) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4889) := by
    have ha : (tripleCharges (sourceA2456 + difference 1 5) (sourceB2456 + difference 5 1) sourceC2456) = raw18489 := by
      apply Matrix.ext; unfold tripleCharges sourceA2456 sourceB2456 sourceC2456 difference raw18489; decide +kernel
    rw [ha]
    exact (canonical18489 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2456 + difference 2 0) (sourceB2456 + difference 0 2) sourceC2456) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4230) := by
    have ha : (tripleCharges (sourceA2456 + difference 2 0) (sourceB2456 + difference 0 2) sourceC2456) = raw33722 := by
      apply Matrix.ext; unfold tripleCharges sourceA2456 sourceB2456 sourceC2456 difference raw33722; decide +kernel
    rw [ha]
    exact (canonical33722 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2456 + difference 2 1) (sourceB2456 + difference 1 2) sourceC2456) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4676) := by
    have ha : (tripleCharges (sourceA2456 + difference 2 1) (sourceB2456 + difference 1 2) sourceC2456) = raw33723 := by
      apply Matrix.ext; unfold tripleCharges sourceA2456 sourceB2456 sourceC2456 difference raw33723; decide +kernel
    rw [ha]
    exact (canonical33723 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2456 + difference 2 3) (sourceB2456 + difference 3 2) sourceC2456) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4798) := by
    have ha : (tripleCharges (sourceA2456 + difference 2 3) (sourceB2456 + difference 3 2) sourceC2456) = raw18192 := by
      apply Matrix.ext; unfold tripleCharges sourceA2456 sourceB2456 sourceC2456 difference raw18192; decide +kernel
    rw [ha]
    exact (canonical18192 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2456 + difference 2 4) (sourceB2456 + difference 4 2) sourceC2456) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4798) := by
    have ha : (tripleCharges (sourceA2456 + difference 2 4) (sourceB2456 + difference 4 2) sourceC2456) = raw33724 := by
      apply Matrix.ext; unfold tripleCharges sourceA2456 sourceB2456 sourceC2456 difference raw33724; decide +kernel
    rw [ha]
    exact (canonical33724 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2456 + difference 2 5) (sourceB2456 + difference 5 2) sourceC2456) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4864) := by
    have ha : (tripleCharges (sourceA2456 + difference 2 5) (sourceB2456 + difference 5 2) sourceC2456) = raw18493 := by
      apply Matrix.ext; unfold tripleCharges sourceA2456 sourceB2456 sourceC2456 difference raw18493; decide +kernel
    rw [ha]
    exact (canonical18493 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2456 + difference 3 0) (sourceB2456 + difference 0 3) sourceC2456) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4234) := by
    have ha : (tripleCharges (sourceA2456 + difference 3 0) (sourceB2456 + difference 0 3) sourceC2456) = raw33725 := by
      apply Matrix.ext; unfold tripleCharges sourceA2456 sourceB2456 sourceC2456 difference raw33725; decide +kernel
    rw [ha]
    exact (canonical33725 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2456 + difference 3 1) (sourceB2456 + difference 1 3) sourceC2456) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4684) := by
    have ha : (tripleCharges (sourceA2456 + difference 3 1) (sourceB2456 + difference 1 3) sourceC2456) = raw33726 := by
      apply Matrix.ext; unfold tripleCharges sourceA2456 sourceB2456 sourceC2456 difference raw33726; decide +kernel
    rw [ha]
    exact (canonical33726 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2456 + difference 3 2) (sourceB2456 + difference 2 3) sourceC2456) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4722) := by
    have ha : (tripleCharges (sourceA2456 + difference 3 2) (sourceB2456 + difference 2 3) sourceC2456) = raw33727 := by
      apply Matrix.ext; unfold tripleCharges sourceA2456 sourceB2456 sourceC2456 difference raw33727; decide +kernel
    rw [ha]
    exact (canonical33727 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2456 + difference 3 4) (sourceB2456 + difference 4 3) sourceC2456) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4828) := by
    have ha : (tripleCharges (sourceA2456 + difference 3 4) (sourceB2456 + difference 4 3) sourceC2456) = raw33728 := by
      apply Matrix.ext; unfold tripleCharges sourceA2456 sourceB2456 sourceC2456 difference raw33728; decide +kernel
    rw [ha]
    exact (canonical33728 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2456 + difference 3 5) (sourceB2456 + difference 5 3) sourceC2456) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4866) := by
    have ha : (tripleCharges (sourceA2456 + difference 3 5) (sourceB2456 + difference 5 3) sourceC2456) = raw18497 := by
      apply Matrix.ext; unfold tripleCharges sourceA2456 sourceB2456 sourceC2456 difference raw18497; decide +kernel
    rw [ha]
    exact (canonical18497 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2456 + difference 4 0) (sourceB2456 + difference 0 4) sourceC2456) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4234) := by
    have ha : (tripleCharges (sourceA2456 + difference 4 0) (sourceB2456 + difference 0 4) sourceC2456) = raw33729 := by
      apply Matrix.ext; unfold tripleCharges sourceA2456 sourceB2456 sourceC2456 difference raw33729; decide +kernel
    rw [ha]
    exact (canonical33729 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2456 + difference 4 1) (sourceB2456 + difference 1 4) sourceC2456) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4684) := by
    have ha : (tripleCharges (sourceA2456 + difference 4 1) (sourceB2456 + difference 1 4) sourceC2456) = raw33730 := by
      apply Matrix.ext; unfold tripleCharges sourceA2456 sourceB2456 sourceC2456 difference raw33730; decide +kernel
    rw [ha]
    exact (canonical33730 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2456 + difference 4 2) (sourceB2456 + difference 2 4) sourceC2456) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4722) := by
    have ha : (tripleCharges (sourceA2456 + difference 4 2) (sourceB2456 + difference 2 4) sourceC2456) = raw33731 := by
      apply Matrix.ext; unfold tripleCharges sourceA2456 sourceB2456 sourceC2456 difference raw33731; decide +kernel
    rw [ha]
    exact (canonical33731 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2456 + difference 4 3) (sourceB2456 + difference 3 4) sourceC2456) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4828) := by
    have ha : (tripleCharges (sourceA2456 + difference 4 3) (sourceB2456 + difference 3 4) sourceC2456) = raw18202 := by
      apply Matrix.ext; unfold tripleCharges sourceA2456 sourceB2456 sourceC2456 difference raw18202; decide +kernel
    rw [ha]
    exact (canonical18202 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2456 + difference 4 5) (sourceB2456 + difference 5 4) sourceC2456) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4866) := by
    have ha : (tripleCharges (sourceA2456 + difference 4 5) (sourceB2456 + difference 5 4) sourceC2456) = raw18502 := by
      apply Matrix.ext; unfold tripleCharges sourceA2456 sourceB2456 sourceC2456 difference raw18502; decide +kernel
    rw [ha]
    exact (canonical18502 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2456 + difference 5 0) (sourceB2456 + difference 0 5) sourceC2456) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4231) := by
    have ha : (tripleCharges (sourceA2456 + difference 5 0) (sourceB2456 + difference 0 5) sourceC2456) = raw33732 := by
      apply Matrix.ext; unfold tripleCharges sourceA2456 sourceB2456 sourceC2456 difference raw33732; decide +kernel
    rw [ha]
    exact (canonical33732 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2456 + difference 5 1) (sourceB2456 + difference 1 5) sourceC2456) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4678) := by
    have ha : (tripleCharges (sourceA2456 + difference 5 1) (sourceB2456 + difference 1 5) sourceC2456) = raw33733 := by
      apply Matrix.ext; unfold tripleCharges sourceA2456 sourceB2456 sourceC2456 difference raw33733; decide +kernel
    rw [ha]
    exact (canonical33733 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2456 + difference 5 2) (sourceB2456 + difference 2 5) sourceC2456) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4720) := by
    have ha : (tripleCharges (sourceA2456 + difference 5 2) (sourceB2456 + difference 2 5) sourceC2456) = raw33734 := by
      apply Matrix.ext; unfold tripleCharges sourceA2456 sourceB2456 sourceC2456 difference raw33734; decide +kernel
    rw [ha]
    exact (canonical33734 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2456 + difference 5 3) (sourceB2456 + difference 3 5) sourceC2456) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4800) := by
    have ha : (tripleCharges (sourceA2456 + difference 5 3) (sourceB2456 + difference 3 5) sourceC2456) = raw18207 := by
      apply Matrix.ext; unfold tripleCharges sourceA2456 sourceB2456 sourceC2456 difference raw18207; decide +kernel
    rw [ha]
    exact (canonical18207 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2456 + difference 5 4) (sourceB2456 + difference 4 5) sourceC2456) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4800) := by
    have ha : (tripleCharges (sourceA2456 + difference 5 4) (sourceB2456 + difference 4 5) sourceC2456) = raw33735 := by
      apply Matrix.ext; unfold tripleCharges sourceA2456 sourceB2456 sourceC2456 difference raw33735; decide +kernel
    rw [ha]
    exact (canonical33735 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2456 sourceB2456 sourceC2456
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2456, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic123
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reindexCheck1976 : Integer.Sparse.reindex keyMap MixedData.row1976 = numericRow1976 := by decide +kernel

theorem numericCheck1976 (x : Master → ℝ) : Integer.Sparse.eval numericRow1976 x =
    (51840 : ℝ) * reducedSource1976 x := by
  norm_num [numericRow1976, reducedSource1976, Integer.Sparse.eval, Sparse.eval, nodeValue4230, nodeValue4231, nodeValue4234, nodeValue4255, nodeValue4676, nodeValue4678, nodeValue4684, nodeValue4720, nodeValue4722, nodeValue4731, nodeValue4798, nodeValue4800, nodeValue4810, nodeValue4828, nodeValue4864, nodeValue4866, nodeValue4889, nodeValue5387, nodeValue5400, nodeValue5432, nodeValue5450]
  ring

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Rows123
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero1976 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1976 (mixedVector B) = 0 := by
  have h4230 : mixedVector B (Sum.inr 4230) = Sparse.eval nodeValue4230 (mixedVector B) := by
    change mixedMoment B node4230 node4230Labels = _
    exact sound4230 B hB hF
  have h4231 : mixedVector B (Sum.inr 4231) = Sparse.eval nodeValue4231 (mixedVector B) := by
    change mixedMoment B node4231 node4231Labels = _
    exact sound4231 B hB hF
  have h4234 : mixedVector B (Sum.inr 4234) = Sparse.eval nodeValue4234 (mixedVector B) := by
    change mixedMoment B node4234 node4234Labels = _
    exact sound4234 B hB hF
  have h4255 : mixedVector B (Sum.inr 4255) = Sparse.eval nodeValue4255 (mixedVector B) := by
    change mixedMoment B node4255 node4255Labels = _
    exact sound4255 B hB hF
  have h4676 : mixedVector B (Sum.inr 4676) = Sparse.eval nodeValue4676 (mixedVector B) := by
    change mixedMoment B node4676 node4676Labels = _
    exact sound4676 B hB hF
  have h4678 : mixedVector B (Sum.inr 4678) = Sparse.eval nodeValue4678 (mixedVector B) := by
    change mixedMoment B node4678 node4678Labels = _
    exact sound4678 B hB hF
  have h4684 : mixedVector B (Sum.inr 4684) = Sparse.eval nodeValue4684 (mixedVector B) := by
    change mixedMoment B node4684 node4684Labels = _
    exact sound4684 B hB hF
  have h4720 : mixedVector B (Sum.inr 4720) = Sparse.eval nodeValue4720 (mixedVector B) := by
    change mixedMoment B node4720 node4720Labels = _
    exact sound4720 B hB hF
  have h4722 : mixedVector B (Sum.inr 4722) = Sparse.eval nodeValue4722 (mixedVector B) := by
    change mixedMoment B node4722 node4722Labels = _
    exact sound4722 B hB hF
  have h4731 : mixedVector B (Sum.inr 4731) = Sparse.eval nodeValue4731 (mixedVector B) := by
    change mixedMoment B node4731 node4731Labels = _
    exact sound4731 B hB hF
  have h4798 : mixedVector B (Sum.inr 4798) = Sparse.eval nodeValue4798 (mixedVector B) := by
    change mixedMoment B node4798 node4798Labels = _
    exact sound4798 B hB hF
  have h4800 : mixedVector B (Sum.inr 4800) = Sparse.eval nodeValue4800 (mixedVector B) := by
    change mixedMoment B node4800 node4800Labels = _
    exact sound4800 B hB hF
  have h4810 : mixedVector B (Sum.inr 4810) = Sparse.eval nodeValue4810 (mixedVector B) := by
    change mixedMoment B node4810 node4810Labels = _
    exact sound4810 B hB hF
  have h4828 : mixedVector B (Sum.inr 4828) = Sparse.eval nodeValue4828 (mixedVector B) := by
    change mixedMoment B node4828 node4828Labels = _
    exact sound4828 B hB hF
  have h4864 : mixedVector B (Sum.inr 4864) = Sparse.eval nodeValue4864 (mixedVector B) := by
    change mixedMoment B node4864 node4864Labels = _
    exact sound4864 B hB hF
  have h4866 : mixedVector B (Sum.inr 4866) = Sparse.eval nodeValue4866 (mixedVector B) := by
    change mixedMoment B node4866 node4866Labels = _
    exact sound4866 B hB hF
  have h4889 : mixedVector B (Sum.inr 4889) = Sparse.eval nodeValue4889 (mixedVector B) := by
    change mixedMoment B node4889 node4889Labels = _
    exact sound4889 B hB hF
  have h5387 : mixedVector B (Sum.inr 5387) = Sparse.eval nodeValue5387 (mixedVector B) := by
    change mixedMoment B node5387 node5387Labels = _
    exact sound5387_e B hB hF
  have h5400 : mixedVector B (Sum.inr 5400) = Sparse.eval nodeValue5400 (mixedVector B) := by
    change mixedMoment B node5400 node5400Labels = _
    exact sound5400 B hB hF
  have h5432 : mixedVector B (Sum.inr 5432) = Sparse.eval nodeValue5432 (mixedVector B) := by
    change mixedMoment B node5432 node5432Labels = _
    exact sound5432 B hB hF
  have h5450 : mixedVector B (Sum.inr 5450) = Sparse.eval nodeValue5450 (mixedVector B) := by
    change mixedMoment B node5450 node5450Labels = _
    exact sound5450_e B hB hF
  simpa only [sourceForm2456, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4230, h4231, h4234, h4255, h4676, h4678, h4684, h4720, h4722, h4731, h4798, h4800, h4810, h4828, h4864, h4866, h4889, h5387, h5400, h5432, h5450, reducedSource1976] using sourceEq2456 B hB

theorem rowSound1976_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1976 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1976, numericCheck1976, reducedZero1976 B hB hF, mul_zero]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedSourceBridge.rowSound1976_e_oai := @OAI.MUB6.Certificate.MixedSourceBridge.rowSound1976_e_oai
