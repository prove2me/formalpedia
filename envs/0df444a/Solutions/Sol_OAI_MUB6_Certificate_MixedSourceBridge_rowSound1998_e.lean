-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedSourceBridge.rowSound1998_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-08T23:17:38.230195+00:00
-- url     : https://prove2.me/submissions/98e31da2-65fe-44d4-86a7-36da8caabfa2

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E070
import Definitions.Def_OAIQ106E086
import Definitions.Def_OAIQ106E088
import Definitions.Def_OAIQ106E092
import Definitions.Def_OAIQ106E093
import Definitions.Def_OAIQ106E094
import Definitions.Def_OAIQ106E097
import Definitions.Def_OAIQ106E189
import Definitions.Def_OAIQ106E106
import Definitions.Def_OAIQ106E107
import Definitions.Def_OAIQ106E119
import Definitions.Def_OAIQ106E121
import Definitions.Def_OAIQ106E126
import Definitions.Def_OAIQ106E140
import Definitions.Def_OAIQ106E147
import Definitions.Def_OAIQ106E170
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound5172_e

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

theorem canonical1656 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1656 raw1656Labels = mixedMoment B node4740 node4740Labels := by
  calc
    mixedMoment B raw1656 raw1656Labels = mixedMoment B raw1656step0 raw1656step0Labels := by
      have ha : raw1656step0 = (fun i j => raw1656 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1656step0 raw1656; decide +kernel
      have hl : raw1656step0Labels = raw1656Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1656 raw1656Labels permutation152 permutation4
    mixedMoment B raw1656step0 raw1656step0Labels = mixedMoment B raw1656step1 raw1656step1Labels := by
      have ha : raw1656step1 = raw1656step0 := by apply Matrix.ext; unfold raw1656step1 raw1656step0; decide +kernel
      have hl : raw1656step0Labels = labelEmbedding7 ∘ raw1656step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1656step0 raw1656step0Labels raw1656step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4740 node4740Labels := by rfl

theorem canonical1657 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1657 raw1657Labels = mixedMoment B node1913 node1913Labels := by
  calc
    mixedMoment B raw1657 raw1657Labels = mixedMoment B raw1657step0 raw1657step0Labels := by
      have ha : raw1657step0 = (fun i j => raw1657 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1657step0 raw1657; decide +kernel
      have hl : raw1657step0Labels = raw1657Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1657 raw1657Labels permutation152 permutation4
    _ = mixedMoment B node1913 node1913Labels := by rfl

theorem canonical1658 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1658 raw1658Labels = mixedMoment B node1922 node1922Labels := by
  calc
    mixedMoment B raw1658 raw1658Labels = mixedMoment B raw1658step0 raw1658step0Labels := by
      have ha : raw1658step0 = (fun i j => raw1658 (permutation170 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1658step0 raw1658; decide +kernel
      have hl : raw1658step0Labels = raw1658Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1658 raw1658Labels permutation170 permutation6
    mixedMoment B raw1658step0 raw1658step0Labels = mixedMoment B raw1658step1 raw1658step1Labels := by
      have ha : raw1658step1 = -raw1658step0 := by apply Matrix.ext; change ∀ i j, raw1658step1 i j = -(raw1658step0 i j); unfold raw1658step1 raw1658step0; decide +kernel
      have hl : raw1658step1Labels = raw1658step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1658step1 raw1658step1Labels = mixedMoment B raw1658step2 raw1658step2Labels := by
      have ha : raw1658step2 = raw1658step1 := by apply Matrix.ext; unfold raw1658step2 raw1658step1; decide +kernel
      have hl : raw1658step1Labels = labelEmbedding1 ∘ raw1658step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1658step1 raw1658step1Labels raw1658step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1922 node1922Labels := by rfl

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

theorem canonical1668 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1668 raw1668Labels = mixedMoment B node4747 node4747Labels := by
  calc
    mixedMoment B raw1668 raw1668Labels = mixedMoment B raw1668step0 raw1668step0Labels := by
      have ha : raw1668step0 = (fun i j => raw1668 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1668step0 raw1668; decide +kernel
      have hl : raw1668step0Labels = raw1668Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1668 raw1668Labels permutation32 permutation4
    mixedMoment B raw1668step0 raw1668step0Labels = mixedMoment B raw1668step1 raw1668step1Labels := by
      have ha : raw1668step1 = raw1668step0 := by apply Matrix.ext; unfold raw1668step1 raw1668step0; decide +kernel
      have hl : raw1668step0Labels = labelEmbedding7 ∘ raw1668step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1668step0 raw1668step0Labels raw1668step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4747 node4747Labels := by rfl

theorem canonical1669 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1669 raw1669Labels = mixedMoment B node1926 node1926Labels := by
  calc
    mixedMoment B raw1669 raw1669Labels = mixedMoment B raw1669step0 raw1669step0Labels := by
      have ha : raw1669step0 = (fun i j => raw1669 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1669step0 raw1669; decide +kernel
      have hl : raw1669step0Labels = raw1669Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1669 raw1669Labels permutation32 permutation4
    _ = mixedMoment B node1926 node1926Labels := by rfl

theorem canonical1670 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1670 raw1670Labels = mixedMoment B node1948 node1948Labels := by
  calc
    mixedMoment B raw1670 raw1670Labels = mixedMoment B raw1670step0 raw1670step0Labels := by
      have ha : raw1670step0 = (fun i j => raw1670 (permutation35 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1670step0 raw1670; decide +kernel
      have hl : raw1670step0Labels = raw1670Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1670 raw1670Labels permutation35 permutation6
    mixedMoment B raw1670step0 raw1670step0Labels = mixedMoment B raw1670step1 raw1670step1Labels := by
      have ha : raw1670step1 = -raw1670step0 := by apply Matrix.ext; change ∀ i j, raw1670step1 i j = -(raw1670step0 i j); unfold raw1670step1 raw1670step0; decide +kernel
      have hl : raw1670step1Labels = raw1670step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1670step1 raw1670step1Labels = mixedMoment B raw1670step2 raw1670step2Labels := by
      have ha : raw1670step2 = raw1670step1 := by apply Matrix.ext; unfold raw1670step2 raw1670step1; decide +kernel
      have hl : raw1670step1Labels = labelEmbedding1 ∘ raw1670step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1670step1 raw1670step1Labels raw1670step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1948 node1948Labels := by rfl

theorem canonical1674 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1674 raw1674Labels = mixedMoment B node4750 node4750Labels := by
  calc
    mixedMoment B raw1674 raw1674Labels = mixedMoment B raw1674step0 raw1674step0Labels := by
      have ha : raw1674step0 = (fun i j => raw1674 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1674step0 raw1674; decide +kernel
      have hl : raw1674step0Labels = raw1674Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1674 raw1674Labels permutation32 permutation4
    mixedMoment B raw1674step0 raw1674step0Labels = mixedMoment B raw1674step1 raw1674step1Labels := by
      have ha : raw1674step1 = raw1674step0 := by apply Matrix.ext; unfold raw1674step1 raw1674step0; decide +kernel
      have hl : raw1674step0Labels = labelEmbedding7 ∘ raw1674step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1674step0 raw1674step0Labels raw1674step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4750 node4750Labels := by rfl

theorem canonical1675 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1675 raw1675Labels = mixedMoment B node1929 node1929Labels := by
  calc
    mixedMoment B raw1675 raw1675Labels = mixedMoment B raw1675step0 raw1675step0Labels := by
      have ha : raw1675step0 = (fun i j => raw1675 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1675step0 raw1675; decide +kernel
      have hl : raw1675step0Labels = raw1675Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1675 raw1675Labels permutation32 permutation4
    _ = mixedMoment B node1929 node1929Labels := by rfl

theorem canonical1676 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1676 raw1676Labels = mixedMoment B node1949 node1949Labels := by
  calc
    mixedMoment B raw1676 raw1676Labels = mixedMoment B raw1676step0 raw1676step0Labels := by
      have ha : raw1676step0 = (fun i j => raw1676 (permutation35 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1676step0 raw1676; decide +kernel
      have hl : raw1676step0Labels = raw1676Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1676 raw1676Labels permutation35 permutation6
    mixedMoment B raw1676step0 raw1676step0Labels = mixedMoment B raw1676step1 raw1676step1Labels := by
      have ha : raw1676step1 = -raw1676step0 := by apply Matrix.ext; change ∀ i j, raw1676step1 i j = -(raw1676step0 i j); unfold raw1676step1 raw1676step0; decide +kernel
      have hl : raw1676step1Labels = raw1676step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1676step1 raw1676step1Labels = mixedMoment B raw1676step2 raw1676step2Labels := by
      have ha : raw1676step2 = raw1676step1 := by apply Matrix.ext; unfold raw1676step2 raw1676step1; decide +kernel
      have hl : raw1676step1Labels = labelEmbedding1 ∘ raw1676step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1676step1 raw1676step1Labels raw1676step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1949 node1949Labels := by rfl

theorem canonical1719 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1719 raw1719Labels = mixedMoment B node4787 node4787Labels := by
  calc
    mixedMoment B raw1719 raw1719Labels = mixedMoment B raw1719step0 raw1719step0Labels := by
      have ha : raw1719step0 = (fun i j => raw1719 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1719step0 raw1719; decide +kernel
      have hl : raw1719step0Labels = raw1719Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1719 raw1719Labels permutation152 permutation4
    mixedMoment B raw1719step0 raw1719step0Labels = mixedMoment B raw1719step1 raw1719step1Labels := by
      have ha : raw1719step1 = raw1719step0 := by apply Matrix.ext; unfold raw1719step1 raw1719step0; decide +kernel
      have hl : raw1719step0Labels = labelEmbedding7 ∘ raw1719step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1719step0 raw1719step0Labels raw1719step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4787 node4787Labels := by rfl

theorem canonical1720 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1720 raw1720Labels = mixedMoment B node2000 node2000Labels := by
  calc
    mixedMoment B raw1720 raw1720Labels = mixedMoment B raw1720step0 raw1720step0Labels := by
      have ha : raw1720step0 = (fun i j => raw1720 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1720step0 raw1720; decide +kernel
      have hl : raw1720step0Labels = raw1720Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1720 raw1720Labels permutation152 permutation4
    _ = mixedMoment B node2000 node2000Labels := by rfl

theorem canonical1721 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1721 raw1721Labels = mixedMoment B node2000 node2000Labels := by
  calc
    mixedMoment B raw1721 raw1721Labels = mixedMoment B raw1721step0 raw1721step0Labels := by
      have ha : raw1721step0 = (fun i j => raw1721 (permutation177 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1721step0 raw1721; decide +kernel
      have hl : raw1721step0Labels = raw1721Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1721 raw1721Labels permutation177 permutation6
    mixedMoment B raw1721step0 raw1721step0Labels = mixedMoment B raw1721step1 raw1721step1Labels := by
      have ha : raw1721step1 = -raw1721step0 := by apply Matrix.ext; change ∀ i j, raw1721step1 i j = -(raw1721step0 i j); unfold raw1721step1 raw1721step0; decide +kernel
      have hl : raw1721step1Labels = raw1721step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1721step1 raw1721step1Labels = mixedMoment B raw1721step2 raw1721step2Labels := by
      have ha : raw1721step2 = raw1721step1 := by apply Matrix.ext; unfold raw1721step2 raw1721step1; decide +kernel
      have hl : raw1721step1Labels = labelEmbedding1 ∘ raw1721step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1721step1 raw1721step1Labels raw1721step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2000 node2000Labels := by rfl

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

theorem canonical1767 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1767 raw1767Labels = mixedMoment B node4835 node4835Labels := by
  calc
    mixedMoment B raw1767 raw1767Labels = mixedMoment B raw1767step0 raw1767step0Labels := by
      have ha : raw1767step0 = (fun i j => raw1767 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1767step0 raw1767; decide +kernel
      have hl : raw1767step0Labels = raw1767Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1767 raw1767Labels permutation32 permutation4
    mixedMoment B raw1767step0 raw1767step0Labels = mixedMoment B raw1767step1 raw1767step1Labels := by
      have ha : raw1767step1 = raw1767step0 := by apply Matrix.ext; unfold raw1767step1 raw1767step0; decide +kernel
      have hl : raw1767step0Labels = labelEmbedding7 ∘ raw1767step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1767step0 raw1767step0Labels raw1767step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4835 node4835Labels := by rfl

theorem canonical1768 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1768 raw1768Labels = mixedMoment B node2054 node2054Labels := by
  calc
    mixedMoment B raw1768 raw1768Labels = mixedMoment B raw1768step0 raw1768step0Labels := by
      have ha : raw1768step0 = (fun i j => raw1768 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1768step0 raw1768; decide +kernel
      have hl : raw1768step0Labels = raw1768Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1768 raw1768Labels permutation32 permutation4
    _ = mixedMoment B node2054 node2054Labels := by rfl

theorem canonical1769 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1769 raw1769Labels = mixedMoment B node2206 node2206Labels := by
  calc
    mixedMoment B raw1769 raw1769Labels = mixedMoment B raw1769step0 raw1769step0Labels := by
      have ha : raw1769step0 = (fun i j => raw1769 (permutation33 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1769step0 raw1769; decide +kernel
      have hl : raw1769step0Labels = raw1769Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1769 raw1769Labels permutation33 permutation6
    mixedMoment B raw1769step0 raw1769step0Labels = mixedMoment B raw1769step1 raw1769step1Labels := by
      have ha : raw1769step1 = -raw1769step0 := by apply Matrix.ext; change ∀ i j, raw1769step1 i j = -(raw1769step0 i j); unfold raw1769step1 raw1769step0; decide +kernel
      have hl : raw1769step1Labels = raw1769step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1769step1 raw1769step1Labels = mixedMoment B raw1769step2 raw1769step2Labels := by
      have ha : raw1769step2 = raw1769step1 := by apply Matrix.ext; unfold raw1769step2 raw1769step1; decide +kernel
      have hl : raw1769step1Labels = labelEmbedding1 ∘ raw1769step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1769step1 raw1769step1Labels raw1769step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2206 node2206Labels := by rfl

theorem canonical1770 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1770 raw1770Labels = mixedMoment B node4839 node4839Labels := by
  calc
    mixedMoment B raw1770 raw1770Labels = mixedMoment B raw1770step0 raw1770step0Labels := by
      have ha : raw1770step0 = (fun i j => raw1770 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1770step0 raw1770; decide +kernel
      have hl : raw1770step0Labels = raw1770Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1770 raw1770Labels permutation32 permutation4
    mixedMoment B raw1770step0 raw1770step0Labels = mixedMoment B raw1770step1 raw1770step1Labels := by
      have ha : raw1770step1 = raw1770step0 := by apply Matrix.ext; unfold raw1770step1 raw1770step0; decide +kernel
      have hl : raw1770step0Labels = labelEmbedding7 ∘ raw1770step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1770step0 raw1770step0Labels raw1770step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4839 node4839Labels := by rfl

theorem canonical1771 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1771 raw1771Labels = mixedMoment B node2058 node2058Labels := by
  calc
    mixedMoment B raw1771 raw1771Labels = mixedMoment B raw1771step0 raw1771step0Labels := by
      have ha : raw1771step0 = (fun i j => raw1771 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1771step0 raw1771; decide +kernel
      have hl : raw1771step0Labels = raw1771Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1771 raw1771Labels permutation32 permutation4
    _ = mixedMoment B node2058 node2058Labels := by rfl

theorem canonical1772 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1772 raw1772Labels = mixedMoment B node2216 node2216Labels := by
  calc
    mixedMoment B raw1772 raw1772Labels = mixedMoment B raw1772step0 raw1772step0Labels := by
      have ha : raw1772step0 = (fun i j => raw1772 (permutation36 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1772step0 raw1772; decide +kernel
      have hl : raw1772step0Labels = raw1772Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1772 raw1772Labels permutation36 permutation6
    mixedMoment B raw1772step0 raw1772step0Labels = mixedMoment B raw1772step1 raw1772step1Labels := by
      have ha : raw1772step1 = -raw1772step0 := by apply Matrix.ext; change ∀ i j, raw1772step1 i j = -(raw1772step0 i j); unfold raw1772step1 raw1772step0; decide +kernel
      have hl : raw1772step1Labels = raw1772step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1772step1 raw1772step1Labels = mixedMoment B raw1772step2 raw1772step2Labels := by
      have ha : raw1772step2 = raw1772step1 := by apply Matrix.ext; unfold raw1772step2 raw1772step1; decide +kernel
      have hl : raw1772step1Labels = labelEmbedding1 ∘ raw1772step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1772step1 raw1772step1Labels raw1772step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2216 node2216Labels := by rfl

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

theorem canonical1800 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1800 raw1800Labels = mixedMoment B node4869 node4869Labels := by
  calc
    mixedMoment B raw1800 raw1800Labels = mixedMoment B raw1800step0 raw1800step0Labels := by
      have ha : raw1800step0 = (fun i j => raw1800 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1800step0 raw1800; decide +kernel
      have hl : raw1800step0Labels = raw1800Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1800 raw1800Labels permutation32 permutation4
    mixedMoment B raw1800step0 raw1800step0Labels = mixedMoment B raw1800step1 raw1800step1Labels := by
      have ha : raw1800step1 = raw1800step0 := by apply Matrix.ext; unfold raw1800step1 raw1800step0; decide +kernel
      have hl : raw1800step0Labels = labelEmbedding7 ∘ raw1800step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1800step0 raw1800step0Labels raw1800step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4869 node4869Labels := by rfl

theorem canonical1801 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1801 raw1801Labels = mixedMoment B node2110 node2110Labels := by
  calc
    mixedMoment B raw1801 raw1801Labels = mixedMoment B raw1801step0 raw1801step0Labels := by
      have ha : raw1801step0 = (fun i j => raw1801 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1801step0 raw1801; decide +kernel
      have hl : raw1801step0Labels = raw1801Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1801 raw1801Labels permutation32 permutation4
    _ = mixedMoment B node2110 node2110Labels := by rfl

theorem canonical1802 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1802 raw1802Labels = mixedMoment B node2275 node2275Labels := by
  calc
    mixedMoment B raw1802 raw1802Labels = mixedMoment B raw1802step0 raw1802step0Labels := by
      have ha : raw1802step0 = (fun i j => raw1802 (permutation50 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1802step0 raw1802; decide +kernel
      have hl : raw1802step0Labels = raw1802Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1802 raw1802Labels permutation50 permutation6
    mixedMoment B raw1802step0 raw1802step0Labels = mixedMoment B raw1802step1 raw1802step1Labels := by
      have ha : raw1802step1 = -raw1802step0 := by apply Matrix.ext; change ∀ i j, raw1802step1 i j = -(raw1802step0 i j); unfold raw1802step1 raw1802step0; decide +kernel
      have hl : raw1802step1Labels = raw1802step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1802step1 raw1802step1Labels = mixedMoment B raw1802step2 raw1802step2Labels := by
      have ha : raw1802step2 = raw1802step1 := by apply Matrix.ext; unfold raw1802step2 raw1802step1; decide +kernel
      have hl : raw1802step1Labels = labelEmbedding1 ∘ raw1802step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1802step1 raw1802step1Labels raw1802step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2275 node2275Labels := by rfl

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

theorem canonical2130 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2130 raw2130Labels = mixedMoment B node5105 node5105Labels := by
  calc
    mixedMoment B raw2130 raw2130Labels = mixedMoment B raw2130step0 raw2130step0Labels := by
      have ha : raw2130step0 = (fun i j => raw2130 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2130step0 raw2130; decide +kernel
      have hl : raw2130step0Labels = raw2130Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2130 raw2130Labels permutation32 permutation4
    mixedMoment B raw2130step0 raw2130step0Labels = mixedMoment B raw2130step1 raw2130step1Labels := by
      have ha : raw2130step1 = raw2130step0 := by apply Matrix.ext; unfold raw2130step1 raw2130step0; decide +kernel
      have hl : raw2130step0Labels = labelEmbedding7 ∘ raw2130step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2130step0 raw2130step0Labels raw2130step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5105 node5105Labels := by rfl

theorem canonical2131 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2131 raw2131Labels = mixedMoment B node2515 node2515Labels := by
  calc
    mixedMoment B raw2131 raw2131Labels = mixedMoment B raw2131step0 raw2131step0Labels := by
      have ha : raw2131step0 = (fun i j => raw2131 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2131step0 raw2131; decide +kernel
      have hl : raw2131step0Labels = raw2131Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2131 raw2131Labels permutation32 permutation4
    _ = mixedMoment B node2515 node2515Labels := by rfl

theorem canonical2132 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2132 raw2132Labels = mixedMoment B node3479 node3479Labels := by
  calc
    mixedMoment B raw2132 raw2132Labels = mixedMoment B raw2132step0 raw2132step0Labels := by
      have ha : raw2132step0 = (fun i j => raw2132 (permutation36 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2132step0 raw2132; decide +kernel
      have hl : raw2132step0Labels = raw2132Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2132 raw2132Labels permutation36 permutation6
    mixedMoment B raw2132step0 raw2132step0Labels = mixedMoment B raw2132step1 raw2132step1Labels := by
      have ha : raw2132step1 = -raw2132step0 := by apply Matrix.ext; change ∀ i j, raw2132step1 i j = -(raw2132step0 i j); unfold raw2132step1 raw2132step0; decide +kernel
      have hl : raw2132step1Labels = raw2132step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2132step1 raw2132step1Labels = mixedMoment B raw2132step2 raw2132step2Labels := by
      have ha : raw2132step2 = raw2132step1 := by apply Matrix.ext; unfold raw2132step2 raw2132step1; decide +kernel
      have hl : raw2132step1Labels = labelEmbedding1 ∘ raw2132step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2132step1 raw2132step1Labels raw2132step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3479 node3479Labels := by rfl

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

theorem canonical2202 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2202 raw2202Labels = mixedMoment B node5170 node5170Labels := by
  calc
    mixedMoment B raw2202 raw2202Labels = mixedMoment B raw2202step0 raw2202step0Labels := by
      have ha : raw2202step0 = (fun i j => raw2202 (permutation32 i) (permutation5 j)) := by apply Matrix.ext; unfold raw2202step0 raw2202; decide +kernel
      have hl : raw2202step0Labels = raw2202Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2202 raw2202Labels permutation32 permutation5
    mixedMoment B raw2202step0 raw2202step0Labels = mixedMoment B raw2202step1 raw2202step1Labels := by
      have ha : raw2202step1 = raw2202step0 := by apply Matrix.ext; unfold raw2202step1 raw2202step0; decide +kernel
      have hl : raw2202step0Labels = labelEmbedding8 ∘ raw2202step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2202step0 raw2202step0Labels raw2202step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5170 node5170Labels := by rfl

theorem canonical2203 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2203 raw2203Labels = mixedMoment B node2954 node2954Labels := by
  calc
    mixedMoment B raw2203 raw2203Labels = mixedMoment B raw2203step0 raw2203step0Labels := by
      have ha : raw2203step0 = (fun i j => raw2203 (permutation34 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2203step0 raw2203; decide +kernel
      have hl : raw2203step0Labels = raw2203Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2203 raw2203Labels permutation34 permutation4
    _ = mixedMoment B node2954 node2954Labels := by rfl

theorem canonical2204 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2204 raw2204Labels = mixedMoment B node3606 node3606Labels := by
  calc
    mixedMoment B raw2204 raw2204Labels = mixedMoment B raw2204step0 raw2204step0Labels := by
      have ha : raw2204step0 = (fun i j => raw2204 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw2204step0 raw2204; decide +kernel
      have hl : raw2204step0Labels = raw2204Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2204 raw2204Labels permutation33 permutation3
    mixedMoment B raw2204step0 raw2204step0Labels = mixedMoment B raw2204step1 raw2204step1Labels := by
      have ha : raw2204step1 = -raw2204step0 := by apply Matrix.ext; change ∀ i j, raw2204step1 i j = -(raw2204step0 i j); unfold raw2204step1 raw2204step0; decide +kernel
      have hl : raw2204step1Labels = raw2204step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2204step1 raw2204step1Labels = mixedMoment B raw2204step2 raw2204step2Labels := by
      have ha : raw2204step2 = raw2204step1 := by apply Matrix.ext; unfold raw2204step2 raw2204step1; decide +kernel
      have hl : raw2204step1Labels = labelEmbedding1 ∘ raw2204step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2204step1 raw2204step1Labels raw2204step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3606 node3606Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical251
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical32230 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32230 raw32230Labels = mixedMoment B node4869 node4869Labels := by
  calc
    mixedMoment B raw32230 raw32230Labels = mixedMoment B raw32230step0 raw32230step0Labels := by
      have hz : ∀ j, raw32230 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32230step0 = (fun i j => raw32230 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32230step0 raw32230; decide +kernel
      have hl : raw32230step0Labels = raw32230Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32230 raw32230Labels permutation346 hz
    mixedMoment B raw32230step0 raw32230step0Labels = mixedMoment B raw32230step1 raw32230step1Labels := by
      have ha : raw32230step1 = (fun i j => raw32230step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw32230step1 raw32230step0; decide +kernel
      have hl : raw32230step1Labels = raw32230step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32230step0 raw32230step0Labels permutation32 permutation6
    mixedMoment B raw32230step1 raw32230step1Labels = mixedMoment B raw32230step2 raw32230step2Labels := by
      have ha : raw32230step2 = raw32230step1 := by apply Matrix.ext; unfold raw32230step2 raw32230step1; decide +kernel
      have hl : raw32230step1Labels = labelEmbedding9 ∘ raw32230step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32230step1 raw32230step1Labels raw32230step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4869 node4869Labels := by rfl

theorem canonical32235 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32235 raw32235Labels = mixedMoment B node4805 node4805Labels := by
  calc
    mixedMoment B raw32235 raw32235Labels = mixedMoment B raw32235step0 raw32235step0Labels := by
      have ha : raw32235step0 = (fun i j => raw32235 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw32235step0 raw32235; decide +kernel
      have hl : raw32235step0Labels = raw32235Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32235 raw32235Labels permutation152 permutation6
    mixedMoment B raw32235step0 raw32235step0Labels = mixedMoment B raw32235step1 raw32235step1Labels := by
      have ha : raw32235step1 = raw32235step0 := by apply Matrix.ext; unfold raw32235step1 raw32235step0; decide +kernel
      have hl : raw32235step0Labels = labelEmbedding9 ∘ raw32235step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32235step0 raw32235step0Labels raw32235step1Labels labelEmbedding9 hl
    _ = mixedMoment B node4805 node4805Labels := by rfl

theorem canonical32241 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32241 raw32241Labels = mixedMoment B node5105 node5105Labels := by
  calc
    mixedMoment B raw32241 raw32241Labels = mixedMoment B raw32241step0 raw32241step0Labels := by
      have hz : ∀ j, raw32241 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32241step0 = (fun i j => raw32241 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32241step0 raw32241; decide +kernel
      have hl : raw32241step0Labels = raw32241Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32241 raw32241Labels permutation346 hz
    mixedMoment B raw32241step0 raw32241step0Labels = mixedMoment B raw32241step1 raw32241step1Labels := by
      have ha : raw32241step1 = (fun i j => raw32241step0 (permutation34 i) (permutation6 j)) := by apply Matrix.ext; unfold raw32241step1 raw32241step0; decide +kernel
      have hl : raw32241step1Labels = raw32241step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32241step0 raw32241step0Labels permutation34 permutation6
    mixedMoment B raw32241step1 raw32241step1Labels = mixedMoment B raw32241step2 raw32241step2Labels := by
      have ha : raw32241step2 = raw32241step1 := by apply Matrix.ext; unfold raw32241step2 raw32241step1; decide +kernel
      have hl : raw32241step1Labels = labelEmbedding9 ∘ raw32241step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32241step1 raw32241step1Labels raw32241step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5105 node5105Labels := by rfl

theorem canonical32242 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32242 raw32242Labels = mixedMoment B node5138 node5138Labels := by
  calc
    mixedMoment B raw32242 raw32242Labels = mixedMoment B raw32242step0 raw32242step0Labels := by
      have ha : raw32242step0 = (fun i j => raw32242 (permutation154 i) (permutation6 j)) := by apply Matrix.ext; unfold raw32242step0 raw32242; decide +kernel
      have hl : raw32242step0Labels = raw32242Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32242 raw32242Labels permutation154 permutation6
    mixedMoment B raw32242step0 raw32242step0Labels = mixedMoment B raw32242step1 raw32242step1Labels := by
      have ha : raw32242step1 = raw32242step0 := by apply Matrix.ext; unfold raw32242step1 raw32242step0; decide +kernel
      have hl : raw32242step0Labels = labelEmbedding9 ∘ raw32242step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32242step0 raw32242step0Labels raw32242step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5138 node5138Labels := by rfl

theorem canonical32243 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32243 raw32243Labels = mixedMoment B node5170 node5170Labels := by
  calc
    mixedMoment B raw32243 raw32243Labels = mixedMoment B raw32243step0 raw32243step0Labels := by
      have hz : ∀ j, raw32243 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32243step0 = (fun i j => raw32243 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32243step0 raw32243; decide +kernel
      have hl : raw32243step0Labels = raw32243Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32243 raw32243Labels permutation346 hz
    mixedMoment B raw32243step0 raw32243step0Labels = mixedMoment B raw32243step1 raw32243step1Labels := by
      have ha : raw32243step1 = (fun i j => raw32243step0 (permutation34 i) (permutation6 j)) := by apply Matrix.ext; unfold raw32243step1 raw32243step0; decide +kernel
      have hl : raw32243step1Labels = raw32243step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32243step0 raw32243step0Labels permutation34 permutation6
    mixedMoment B raw32243step1 raw32243step1Labels = mixedMoment B raw32243step2 raw32243step2Labels := by
      have ha : raw32243step2 = raw32243step1 := by apply Matrix.ext; unfold raw32243step2 raw32243step1; decide +kernel
      have hl : raw32243step1Labels = labelEmbedding9 ∘ raw32243step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32243step1 raw32243step1Labels raw32243step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5170 node5170Labels := by rfl

theorem canonical32244 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32244 raw32244Labels = mixedMoment B node5173 node5173Labels := by
  calc
    mixedMoment B raw32244 raw32244Labels = mixedMoment B raw32244step0 raw32244step0Labels := by
      have hz : ∀ j, raw32244 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32244step0 = (fun i j => raw32244 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32244step0 raw32244; decide +kernel
      have hl : raw32244step0Labels = raw32244Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32244 raw32244Labels permutation346 hz
    mixedMoment B raw32244step0 raw32244step0Labels = mixedMoment B raw32244step1 raw32244step1Labels := by
      have ha : raw32244step1 = (fun i j => raw32244step0 (permutation34 i) (permutation6 j)) := by apply Matrix.ext; unfold raw32244step1 raw32244step0; decide +kernel
      have hl : raw32244step1Labels = raw32244step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32244step0 raw32244step0Labels permutation34 permutation6
    mixedMoment B raw32244step1 raw32244step1Labels = mixedMoment B raw32244step2 raw32244step2Labels := by
      have ha : raw32244step2 = raw32244step1 := by apply Matrix.ext; unfold raw32244step2 raw32244step1; decide +kernel
      have hl : raw32244step1Labels = labelEmbedding9 ∘ raw32244step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32244step1 raw32244step1Labels raw32244step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5173 node5173Labels := by rfl

theorem canonical32245 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32245 raw32245Labels = mixedMoment B node4839 node4839Labels := by
  calc
    mixedMoment B raw32245 raw32245Labels = mixedMoment B raw32245step0 raw32245step0Labels := by
      have hz : ∀ j, raw32245 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32245step0 = (fun i j => raw32245 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32245step0 raw32245; decide +kernel
      have hl : raw32245step0Labels = raw32245Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32245 raw32245Labels permutation346 hz
    mixedMoment B raw32245step0 raw32245step0Labels = mixedMoment B raw32245step1 raw32245step1Labels := by
      have ha : raw32245step1 = (fun i j => raw32245step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw32245step1 raw32245step0; decide +kernel
      have hl : raw32245step1Labels = raw32245step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32245step0 raw32245step0Labels permutation32 permutation6
    mixedMoment B raw32245step1 raw32245step1Labels = mixedMoment B raw32245step2 raw32245step2Labels := by
      have ha : raw32245step2 = raw32245step1 := by apply Matrix.ext; unfold raw32245step2 raw32245step1; decide +kernel
      have hl : raw32245step1Labels = labelEmbedding9 ∘ raw32245step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32245step1 raw32245step1Labels raw32245step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4839 node4839Labels := by rfl

theorem canonical32250 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32250 raw32250Labels = mixedMoment B node4838 node4838Labels := by
  calc
    mixedMoment B raw32250 raw32250Labels = mixedMoment B raw32250step0 raw32250step0Labels := by
      have hz : ∀ j, raw32250 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32250step0 = (fun i j => raw32250 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32250step0 raw32250; decide +kernel
      have hl : raw32250step0Labels = raw32250Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32250 raw32250Labels permutation346 hz
    mixedMoment B raw32250step0 raw32250step0Labels = mixedMoment B raw32250step1 raw32250step1Labels := by
      have ha : raw32250step1 = (fun i j => raw32250step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw32250step1 raw32250step0; decide +kernel
      have hl : raw32250step1Labels = raw32250step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32250step0 raw32250step0Labels permutation32 permutation6
    mixedMoment B raw32250step1 raw32250step1Labels = mixedMoment B raw32250step2 raw32250step2Labels := by
      have ha : raw32250step2 = raw32250step1 := by apply Matrix.ext; unfold raw32250step2 raw32250step1; decide +kernel
      have hl : raw32250step1Labels = labelEmbedding9 ∘ raw32250step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32250step1 raw32250step1Labels raw32250step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4838 node4838Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical253
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical32487 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32487 raw32487Labels = mixedMoment B node5172 node5172Labels := by
  calc
    mixedMoment B raw32487 raw32487Labels = mixedMoment B raw32487step0 raw32487step0Labels := by
      have hz : ∀ j, raw32487 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32487step0 = (fun i j => raw32487 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32487step0 raw32487; decide +kernel
      have hl : raw32487step0Labels = raw32487Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32487 raw32487Labels permutation346 hz
    mixedMoment B raw32487step0 raw32487step0Labels = mixedMoment B raw32487step1 raw32487step1Labels := by
      have ha : raw32487step1 = (fun i j => raw32487step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw32487step1 raw32487step0; decide +kernel
      have hl : raw32487step1Labels = raw32487step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32487step0 raw32487step0Labels permutation32 permutation6
    mixedMoment B raw32487step1 raw32487step1Labels = mixedMoment B raw32487step2 raw32487step2Labels := by
      have ha : raw32487step2 = raw32487step1 := by apply Matrix.ext; unfold raw32487step2 raw32487step1; decide +kernel
      have hl : raw32487step1Labels = labelEmbedding9 ∘ raw32487step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32487step1 raw32487step1Labels raw32487step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5172 node5172Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical257
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical32906 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32906 raw32906Labels = mixedMoment B node4787 node4787Labels := by
  calc
    mixedMoment B raw32906 raw32906Labels = mixedMoment B raw32906step0 raw32906step0Labels := by
      have ha : raw32906step0 = (fun i j => raw32906 (permutation179 i) (permutation4 j)) := by apply Matrix.ext; unfold raw32906step0 raw32906; decide +kernel
      have hl : raw32906step0Labels = raw32906Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32906 raw32906Labels permutation179 permutation4
    mixedMoment B raw32906step0 raw32906step0Labels = mixedMoment B raw32906step1 raw32906step1Labels := by
      have ha : raw32906step1 = -raw32906step0 := by apply Matrix.ext; change ∀ i j, raw32906step1 i j = -(raw32906step0 i j); unfold raw32906step1 raw32906step0; decide +kernel
      have hl : raw32906step1Labels = raw32906step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32906step1 raw32906step1Labels = mixedMoment B raw32906step2 raw32906step2Labels := by
      have ha : raw32906step2 = raw32906step1 := by apply Matrix.ext; unfold raw32906step2 raw32906step1; decide +kernel
      have hl : raw32906step1Labels = labelEmbedding7 ∘ raw32906step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32906step1 raw32906step1Labels raw32906step2Labels labelEmbedding7 hl
    _ = mixedMoment B node4787 node4787Labels := by rfl

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

theorem canonical33558 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33558 raw33558Labels = mixedMoment B node4471 node4471Labels := by
  calc
    mixedMoment B raw33558 raw33558Labels = mixedMoment B raw33558step0 raw33558step0Labels := by
      have hz : ∀ j, raw33558 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33558step0 = (fun i j => raw33558 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33558step0 raw33558; decide +kernel
      have hl : raw33558step0Labels = raw33558Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33558 raw33558Labels permutation346 hz
    mixedMoment B raw33558step0 raw33558step0Labels = mixedMoment B raw33558step1 raw33558step1Labels := by
      have ha : raw33558step1 = (fun i j => raw33558step0 (permutation51 i) (permutation4 j)) := by apply Matrix.ext; unfold raw33558step1 raw33558step0; decide +kernel
      have hl : raw33558step1Labels = raw33558step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33558step0 raw33558step0Labels permutation51 permutation4
    mixedMoment B raw33558step1 raw33558step1Labels = mixedMoment B raw33558step2 raw33558step2Labels := by
      have ha : raw33558step2 = -raw33558step1 := by apply Matrix.ext; change ∀ i j, raw33558step2 i j = -(raw33558step1 i j); unfold raw33558step2 raw33558step1; decide +kernel
      have hl : raw33558step2Labels = raw33558step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33558step2 raw33558step2Labels = mixedMoment B raw33558step3 raw33558step3Labels := by
      have ha : raw33558step3 = raw33558step2 := by apply Matrix.ext; unfold raw33558step3 raw33558step2; decide +kernel
      have hl : raw33558step2Labels = labelEmbedding7 ∘ raw33558step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33558step2 raw33558step2Labels raw33558step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4471 node4471Labels := by rfl

theorem canonical33559 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33559 raw33559Labels = mixedMoment B node4813 node4813Labels := by
  calc
    mixedMoment B raw33559 raw33559Labels = mixedMoment B raw33559step0 raw33559step0Labels := by
      have ha : raw33559step0 = (fun i j => raw33559 (permutation195 i) (permutation4 j)) := by apply Matrix.ext; unfold raw33559step0 raw33559; decide +kernel
      have hl : raw33559step0Labels = raw33559Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33559 raw33559Labels permutation195 permutation4
    mixedMoment B raw33559step0 raw33559step0Labels = mixedMoment B raw33559step1 raw33559step1Labels := by
      have ha : raw33559step1 = -raw33559step0 := by apply Matrix.ext; change ∀ i j, raw33559step1 i j = -(raw33559step0 i j); unfold raw33559step1 raw33559step0; decide +kernel
      have hl : raw33559step1Labels = raw33559step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33559step1 raw33559step1Labels = mixedMoment B raw33559step2 raw33559step2Labels := by
      have ha : raw33559step2 = raw33559step1 := by apply Matrix.ext; unfold raw33559step2 raw33559step1; decide +kernel
      have hl : raw33559step1Labels = labelEmbedding7 ∘ raw33559step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33559step1 raw33559step1Labels raw33559step2Labels labelEmbedding7 hl
    _ = mixedMoment B node4813 node4813Labels := by rfl

theorem canonical33560 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33560 raw33560Labels = mixedMoment B node4867 node4867Labels := by
  calc
    mixedMoment B raw33560 raw33560Labels = mixedMoment B raw33560step0 raw33560step0Labels := by
      have hz : ∀ j, raw33560 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33560step0 = (fun i j => raw33560 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33560step0 raw33560; decide +kernel
      have hl : raw33560step0Labels = raw33560Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33560 raw33560Labels permutation346 hz
    mixedMoment B raw33560step0 raw33560step0Labels = mixedMoment B raw33560step1 raw33560step1Labels := by
      have ha : raw33560step1 = (fun i j => raw33560step0 (permutation34 i) (permutation6 j)) := by apply Matrix.ext; unfold raw33560step1 raw33560step0; decide +kernel
      have hl : raw33560step1Labels = raw33560step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33560step0 raw33560step0Labels permutation34 permutation6
    mixedMoment B raw33560step1 raw33560step1Labels = mixedMoment B raw33560step2 raw33560step2Labels := by
      have ha : raw33560step2 = raw33560step1 := by apply Matrix.ext; unfold raw33560step2 raw33560step1; decide +kernel
      have hl : raw33560step1Labels = labelEmbedding9 ∘ raw33560step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33560step1 raw33560step1Labels raw33560step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4867 node4867Labels := by rfl

theorem canonical33561 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33561 raw33561Labels = mixedMoment B node4870 node4870Labels := by
  calc
    mixedMoment B raw33561 raw33561Labels = mixedMoment B raw33561step0 raw33561step0Labels := by
      have hz : ∀ j, raw33561 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33561step0 = (fun i j => raw33561 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33561step0 raw33561; decide +kernel
      have hl : raw33561step0Labels = raw33561Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33561 raw33561Labels permutation346 hz
    mixedMoment B raw33561step0 raw33561step0Labels = mixedMoment B raw33561step1 raw33561step1Labels := by
      have ha : raw33561step1 = (fun i j => raw33561step0 (permutation34 i) (permutation6 j)) := by apply Matrix.ext; unfold raw33561step1 raw33561step0; decide +kernel
      have hl : raw33561step1Labels = raw33561step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33561step0 raw33561step0Labels permutation34 permutation6
    mixedMoment B raw33561step1 raw33561step1Labels = mixedMoment B raw33561step2 raw33561step2Labels := by
      have ha : raw33561step2 = raw33561step1 := by apply Matrix.ext; unfold raw33561step2 raw33561step1; decide +kernel
      have hl : raw33561step1Labels = labelEmbedding9 ∘ raw33561step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33561step1 raw33561step1Labels raw33561step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4870 node4870Labels := by rfl

theorem canonical33649 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33649 raw33649Labels = mixedMoment B node4835 node4835Labels := by
  calc
    mixedMoment B raw33649 raw33649Labels = mixedMoment B raw33649step0 raw33649step0Labels := by
      have hz : ∀ j, raw33649 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33649step0 = (fun i j => raw33649 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33649step0 raw33649; decide +kernel
      have hl : raw33649step0Labels = raw33649Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33649 raw33649Labels permutation346 hz
    mixedMoment B raw33649step0 raw33649step0Labels = mixedMoment B raw33649step1 raw33649step1Labels := by
      have ha : raw33649step1 = (fun i j => raw33649step0 (permutation34 i) (permutation6 j)) := by apply Matrix.ext; unfold raw33649step1 raw33649step0; decide +kernel
      have hl : raw33649step1Labels = raw33649step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33649step0 raw33649step0Labels permutation34 permutation6
    mixedMoment B raw33649step1 raw33649step1Labels = mixedMoment B raw33649step2 raw33649step2Labels := by
      have ha : raw33649step2 = raw33649step1 := by apply Matrix.ext; unfold raw33649step2 raw33649step1; decide +kernel
      have hl : raw33649step1Labels = labelEmbedding9 ∘ raw33649step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33649step1 raw33649step1Labels raw33649step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4835 node4835Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical264
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical33866 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33866 raw33866Labels = mixedMoment B node4407 node4407Labels := by
  calc
    mixedMoment B raw33866 raw33866Labels = mixedMoment B raw33866step0 raw33866step0Labels := by
      have ha : raw33866step0 = (fun i j => raw33866 (permutation171 i) (permutation4 j)) := by apply Matrix.ext; unfold raw33866step0 raw33866; decide +kernel
      have hl : raw33866step0Labels = raw33866Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33866 raw33866Labels permutation171 permutation4
    mixedMoment B raw33866step0 raw33866step0Labels = mixedMoment B raw33866step1 raw33866step1Labels := by
      have ha : raw33866step1 = -raw33866step0 := by apply Matrix.ext; change ∀ i j, raw33866step1 i j = -(raw33866step0 i j); unfold raw33866step1 raw33866step0; decide +kernel
      have hl : raw33866step1Labels = raw33866step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33866step1 raw33866step1Labels = mixedMoment B raw33866step2 raw33866step2Labels := by
      have ha : raw33866step2 = raw33866step1 := by apply Matrix.ext; unfold raw33866step2 raw33866step1; decide +kernel
      have hl : raw33866step1Labels = labelEmbedding7 ∘ raw33866step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33866step1 raw33866step1Labels raw33866step2Labels labelEmbedding7 hl
    _ = mixedMoment B node4407 node4407Labels := by rfl

theorem canonical33867 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33867 raw33867Labels = mixedMoment B node4740 node4740Labels := by
  calc
    mixedMoment B raw33867 raw33867Labels = mixedMoment B raw33867step0 raw33867step0Labels := by
      have ha : raw33867step0 = (fun i j => raw33867 (permutation154 i) (permutation6 j)) := by apply Matrix.ext; unfold raw33867step0 raw33867; decide +kernel
      have hl : raw33867step0Labels = raw33867Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33867 raw33867Labels permutation154 permutation6
    mixedMoment B raw33867step0 raw33867step0Labels = mixedMoment B raw33867step1 raw33867step1Labels := by
      have ha : raw33867step1 = raw33867step0 := by apply Matrix.ext; unfold raw33867step1 raw33867step0; decide +kernel
      have hl : raw33867step0Labels = labelEmbedding9 ∘ raw33867step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33867step0 raw33867step0Labels raw33867step1Labels labelEmbedding9 hl
    _ = mixedMoment B node4740 node4740Labels := by rfl

theorem canonical33868 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33868 raw33868Labels = mixedMoment B node4803 node4803Labels := by
  calc
    mixedMoment B raw33868 raw33868Labels = mixedMoment B raw33868step0 raw33868step0Labels := by
      have ha : raw33868step0 = (fun i j => raw33868 (permutation154 i) (permutation6 j)) := by apply Matrix.ext; unfold raw33868step0 raw33868; decide +kernel
      have hl : raw33868step0Labels = raw33868Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33868 raw33868Labels permutation154 permutation6
    mixedMoment B raw33868step0 raw33868step0Labels = mixedMoment B raw33868step1 raw33868step1Labels := by
      have ha : raw33868step1 = raw33868step0 := by apply Matrix.ext; unfold raw33868step1 raw33868step0; decide +kernel
      have hl : raw33868step0Labels = labelEmbedding9 ∘ raw33868step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33868step0 raw33868step0Labels raw33868step1Labels labelEmbedding9 hl
    _ = mixedMoment B node4803 node4803Labels := by rfl

theorem canonical33869 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33869 raw33869Labels = mixedMoment B node4806 node4806Labels := by
  calc
    mixedMoment B raw33869 raw33869Labels = mixedMoment B raw33869step0 raw33869step0Labels := by
      have ha : raw33869step0 = (fun i j => raw33869 (permutation154 i) (permutation6 j)) := by apply Matrix.ext; unfold raw33869step0 raw33869; decide +kernel
      have hl : raw33869step0Labels = raw33869Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33869 raw33869Labels permutation154 permutation6
    mixedMoment B raw33869step0 raw33869step0Labels = mixedMoment B raw33869step1 raw33869step1Labels := by
      have ha : raw33869step1 = raw33869step0 := by apply Matrix.ext; unfold raw33869step1 raw33869step0; decide +kernel
      have hl : raw33869step0Labels = labelEmbedding9 ∘ raw33869step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33869step0 raw33869step0Labels raw33869step1Labels labelEmbedding9 hl
    _ = mixedMoment B node4806 node4806Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical267
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical34185 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34185 raw34185Labels = mixedMoment B node4410 node4410Labels := by
  calc
    mixedMoment B raw34185 raw34185Labels = mixedMoment B raw34185step0 raw34185step0Labels := by
      have hz : ∀ j, raw34185 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34185step0 = (fun i j => raw34185 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34185step0 raw34185; decide +kernel
      have hl : raw34185step0Labels = raw34185Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34185 raw34185Labels permutation346 hz
    mixedMoment B raw34185step0 raw34185step0Labels = mixedMoment B raw34185step1 raw34185step1Labels := by
      have ha : raw34185step1 = (fun i j => raw34185step0 (permutation37 i) (permutation4 j)) := by apply Matrix.ext; unfold raw34185step1 raw34185step0; decide +kernel
      have hl : raw34185step1Labels = raw34185step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34185step0 raw34185step0Labels permutation37 permutation4
    mixedMoment B raw34185step1 raw34185step1Labels = mixedMoment B raw34185step2 raw34185step2Labels := by
      have ha : raw34185step2 = -raw34185step1 := by apply Matrix.ext; change ∀ i j, raw34185step2 i j = -(raw34185step1 i j); unfold raw34185step2 raw34185step1; decide +kernel
      have hl : raw34185step2Labels = raw34185step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34185step2 raw34185step2Labels = mixedMoment B raw34185step3 raw34185step3Labels := by
      have ha : raw34185step3 = raw34185step2 := by apply Matrix.ext; unfold raw34185step3 raw34185step2; decide +kernel
      have hl : raw34185step2Labels = labelEmbedding7 ∘ raw34185step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34185step2 raw34185step2Labels raw34185step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4410 node4410Labels := by rfl

theorem canonical34186 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34186 raw34186Labels = mixedMoment B node4747 node4747Labels := by
  calc
    mixedMoment B raw34186 raw34186Labels = mixedMoment B raw34186step0 raw34186step0Labels := by
      have hz : ∀ j, raw34186 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34186step0 = (fun i j => raw34186 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34186step0 raw34186; decide +kernel
      have hl : raw34186step0Labels = raw34186Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34186 raw34186Labels permutation346 hz
    mixedMoment B raw34186step0 raw34186step0Labels = mixedMoment B raw34186step1 raw34186step1Labels := by
      have ha : raw34186step1 = (fun i j => raw34186step0 (permutation37 i) (permutation4 j)) := by apply Matrix.ext; unfold raw34186step1 raw34186step0; decide +kernel
      have hl : raw34186step1Labels = raw34186step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34186step0 raw34186step0Labels permutation37 permutation4
    mixedMoment B raw34186step1 raw34186step1Labels = mixedMoment B raw34186step2 raw34186step2Labels := by
      have ha : raw34186step2 = -raw34186step1 := by apply Matrix.ext; change ∀ i j, raw34186step2 i j = -(raw34186step1 i j); unfold raw34186step2 raw34186step1; decide +kernel
      have hl : raw34186step2Labels = raw34186step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34186step2 raw34186step2Labels = mixedMoment B raw34186step3 raw34186step3Labels := by
      have ha : raw34186step3 = raw34186step2 := by apply Matrix.ext; unfold raw34186step3 raw34186step2; decide +kernel
      have hl : raw34186step2Labels = labelEmbedding7 ∘ raw34186step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34186step2 raw34186step2Labels raw34186step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4747 node4747Labels := by rfl

theorem canonical34187 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34187 raw34187Labels = mixedMoment B node4783 node4783Labels := by
  calc
    mixedMoment B raw34187 raw34187Labels = mixedMoment B raw34187step0 raw34187step0Labels := by
      have ha : raw34187step0 = (fun i j => raw34187 (permutation181 i) (permutation4 j)) := by apply Matrix.ext; unfold raw34187step0 raw34187; decide +kernel
      have hl : raw34187step0Labels = raw34187Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34187 raw34187Labels permutation181 permutation4
    mixedMoment B raw34187step0 raw34187step0Labels = mixedMoment B raw34187step1 raw34187step1Labels := by
      have ha : raw34187step1 = -raw34187step0 := by apply Matrix.ext; change ∀ i j, raw34187step1 i j = -(raw34187step0 i j); unfold raw34187step1 raw34187step0; decide +kernel
      have hl : raw34187step1Labels = raw34187step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34187step1 raw34187step1Labels = mixedMoment B raw34187step2 raw34187step2Labels := by
      have ha : raw34187step2 = raw34187step1 := by apply Matrix.ext; unfold raw34187step2 raw34187step1; decide +kernel
      have hl : raw34187step1Labels = labelEmbedding7 ∘ raw34187step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34187step1 raw34187step1Labels raw34187step2Labels labelEmbedding7 hl
    _ = mixedMoment B node4783 node4783Labels := by rfl

theorem canonical34188 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34188 raw34188Labels = mixedMoment B node4836 node4836Labels := by
  calc
    mixedMoment B raw34188 raw34188Labels = mixedMoment B raw34188step0 raw34188step0Labels := by
      have hz : ∀ j, raw34188 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34188step0 = (fun i j => raw34188 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34188step0 raw34188; decide +kernel
      have hl : raw34188step0Labels = raw34188Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34188 raw34188Labels permutation346 hz
    mixedMoment B raw34188step0 raw34188step0Labels = mixedMoment B raw34188step1 raw34188step1Labels := by
      have ha : raw34188step1 = (fun i j => raw34188step0 (permutation34 i) (permutation6 j)) := by apply Matrix.ext; unfold raw34188step1 raw34188step0; decide +kernel
      have hl : raw34188step1Labels = raw34188step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34188step0 raw34188step0Labels permutation34 permutation6
    mixedMoment B raw34188step1 raw34188step1Labels = mixedMoment B raw34188step2 raw34188step2Labels := by
      have ha : raw34188step2 = raw34188step1 := by apply Matrix.ext; unfold raw34188step2 raw34188step1; decide +kernel
      have hl : raw34188step1Labels = labelEmbedding9 ∘ raw34188step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34188step1 raw34188step1Labels raw34188step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4836 node4836Labels := by rfl

theorem canonical34189 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34189 raw34189Labels = mixedMoment B node4840 node4840Labels := by
  calc
    mixedMoment B raw34189 raw34189Labels = mixedMoment B raw34189step0 raw34189step0Labels := by
      have hz : ∀ j, raw34189 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34189step0 = (fun i j => raw34189 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34189step0 raw34189; decide +kernel
      have hl : raw34189step0Labels = raw34189Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34189 raw34189Labels permutation346 hz
    mixedMoment B raw34189step0 raw34189step0Labels = mixedMoment B raw34189step1 raw34189step1Labels := by
      have ha : raw34189step1 = (fun i j => raw34189step0 (permutation34 i) (permutation6 j)) := by apply Matrix.ext; unfold raw34189step1 raw34189step0; decide +kernel
      have hl : raw34189step1Labels = raw34189step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34189step0 raw34189step0Labels permutation34 permutation6
    mixedMoment B raw34189step1 raw34189step1Labels = mixedMoment B raw34189step2 raw34189step2Labels := by
      have ha : raw34189step2 = raw34189step1 := by apply Matrix.ext; unfold raw34189step2 raw34189step1; decide +kernel
      have hl : raw34189step1Labels = labelEmbedding9 ∘ raw34189step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34189step1 raw34189step1Labels raw34189step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4840 node4840Labels := by rfl

theorem canonical34190 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34190 raw34190Labels = mixedMoment B node4412 node4412Labels := by
  calc
    mixedMoment B raw34190 raw34190Labels = mixedMoment B raw34190step0 raw34190step0Labels := by
      have hz : ∀ j, raw34190 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34190step0 = (fun i j => raw34190 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34190step0 raw34190; decide +kernel
      have hl : raw34190step0Labels = raw34190Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34190 raw34190Labels permutation346 hz
    mixedMoment B raw34190step0 raw34190step0Labels = mixedMoment B raw34190step1 raw34190step1Labels := by
      have ha : raw34190step1 = (fun i j => raw34190step0 (permutation36 i) (permutation4 j)) := by apply Matrix.ext; unfold raw34190step1 raw34190step0; decide +kernel
      have hl : raw34190step1Labels = raw34190step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34190step0 raw34190step0Labels permutation36 permutation4
    mixedMoment B raw34190step1 raw34190step1Labels = mixedMoment B raw34190step2 raw34190step2Labels := by
      have ha : raw34190step2 = -raw34190step1 := by apply Matrix.ext; change ∀ i j, raw34190step2 i j = -(raw34190step1 i j); unfold raw34190step2 raw34190step1; decide +kernel
      have hl : raw34190step2Labels = raw34190step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34190step2 raw34190step2Labels = mixedMoment B raw34190step3 raw34190step3Labels := by
      have ha : raw34190step3 = raw34190step2 := by apply Matrix.ext; unfold raw34190step3 raw34190step2; decide +kernel
      have hl : raw34190step2Labels = labelEmbedding7 ∘ raw34190step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34190step2 raw34190step2Labels raw34190step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4412 node4412Labels := by rfl

theorem canonical34191 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34191 raw34191Labels = mixedMoment B node4750 node4750Labels := by
  calc
    mixedMoment B raw34191 raw34191Labels = mixedMoment B raw34191step0 raw34191step0Labels := by
      have hz : ∀ j, raw34191 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34191step0 = (fun i j => raw34191 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34191step0 raw34191; decide +kernel
      have hl : raw34191step0Labels = raw34191Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34191 raw34191Labels permutation346 hz
    mixedMoment B raw34191step0 raw34191step0Labels = mixedMoment B raw34191step1 raw34191step1Labels := by
      have ha : raw34191step1 = (fun i j => raw34191step0 (permutation36 i) (permutation4 j)) := by apply Matrix.ext; unfold raw34191step1 raw34191step0; decide +kernel
      have hl : raw34191step1Labels = raw34191step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34191step0 raw34191step0Labels permutation36 permutation4
    mixedMoment B raw34191step1 raw34191step1Labels = mixedMoment B raw34191step2 raw34191step2Labels := by
      have ha : raw34191step2 = -raw34191step1 := by apply Matrix.ext; change ∀ i j, raw34191step2 i j = -(raw34191step1 i j); unfold raw34191step2 raw34191step1; decide +kernel
      have hl : raw34191step2Labels = raw34191step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34191step2 raw34191step2Labels = mixedMoment B raw34191step3 raw34191step3Labels := by
      have ha : raw34191step3 = raw34191step2 := by apply Matrix.ext; unfold raw34191step3 raw34191step2; decide +kernel
      have hl : raw34191step2Labels = labelEmbedding7 ∘ raw34191step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34191step2 raw34191step2Labels raw34191step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4750 node4750Labels := by rfl

theorem canonical34192 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34192 raw34192Labels = mixedMoment B node4785 node4785Labels := by
  calc
    mixedMoment B raw34192 raw34192Labels = mixedMoment B raw34192step0 raw34192step0Labels := by
      have ha : raw34192step0 = (fun i j => raw34192 (permutation180 i) (permutation4 j)) := by apply Matrix.ext; unfold raw34192step0 raw34192; decide +kernel
      have hl : raw34192step0Labels = raw34192Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34192 raw34192Labels permutation180 permutation4
    mixedMoment B raw34192step0 raw34192step0Labels = mixedMoment B raw34192step1 raw34192step1Labels := by
      have ha : raw34192step1 = -raw34192step0 := by apply Matrix.ext; change ∀ i j, raw34192step1 i j = -(raw34192step0 i j); unfold raw34192step1 raw34192step0; decide +kernel
      have hl : raw34192step1Labels = raw34192step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34192step1 raw34192step1Labels = mixedMoment B raw34192step2 raw34192step2Labels := by
      have ha : raw34192step2 = raw34192step1 := by apply Matrix.ext; unfold raw34192step2 raw34192step1; decide +kernel
      have hl : raw34192step1Labels = labelEmbedding7 ∘ raw34192step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34192step1 raw34192step1Labels raw34192step2Labels labelEmbedding7 hl
    _ = mixedMoment B node4785 node4785Labels := by rfl

theorem canonical34193 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34193 raw34193Labels = mixedMoment B node4842 node4842Labels := by
  calc
    mixedMoment B raw34193 raw34193Labels = mixedMoment B raw34193step0 raw34193step0Labels := by
      have hz : ∀ j, raw34193 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34193step0 = (fun i j => raw34193 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34193step0 raw34193; decide +kernel
      have hl : raw34193step0Labels = raw34193Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34193 raw34193Labels permutation346 hz
    mixedMoment B raw34193step0 raw34193step0Labels = mixedMoment B raw34193step1 raw34193step1Labels := by
      have ha : raw34193step1 = (fun i j => raw34193step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw34193step1 raw34193step0; decide +kernel
      have hl : raw34193step1Labels = raw34193step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34193step0 raw34193step0Labels permutation32 permutation6
    mixedMoment B raw34193step1 raw34193step1Labels = mixedMoment B raw34193step2 raw34193step2Labels := by
      have ha : raw34193step2 = raw34193step1 := by apply Matrix.ext; unfold raw34193step2 raw34193step1; decide +kernel
      have hl : raw34193step1Labels = labelEmbedding9 ∘ raw34193step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34193step1 raw34193step1Labels raw34193step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4842 node4842Labels := by rfl

theorem canonical34194 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34194 raw34194Labels = mixedMoment B node4424 node4424Labels := by
  calc
    mixedMoment B raw34194 raw34194Labels = mixedMoment B raw34194step0 raw34194step0Labels := by
      have hz : ∀ j, raw34194 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34194step0 = (fun i j => raw34194 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34194step0 raw34194; decide +kernel
      have hl : raw34194step0Labels = raw34194Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34194 raw34194Labels permutation346 hz
    mixedMoment B raw34194step0 raw34194step0Labels = mixedMoment B raw34194step1 raw34194step1Labels := by
      have ha : raw34194step1 = (fun i j => raw34194step0 (permutation35 i) (permutation4 j)) := by apply Matrix.ext; unfold raw34194step1 raw34194step0; decide +kernel
      have hl : raw34194step1Labels = raw34194step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34194step0 raw34194step0Labels permutation35 permutation4
    mixedMoment B raw34194step1 raw34194step1Labels = mixedMoment B raw34194step2 raw34194step2Labels := by
      have ha : raw34194step2 = -raw34194step1 := by apply Matrix.ext; change ∀ i j, raw34194step2 i j = -(raw34194step1 i j); unfold raw34194step2 raw34194step1; decide +kernel
      have hl : raw34194step2Labels = raw34194step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34194step2 raw34194step2Labels = mixedMoment B raw34194step3 raw34194step3Labels := by
      have ha : raw34194step3 = raw34194step2 := by apply Matrix.ext; unfold raw34194step3 raw34194step2; decide +kernel
      have hl : raw34194step2Labels = labelEmbedding7 ∘ raw34194step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34194step2 raw34194step2Labels raw34194step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4424 node4424Labels := by rfl

theorem canonical34195 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34195 raw34195Labels = mixedMoment B node4752 node4752Labels := by
  calc
    mixedMoment B raw34195 raw34195Labels = mixedMoment B raw34195step0 raw34195step0Labels := by
      have hz : ∀ j, raw34195 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34195step0 = (fun i j => raw34195 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34195step0 raw34195; decide +kernel
      have hl : raw34195step0Labels = raw34195Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34195 raw34195Labels permutation346 hz
    mixedMoment B raw34195step0 raw34195step0Labels = mixedMoment B raw34195step1 raw34195step1Labels := by
      have ha : raw34195step1 = (fun i j => raw34195step0 (permutation35 i) (permutation4 j)) := by apply Matrix.ext; unfold raw34195step1 raw34195step0; decide +kernel
      have hl : raw34195step1Labels = raw34195step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34195step0 raw34195step0Labels permutation35 permutation4
    mixedMoment B raw34195step1 raw34195step1Labels = mixedMoment B raw34195step2 raw34195step2Labels := by
      have ha : raw34195step2 = -raw34195step1 := by apply Matrix.ext; change ∀ i j, raw34195step2 i j = -(raw34195step1 i j); unfold raw34195step2 raw34195step1; decide +kernel
      have hl : raw34195step2Labels = raw34195step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34195step2 raw34195step2Labels = mixedMoment B raw34195step3 raw34195step3Labels := by
      have ha : raw34195step3 = raw34195step2 := by apply Matrix.ext; unfold raw34195step3 raw34195step2; decide +kernel
      have hl : raw34195step2Labels = labelEmbedding7 ∘ raw34195step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34195step2 raw34195step2Labels raw34195step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4752 node4752Labels := by rfl

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

theorem canonical1236 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1236 raw1236Labels = mixedMoment B node4424 node4424Labels := by
  calc
    mixedMoment B raw1236 raw1236Labels = mixedMoment B raw1236step0 raw1236step0Labels := by
      have ha : raw1236step0 = (fun i j => raw1236 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1236step0 raw1236; decide +kernel
      have hl : raw1236step0Labels = raw1236Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1236 raw1236Labels permutation32 permutation4
    mixedMoment B raw1236step0 raw1236step0Labels = mixedMoment B raw1236step1 raw1236step1Labels := by
      have ha : raw1236step1 = raw1236step0 := by apply Matrix.ext; unfold raw1236step1 raw1236step0; decide +kernel
      have hl : raw1236step0Labels = labelEmbedding7 ∘ raw1236step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1236step0 raw1236step0Labels raw1236step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4424 node4424Labels := by rfl

theorem canonical1237 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1237 raw1237Labels = mixedMoment B node1005 node1005Labels := by
  calc
    mixedMoment B raw1237 raw1237Labels = mixedMoment B raw1237step0 raw1237step0Labels := by
      have ha : raw1237step0 = (fun i j => raw1237 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1237step0 raw1237; decide +kernel
      have hl : raw1237step0Labels = raw1237Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1237 raw1237Labels permutation32 permutation4
    _ = mixedMoment B node1005 node1005Labels := by rfl

theorem canonical1238 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1238 raw1238Labels = mixedMoment B node1623 node1623Labels := by
  calc
    mixedMoment B raw1238 raw1238Labels = mixedMoment B raw1238step0 raw1238step0Labels := by
      have ha : raw1238step0 = (fun i j => raw1238 (permutation33 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1238step0 raw1238; decide +kernel
      have hl : raw1238step0Labels = raw1238Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1238 raw1238Labels permutation33 permutation6
    mixedMoment B raw1238step0 raw1238step0Labels = mixedMoment B raw1238step1 raw1238step1Labels := by
      have ha : raw1238step1 = -raw1238step0 := by apply Matrix.ext; change ∀ i j, raw1238step1 i j = -(raw1238step0 i j); unfold raw1238step1 raw1238step0; decide +kernel
      have hl : raw1238step1Labels = raw1238step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1238step1 raw1238step1Labels = mixedMoment B raw1238step2 raw1238step2Labels := by
      have ha : raw1238step2 = raw1238step1 := by apply Matrix.ext; unfold raw1238step2 raw1238step1; decide +kernel
      have hl : raw1238step1Labels = labelEmbedding1 ∘ raw1238step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1238step1 raw1238step1Labels raw1238step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1623 node1623Labels := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons69
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singleton4424 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4424 node4424Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1005 node1005Labels + mixedMoment B node1623 node1623Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1236 singletonSmall4424
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4424) = raw1236Labels := by decide +kernel
  rw [hl, canonical1236 B hB] at h
  have hc0 : mixedMoment B raw1236 (Fin.cases (0 : Fin 2) singletonSmall4424) =
      mixedMoment B node1005 node1005Labels := by
    have ha : raw1236 = raw1237 := by apply Matrix.ext; unfold raw1236 raw1237; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4424 = raw1237Labels := by decide +kernel
    rw [ha, hj, canonical1237 B hB]
  have hc1 : mixedMoment B raw1236 (Fin.cases (1 : Fin 2) singletonSmall4424) =
      mixedMoment B node1623 node1623Labels := by
    have ha : raw1236 = raw1238 := by apply Matrix.ext; unfold raw1236 raw1238; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4424 = raw1238Labels := by decide +kernel
    rw [ha, hj, canonical1238 B hB]
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

theorem singleton4740 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4740 node4740Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1913 node1913Labels + mixedMoment B node1922 node1922Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1656 singletonSmall4740
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4740) = raw1656Labels := by decide +kernel
  rw [hl, canonical1656 B hB] at h
  have hc0 : mixedMoment B raw1656 (Fin.cases (0 : Fin 2) singletonSmall4740) =
      mixedMoment B node1913 node1913Labels := by
    have ha : raw1656 = raw1657 := by apply Matrix.ext; unfold raw1656 raw1657; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4740 = raw1657Labels := by decide +kernel
    rw [ha, hj, canonical1657 B hB]
  have hc1 : mixedMoment B raw1656 (Fin.cases (1 : Fin 2) singletonSmall4740) =
      mixedMoment B node1922 node1922Labels := by
    have ha : raw1656 = raw1658 := by apply Matrix.ext; unfold raw1656 raw1658; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4740 = raw1658Labels := by decide +kernel
    rw [ha, hj, canonical1658 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4747 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4747 node4747Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1926 node1926Labels + mixedMoment B node1948 node1948Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1668 singletonSmall4747
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4747) = raw1668Labels := by decide +kernel
  rw [hl, canonical1668 B hB] at h
  have hc0 : mixedMoment B raw1668 (Fin.cases (0 : Fin 2) singletonSmall4747) =
      mixedMoment B node1926 node1926Labels := by
    have ha : raw1668 = raw1669 := by apply Matrix.ext; unfold raw1668 raw1669; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4747 = raw1669Labels := by decide +kernel
    rw [ha, hj, canonical1669 B hB]
  have hc1 : mixedMoment B raw1668 (Fin.cases (1 : Fin 2) singletonSmall4747) =
      mixedMoment B node1948 node1948Labels := by
    have ha : raw1668 = raw1670 := by apply Matrix.ext; unfold raw1668 raw1670; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4747 = raw1670Labels := by decide +kernel
    rw [ha, hj, canonical1670 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4750 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4750 node4750Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1929 node1929Labels + mixedMoment B node1949 node1949Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1674 singletonSmall4750
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4750) = raw1674Labels := by decide +kernel
  rw [hl, canonical1674 B hB] at h
  have hc0 : mixedMoment B raw1674 (Fin.cases (0 : Fin 2) singletonSmall4750) =
      mixedMoment B node1929 node1929Labels := by
    have ha : raw1674 = raw1675 := by apply Matrix.ext; unfold raw1674 raw1675; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4750 = raw1675Labels := by decide +kernel
    rw [ha, hj, canonical1675 B hB]
  have hc1 : mixedMoment B raw1674 (Fin.cases (1 : Fin 2) singletonSmall4750) =
      mixedMoment B node1949 node1949Labels := by
    have ha : raw1674 = raw1676 := by apply Matrix.ext; unfold raw1674 raw1676; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4750 = raw1676Labels := by decide +kernel
    rw [ha, hj, canonical1676 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4787 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4787 node4787Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2000 node2000Labels + mixedMoment B node2000 node2000Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1719 singletonSmall4787
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4787) = raw1719Labels := by decide +kernel
  rw [hl, canonical1719 B hB] at h
  have hc0 : mixedMoment B raw1719 (Fin.cases (0 : Fin 2) singletonSmall4787) =
      mixedMoment B node2000 node2000Labels := by
    have ha : raw1719 = raw1720 := by apply Matrix.ext; unfold raw1719 raw1720; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4787 = raw1720Labels := by decide +kernel
    rw [ha, hj, canonical1720 B hB]
  have hc1 : mixedMoment B raw1719 (Fin.cases (1 : Fin 2) singletonSmall4787) =
      mixedMoment B node2000 node2000Labels := by
    have ha : raw1719 = raw1721 := by apply Matrix.ext; unfold raw1719 raw1721; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4787 = raw1721Labels := by decide +kernel
    rw [ha, hj, canonical1721 B hB]
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

theorem singleton4835 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4835 node4835Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2054 node2054Labels + mixedMoment B node2206 node2206Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1767 singletonSmall4835
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4835) = raw1767Labels := by decide +kernel
  rw [hl, canonical1767 B hB] at h
  have hc0 : mixedMoment B raw1767 (Fin.cases (0 : Fin 2) singletonSmall4835) =
      mixedMoment B node2054 node2054Labels := by
    have ha : raw1767 = raw1768 := by apply Matrix.ext; unfold raw1767 raw1768; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4835 = raw1768Labels := by decide +kernel
    rw [ha, hj, canonical1768 B hB]
  have hc1 : mixedMoment B raw1767 (Fin.cases (1 : Fin 2) singletonSmall4835) =
      mixedMoment B node2206 node2206Labels := by
    have ha : raw1767 = raw1769 := by apply Matrix.ext; unfold raw1767 raw1769; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4835 = raw1769Labels := by decide +kernel
    rw [ha, hj, canonical1769 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4839 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4839 node4839Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2058 node2058Labels + mixedMoment B node2216 node2216Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1770 singletonSmall4839
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4839) = raw1770Labels := by decide +kernel
  rw [hl, canonical1770 B hB] at h
  have hc0 : mixedMoment B raw1770 (Fin.cases (0 : Fin 2) singletonSmall4839) =
      mixedMoment B node2058 node2058Labels := by
    have ha : raw1770 = raw1771 := by apply Matrix.ext; unfold raw1770 raw1771; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4839 = raw1771Labels := by decide +kernel
    rw [ha, hj, canonical1771 B hB]
  have hc1 : mixedMoment B raw1770 (Fin.cases (1 : Fin 2) singletonSmall4839) =
      mixedMoment B node2216 node2216Labels := by
    have ha : raw1770 = raw1772 := by apply Matrix.ext; unfold raw1770 raw1772; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4839 = raw1772Labels := by decide +kernel
    rw [ha, hj, canonical1772 B hB]
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

theorem singleton4869 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4869 node4869Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2110 node2110Labels + mixedMoment B node2275 node2275Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1800 singletonSmall4869
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4869) = raw1800Labels := by decide +kernel
  rw [hl, canonical1800 B hB] at h
  have hc0 : mixedMoment B raw1800 (Fin.cases (0 : Fin 2) singletonSmall4869) =
      mixedMoment B node2110 node2110Labels := by
    have ha : raw1800 = raw1801 := by apply Matrix.ext; unfold raw1800 raw1801; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4869 = raw1801Labels := by decide +kernel
    rw [ha, hj, canonical1801 B hB]
  have hc1 : mixedMoment B raw1800 (Fin.cases (1 : Fin 2) singletonSmall4869) =
      mixedMoment B node2275 node2275Labels := by
    have ha : raw1800 = raw1802 := by apply Matrix.ext; unfold raw1800 raw1802; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4869 = raw1802Labels := by decide +kernel
    rw [ha, hj, canonical1802 B hB]
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

theorem singleton5105 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5105 node5105Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2515 node2515Labels + mixedMoment B node3479 node3479Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2130 singletonSmall5105
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5105) = raw2130Labels := by decide +kernel
  rw [hl, canonical2130 B hB] at h
  have hc0 : mixedMoment B raw2130 (Fin.cases (0 : Fin 2) singletonSmall5105) =
      mixedMoment B node2515 node2515Labels := by
    have ha : raw2130 = raw2131 := by apply Matrix.ext; unfold raw2130 raw2131; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5105 = raw2131Labels := by decide +kernel
    rw [ha, hj, canonical2131 B hB]
  have hc1 : mixedMoment B raw2130 (Fin.cases (1 : Fin 2) singletonSmall5105) =
      mixedMoment B node3479 node3479Labels := by
    have ha : raw2130 = raw2132 := by apply Matrix.ext; unfold raw2130 raw2132; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5105 = raw2132Labels := by decide +kernel
    rw [ha, hj, canonical2132 B hB]
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

theorem singleton5170 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5170 node5170Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2954 node2954Labels + mixedMoment B node3606 node3606Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2202 singletonSmall5170
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5170) = raw2202Labels := by decide +kernel
  rw [hl, canonical2202 B hB] at h
  have hc0 : mixedMoment B raw2202 (Fin.cases (0 : Fin 2) singletonSmall5170) =
      mixedMoment B node2954 node2954Labels := by
    have ha : raw2202 = raw2203 := by apply Matrix.ext; unfold raw2202 raw2203; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5170 = raw2203Labels := by decide +kernel
    rw [ha, hj, canonical2203 B hB]
  have hc1 : mixedMoment B raw2202 (Fin.cases (1 : Fin 2) singletonSmall5170) =
      mixedMoment B node3606 node3606Labels := by
    have ha : raw2202 = raw2204 := by apply Matrix.ext; unfold raw2202 raw2204; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5170 = raw2204Labels := by decide +kernel
    rw [ha, hj, canonical2204 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

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

theorem sound1005 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1005 node1005Labels = Sparse.eval nodeValue1005 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1005) = mixedMoment B node1005 node1005Labels := rfl
  simpa [nodeValue1005, Sparse.eval] using hc.symm

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

theorem sound1623 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1623 node1623Labels = Sparse.eval nodeValue1623 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1623) = mixedMoment B node1623 node1623Labels := rfl
  simpa [nodeValue1623, Sparse.eval] using hc.symm

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

theorem sound1913 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1913 node1913Labels = Sparse.eval nodeValue1913 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1913) = mixedMoment B node1913 node1913Labels := rfl
  simpa [nodeValue1913, Sparse.eval] using hc.symm

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

theorem sound1922 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1922 node1922Labels = Sparse.eval nodeValue1922 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1922) = mixedMoment B node1922 node1922Labels := rfl
  simpa [nodeValue1922, Sparse.eval] using hc.symm

theorem sound1926 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1926 node1926Labels = Sparse.eval nodeValue1926 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1926) = mixedMoment B node1926 node1926Labels := rfl
  simpa [nodeValue1926, Sparse.eval] using hc.symm

theorem sound1929 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1929 node1929Labels = Sparse.eval nodeValue1929 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1929) = mixedMoment B node1929 node1929Labels := rfl
  simpa [nodeValue1929, Sparse.eval] using hc.symm

theorem sound1948 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1948 node1948Labels = Sparse.eval nodeValue1948 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1948) = mixedMoment B node1948 node1948Labels := rfl
  simpa [nodeValue1948, Sparse.eval] using hc.symm

theorem sound1949 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1949 node1949Labels = Sparse.eval nodeValue1949 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1949) = mixedMoment B node1949 node1949Labels := rfl
  simpa [nodeValue1949, Sparse.eval] using hc.symm

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

theorem sound2000 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2000 node2000Labels = Sparse.eval nodeValue2000 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2000) = mixedMoment B node2000 node2000Labels := rfl
  simpa [nodeValue2000, Sparse.eval] using hc.symm

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

theorem sound2054 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2054 node2054Labels = Sparse.eval nodeValue2054 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2054) = mixedMoment B node2054 node2054Labels := rfl
  simpa [nodeValue2054, Sparse.eval] using hc.symm

theorem sound2058 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2058 node2058Labels = Sparse.eval nodeValue2058 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2058) = mixedMoment B node2058 node2058Labels := rfl
  simpa [nodeValue2058, Sparse.eval] using hc.symm

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

theorem sound2206 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2206 node2206Labels = Sparse.eval nodeValue2206 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2206) = mixedMoment B node2206 node2206Labels := rfl
  simpa [nodeValue2206, Sparse.eval] using hc.symm

theorem sound2214 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2214 node2214Labels = Sparse.eval nodeValue2214 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2214) = mixedMoment B node2214 node2214Labels := rfl
  simpa [nodeValue2214, Sparse.eval] using hc.symm

theorem sound2216 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2216 node2216Labels = Sparse.eval nodeValue2216 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2216) = mixedMoment B node2216 node2216Labels := rfl
  simpa [nodeValue2216, Sparse.eval] using hc.symm

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

theorem sound2275 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2275 node2275Labels = Sparse.eval nodeValue2275 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2275) = mixedMoment B node2275 node2275Labels := rfl
  simpa [nodeValue2275, Sparse.eval] using hc.symm

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

theorem sound2515 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2515 node2515Labels = Sparse.eval nodeValue2515 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2515) = mixedMoment B node2515 node2515Labels := rfl
  simpa [nodeValue2515, Sparse.eval] using hc.symm

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

theorem sound2954 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2954 node2954Labels = Sparse.eval nodeValue2954 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2954) = mixedMoment B node2954 node2954Labels := rfl
  simpa [nodeValue2954, Sparse.eval] using hc.symm

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

theorem sound3479 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3479 node3479Labels = Sparse.eval nodeValue3479 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3479) = mixedMoment B node3479 node3479Labels := rfl
  simpa [nodeValue3479, Sparse.eval] using hc.symm

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

theorem sound3606 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3606 node3606Labels = Sparse.eval nodeValue3606 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3606) = mixedMoment B node3606 node3606Labels := rfl
  simpa [nodeValue3606, Sparse.eval] using hc.symm

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

theorem sound4407 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4407 node4407Labels = Sparse.eval nodeValue4407 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4407) = mixedMoment B node4407 node4407Labels := rfl
  simpa [nodeValue4407, Sparse.eval] using hc.symm

theorem sound4410 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4410 node4410Labels = Sparse.eval nodeValue4410 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4410) = mixedMoment B node4410 node4410Labels := rfl
  simpa [nodeValue4410, Sparse.eval] using hc.symm

theorem sound4412 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4412 node4412Labels = Sparse.eval nodeValue4412 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4412) = mixedMoment B node4412 node4412Labels := rfl
  simpa [nodeValue4412, Sparse.eval] using hc.symm

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

theorem sound4424 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4424 node4424Labels = Sparse.eval nodeValue4424 (mixedVector B) := by
  have h := singleton4424 B _hB
  rw [sound1005 B _hB _hF, sound1623 B _hB _hF] at h
  norm_num [nodeValue4424, nodeValue1005, nodeValue1623, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4471 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4471 node4471Labels = Sparse.eval nodeValue4471 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4471) = mixedMoment B node4471 node4471Labels := rfl
  simpa [nodeValue4471, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros74
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero4752 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4752 node4752Labels = 0 := by
  exact mixedMoment_order_one B hB node4752 node4752Labels 1
    (by decide +kernel) (by decide +kernel)

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

theorem sound4740 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4740 node4740Labels = Sparse.eval nodeValue4740 (mixedVector B) := by
  have h := singleton4740 B _hB
  rw [sound1913 B _hB _hF, sound1922 B _hB _hF] at h
  norm_num [nodeValue4740, nodeValue1913, nodeValue1922, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4747 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4747 node4747Labels = Sparse.eval nodeValue4747 (mixedVector B) := by
  have h := singleton4747 B _hB
  rw [sound1926 B _hB _hF, sound1948 B _hB _hF] at h
  norm_num [nodeValue4747, nodeValue1926, nodeValue1948, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4750 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4750 node4750Labels = Sparse.eval nodeValue4750 (mixedVector B) := by
  have h := singleton4750 B _hB
  rw [sound1929 B _hB _hF, sound1949 B _hB _hF] at h
  norm_num [nodeValue4750, nodeValue1929, nodeValue1949, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4752 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4752 node4752Labels = Sparse.eval nodeValue4752 (mixedVector B) := by
  simpa only [nodeValue4752, Sparse.eval_nil] using zero4752 B _hB _hF

theorem sound4783 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4783 node4783Labels = Sparse.eval nodeValue4783 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4783) = mixedMoment B node4783 node4783Labels := rfl
  simpa [nodeValue4783, Sparse.eval] using hc.symm

theorem sound4785 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4785 node4785Labels = Sparse.eval nodeValue4785 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4785) = mixedMoment B node4785 node4785Labels := rfl
  simpa [nodeValue4785, Sparse.eval] using hc.symm

theorem sound4787 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4787 node4787Labels = Sparse.eval nodeValue4787 (mixedVector B) := by
  have h := singleton4787 B _hB
  rw [sound2000 B _hB _hF] at h
  norm_num [nodeValue4787, nodeValue2000, Sparse.eval] at h ⊢
  linarith only [h]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros75
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero4838 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4838 node4838Labels = 0 := by
  exact mixedMoment_order_one B hB node4838 node4838Labels 1
    (by decide +kernel) (by decide +kernel)

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

theorem sound4803 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4803 node4803Labels = Sparse.eval nodeValue4803 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4803) = mixedMoment B node4803 node4803Labels := rfl
  simpa [nodeValue4803, Sparse.eval] using hc.symm

theorem sound4805 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4805 node4805Labels = Sparse.eval nodeValue4805 (mixedVector B) := by
  have h := singleton4805 B _hB
  rw [sound2023 B _hB _hF, sound2214 B _hB _hF] at h
  norm_num [nodeValue4805, nodeValue2023, nodeValue2214, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4806 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4806 node4806Labels = Sparse.eval nodeValue4806 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4806) = mixedMoment B node4806 node4806Labels := rfl
  simpa [nodeValue4806, Sparse.eval] using hc.symm

theorem sound4813 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4813 node4813Labels = Sparse.eval nodeValue4813 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4813) = mixedMoment B node4813 node4813Labels := rfl
  simpa [nodeValue4813, Sparse.eval] using hc.symm

theorem sound4835 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4835 node4835Labels = Sparse.eval nodeValue4835 (mixedVector B) := by
  have h := singleton4835 B _hB
  rw [sound2054 B _hB _hF, sound2206 B _hB _hF] at h
  norm_num [nodeValue4835, nodeValue2054, nodeValue2206, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4836 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4836 node4836Labels = Sparse.eval nodeValue4836 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4836) = mixedMoment B node4836 node4836Labels := rfl
  simpa [nodeValue4836, Sparse.eval] using hc.symm

theorem sound4838 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4838 node4838Labels = Sparse.eval nodeValue4838 (mixedVector B) := by
  simpa only [nodeValue4838, Sparse.eval_nil] using zero4838 B _hB _hF

theorem sound4839 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4839 node4839Labels = Sparse.eval nodeValue4839 (mixedVector B) := by
  have h := singleton4839 B _hB
  rw [sound2058 B _hB _hF, sound2216 B _hB _hF] at h
  norm_num [nodeValue4839, nodeValue2058, nodeValue2216, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4840 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4840 node4840Labels = Sparse.eval nodeValue4840 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4840) = mixedMoment B node4840 node4840Labels := rfl
  simpa [nodeValue4840, Sparse.eval] using hc.symm

theorem sound4842 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4842 node4842Labels = Sparse.eval nodeValue4842 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4842) = mixedMoment B node4842 node4842Labels := rfl
  simpa [nodeValue4842, Sparse.eval] using hc.symm

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

theorem sound4867 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4867 node4867Labels = Sparse.eval nodeValue4867 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4867) = mixedMoment B node4867 node4867Labels := rfl
  simpa [nodeValue4867, Sparse.eval] using hc.symm

theorem sound4869 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4869 node4869Labels = Sparse.eval nodeValue4869 (mixedVector B) := by
  have h := singleton4869 B _hB
  rw [sound2110 B _hB _hF, sound2275 B _hB _hF] at h
  norm_num [nodeValue4869, nodeValue2110, nodeValue2275, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4870 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4870 node4870Labels = Sparse.eval nodeValue4870 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4870) = mixedMoment B node4870 node4870Labels := rfl
  simpa [nodeValue4870, Sparse.eval] using hc.symm

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

theorem sound5105 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5105 node5105Labels = Sparse.eval nodeValue5105 (mixedVector B) := by
  have h := singleton5105 B _hB
  rw [sound2515 B _hB _hF, sound3479 B _hB _hF] at h
  norm_num [nodeValue5105, nodeValue2515, nodeValue3479, Sparse.eval] at h ⊢
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

theorem sound5138 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5138 node5138Labels = Sparse.eval nodeValue5138 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5138) = mixedMoment B node5138 node5138Labels := rfl
  simpa [nodeValue5138, Sparse.eval] using hc.symm

theorem sound5170 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5170 node5170Labels = Sparse.eval nodeValue5170 (mixedVector B) := by
  have h := singleton5170 B _hB
  rw [sound2954 B _hB _hF, sound3606 B _hB _hF] at h
  norm_num [nodeValue5170, nodeValue2954, nodeValue3606, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5173 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5173 node5173Labels = Sparse.eval nodeValue5173 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5173) = mixedMoment B node5173 node5173Labels := rfl
  simpa [nodeValue5173, Sparse.eval] using hc.symm

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources77
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sourceEq2481 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2481 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2481 + difference 0 1) (sourceB2481 + difference 1 0) sourceC2481) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5105) := by
    have ha : (tripleCharges (sourceA2481 + difference 0 1) (sourceB2481 + difference 1 0) sourceC2481) = raw32241 := by
      apply Matrix.ext; unfold tripleCharges sourceA2481 sourceB2481 sourceC2481 difference raw32241; decide +kernel
    rw [ha]
    exact (canonical32241 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2481 + difference 0 2) (sourceB2481 + difference 2 0) sourceC2481) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5138) := by
    have ha : (tripleCharges (sourceA2481 + difference 0 2) (sourceB2481 + difference 2 0) sourceC2481) = raw32242 := by
      apply Matrix.ext; unfold tripleCharges sourceA2481 sourceB2481 sourceC2481 difference raw32242; decide +kernel
    rw [ha]
    exact (canonical32242 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2481 + difference 0 3) (sourceB2481 + difference 3 0) sourceC2481) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5172) := by
    have ha : (tripleCharges (sourceA2481 + difference 0 3) (sourceB2481 + difference 3 0) sourceC2481) = raw32487 := by
      apply Matrix.ext; unfold tripleCharges sourceA2481 sourceB2481 sourceC2481 difference raw32487; decide +kernel
    rw [ha]
    exact (canonical32487 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2481 + difference 0 4) (sourceB2481 + difference 4 0) sourceC2481) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5170) := by
    have ha : (tripleCharges (sourceA2481 + difference 0 4) (sourceB2481 + difference 4 0) sourceC2481) = raw32243 := by
      apply Matrix.ext; unfold tripleCharges sourceA2481 sourceB2481 sourceC2481 difference raw32243; decide +kernel
    rw [ha]
    exact (canonical32243 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2481 + difference 0 5) (sourceB2481 + difference 5 0) sourceC2481) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5173) := by
    have ha : (tripleCharges (sourceA2481 + difference 0 5) (sourceB2481 + difference 5 0) sourceC2481) = raw32244 := by
      apply Matrix.ext; unfold tripleCharges sourceA2481 sourceB2481 sourceC2481 difference raw32244; decide +kernel
    rw [ha]
    exact (canonical32244 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2481 + difference 1 0) (sourceB2481 + difference 0 1) sourceC2481) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4471) := by
    have ha : (tripleCharges (sourceA2481 + difference 1 0) (sourceB2481 + difference 0 1) sourceC2481) = raw33558 := by
      apply Matrix.ext; unfold tripleCharges sourceA2481 sourceB2481 sourceC2481 difference raw33558; decide +kernel
    rw [ha]
    exact (canonical33558 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2481 + difference 1 2) (sourceB2481 + difference 2 1) sourceC2481) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4813) := by
    have ha : (tripleCharges (sourceA2481 + difference 1 2) (sourceB2481 + difference 2 1) sourceC2481) = raw33559 := by
      apply Matrix.ext; unfold tripleCharges sourceA2481 sourceB2481 sourceC2481 difference raw33559; decide +kernel
    rw [ha]
    exact (canonical33559 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2481 + difference 1 3) (sourceB2481 + difference 3 1) sourceC2481) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4869) := by
    have ha : (tripleCharges (sourceA2481 + difference 1 3) (sourceB2481 + difference 3 1) sourceC2481) = raw32230 := by
      apply Matrix.ext; unfold tripleCharges sourceA2481 sourceB2481 sourceC2481 difference raw32230; decide +kernel
    rw [ha]
    exact (canonical32230 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2481 + difference 1 4) (sourceB2481 + difference 4 1) sourceC2481) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4867) := by
    have ha : (tripleCharges (sourceA2481 + difference 1 4) (sourceB2481 + difference 4 1) sourceC2481) = raw33560 := by
      apply Matrix.ext; unfold tripleCharges sourceA2481 sourceB2481 sourceC2481 difference raw33560; decide +kernel
    rw [ha]
    exact (canonical33560 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2481 + difference 1 5) (sourceB2481 + difference 5 1) sourceC2481) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4870) := by
    have ha : (tripleCharges (sourceA2481 + difference 1 5) (sourceB2481 + difference 5 1) sourceC2481) = raw33561 := by
      apply Matrix.ext; unfold tripleCharges sourceA2481 sourceB2481 sourceC2481 difference raw33561; decide +kernel
    rw [ha]
    exact (canonical33561 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2481 + difference 2 0) (sourceB2481 + difference 0 2) sourceC2481) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4407) := by
    have ha : (tripleCharges (sourceA2481 + difference 2 0) (sourceB2481 + difference 0 2) sourceC2481) = raw33866 := by
      apply Matrix.ext; unfold tripleCharges sourceA2481 sourceB2481 sourceC2481 difference raw33866; decide +kernel
    rw [ha]
    exact (canonical33866 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2481 + difference 2 1) (sourceB2481 + difference 1 2) sourceC2481) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4740) := by
    have ha : (tripleCharges (sourceA2481 + difference 2 1) (sourceB2481 + difference 1 2) sourceC2481) = raw33867 := by
      apply Matrix.ext; unfold tripleCharges sourceA2481 sourceB2481 sourceC2481 difference raw33867; decide +kernel
    rw [ha]
    exact (canonical33867 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2481 + difference 2 3) (sourceB2481 + difference 3 2) sourceC2481) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4805) := by
    have ha : (tripleCharges (sourceA2481 + difference 2 3) (sourceB2481 + difference 3 2) sourceC2481) = raw32235 := by
      apply Matrix.ext; unfold tripleCharges sourceA2481 sourceB2481 sourceC2481 difference raw32235; decide +kernel
    rw [ha]
    exact (canonical32235 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2481 + difference 2 4) (sourceB2481 + difference 4 2) sourceC2481) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4803) := by
    have ha : (tripleCharges (sourceA2481 + difference 2 4) (sourceB2481 + difference 4 2) sourceC2481) = raw33868 := by
      apply Matrix.ext; unfold tripleCharges sourceA2481 sourceB2481 sourceC2481 difference raw33868; decide +kernel
    rw [ha]
    exact (canonical33868 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2481 + difference 2 5) (sourceB2481 + difference 5 2) sourceC2481) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4806) := by
    have ha : (tripleCharges (sourceA2481 + difference 2 5) (sourceB2481 + difference 5 2) sourceC2481) = raw33869 := by
      apply Matrix.ext; unfold tripleCharges sourceA2481 sourceB2481 sourceC2481 difference raw33869; decide +kernel
    rw [ha]
    exact (canonical33869 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2481 + difference 3 0) (sourceB2481 + difference 0 3) sourceC2481) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4410) := by
    have ha : (tripleCharges (sourceA2481 + difference 3 0) (sourceB2481 + difference 0 3) sourceC2481) = raw34185 := by
      apply Matrix.ext; unfold tripleCharges sourceA2481 sourceB2481 sourceC2481 difference raw34185; decide +kernel
    rw [ha]
    exact (canonical34185 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2481 + difference 3 1) (sourceB2481 + difference 1 3) sourceC2481) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4747) := by
    have ha : (tripleCharges (sourceA2481 + difference 3 1) (sourceB2481 + difference 1 3) sourceC2481) = raw34186 := by
      apply Matrix.ext; unfold tripleCharges sourceA2481 sourceB2481 sourceC2481 difference raw34186; decide +kernel
    rw [ha]
    exact (canonical34186 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2481 + difference 3 2) (sourceB2481 + difference 2 3) sourceC2481) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4783) := by
    have ha : (tripleCharges (sourceA2481 + difference 3 2) (sourceB2481 + difference 2 3) sourceC2481) = raw34187 := by
      apply Matrix.ext; unfold tripleCharges sourceA2481 sourceB2481 sourceC2481 difference raw34187; decide +kernel
    rw [ha]
    exact (canonical34187 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2481 + difference 3 4) (sourceB2481 + difference 4 3) sourceC2481) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4836) := by
    have ha : (tripleCharges (sourceA2481 + difference 3 4) (sourceB2481 + difference 4 3) sourceC2481) = raw34188 := by
      apply Matrix.ext; unfold tripleCharges sourceA2481 sourceB2481 sourceC2481 difference raw34188; decide +kernel
    rw [ha]
    exact (canonical34188 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2481 + difference 3 5) (sourceB2481 + difference 5 3) sourceC2481) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4840) := by
    have ha : (tripleCharges (sourceA2481 + difference 3 5) (sourceB2481 + difference 5 3) sourceC2481) = raw34189 := by
      apply Matrix.ext; unfold tripleCharges sourceA2481 sourceB2481 sourceC2481 difference raw34189; decide +kernel
    rw [ha]
    exact (canonical34189 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2481 + difference 4 0) (sourceB2481 + difference 0 4) sourceC2481) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4412) := by
    have ha : (tripleCharges (sourceA2481 + difference 4 0) (sourceB2481 + difference 0 4) sourceC2481) = raw34190 := by
      apply Matrix.ext; unfold tripleCharges sourceA2481 sourceB2481 sourceC2481 difference raw34190; decide +kernel
    rw [ha]
    exact (canonical34190 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2481 + difference 4 1) (sourceB2481 + difference 1 4) sourceC2481) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4750) := by
    have ha : (tripleCharges (sourceA2481 + difference 4 1) (sourceB2481 + difference 1 4) sourceC2481) = raw34191 := by
      apply Matrix.ext; unfold tripleCharges sourceA2481 sourceB2481 sourceC2481 difference raw34191; decide +kernel
    rw [ha]
    exact (canonical34191 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2481 + difference 4 2) (sourceB2481 + difference 2 4) sourceC2481) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4785) := by
    have ha : (tripleCharges (sourceA2481 + difference 4 2) (sourceB2481 + difference 2 4) sourceC2481) = raw34192 := by
      apply Matrix.ext; unfold tripleCharges sourceA2481 sourceB2481 sourceC2481 difference raw34192; decide +kernel
    rw [ha]
    exact (canonical34192 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2481 + difference 4 3) (sourceB2481 + difference 3 4) sourceC2481) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4839) := by
    have ha : (tripleCharges (sourceA2481 + difference 4 3) (sourceB2481 + difference 3 4) sourceC2481) = raw32245 := by
      apply Matrix.ext; unfold tripleCharges sourceA2481 sourceB2481 sourceC2481 difference raw32245; decide +kernel
    rw [ha]
    exact (canonical32245 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2481 + difference 4 5) (sourceB2481 + difference 5 4) sourceC2481) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4842) := by
    have ha : (tripleCharges (sourceA2481 + difference 4 5) (sourceB2481 + difference 5 4) sourceC2481) = raw34193 := by
      apply Matrix.ext; unfold tripleCharges sourceA2481 sourceB2481 sourceC2481 difference raw34193; decide +kernel
    rw [ha]
    exact (canonical34193 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2481 + difference 5 0) (sourceB2481 + difference 0 5) sourceC2481) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4424) := by
    have ha : (tripleCharges (sourceA2481 + difference 5 0) (sourceB2481 + difference 0 5) sourceC2481) = raw34194 := by
      apply Matrix.ext; unfold tripleCharges sourceA2481 sourceB2481 sourceC2481 difference raw34194; decide +kernel
    rw [ha]
    exact (canonical34194 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2481 + difference 5 1) (sourceB2481 + difference 1 5) sourceC2481) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4752) := by
    have ha : (tripleCharges (sourceA2481 + difference 5 1) (sourceB2481 + difference 1 5) sourceC2481) = raw34195 := by
      apply Matrix.ext; unfold tripleCharges sourceA2481 sourceB2481 sourceC2481 difference raw34195; decide +kernel
    rw [ha]
    exact (canonical34195 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2481 + difference 5 2) (sourceB2481 + difference 2 5) sourceC2481) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4787) := by
    have ha : (tripleCharges (sourceA2481 + difference 5 2) (sourceB2481 + difference 2 5) sourceC2481) = raw32906 := by
      apply Matrix.ext; unfold tripleCharges sourceA2481 sourceB2481 sourceC2481 difference raw32906; decide +kernel
    rw [ha]
    exact (canonical32906 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2481 + difference 5 3) (sourceB2481 + difference 3 5) sourceC2481) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4838) := by
    have ha : (tripleCharges (sourceA2481 + difference 5 3) (sourceB2481 + difference 3 5) sourceC2481) = raw32250 := by
      apply Matrix.ext; unfold tripleCharges sourceA2481 sourceB2481 sourceC2481 difference raw32250; decide +kernel
    rw [ha]
    exact (canonical32250 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2481 + difference 5 4) (sourceB2481 + difference 4 5) sourceC2481) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4835) := by
    have ha : (tripleCharges (sourceA2481 + difference 5 4) (sourceB2481 + difference 4 5) sourceC2481) = raw33649 := by
      apply Matrix.ext; unfold tripleCharges sourceA2481 sourceB2481 sourceC2481 difference raw33649; decide +kernel
    rw [ha]
    exact (canonical33649 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2481 sourceB2481 sourceC2481
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2481, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic124
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reindexCheck1998 : Integer.Sparse.reindex keyMap MixedData.row1998 = numericRow1998 := by decide +kernel

theorem numericCheck1998 (x : Master → ℝ) : Integer.Sparse.eval numericRow1998 x =
    (17280 : ℝ) * reducedSource1998 x := by
  norm_num [numericRow1998, reducedSource1998, Integer.Sparse.eval, Sparse.eval, nodeValue4407, nodeValue4410, nodeValue4412, nodeValue4424, nodeValue4471, nodeValue4740, nodeValue4747, nodeValue4750, nodeValue4752, nodeValue4783, nodeValue4785, nodeValue4787, nodeValue4803, nodeValue4805, nodeValue4806, nodeValue4813, nodeValue4835, nodeValue4836, nodeValue4838, nodeValue4839, nodeValue4840, nodeValue4842, nodeValue4867, nodeValue4869, nodeValue4870, nodeValue5105, nodeValue5138, nodeValue5170, nodeValue5172, nodeValue5173]
  ring

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Rows124
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero1998 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1998 (mixedVector B) = 0 := by
  have h4407 : mixedVector B (Sum.inr 4407) = Sparse.eval nodeValue4407 (mixedVector B) := by
    change mixedMoment B node4407 node4407Labels = _
    exact sound4407 B hB hF
  have h4410 : mixedVector B (Sum.inr 4410) = Sparse.eval nodeValue4410 (mixedVector B) := by
    change mixedMoment B node4410 node4410Labels = _
    exact sound4410 B hB hF
  have h4412 : mixedVector B (Sum.inr 4412) = Sparse.eval nodeValue4412 (mixedVector B) := by
    change mixedMoment B node4412 node4412Labels = _
    exact sound4412 B hB hF
  have h4424 : mixedVector B (Sum.inr 4424) = Sparse.eval nodeValue4424 (mixedVector B) := by
    change mixedMoment B node4424 node4424Labels = _
    exact sound4424 B hB hF
  have h4471 : mixedVector B (Sum.inr 4471) = Sparse.eval nodeValue4471 (mixedVector B) := by
    change mixedMoment B node4471 node4471Labels = _
    exact sound4471 B hB hF
  have h4740 : mixedVector B (Sum.inr 4740) = Sparse.eval nodeValue4740 (mixedVector B) := by
    change mixedMoment B node4740 node4740Labels = _
    exact sound4740 B hB hF
  have h4747 : mixedVector B (Sum.inr 4747) = Sparse.eval nodeValue4747 (mixedVector B) := by
    change mixedMoment B node4747 node4747Labels = _
    exact sound4747 B hB hF
  have h4750 : mixedVector B (Sum.inr 4750) = Sparse.eval nodeValue4750 (mixedVector B) := by
    change mixedMoment B node4750 node4750Labels = _
    exact sound4750 B hB hF
  have h4752 : mixedVector B (Sum.inr 4752) = Sparse.eval nodeValue4752 (mixedVector B) := by
    change mixedMoment B node4752 node4752Labels = _
    exact sound4752 B hB hF
  have h4783 : mixedVector B (Sum.inr 4783) = Sparse.eval nodeValue4783 (mixedVector B) := by
    change mixedMoment B node4783 node4783Labels = _
    exact sound4783 B hB hF
  have h4785 : mixedVector B (Sum.inr 4785) = Sparse.eval nodeValue4785 (mixedVector B) := by
    change mixedMoment B node4785 node4785Labels = _
    exact sound4785 B hB hF
  have h4787 : mixedVector B (Sum.inr 4787) = Sparse.eval nodeValue4787 (mixedVector B) := by
    change mixedMoment B node4787 node4787Labels = _
    exact sound4787 B hB hF
  have h4803 : mixedVector B (Sum.inr 4803) = Sparse.eval nodeValue4803 (mixedVector B) := by
    change mixedMoment B node4803 node4803Labels = _
    exact sound4803 B hB hF
  have h4805 : mixedVector B (Sum.inr 4805) = Sparse.eval nodeValue4805 (mixedVector B) := by
    change mixedMoment B node4805 node4805Labels = _
    exact sound4805 B hB hF
  have h4806 : mixedVector B (Sum.inr 4806) = Sparse.eval nodeValue4806 (mixedVector B) := by
    change mixedMoment B node4806 node4806Labels = _
    exact sound4806 B hB hF
  have h4813 : mixedVector B (Sum.inr 4813) = Sparse.eval nodeValue4813 (mixedVector B) := by
    change mixedMoment B node4813 node4813Labels = _
    exact sound4813 B hB hF
  have h4835 : mixedVector B (Sum.inr 4835) = Sparse.eval nodeValue4835 (mixedVector B) := by
    change mixedMoment B node4835 node4835Labels = _
    exact sound4835 B hB hF
  have h4836 : mixedVector B (Sum.inr 4836) = Sparse.eval nodeValue4836 (mixedVector B) := by
    change mixedMoment B node4836 node4836Labels = _
    exact sound4836 B hB hF
  have h4838 : mixedVector B (Sum.inr 4838) = Sparse.eval nodeValue4838 (mixedVector B) := by
    change mixedMoment B node4838 node4838Labels = _
    exact sound4838 B hB hF
  have h4839 : mixedVector B (Sum.inr 4839) = Sparse.eval nodeValue4839 (mixedVector B) := by
    change mixedMoment B node4839 node4839Labels = _
    exact sound4839 B hB hF
  have h4840 : mixedVector B (Sum.inr 4840) = Sparse.eval nodeValue4840 (mixedVector B) := by
    change mixedMoment B node4840 node4840Labels = _
    exact sound4840 B hB hF
  have h4842 : mixedVector B (Sum.inr 4842) = Sparse.eval nodeValue4842 (mixedVector B) := by
    change mixedMoment B node4842 node4842Labels = _
    exact sound4842 B hB hF
  have h4867 : mixedVector B (Sum.inr 4867) = Sparse.eval nodeValue4867 (mixedVector B) := by
    change mixedMoment B node4867 node4867Labels = _
    exact sound4867 B hB hF
  have h4869 : mixedVector B (Sum.inr 4869) = Sparse.eval nodeValue4869 (mixedVector B) := by
    change mixedMoment B node4869 node4869Labels = _
    exact sound4869 B hB hF
  have h4870 : mixedVector B (Sum.inr 4870) = Sparse.eval nodeValue4870 (mixedVector B) := by
    change mixedMoment B node4870 node4870Labels = _
    exact sound4870 B hB hF
  have h5105 : mixedVector B (Sum.inr 5105) = Sparse.eval nodeValue5105 (mixedVector B) := by
    change mixedMoment B node5105 node5105Labels = _
    exact sound5105 B hB hF
  have h5138 : mixedVector B (Sum.inr 5138) = Sparse.eval nodeValue5138 (mixedVector B) := by
    change mixedMoment B node5138 node5138Labels = _
    exact sound5138 B hB hF
  have h5170 : mixedVector B (Sum.inr 5170) = Sparse.eval nodeValue5170 (mixedVector B) := by
    change mixedMoment B node5170 node5170Labels = _
    exact sound5170 B hB hF
  have h5172 : mixedVector B (Sum.inr 5172) = Sparse.eval nodeValue5172 (mixedVector B) := by
    change mixedMoment B node5172 node5172Labels = _
    exact sound5172_e B hB hF
  have h5173 : mixedVector B (Sum.inr 5173) = Sparse.eval nodeValue5173 (mixedVector B) := by
    change mixedMoment B node5173 node5173Labels = _
    exact sound5173 B hB hF
  simpa only [sourceForm2481, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4407, h4410, h4412, h4424, h4471, h4740, h4747, h4750, h4752, h4783, h4785, h4787, h4803, h4805, h4806, h4813, h4835, h4836, h4838, h4839, h4840, h4842, h4867, h4869, h4870, h5105, h5138, h5170, h5172, h5173, reducedSource1998] using sourceEq2481 B hB

theorem rowSound1998_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1998 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1998, numericCheck1998, reducedZero1998 B hB hF, mul_zero]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedSourceBridge.rowSound1998_e_oai := @OAI.MUB6.Certificate.MixedSourceBridge.rowSound1998_e_oai
