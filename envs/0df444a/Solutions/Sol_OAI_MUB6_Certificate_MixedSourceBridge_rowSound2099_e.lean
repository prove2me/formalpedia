-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedSourceBridge.rowSound2099_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-08T23:06:52.11174+00:00
-- url     : https://prove2.me/submissions/9901b592-c3ad-4daa-81ca-1395a87607c8

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E070
import Definitions.Def_OAIQ106E086
import Definitions.Def_OAIQ106E088
import Definitions.Def_OAIQ106E091
import Definitions.Def_OAIQ106E093
import Definitions.Def_OAIQ106E094
import Definitions.Def_OAIQ106E095
import Definitions.Def_OAIQ106E193
import Definitions.Def_OAIQ106E100
import Definitions.Def_OAIQ106E195
import Definitions.Def_OAIQ106E101
import Definitions.Def_OAIQ106E106
import Definitions.Def_OAIQ106E108
import Definitions.Def_OAIQ106E109
import Definitions.Def_OAIQ106E119
import Definitions.Def_OAIQ106E121
import Definitions.Def_OAIQ106E126
import Definitions.Def_OAIQ106E140
import Definitions.Def_OAIQ106E147
import Definitions.Def_OAIQ106E170
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound5387_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound5439_e

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

theorem canonical1545 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1545 raw1545Labels = mixedMoment B node4672 node4672Labels := by
  calc
    mixedMoment B raw1545 raw1545Labels = mixedMoment B raw1545step0 raw1545step0Labels := by
      have ha : raw1545step0 = (fun i j => raw1545 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1545step0 raw1545; decide +kernel
      have hl : raw1545step0Labels = raw1545Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1545 raw1545Labels permutation152 permutation4
    mixedMoment B raw1545step0 raw1545step0Labels = mixedMoment B raw1545step1 raw1545step1Labels := by
      have ha : raw1545step1 = raw1545step0 := by apply Matrix.ext; unfold raw1545step1 raw1545step0; decide +kernel
      have hl : raw1545step0Labels = labelEmbedding7 ∘ raw1545step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1545step0 raw1545step0Labels raw1545step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4672 node4672Labels := by rfl

theorem canonical1546 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1546 raw1546Labels = mixedMoment B node1798 node1798Labels := by
  calc
    mixedMoment B raw1546 raw1546Labels = mixedMoment B raw1546step0 raw1546step0Labels := by
      have ha : raw1546step0 = (fun i j => raw1546 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1546step0 raw1546; decide +kernel
      have hl : raw1546step0Labels = raw1546Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1546 raw1546Labels permutation152 permutation4
    _ = mixedMoment B node1798 node1798Labels := by rfl

theorem canonical1547 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1547 raw1547Labels = mixedMoment B node2067 node2067Labels := by
  calc
    mixedMoment B raw1547 raw1547Labels = mixedMoment B raw1547step0 raw1547step0Labels := by
      have ha : raw1547step0 = (fun i j => raw1547 (permutation176 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1547step0 raw1547; decide +kernel
      have hl : raw1547step0Labels = raw1547Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1547 raw1547Labels permutation176 permutation6
    mixedMoment B raw1547step0 raw1547step0Labels = mixedMoment B raw1547step1 raw1547step1Labels := by
      have ha : raw1547step1 = -raw1547step0 := by apply Matrix.ext; change ∀ i j, raw1547step1 i j = -(raw1547step0 i j); unfold raw1547step1 raw1547step0; decide +kernel
      have hl : raw1547step1Labels = raw1547step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1547step1 raw1547step1Labels = mixedMoment B raw1547step2 raw1547step2Labels := by
      have ha : raw1547step2 = raw1547step1 := by apply Matrix.ext; unfold raw1547step2 raw1547step1; decide +kernel
      have hl : raw1547step1Labels = labelEmbedding1 ∘ raw1547step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1547step1 raw1547step1Labels raw1547step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2067 node2067Labels := by rfl

theorem canonical1569 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1569 raw1569Labels = mixedMoment B node4685 node4685Labels := by
  calc
    mixedMoment B raw1569 raw1569Labels = mixedMoment B raw1569step0 raw1569step0Labels := by
      have ha : raw1569step0 = (fun i j => raw1569 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1569step0 raw1569; decide +kernel
      have hl : raw1569step0Labels = raw1569Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1569 raw1569Labels permutation152 permutation4
    mixedMoment B raw1569step0 raw1569step0Labels = mixedMoment B raw1569step1 raw1569step1Labels := by
      have ha : raw1569step1 = raw1569step0 := by apply Matrix.ext; unfold raw1569step1 raw1569step0; decide +kernel
      have hl : raw1569step0Labels = labelEmbedding7 ∘ raw1569step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1569step0 raw1569step0Labels raw1569step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4685 node4685Labels := by rfl

theorem canonical1570 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1570 raw1570Labels = mixedMoment B node1811 node1811Labels := by
  calc
    mixedMoment B raw1570 raw1570Labels = mixedMoment B raw1570step0 raw1570step0Labels := by
      have ha : raw1570step0 = (fun i j => raw1570 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1570step0 raw1570; decide +kernel
      have hl : raw1570step0Labels = raw1570Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1570 raw1570Labels permutation152 permutation4
    _ = mixedMoment B node1811 node1811Labels := by rfl

theorem canonical1571 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1571 raw1571Labels = mixedMoment B node2156 node2156Labels := by
  calc
    mixedMoment B raw1571 raw1571Labels = mixedMoment B raw1571step0 raw1571step0Labels := by
      have ha : raw1571step0 = (fun i j => raw1571 (permutation170 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1571step0 raw1571; decide +kernel
      have hl : raw1571step0Labels = raw1571Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1571 raw1571Labels permutation170 permutation6
    mixedMoment B raw1571step0 raw1571step0Labels = mixedMoment B raw1571step1 raw1571step1Labels := by
      have ha : raw1571step1 = -raw1571step0 := by apply Matrix.ext; change ∀ i j, raw1571step1 i j = -(raw1571step0 i j); unfold raw1571step1 raw1571step0; decide +kernel
      have hl : raw1571step1Labels = raw1571step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1571step1 raw1571step1Labels = mixedMoment B raw1571step2 raw1571step2Labels := by
      have ha : raw1571step2 = raw1571step1 := by apply Matrix.ext; unfold raw1571step2 raw1571step1; decide +kernel
      have hl : raw1571step1Labels = labelEmbedding1 ∘ raw1571step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1571step1 raw1571step1Labels raw1571step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2156 node2156Labels := by rfl

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

theorem canonical1779 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1779 raw1779Labels = mixedMoment B node4859 node4859Labels := by
  calc
    mixedMoment B raw1779 raw1779Labels = mixedMoment B raw1779step0 raw1779step0Labels := by
      have ha : raw1779step0 = (fun i j => raw1779 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1779step0 raw1779; decide +kernel
      have hl : raw1779step0Labels = raw1779Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1779 raw1779Labels permutation152 permutation4
    mixedMoment B raw1779step0 raw1779step0Labels = mixedMoment B raw1779step1 raw1779step1Labels := by
      have ha : raw1779step1 = raw1779step0 := by apply Matrix.ext; unfold raw1779step1 raw1779step0; decide +kernel
      have hl : raw1779step0Labels = labelEmbedding7 ∘ raw1779step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1779step0 raw1779step0Labels raw1779step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4859 node4859Labels := by rfl

theorem canonical1780 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1780 raw1780Labels = mixedMoment B node2100 node2100Labels := by
  calc
    mixedMoment B raw1780 raw1780Labels = mixedMoment B raw1780step0 raw1780step0Labels := by
      have ha : raw1780step0 = (fun i j => raw1780 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1780step0 raw1780; decide +kernel
      have hl : raw1780step0Labels = raw1780Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1780 raw1780Labels permutation152 permutation4
    _ = mixedMoment B node2100 node2100Labels := by rfl

theorem canonical1781 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1781 raw1781Labels = mixedMoment B node2100 node2100Labels := by
  calc
    mixedMoment B raw1781 raw1781Labels = mixedMoment B raw1781step0 raw1781step0Labels := by
      have ha : raw1781step0 = (fun i j => raw1781 (permutation176 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1781step0 raw1781; decide +kernel
      have hl : raw1781step0Labels = raw1781Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1781 raw1781Labels permutation176 permutation6
    mixedMoment B raw1781step0 raw1781step0Labels = mixedMoment B raw1781step1 raw1781step1Labels := by
      have ha : raw1781step1 = -raw1781step0 := by apply Matrix.ext; change ∀ i j, raw1781step1 i j = -(raw1781step0 i j); unfold raw1781step1 raw1781step0; decide +kernel
      have hl : raw1781step1Labels = raw1781step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1781step1 raw1781step1Labels = mixedMoment B raw1781step2 raw1781step2Labels := by
      have ha : raw1781step2 = raw1781step1 := by apply Matrix.ext; unfold raw1781step2 raw1781step1; decide +kernel
      have hl : raw1781step1Labels = labelEmbedding1 ∘ raw1781step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1781step1 raw1781step1Labels raw1781step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2100 node2100Labels := by rfl

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

theorem canonical18299 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18299 raw18299Labels = mixedMoment B node5387 node5387Labels := by
  calc
    mixedMoment B raw18299 raw18299Labels = mixedMoment B raw18299step0 raw18299step0Labels := by
      have hz : ∀ j, raw18299 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw18299step0 = (fun i j => raw18299 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw18299step0 raw18299; decide +kernel
      have hl : raw18299step0Labels = raw18299Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18299 raw18299Labels permutation434 hz
    _ = mixedMoment B node5387 node5387Labels := by rfl

theorem canonical18302 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18302 raw18302Labels = mixedMoment B node5439 node5439Labels := by
  calc
    mixedMoment B raw18302 raw18302Labels = mixedMoment B raw18302step0 raw18302step0Labels := by
      have hz : ∀ j, raw18302 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw18302step0 = (fun i j => raw18302 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw18302step0 raw18302; decide +kernel
      have hl : raw18302step0Labels = raw18302Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18302 raw18302Labels permutation434 hz
    _ = mixedMoment B node5439 node5439Labels := by rfl

theorem canonical18303 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18303 raw18303Labels = mixedMoment B node5387 node5387Labels := by
  calc
    mixedMoment B raw18303 raw18303Labels = mixedMoment B raw18303step0 raw18303step0Labels := by
      have hz : ∀ j, raw18303 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18303step0 = (fun i j => raw18303 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18303step0 raw18303; decide +kernel
      have hl : raw18303step0Labels = raw18303Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18303 raw18303Labels permutation346 hz
    _ = mixedMoment B node5387 node5387Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical143
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical18345 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18345 raw18345Labels = mixedMoment B node5448 node5448Labels := by
  calc
    mixedMoment B raw18345 raw18345Labels = mixedMoment B raw18345step0 raw18345step0Labels := by
      have hz : ∀ j, raw18345 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18345step0 = (fun i j => raw18345 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18345step0 raw18345; decide +kernel
      have hl : raw18345step0Labels = raw18345Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18345 raw18345Labels permutation346 hz
    mixedMoment B raw18345step0 raw18345step0Labels = mixedMoment B raw18345step1 raw18345step1Labels := by
      have ha : raw18345step1 = (fun i j => raw18345step0 (permutation60 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18345step1 raw18345step0; decide +kernel
      have hl : raw18345step1Labels = raw18345step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18345step0 raw18345step0Labels permutation60 permutation3
    mixedMoment B raw18345step1 raw18345step1Labels = mixedMoment B raw18345step2 raw18345step2Labels := by
      have ha : raw18345step2 = raw18345step1 := by apply Matrix.ext; unfold raw18345step2 raw18345step1; decide +kernel
      have hl : raw18345step1Labels = labelEmbedding6 ∘ raw18345step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18345step1 raw18345step1Labels raw18345step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5448 node5448Labels := by rfl

theorem canonical18350 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18350 raw18350Labels = mixedMoment B node5439 node5439Labels := by
  calc
    mixedMoment B raw18350 raw18350Labels = mixedMoment B raw18350step0 raw18350step0Labels := by
      have hz : ∀ j, raw18350 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw18350step0 = (fun i j => raw18350 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw18350step0 raw18350; decide +kernel
      have hl : raw18350step0Labels = raw18350Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18350 raw18350Labels permutation520 hz
    _ = mixedMoment B node5439 node5439Labels := by rfl

theorem canonical18351 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18351 raw18351Labels = mixedMoment B node5437 node5437Labels := by
  calc
    mixedMoment B raw18351 raw18351Labels = mixedMoment B raw18351step0 raw18351step0Labels := by
      have ha : raw18351step0 = (fun i j => raw18351 (permutation170 i) (permutation2 j)) := by apply Matrix.ext; unfold raw18351step0 raw18351; decide +kernel
      have hl : raw18351step0Labels = raw18351Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18351 raw18351Labels permutation170 permutation2
    _ = mixedMoment B node5437 node5437Labels := by rfl

theorem canonical18352 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18352 raw18352Labels = mixedMoment B node5384 node5384Labels := by
  calc
    mixedMoment B raw18352 raw18352Labels = mixedMoment B raw18352step0 raw18352step0Labels := by
      have hz : ∀ j, raw18352 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18352step0 = (fun i j => raw18352 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18352step0 raw18352; decide +kernel
      have hl : raw18352step0Labels = raw18352Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18352 raw18352Labels permutation346 hz
    mixedMoment B raw18352step0 raw18352step0Labels = mixedMoment B raw18352step1 raw18352step1Labels := by
      have ha : raw18352step1 = (fun i j => raw18352step0 (permutation61 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18352step1 raw18352step0; decide +kernel
      have hl : raw18352step1Labels = raw18352step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18352step0 raw18352step0Labels permutation61 permutation3
    mixedMoment B raw18352step1 raw18352step1Labels = mixedMoment B raw18352step2 raw18352step2Labels := by
      have ha : raw18352step2 = raw18352step1 := by apply Matrix.ext; unfold raw18352step2 raw18352step1; decide +kernel
      have hl : raw18352step1Labels = labelEmbedding6 ∘ raw18352step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18352step1 raw18352step1Labels raw18352step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5384 node5384Labels := by rfl

theorem canonical18356 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18356 raw18356Labels = mixedMoment B node5384 node5384Labels := by
  calc
    mixedMoment B raw18356 raw18356Labels = mixedMoment B raw18356step0 raw18356step0Labels := by
      have hz : ∀ j, raw18356 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18356step0 = (fun i j => raw18356 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18356step0 raw18356; decide +kernel
      have hl : raw18356step0Labels = raw18356Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18356 raw18356Labels permutation346 hz
    mixedMoment B raw18356step0 raw18356step0Labels = mixedMoment B raw18356step1 raw18356step1Labels := by
      have ha : raw18356step1 = (fun i j => raw18356step0 (permutation60 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18356step1 raw18356step0; decide +kernel
      have hl : raw18356step1Labels = raw18356step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18356step0 raw18356step0Labels permutation60 permutation3
    mixedMoment B raw18356step1 raw18356step1Labels = mixedMoment B raw18356step2 raw18356step2Labels := by
      have ha : raw18356step2 = raw18356step1 := by apply Matrix.ext; unfold raw18356step2 raw18356step1; decide +kernel
      have hl : raw18356step1Labels = labelEmbedding6 ∘ raw18356step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18356step1 raw18356step1Labels raw18356step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5384 node5384Labels := by rfl

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

theorem canonical1941 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1941 raw1941Labels = mixedMoment B node4967 node4967Labels := by
  calc
    mixedMoment B raw1941 raw1941Labels = mixedMoment B raw1941step0 raw1941step0Labels := by
      have ha : raw1941step0 = (fun i j => raw1941 (permutation152 i) (permutation5 j)) := by apply Matrix.ext; unfold raw1941step0 raw1941; decide +kernel
      have hl : raw1941step0Labels = raw1941Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1941 raw1941Labels permutation152 permutation5
    mixedMoment B raw1941step0 raw1941step0Labels = mixedMoment B raw1941step1 raw1941step1Labels := by
      have ha : raw1941step1 = raw1941step0 := by apply Matrix.ext; unfold raw1941step1 raw1941step0; decide +kernel
      have hl : raw1941step0Labels = labelEmbedding8 ∘ raw1941step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1941step0 raw1941step0Labels raw1941step1Labels labelEmbedding8 hl
    _ = mixedMoment B node4967 node4967Labels := by rfl

theorem canonical1942 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1942 raw1942Labels = mixedMoment B node2814 node2814Labels := by
  calc
    mixedMoment B raw1942 raw1942Labels = mixedMoment B raw1942step0 raw1942step0Labels := by
      have ha : raw1942step0 = (fun i j => raw1942 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1942step0 raw1942; decide +kernel
      have hl : raw1942step0Labels = raw1942Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1942 raw1942Labels permutation152 permutation4
    _ = mixedMoment B node2814 node2814Labels := by rfl

theorem canonical1943 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1943 raw1943Labels = mixedMoment B node3585 node3585Labels := by
  calc
    mixedMoment B raw1943 raw1943Labels = mixedMoment B raw1943step0 raw1943step0Labels := by
      have ha : raw1943step0 = (fun i j => raw1943 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw1943step0 raw1943; decide +kernel
      have hl : raw1943step0Labels = raw1943Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1943 raw1943Labels permutation152 permutation3
    mixedMoment B raw1943step0 raw1943step0Labels = mixedMoment B raw1943step1 raw1943step1Labels := by
      have ha : raw1943step1 = -raw1943step0 := by apply Matrix.ext; change ∀ i j, raw1943step1 i j = -(raw1943step0 i j); unfold raw1943step1 raw1943step0; decide +kernel
      have hl : raw1943step1Labels = raw1943step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1943step1 raw1943step1Labels = mixedMoment B raw1943step2 raw1943step2Labels := by
      have ha : raw1943step2 = raw1943step1 := by apply Matrix.ext; unfold raw1943step2 raw1943step1; decide +kernel
      have hl : raw1943step1Labels = labelEmbedding1 ∘ raw1943step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1943step1 raw1943step1Labels raw1943step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3585 node3585Labels := by rfl

theorem canonical1947 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1947 raw1947Labels = mixedMoment B node4969 node4969Labels := by
  calc
    mixedMoment B raw1947 raw1947Labels = mixedMoment B raw1947step0 raw1947step0Labels := by
      have ha : raw1947step0 = (fun i j => raw1947 (permutation152 i) (permutation5 j)) := by apply Matrix.ext; unfold raw1947step0 raw1947; decide +kernel
      have hl : raw1947step0Labels = raw1947Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1947 raw1947Labels permutation152 permutation5
    mixedMoment B raw1947step0 raw1947step0Labels = mixedMoment B raw1947step1 raw1947step1Labels := by
      have ha : raw1947step1 = raw1947step0 := by apply Matrix.ext; unfold raw1947step1 raw1947step0; decide +kernel
      have hl : raw1947step0Labels = labelEmbedding8 ∘ raw1947step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1947step0 raw1947step0Labels raw1947step1Labels labelEmbedding8 hl
    _ = mixedMoment B node4969 node4969Labels := by rfl

theorem canonical1948 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1948 raw1948Labels = mixedMoment B node2804 node2804Labels := by
  calc
    mixedMoment B raw1948 raw1948Labels = mixedMoment B raw1948step0 raw1948step0Labels := by
      have ha : raw1948step0 = (fun i j => raw1948 (permutation164 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1948step0 raw1948; decide +kernel
      have hl : raw1948step0Labels = raw1948Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1948 raw1948Labels permutation164 permutation4
    _ = mixedMoment B node2804 node2804Labels := by rfl

theorem canonical1949 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1949 raw1949Labels = mixedMoment B node3586 node3586Labels := by
  calc
    mixedMoment B raw1949 raw1949Labels = mixedMoment B raw1949step0 raw1949step0Labels := by
      have ha : raw1949step0 = (fun i j => raw1949 (permutation153 i) (permutation3 j)) := by apply Matrix.ext; unfold raw1949step0 raw1949; decide +kernel
      have hl : raw1949step0Labels = raw1949Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1949 raw1949Labels permutation153 permutation3
    mixedMoment B raw1949step0 raw1949step0Labels = mixedMoment B raw1949step1 raw1949step1Labels := by
      have ha : raw1949step1 = -raw1949step0 := by apply Matrix.ext; change ∀ i j, raw1949step1 i j = -(raw1949step0 i j); unfold raw1949step1 raw1949step0; decide +kernel
      have hl : raw1949step1Labels = raw1949step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1949step1 raw1949step1Labels = mixedMoment B raw1949step2 raw1949step2Labels := by
      have ha : raw1949step2 = raw1949step1 := by apply Matrix.ext; unfold raw1949step2 raw1949step1; decide +kernel
      have hl : raw1949step1Labels = labelEmbedding1 ∘ raw1949step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1949step1 raw1949step1Labels raw1949step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3586 node3586Labels := by rfl

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

theorem canonical2427 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2427 raw2427Labels = mixedMoment B node5374 node5374Labels := by
  calc
    mixedMoment B raw2427 raw2427Labels = mixedMoment B raw2427step0 raw2427step0Labels := by
      have ha : raw2427step0 = (fun i j => raw2427 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2427step0 raw2427; decide +kernel
      have hl : raw2427step0Labels = raw2427Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2427 raw2427Labels permutation152 permutation4
    mixedMoment B raw2427step0 raw2427step0Labels = mixedMoment B raw2427step1 raw2427step1Labels := by
      have ha : raw2427step1 = raw2427step0 := by apply Matrix.ext; unfold raw2427step1 raw2427step0; decide +kernel
      have hl : raw2427step0Labels = labelEmbedding7 ∘ raw2427step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2427step0 raw2427step0Labels raw2427step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5374 node5374Labels := by rfl

theorem canonical2428 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2428 raw2428Labels = mixedMoment B node3713 node3713Labels := by
  calc
    mixedMoment B raw2428 raw2428Labels = mixedMoment B raw2428step0 raw2428step0Labels := by
      have ha : raw2428step0 = (fun i j => raw2428 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2428step0 raw2428; decide +kernel
      have hl : raw2428step0Labels = raw2428Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2428 raw2428Labels permutation152 permutation4
    _ = mixedMoment B node3713 node3713Labels := by rfl

theorem canonical2429 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2429 raw2429Labels = mixedMoment B node3713 node3713Labels := by
  calc
    mixedMoment B raw2429 raw2429Labels = mixedMoment B raw2429step0 raw2429step0Labels := by
      have ha : raw2429step0 = (fun i j => raw2429 (permutation176 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2429step0 raw2429; decide +kernel
      have hl : raw2429step0Labels = raw2429Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2429 raw2429Labels permutation176 permutation6
    mixedMoment B raw2429step0 raw2429step0Labels = mixedMoment B raw2429step1 raw2429step1Labels := by
      have ha : raw2429step1 = -raw2429step0 := by apply Matrix.ext; change ∀ i j, raw2429step1 i j = -(raw2429step0 i j); unfold raw2429step1 raw2429step0; decide +kernel
      have hl : raw2429step1Labels = raw2429step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2429step1 raw2429step1Labels = mixedMoment B raw2429step2 raw2429step2Labels := by
      have ha : raw2429step2 = raw2429step1 := by apply Matrix.ext; unfold raw2429step2 raw2429step1; decide +kernel
      have hl : raw2429step1Labels = labelEmbedding1 ∘ raw2429step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2429step1 raw2429step1Labels raw2429step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3713 node3713Labels := by rfl

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

theorem canonical2436 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2436 raw2436Labels = mixedMoment B node5383 node5383Labels := by
  calc
    mixedMoment B raw2436 raw2436Labels = mixedMoment B raw2436step0 raw2436step0Labels := by
      have ha : raw2436step0 = (fun i j => raw2436 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2436step0 raw2436; decide +kernel
      have hl : raw2436step0Labels = raw2436Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2436 raw2436Labels permutation152 permutation4
    mixedMoment B raw2436step0 raw2436step0Labels = mixedMoment B raw2436step1 raw2436step1Labels := by
      have ha : raw2436step1 = raw2436step0 := by apply Matrix.ext; unfold raw2436step1 raw2436step0; decide +kernel
      have hl : raw2436step0Labels = labelEmbedding7 ∘ raw2436step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2436step0 raw2436step0Labels raw2436step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5383 node5383Labels := by rfl

theorem canonical2437 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2437 raw2437Labels = mixedMoment B node3731 node3731Labels := by
  calc
    mixedMoment B raw2437 raw2437Labels = mixedMoment B raw2437step0 raw2437step0Labels := by
      have ha : raw2437step0 = (fun i j => raw2437 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2437step0 raw2437; decide +kernel
      have hl : raw2437step0Labels = raw2437Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2437 raw2437Labels permutation152 permutation4
    _ = mixedMoment B node3731 node3731Labels := by rfl

theorem canonical2438 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2438 raw2438Labels = mixedMoment B node3867 node3867Labels := by
  calc
    mixedMoment B raw2438 raw2438Labels = mixedMoment B raw2438step0 raw2438step0Labels := by
      have ha : raw2438step0 = (fun i j => raw2438 (permutation176 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2438step0 raw2438; decide +kernel
      have hl : raw2438step0Labels = raw2438Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2438 raw2438Labels permutation176 permutation6
    mixedMoment B raw2438step0 raw2438step0Labels = mixedMoment B raw2438step1 raw2438step1Labels := by
      have ha : raw2438step1 = -raw2438step0 := by apply Matrix.ext; change ∀ i j, raw2438step1 i j = -(raw2438step0 i j); unfold raw2438step1 raw2438step0; decide +kernel
      have hl : raw2438step1Labels = raw2438step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2438step1 raw2438step1Labels = mixedMoment B raw2438step2 raw2438step2Labels := by
      have ha : raw2438step2 = raw2438step1 := by apply Matrix.ext; unfold raw2438step2 raw2438step1; decide +kernel
      have hl : raw2438step1Labels = labelEmbedding1 ∘ raw2438step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2438step1 raw2438step1Labels raw2438step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3867 node3867Labels := by rfl

theorem canonical2439 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2439 raw2439Labels = mixedMoment B node5384 node5384Labels := by
  calc
    mixedMoment B raw2439 raw2439Labels = mixedMoment B raw2439step0 raw2439step0Labels := by
      have ha : raw2439step0 = (fun i j => raw2439 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2439step0 raw2439; decide +kernel
      have hl : raw2439step0Labels = raw2439Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2439 raw2439Labels permutation32 permutation4
    mixedMoment B raw2439step0 raw2439step0Labels = mixedMoment B raw2439step1 raw2439step1Labels := by
      have ha : raw2439step1 = raw2439step0 := by apply Matrix.ext; unfold raw2439step1 raw2439step0; decide +kernel
      have hl : raw2439step0Labels = labelEmbedding7 ∘ raw2439step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2439step0 raw2439step0Labels raw2439step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5384 node5384Labels := by rfl

theorem canonical2440 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2440 raw2440Labels = mixedMoment B node3732 node3732Labels := by
  calc
    mixedMoment B raw2440 raw2440Labels = mixedMoment B raw2440step0 raw2440step0Labels := by
      have ha : raw2440step0 = (fun i j => raw2440 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2440step0 raw2440; decide +kernel
      have hl : raw2440step0Labels = raw2440Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2440 raw2440Labels permutation32 permutation4
    _ = mixedMoment B node3732 node3732Labels := by rfl

theorem canonical2441 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2441 raw2441Labels = mixedMoment B node3811 node3811Labels := by
  calc
    mixedMoment B raw2441 raw2441Labels = mixedMoment B raw2441step0 raw2441step0Labels := by
      have ha : raw2441step0 = (fun i j => raw2441 (permutation149 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2441step0 raw2441; decide +kernel
      have hl : raw2441step0Labels = raw2441Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2441 raw2441Labels permutation149 permutation6
    mixedMoment B raw2441step0 raw2441step0Labels = mixedMoment B raw2441step1 raw2441step1Labels := by
      have ha : raw2441step1 = raw2441step0 := by apply Matrix.ext; unfold raw2441step1 raw2441step0; decide +kernel
      have hl : raw2441step0Labels = labelEmbedding1 ∘ raw2441step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2441step0 raw2441step0Labels raw2441step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3811 node3811Labels := by rfl

theorem canonical2535 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2535 raw2535Labels = mixedMoment B node5437 node5437Labels := by
  calc
    mixedMoment B raw2535 raw2535Labels = mixedMoment B raw2535step0 raw2535step0Labels := by
      have ha : raw2535step0 = (fun i j => raw2535 (permutation152 i) (permutation5 j)) := by apply Matrix.ext; unfold raw2535step0 raw2535; decide +kernel
      have hl : raw2535step0Labels = raw2535Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2535 raw2535Labels permutation152 permutation5
    mixedMoment B raw2535step0 raw2535step0Labels = mixedMoment B raw2535step1 raw2535step1Labels := by
      have ha : raw2535step1 = raw2535step0 := by apply Matrix.ext; unfold raw2535step1 raw2535step0; decide +kernel
      have hl : raw2535step0Labels = labelEmbedding8 ∘ raw2535step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2535step0 raw2535step0Labels raw2535step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5437 node5437Labels := by rfl

theorem canonical2536 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2536 raw2536Labels = mixedMoment B node3899 node3899Labels := by
  calc
    mixedMoment B raw2536 raw2536Labels = mixedMoment B raw2536step0 raw2536step0Labels := by
      have ha : raw2536step0 = (fun i j => raw2536 (permutation373 i) (permutation2 j)) := by apply Matrix.ext; unfold raw2536step0 raw2536; decide +kernel
      have hl : raw2536step0Labels = raw2536Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2536 raw2536Labels permutation373 permutation2
    _ = mixedMoment B node3899 node3899Labels := by rfl

theorem canonical2537 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2537 raw2537Labels = mixedMoment B node3899 node3899Labels := by
  calc
    mixedMoment B raw2537 raw2537Labels = mixedMoment B raw2537step0 raw2537step0Labels := by
      have ha : raw2537step0 = (fun i j => raw2537 (permutation161 i) (permutation3 j)) := by apply Matrix.ext; unfold raw2537step0 raw2537; decide +kernel
      have hl : raw2537step0Labels = raw2537Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2537 raw2537Labels permutation161 permutation3
    mixedMoment B raw2537step0 raw2537step0Labels = mixedMoment B raw2537step1 raw2537step1Labels := by
      have ha : raw2537step1 = -raw2537step0 := by apply Matrix.ext; change ∀ i j, raw2537step1 i j = -(raw2537step0 i j); unfold raw2537step1 raw2537step0; decide +kernel
      have hl : raw2537step1Labels = raw2537step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2537step1 raw2537step1Labels = mixedMoment B raw2537step2 raw2537step2Labels := by
      have ha : raw2537step2 = raw2537step1 := by apply Matrix.ext; unfold raw2537step2 raw2537step1; decide +kernel
      have hl : raw2537step1Labels = labelEmbedding1 ∘ raw2537step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2537step1 raw2537step1Labels raw2537step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3899 node3899Labels := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical250
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical32031 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32031 raw32031Labels = mixedMoment B node4967 node4967Labels := by
  calc
    _ = mixedMoment B node4967 node4967Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical268
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical34417 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34417 raw34417Labels = mixedMoment B node4969 node4969Labels := by
  calc
    mixedMoment B raw34417 raw34417Labels = mixedMoment B raw34417step0 raw34417step0Labels := by
      have ha : raw34417step0 = (fun i j => raw34417 (permutation161 i) (permutation2 j)) := by apply Matrix.ext; unfold raw34417step0 raw34417; decide +kernel
      have hl : raw34417step0Labels = raw34417Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34417 raw34417Labels permutation161 permutation2
    _ = mixedMoment B node4969 node4969Labels := by rfl

theorem canonical34421 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34421 raw34421Labels = mixedMoment B node4969 node4969Labels := by
  calc
    mixedMoment B raw34421 raw34421Labels = mixedMoment B raw34421step0 raw34421step0Labels := by
      have ha : raw34421step0 = (fun i j => raw34421 (permutation155 i) (permutation2 j)) := by apply Matrix.ext; unfold raw34421step0 raw34421; decide +kernel
      have hl : raw34421step0Labels = raw34421Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34421 raw34421Labels permutation155 permutation2
    _ = mixedMoment B node4969 node4969Labels := by rfl

theorem canonical34424 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34424 raw34424Labels = mixedMoment B node4969 node4969Labels := by
  calc
    mixedMoment B raw34424 raw34424Labels = mixedMoment B raw34424step0 raw34424step0Labels := by
      have ha : raw34424step0 = (fun i j => raw34424 (permutation153 i) (permutation2 j)) := by apply Matrix.ext; unfold raw34424step0 raw34424; decide +kernel
      have hl : raw34424step0Labels = raw34424Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34424 raw34424Labels permutation153 permutation2
    _ = mixedMoment B node4969 node4969Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical271
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical34788 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34788 raw34788Labels = mixedMoment B node5384 node5384Labels := by
  calc
    mixedMoment B raw34788 raw34788Labels = mixedMoment B raw34788step0 raw34788step0Labels := by
      have hz : ∀ j, raw34788 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw34788step0 = (fun i j => raw34788 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw34788step0 raw34788; decide +kernel
      have hl : raw34788step0Labels = raw34788Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34788 raw34788Labels permutation434 hz
    mixedMoment B raw34788step0 raw34788step0Labels = mixedMoment B raw34788step1 raw34788step1Labels := by
      have ha : raw34788step1 = (fun i j => raw34788step0 (permutation60 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34788step1 raw34788step0; decide +kernel
      have hl : raw34788step1Labels = raw34788step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34788step0 raw34788step0Labels permutation60 permutation3
    mixedMoment B raw34788step1 raw34788step1Labels = mixedMoment B raw34788step2 raw34788step2Labels := by
      have ha : raw34788step2 = raw34788step1 := by apply Matrix.ext; unfold raw34788step2 raw34788step1; decide +kernel
      have hl : raw34788step1Labels = labelEmbedding6 ∘ raw34788step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34788step1 raw34788step1Labels raw34788step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5384 node5384Labels := by rfl

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

theorem canonical35551 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35551 raw35551Labels = mixedMoment B node4685 node4685Labels := by
  calc
    mixedMoment B raw35551 raw35551Labels = mixedMoment B raw35551step0 raw35551step0Labels := by
      have ha : raw35551step0 = (fun i j => raw35551 (permutation265 i) (permutation3 j)) := by apply Matrix.ext; unfold raw35551step0 raw35551; decide +kernel
      have hl : raw35551step0Labels = raw35551Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35551 raw35551Labels permutation265 permutation3
    mixedMoment B raw35551step0 raw35551step0Labels = mixedMoment B raw35551step1 raw35551step1Labels := by
      have ha : raw35551step1 = raw35551step0 := by apply Matrix.ext; unfold raw35551step1 raw35551step0; decide +kernel
      have hl : raw35551step0Labels = labelEmbedding6 ∘ raw35551step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35551step0 raw35551step0Labels raw35551step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4685 node4685Labels := by rfl

theorem canonical35552 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35552 raw35552Labels = mixedMoment B node5387 node5387Labels := by
  calc
    mixedMoment B raw35552 raw35552Labels = mixedMoment B raw35552step0 raw35552step0Labels := by
      have hz : ∀ j, raw35552 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw35552step0 = (fun i j => raw35552 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw35552step0 raw35552; decide +kernel
      have hl : raw35552step0Labels = raw35552Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35552 raw35552Labels permutation520 hz
    _ = mixedMoment B node5387 node5387Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical289
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical37027 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37027 raw37027Labels = mixedMoment B node4859 node4859Labels := by
  calc
    mixedMoment B raw37027 raw37027Labels = mixedMoment B raw37027step0 raw37027step0Labels := by
      have ha : raw37027step0 = (fun i j => raw37027 (permutation283 i) (permutation3 j)) := by apply Matrix.ext; unfold raw37027step0 raw37027; decide +kernel
      have hl : raw37027step0Labels = raw37027Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37027 raw37027Labels permutation283 permutation3
    mixedMoment B raw37027step0 raw37027step0Labels = mixedMoment B raw37027step1 raw37027step1Labels := by
      have ha : raw37027step1 = raw37027step0 := by apply Matrix.ext; unfold raw37027step1 raw37027step0; decide +kernel
      have hl : raw37027step0Labels = labelEmbedding6 ∘ raw37027step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37027step0 raw37027step0Labels raw37027step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4859 node4859Labels := by rfl

theorem canonical37028 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37028 raw37028Labels = mixedMoment B node5448 node5448Labels := by
  calc
    mixedMoment B raw37028 raw37028Labels = mixedMoment B raw37028step0 raw37028step0Labels := by
      have hz : ∀ j, raw37028 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw37028step0 = (fun i j => raw37028 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw37028step0 raw37028; decide +kernel
      have hl : raw37028step0Labels = raw37028Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37028 raw37028Labels permutation434 hz
    mixedMoment B raw37028step0 raw37028step0Labels = mixedMoment B raw37028step1 raw37028step1Labels := by
      have ha : raw37028step1 = (fun i j => raw37028step0 (permutation60 i) (permutation3 j)) := by apply Matrix.ext; unfold raw37028step1 raw37028step0; decide +kernel
      have hl : raw37028step1Labels = raw37028step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37028step0 raw37028step0Labels permutation60 permutation3
    mixedMoment B raw37028step1 raw37028step1Labels = mixedMoment B raw37028step2 raw37028step2Labels := by
      have ha : raw37028step2 = raw37028step1 := by apply Matrix.ext; unfold raw37028step2 raw37028step1; decide +kernel
      have hl : raw37028step1Labels = labelEmbedding6 ∘ raw37028step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37028step1 raw37028step1Labels raw37028step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5448 node5448Labels := by rfl

theorem canonical37029 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37029 raw37029Labels = mixedMoment B node5448 node5448Labels := by
  calc
    mixedMoment B raw37029 raw37029Labels = mixedMoment B raw37029step0 raw37029step0Labels := by
      have hz : ∀ j, raw37029 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw37029step0 = (fun i j => raw37029 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw37029step0 raw37029; decide +kernel
      have hl : raw37029step0Labels = raw37029Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37029 raw37029Labels permutation520 hz
    mixedMoment B raw37029step0 raw37029step0Labels = mixedMoment B raw37029step1 raw37029step1Labels := by
      have ha : raw37029step1 = (fun i j => raw37029step0 (permutation60 i) (permutation3 j)) := by apply Matrix.ext; unfold raw37029step1 raw37029step0; decide +kernel
      have hl : raw37029step1Labels = raw37029step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37029step0 raw37029step0Labels permutation60 permutation3
    mixedMoment B raw37029step1 raw37029step1Labels = mixedMoment B raw37029step2 raw37029step2Labels := by
      have ha : raw37029step2 = raw37029step1 := by apply Matrix.ext; unfold raw37029step2 raw37029step1; decide +kernel
      have hl : raw37029step1Labels = labelEmbedding6 ∘ raw37029step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37029step1 raw37029step1Labels raw37029step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5448 node5448Labels := by rfl

theorem canonical37030 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37030 raw37030Labels = mixedMoment B node5383 node5383Labels := by
  calc
    mixedMoment B raw37030 raw37030Labels = mixedMoment B raw37030step0 raw37030step0Labels := by
      have ha : raw37030step0 = (fun i j => raw37030 (permutation333 i) (permutation5 j)) := by apply Matrix.ext; unfold raw37030step0 raw37030; decide +kernel
      have hl : raw37030step0Labels = raw37030Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37030 raw37030Labels permutation333 permutation5
    mixedMoment B raw37030step0 raw37030step0Labels = mixedMoment B raw37030step1 raw37030step1Labels := by
      have ha : raw37030step1 = -raw37030step0 := by apply Matrix.ext; change ∀ i j, raw37030step1 i j = -(raw37030step0 i j); unfold raw37030step1 raw37030step0; decide +kernel
      have hl : raw37030step1Labels = raw37030step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw37030step1 raw37030step1Labels = mixedMoment B raw37030step2 raw37030step2Labels := by
      have ha : raw37030step2 = raw37030step1 := by apply Matrix.ext; unfold raw37030step2 raw37030step1; decide +kernel
      have hl : raw37030step1Labels = labelEmbedding8 ∘ raw37030step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37030step1 raw37030step1Labels raw37030step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5383 node5383Labels := by rfl

theorem canonical37031 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37031 raw37031Labels = mixedMoment B node4672 node4672Labels := by
  calc
    mixedMoment B raw37031 raw37031Labels = mixedMoment B raw37031step0 raw37031step0Labels := by
      have ha : raw37031step0 = (fun i j => raw37031 (permutation286 i) (permutation3 j)) := by apply Matrix.ext; unfold raw37031step0 raw37031; decide +kernel
      have hl : raw37031step0Labels = raw37031Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37031 raw37031Labels permutation286 permutation3
    mixedMoment B raw37031step0 raw37031step0Labels = mixedMoment B raw37031step1 raw37031step1Labels := by
      have ha : raw37031step1 = raw37031step0 := by apply Matrix.ext; unfold raw37031step1 raw37031step0; decide +kernel
      have hl : raw37031step0Labels = labelEmbedding6 ∘ raw37031step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37031step0 raw37031step0Labels raw37031step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4672 node4672Labels := by rfl

theorem canonical37032 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37032 raw37032Labels = mixedMoment B node5384 node5384Labels := by
  calc
    mixedMoment B raw37032 raw37032Labels = mixedMoment B raw37032step0 raw37032step0Labels := by
      have hz : ∀ j, raw37032 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw37032step0 = (fun i j => raw37032 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw37032step0 raw37032; decide +kernel
      have hl : raw37032step0Labels = raw37032Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37032 raw37032Labels permutation434 hz
    mixedMoment B raw37032step0 raw37032step0Labels = mixedMoment B raw37032step1 raw37032step1Labels := by
      have ha : raw37032step1 = (fun i j => raw37032step0 (permutation61 i) (permutation3 j)) := by apply Matrix.ext; unfold raw37032step1 raw37032step0; decide +kernel
      have hl : raw37032step1Labels = raw37032step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37032step0 raw37032step0Labels permutation61 permutation3
    mixedMoment B raw37032step1 raw37032step1Labels = mixedMoment B raw37032step2 raw37032step2Labels := by
      have ha : raw37032step2 = raw37032step1 := by apply Matrix.ext; unfold raw37032step2 raw37032step1; decide +kernel
      have hl : raw37032step1Labels = labelEmbedding6 ∘ raw37032step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37032step1 raw37032step1Labels raw37032step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5384 node5384Labels := by rfl

theorem canonical37033 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37033 raw37033Labels = mixedMoment B node5384 node5384Labels := by
  calc
    mixedMoment B raw37033 raw37033Labels = mixedMoment B raw37033step0 raw37033step0Labels := by
      have hz : ∀ j, raw37033 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw37033step0 = (fun i j => raw37033 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw37033step0 raw37033; decide +kernel
      have hl : raw37033step0Labels = raw37033Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37033 raw37033Labels permutation520 hz
    mixedMoment B raw37033step0 raw37033step0Labels = mixedMoment B raw37033step1 raw37033step1Labels := by
      have ha : raw37033step1 = (fun i j => raw37033step0 (permutation61 i) (permutation3 j)) := by apply Matrix.ext; unfold raw37033step1 raw37033step0; decide +kernel
      have hl : raw37033step1Labels = raw37033step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37033step0 raw37033step0Labels permutation61 permutation3
    mixedMoment B raw37033step1 raw37033step1Labels = mixedMoment B raw37033step2 raw37033step2Labels := by
      have ha : raw37033step2 = raw37033step1 := by apply Matrix.ext; unfold raw37033step2 raw37033step1; decide +kernel
      have hl : raw37033step1Labels = labelEmbedding6 ∘ raw37033step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37033step1 raw37033step1Labels raw37033step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5384 node5384Labels := by rfl

theorem canonical37034 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37034 raw37034Labels = mixedMoment B node5374 node5374Labels := by
  calc
    mixedMoment B raw37034 raw37034Labels = mixedMoment B raw37034step0 raw37034step0Labels := by
      have ha : raw37034step0 = (fun i j => raw37034 (permutation286 i) (permutation3 j)) := by apply Matrix.ext; unfold raw37034step0 raw37034; decide +kernel
      have hl : raw37034step0Labels = raw37034Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37034 raw37034Labels permutation286 permutation3
    mixedMoment B raw37034step0 raw37034step0Labels = mixedMoment B raw37034step1 raw37034step1Labels := by
      have ha : raw37034step1 = raw37034step0 := by apply Matrix.ext; unfold raw37034step1 raw37034step0; decide +kernel
      have hl : raw37034step0Labels = labelEmbedding6 ∘ raw37034step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37034step0 raw37034step0Labels raw37034step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5374 node5374Labels := by rfl

theorem canonical37035 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37035 raw37035Labels = mixedMoment B node4672 node4672Labels := by
  calc
    mixedMoment B raw37035 raw37035Labels = mixedMoment B raw37035step0 raw37035step0Labels := by
      have ha : raw37035step0 = (fun i j => raw37035 (permutation284 i) (permutation3 j)) := by apply Matrix.ext; unfold raw37035step0 raw37035; decide +kernel
      have hl : raw37035step0Labels = raw37035Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37035 raw37035Labels permutation284 permutation3
    mixedMoment B raw37035step0 raw37035step0Labels = mixedMoment B raw37035step1 raw37035step1Labels := by
      have ha : raw37035step1 = raw37035step0 := by apply Matrix.ext; unfold raw37035step1 raw37035step0; decide +kernel
      have hl : raw37035step0Labels = labelEmbedding6 ∘ raw37035step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37035step0 raw37035step0Labels raw37035step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4672 node4672Labels := by rfl

theorem canonical37036 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37036 raw37036Labels = mixedMoment B node5384 node5384Labels := by
  calc
    mixedMoment B raw37036 raw37036Labels = mixedMoment B raw37036step0 raw37036step0Labels := by
      have hz : ∀ j, raw37036 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw37036step0 = (fun i j => raw37036 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw37036step0 raw37036; decide +kernel
      have hl : raw37036step0Labels = raw37036Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37036 raw37036Labels permutation520 hz
    mixedMoment B raw37036step0 raw37036step0Labels = mixedMoment B raw37036step1 raw37036step1Labels := by
      have ha : raw37036step1 = (fun i j => raw37036step0 (permutation60 i) (permutation3 j)) := by apply Matrix.ext; unfold raw37036step1 raw37036step0; decide +kernel
      have hl : raw37036step1Labels = raw37036step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37036step0 raw37036step0Labels permutation60 permutation3
    mixedMoment B raw37036step1 raw37036step1Labels = mixedMoment B raw37036step2 raw37036step2Labels := by
      have ha : raw37036step2 = raw37036step1 := by apply Matrix.ext; unfold raw37036step2 raw37036step1; decide +kernel
      have hl : raw37036step1Labels = labelEmbedding6 ∘ raw37036step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37036step1 raw37036step1Labels raw37036step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5384 node5384Labels := by rfl

theorem canonical37037 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37037 raw37037Labels = mixedMoment B node5374 node5374Labels := by
  calc
    mixedMoment B raw37037 raw37037Labels = mixedMoment B raw37037step0 raw37037step0Labels := by
      have ha : raw37037step0 = (fun i j => raw37037 (permutation284 i) (permutation3 j)) := by apply Matrix.ext; unfold raw37037step0 raw37037; decide +kernel
      have hl : raw37037step0Labels = raw37037Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37037 raw37037Labels permutation284 permutation3
    mixedMoment B raw37037step0 raw37037step0Labels = mixedMoment B raw37037step1 raw37037step1Labels := by
      have ha : raw37037step1 = raw37037step0 := by apply Matrix.ext; unfold raw37037step1 raw37037step0; decide +kernel
      have hl : raw37037step0Labels = labelEmbedding6 ∘ raw37037step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37037step0 raw37037step0Labels raw37037step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5374 node5374Labels := by rfl

theorem canonical37038 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37038 raw37038Labels = mixedMoment B node4672 node4672Labels := by
  calc
    mixedMoment B raw37038 raw37038Labels = mixedMoment B raw37038step0 raw37038step0Labels := by
      have ha : raw37038step0 = (fun i j => raw37038 (permutation283 i) (permutation3 j)) := by apply Matrix.ext; unfold raw37038step0 raw37038; decide +kernel
      have hl : raw37038step0Labels = raw37038Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37038 raw37038Labels permutation283 permutation3
    mixedMoment B raw37038step0 raw37038step0Labels = mixedMoment B raw37038step1 raw37038step1Labels := by
      have ha : raw37038step1 = raw37038step0 := by apply Matrix.ext; unfold raw37038step1 raw37038step0; decide +kernel
      have hl : raw37038step0Labels = labelEmbedding6 ∘ raw37038step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37038step0 raw37038step0Labels raw37038step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4672 node4672Labels := by rfl

theorem canonical37039 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37039 raw37039Labels = mixedMoment B node5374 node5374Labels := by
  calc
    mixedMoment B raw37039 raw37039Labels = mixedMoment B raw37039step0 raw37039step0Labels := by
      have ha : raw37039step0 = (fun i j => raw37039 (permutation283 i) (permutation3 j)) := by apply Matrix.ext; unfold raw37039step0 raw37039; decide +kernel
      have hl : raw37039step0Labels = raw37039Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37039 raw37039Labels permutation283 permutation3
    mixedMoment B raw37039step0 raw37039step0Labels = mixedMoment B raw37039step1 raw37039step1Labels := by
      have ha : raw37039step1 = raw37039step0 := by apply Matrix.ext; unfold raw37039step1 raw37039step0; decide +kernel
      have hl : raw37039step0Labels = labelEmbedding6 ∘ raw37039step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37039step0 raw37039step0Labels raw37039step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5374 node5374Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical94
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical12080 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12080 raw12080Labels = mixedMoment B node5439 node5439Labels := by
  calc
    mixedMoment B raw12080 raw12080Labels = mixedMoment B raw12080step0 raw12080step0Labels := by
      have hz : ∀ j, raw12080 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw12080step0 = (fun i j => raw12080 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw12080step0 raw12080; decide +kernel
      have hl : raw12080step0Labels = raw12080Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12080 raw12080Labels permutation346 hz
    _ = mixedMoment B node5439 node5439Labels := by rfl

theorem canonical12089 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12089 raw12089Labels = mixedMoment B node5166 node5166Labels := by
  calc
    _ = mixedMoment B node5166 node5166Labels := by rfl

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

theorem singleton4672 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4672 node4672Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1798 node1798Labels + mixedMoment B node2067 node2067Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1545 singletonSmall4672
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4672) = raw1545Labels := by decide +kernel
  rw [hl, canonical1545 B hB] at h
  have hc0 : mixedMoment B raw1545 (Fin.cases (0 : Fin 2) singletonSmall4672) =
      mixedMoment B node1798 node1798Labels := by
    have ha : raw1545 = raw1546 := by apply Matrix.ext; unfold raw1545 raw1546; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4672 = raw1546Labels := by decide +kernel
    rw [ha, hj, canonical1546 B hB]
  have hc1 : mixedMoment B raw1545 (Fin.cases (1 : Fin 2) singletonSmall4672) =
      mixedMoment B node2067 node2067Labels := by
    have ha : raw1545 = raw1547 := by apply Matrix.ext; unfold raw1545 raw1547; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4672 = raw1547Labels := by decide +kernel
    rw [ha, hj, canonical1547 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4685 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4685 node4685Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1811 node1811Labels + mixedMoment B node2156 node2156Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1569 singletonSmall4685
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4685) = raw1569Labels := by decide +kernel
  rw [hl, canonical1569 B hB] at h
  have hc0 : mixedMoment B raw1569 (Fin.cases (0 : Fin 2) singletonSmall4685) =
      mixedMoment B node1811 node1811Labels := by
    have ha : raw1569 = raw1570 := by apply Matrix.ext; unfold raw1569 raw1570; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4685 = raw1570Labels := by decide +kernel
    rw [ha, hj, canonical1570 B hB]
  have hc1 : mixedMoment B raw1569 (Fin.cases (1 : Fin 2) singletonSmall4685) =
      mixedMoment B node2156 node2156Labels := by
    have ha : raw1569 = raw1571 := by apply Matrix.ext; unfold raw1569 raw1571; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4685 = raw1571Labels := by decide +kernel
    rw [ha, hj, canonical1571 B hB]
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

theorem singleton4859 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4859 node4859Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2100 node2100Labels + mixedMoment B node2100 node2100Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1779 singletonSmall4859
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4859) = raw1779Labels := by decide +kernel
  rw [hl, canonical1779 B hB] at h
  have hc0 : mixedMoment B raw1779 (Fin.cases (0 : Fin 2) singletonSmall4859) =
      mixedMoment B node2100 node2100Labels := by
    have ha : raw1779 = raw1780 := by apply Matrix.ext; unfold raw1779 raw1780; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4859 = raw1780Labels := by decide +kernel
    rw [ha, hj, canonical1780 B hB]
  have hc1 : mixedMoment B raw1779 (Fin.cases (1 : Fin 2) singletonSmall4859) =
      mixedMoment B node2100 node2100Labels := by
    have ha : raw1779 = raw1781 := by apply Matrix.ext; unfold raw1779 raw1781; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4859 = raw1781Labels := by decide +kernel
    rw [ha, hj, canonical1781 B hB]
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

theorem singleton4967 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4967 node4967Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2814 node2814Labels + mixedMoment B node3585 node3585Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1941 singletonSmall4967
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4967) = raw1941Labels := by decide +kernel
  rw [hl, canonical1941 B hB] at h
  have hc0 : mixedMoment B raw1941 (Fin.cases (0 : Fin 2) singletonSmall4967) =
      mixedMoment B node2814 node2814Labels := by
    have ha : raw1941 = raw1942 := by apply Matrix.ext; unfold raw1941 raw1942; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4967 = raw1942Labels := by decide +kernel
    rw [ha, hj, canonical1942 B hB]
  have hc1 : mixedMoment B raw1941 (Fin.cases (1 : Fin 2) singletonSmall4967) =
      mixedMoment B node3585 node3585Labels := by
    have ha : raw1941 = raw1943 := by apply Matrix.ext; unfold raw1941 raw1943; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4967 = raw1943Labels := by decide +kernel
    rw [ha, hj, canonical1943 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4969 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4969 node4969Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2804 node2804Labels + mixedMoment B node3586 node3586Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1947 singletonSmall4969
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4969) = raw1947Labels := by decide +kernel
  rw [hl, canonical1947 B hB] at h
  have hc0 : mixedMoment B raw1947 (Fin.cases (0 : Fin 2) singletonSmall4969) =
      mixedMoment B node2804 node2804Labels := by
    have ha : raw1947 = raw1948 := by apply Matrix.ext; unfold raw1947 raw1948; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4969 = raw1948Labels := by decide +kernel
    rw [ha, hj, canonical1948 B hB]
  have hc1 : mixedMoment B raw1947 (Fin.cases (1 : Fin 2) singletonSmall4969) =
      mixedMoment B node3586 node3586Labels := by
    have ha : raw1947 = raw1949 := by apply Matrix.ext; unfold raw1947 raw1949; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4969 = raw1949Labels := by decide +kernel
    rw [ha, hj, canonical1949 B hB]
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

theorem singleton5374 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5374 node5374Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3713 node3713Labels + mixedMoment B node3713 node3713Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2427 singletonSmall5374
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5374) = raw2427Labels := by decide +kernel
  rw [hl, canonical2427 B hB] at h
  have hc0 : mixedMoment B raw2427 (Fin.cases (0 : Fin 2) singletonSmall5374) =
      mixedMoment B node3713 node3713Labels := by
    have ha : raw2427 = raw2428 := by apply Matrix.ext; unfold raw2427 raw2428; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5374 = raw2428Labels := by decide +kernel
    rw [ha, hj, canonical2428 B hB]
  have hc1 : mixedMoment B raw2427 (Fin.cases (1 : Fin 2) singletonSmall5374) =
      mixedMoment B node3713 node3713Labels := by
    have ha : raw2427 = raw2429 := by apply Matrix.ext; unfold raw2427 raw2429; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5374 = raw2429Labels := by decide +kernel
    rw [ha, hj, canonical2429 B hB]
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

theorem singleton5383 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5383 node5383Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3731 node3731Labels + mixedMoment B node3867 node3867Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2436 singletonSmall5383
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5383) = raw2436Labels := by decide +kernel
  rw [hl, canonical2436 B hB] at h
  have hc0 : mixedMoment B raw2436 (Fin.cases (0 : Fin 2) singletonSmall5383) =
      mixedMoment B node3731 node3731Labels := by
    have ha : raw2436 = raw2437 := by apply Matrix.ext; unfold raw2436 raw2437; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5383 = raw2437Labels := by decide +kernel
    rw [ha, hj, canonical2437 B hB]
  have hc1 : mixedMoment B raw2436 (Fin.cases (1 : Fin 2) singletonSmall5383) =
      mixedMoment B node3867 node3867Labels := by
    have ha : raw2436 = raw2438 := by apply Matrix.ext; unfold raw2436 raw2438; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5383 = raw2438Labels := by decide +kernel
    rw [ha, hj, canonical2438 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton5384 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5384 node5384Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3732 node3732Labels + mixedMoment B node3811 node3811Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2439 singletonSmall5384
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5384) = raw2439Labels := by decide +kernel
  rw [hl, canonical2439 B hB] at h
  have hc0 : mixedMoment B raw2439 (Fin.cases (0 : Fin 2) singletonSmall5384) =
      mixedMoment B node3732 node3732Labels := by
    have ha : raw2439 = raw2440 := by apply Matrix.ext; unfold raw2439 raw2440; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5384 = raw2440Labels := by decide +kernel
    rw [ha, hj, canonical2440 B hB]
  have hc1 : mixedMoment B raw2439 (Fin.cases (1 : Fin 2) singletonSmall5384) =
      mixedMoment B node3811 node3811Labels := by
    have ha : raw2439 = raw2441 := by apply Matrix.ext; unfold raw2439 raw2441; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5384 = raw2441Labels := by decide +kernel
    rw [ha, hj, canonical2441 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton5437 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5437 node5437Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3899 node3899Labels + mixedMoment B node3899 node3899Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2535 singletonSmall5437
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5437) = raw2535Labels := by decide +kernel
  rw [hl, canonical2535 B hB] at h
  have hc0 : mixedMoment B raw2535 (Fin.cases (0 : Fin 2) singletonSmall5437) =
      mixedMoment B node3899 node3899Labels := by
    have ha : raw2535 = raw2536 := by apply Matrix.ext; unfold raw2535 raw2536; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5437 = raw2536Labels := by decide +kernel
    rw [ha, hj, canonical2536 B hB]
  have hc1 : mixedMoment B raw2535 (Fin.cases (1 : Fin 2) singletonSmall5437) =
      mixedMoment B node3899 node3899Labels := by
    have ha : raw2535 = raw2537 := by apply Matrix.ext; unfold raw2535 raw2537; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5437 = raw2537Labels := by decide +kernel
    rw [ha, hj, canonical2537 B hB]
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

theorem sound1798 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1798 node1798Labels = Sparse.eval nodeValue1798 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1798) = mixedMoment B node1798 node1798Labels := rfl
  simpa [nodeValue1798, Sparse.eval] using hc.symm

theorem sound1811 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1811 node1811Labels = Sparse.eval nodeValue1811 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1811) = mixedMoment B node1811 node1811Labels := rfl
  simpa [nodeValue1811, Sparse.eval] using hc.symm

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

theorem sound2067 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2067 node2067Labels = Sparse.eval nodeValue2067 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2067) = mixedMoment B node2067 node2067Labels := rfl
  simpa [nodeValue2067, Sparse.eval] using hc.symm

theorem sound2100 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2100 node2100Labels = Sparse.eval nodeValue2100 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2100) = mixedMoment B node2100 node2100Labels := rfl
  simpa [nodeValue2100, Sparse.eval] using hc.symm

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

theorem sound2156 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2156 node2156Labels = Sparse.eval nodeValue2156 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2156) = mixedMoment B node2156 node2156Labels := rfl
  simpa [nodeValue2156, Sparse.eval] using hc.symm

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

theorem sound2804 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2804 node2804Labels = Sparse.eval nodeValue2804 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2804) = mixedMoment B node2804 node2804Labels := rfl
  simpa [nodeValue2804, Sparse.eval] using hc.symm

theorem sound2814 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2814 node2814Labels = Sparse.eval nodeValue2814 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2814) = mixedMoment B node2814 node2814Labels := rfl
  simpa [nodeValue2814, Sparse.eval] using hc.symm

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

theorem sound3585 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3585 node3585Labels = Sparse.eval nodeValue3585 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3585) = mixedMoment B node3585 node3585Labels := rfl
  simpa [nodeValue3585, Sparse.eval] using hc.symm

theorem sound3586 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3586 node3586Labels = Sparse.eval nodeValue3586 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3586) = mixedMoment B node3586 node3586Labels := rfl
  simpa [nodeValue3586, Sparse.eval] using hc.symm

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

theorem sound3713 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3713 node3713Labels = Sparse.eval nodeValue3713 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3713) = mixedMoment B node3713 node3713Labels := rfl
  simpa [nodeValue3713, Sparse.eval] using hc.symm

theorem sound3731 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3731 node3731Labels = Sparse.eval nodeValue3731 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3731) = mixedMoment B node3731 node3731Labels := rfl
  simpa [nodeValue3731, Sparse.eval] using hc.symm

theorem sound3732 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3732 node3732Labels = Sparse.eval nodeValue3732 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3732) = mixedMoment B node3732 node3732Labels := rfl
  simpa [nodeValue3732, Sparse.eval] using hc.symm

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

theorem sound3811 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3811 node3811Labels = Sparse.eval nodeValue3811 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3811) = mixedMoment B node3811 node3811Labels := rfl
  simpa [nodeValue3811, Sparse.eval] using hc.symm

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

theorem sound3867 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3867 node3867Labels = Sparse.eval nodeValue3867 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3867) = mixedMoment B node3867 node3867Labels := rfl
  simpa [nodeValue3867, Sparse.eval] using hc.symm

theorem sound3885 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3885 node3885Labels = Sparse.eval nodeValue3885 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3885) = mixedMoment B node3885 node3885Labels := rfl
  simpa [nodeValue3885, Sparse.eval] using hc.symm

theorem sound3899 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3899 node3899Labels = Sparse.eval nodeValue3899 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3899) = mixedMoment B node3899 node3899Labels := rfl
  simpa [nodeValue3899, Sparse.eval] using hc.symm

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

theorem sound4672 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4672 node4672Labels = Sparse.eval nodeValue4672 (mixedVector B) := by
  have h := singleton4672 B _hB
  rw [sound1798 B _hB _hF, sound2067 B _hB _hF] at h
  norm_num [nodeValue4672, nodeValue1798, nodeValue2067, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4685 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4685 node4685Labels = Sparse.eval nodeValue4685 (mixedVector B) := by
  have h := singleton4685 B _hB
  rw [sound1811 B _hB _hF, sound2156 B _hB _hF] at h
  norm_num [nodeValue4685, nodeValue1811, nodeValue2156, Sparse.eval] at h ⊢
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

theorem sound4859 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4859 node4859Labels = Sparse.eval nodeValue4859 (mixedVector B) := by
  have h := singleton4859 B _hB
  rw [sound2100 B _hB _hF] at h
  norm_num [nodeValue4859, nodeValue2100, Sparse.eval] at h ⊢
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

theorem sound4967 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4967 node4967Labels = Sparse.eval nodeValue4967 (mixedVector B) := by
  have h := singleton4967 B _hB
  rw [sound2814 B _hB _hF, sound3585 B _hB _hF] at h
  norm_num [nodeValue4967, nodeValue2814, nodeValue3585, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4969 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4969 node4969Labels = Sparse.eval nodeValue4969 (mixedVector B) := by
  have h := singleton4969 B _hB
  rw [sound2804 B _hB _hF, sound3586 B _hB _hF] at h
  norm_num [nodeValue4969, nodeValue2804, nodeValue3586, Sparse.eval] at h ⊢
  linarith only [h]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros80
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero5166 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node5166 node5166Labels = 0 := by
  exact mixedMoment_alpha B hF node5166 node5166Labels 1 permutation161
    (by decide +kernel)

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

theorem sound5166 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5166 node5166Labels = Sparse.eval nodeValue5166 (mixedVector B) := by
  simpa only [nodeValue5166, Sparse.eval_nil] using zero5166 B _hB _hF

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

theorem sound5374 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5374 node5374Labels = Sparse.eval nodeValue5374 (mixedVector B) := by
  have h := singleton5374 B _hB
  rw [sound3713 B _hB _hF] at h
  norm_num [nodeValue5374, nodeValue3713, Sparse.eval] at h ⊢
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

theorem sound5383 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5383 node5383Labels = Sparse.eval nodeValue5383 (mixedVector B) := by
  have h := singleton5383 B _hB
  rw [sound3731 B _hB _hF, sound3867 B _hB _hF] at h
  norm_num [nodeValue5383, nodeValue3731, nodeValue3867, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5384 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5384 node5384Labels = Sparse.eval nodeValue5384 (mixedVector B) := by
  have h := singleton5384 B _hB
  rw [sound3732 B _hB _hF, sound3811 B _hB _hF] at h
  norm_num [nodeValue5384, nodeValue3732, nodeValue3811, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5437 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5437 node5437Labels = Sparse.eval nodeValue5437 (mixedVector B) := by
  have h := singleton5437 B _hB
  rw [sound3899 B _hB _hF] at h
  norm_num [nodeValue5437, nodeValue3899, Sparse.eval] at h ⊢
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

theorem sound5448 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5448 node5448Labels = Sparse.eval nodeValue5448 (mixedVector B) := by
  have h := singleton5448 B _hB
  rw [sound3885 B _hB _hF] at h
  norm_num [nodeValue5448, nodeValue3885, Sparse.eval] at h ⊢
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources82
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sourceEq2639 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2639 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2639 + difference 0 1) (sourceB2639 + difference 1 0) sourceC2639) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4859) := by
    have ha : (tripleCharges (sourceA2639 + difference 0 1) (sourceB2639 + difference 1 0) sourceC2639) = raw37027 := by
      apply Matrix.ext; unfold tripleCharges sourceA2639 sourceB2639 sourceC2639 difference raw37027; decide +kernel
    rw [ha]
    exact (canonical37027 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2639 + difference 0 2) (sourceB2639 + difference 2 0) sourceC2639) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5448) := by
    have ha : (tripleCharges (sourceA2639 + difference 0 2) (sourceB2639 + difference 2 0) sourceC2639) = raw18345 := by
      apply Matrix.ext; unfold tripleCharges sourceA2639 sourceB2639 sourceC2639 difference raw18345; decide +kernel
    rw [ha]
    exact (canonical18345 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2639 + difference 0 3) (sourceB2639 + difference 3 0) sourceC2639) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5448) := by
    have ha : (tripleCharges (sourceA2639 + difference 0 3) (sourceB2639 + difference 3 0) sourceC2639) = raw37028 := by
      apply Matrix.ext; unfold tripleCharges sourceA2639 sourceB2639 sourceC2639 difference raw37028; decide +kernel
    rw [ha]
    exact (canonical37028 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2639 + difference 0 4) (sourceB2639 + difference 4 0) sourceC2639) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5448) := by
    have ha : (tripleCharges (sourceA2639 + difference 0 4) (sourceB2639 + difference 4 0) sourceC2639) = raw37029 := by
      apply Matrix.ext; unfold tripleCharges sourceA2639 sourceB2639 sourceC2639 difference raw37029; decide +kernel
    rw [ha]
    exact (canonical37029 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2639 + difference 0 5) (sourceB2639 + difference 5 0) sourceC2639) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5383) := by
    have ha : (tripleCharges (sourceA2639 + difference 0 5) (sourceB2639 + difference 5 0) sourceC2639) = raw37030 := by
      apply Matrix.ext; unfold tripleCharges sourceA2639 sourceB2639 sourceC2639 difference raw37030; decide +kernel
    rw [ha]
    exact (canonical37030 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2639 + difference 1 0) (sourceB2639 + difference 0 1) sourceC2639) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5166) := by
    have ha : (tripleCharges (sourceA2639 + difference 1 0) (sourceB2639 + difference 0 1) sourceC2639) = raw12089 := by
      apply Matrix.ext; unfold tripleCharges sourceA2639 sourceB2639 sourceC2639 difference raw12089; decide +kernel
    rw [ha]
    exact (canonical12089 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2639 + difference 1 2) (sourceB2639 + difference 2 1) sourceC2639) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5439) := by
    have ha : (tripleCharges (sourceA2639 + difference 1 2) (sourceB2639 + difference 2 1) sourceC2639) = raw12080 := by
      apply Matrix.ext; unfold tripleCharges sourceA2639 sourceB2639 sourceC2639 difference raw12080; decide +kernel
    rw [ha]
    exact (canonical12080 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2639 + difference 1 3) (sourceB2639 + difference 3 1) sourceC2639) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5439) := by
    have ha : (tripleCharges (sourceA2639 + difference 1 3) (sourceB2639 + difference 3 1) sourceC2639) = raw18302 := by
      apply Matrix.ext; unfold tripleCharges sourceA2639 sourceB2639 sourceC2639 difference raw18302; decide +kernel
    rw [ha]
    exact (canonical18302 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2639 + difference 1 4) (sourceB2639 + difference 4 1) sourceC2639) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5439) := by
    have ha : (tripleCharges (sourceA2639 + difference 1 4) (sourceB2639 + difference 4 1) sourceC2639) = raw18350 := by
      apply Matrix.ext; unfold tripleCharges sourceA2639 sourceB2639 sourceC2639 difference raw18350; decide +kernel
    rw [ha]
    exact (canonical18350 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2639 + difference 1 5) (sourceB2639 + difference 5 1) sourceC2639) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5437) := by
    have ha : (tripleCharges (sourceA2639 + difference 1 5) (sourceB2639 + difference 5 1) sourceC2639) = raw18351 := by
      apply Matrix.ext; unfold tripleCharges sourceA2639 sourceB2639 sourceC2639 difference raw18351; decide +kernel
    rw [ha]
    exact (canonical18351 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2639 + difference 2 0) (sourceB2639 + difference 0 2) sourceC2639) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4969) := by
    have ha : (tripleCharges (sourceA2639 + difference 2 0) (sourceB2639 + difference 0 2) sourceC2639) = raw34417 := by
      apply Matrix.ext; unfold tripleCharges sourceA2639 sourceB2639 sourceC2639 difference raw34417; decide +kernel
    rw [ha]
    exact (canonical34417 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2639 + difference 2 1) (sourceB2639 + difference 1 2) sourceC2639) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4672) := by
    have ha : (tripleCharges (sourceA2639 + difference 2 1) (sourceB2639 + difference 1 2) sourceC2639) = raw37031 := by
      apply Matrix.ext; unfold tripleCharges sourceA2639 sourceB2639 sourceC2639 difference raw37031; decide +kernel
    rw [ha]
    exact (canonical37031 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2639 + difference 2 3) (sourceB2639 + difference 3 2) sourceC2639) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5384) := by
    have ha : (tripleCharges (sourceA2639 + difference 2 3) (sourceB2639 + difference 3 2) sourceC2639) = raw37032 := by
      apply Matrix.ext; unfold tripleCharges sourceA2639 sourceB2639 sourceC2639 difference raw37032; decide +kernel
    rw [ha]
    exact (canonical37032 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2639 + difference 2 4) (sourceB2639 + difference 4 2) sourceC2639) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5384) := by
    have ha : (tripleCharges (sourceA2639 + difference 2 4) (sourceB2639 + difference 4 2) sourceC2639) = raw37033 := by
      apply Matrix.ext; unfold tripleCharges sourceA2639 sourceB2639 sourceC2639 difference raw37033; decide +kernel
    rw [ha]
    exact (canonical37033 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2639 + difference 2 5) (sourceB2639 + difference 5 2) sourceC2639) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5374) := by
    have ha : (tripleCharges (sourceA2639 + difference 2 5) (sourceB2639 + difference 5 2) sourceC2639) = raw37034 := by
      apply Matrix.ext; unfold tripleCharges sourceA2639 sourceB2639 sourceC2639 difference raw37034; decide +kernel
    rw [ha]
    exact (canonical37034 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2639 + difference 3 0) (sourceB2639 + difference 0 3) sourceC2639) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4969) := by
    have ha : (tripleCharges (sourceA2639 + difference 3 0) (sourceB2639 + difference 0 3) sourceC2639) = raw34421 := by
      apply Matrix.ext; unfold tripleCharges sourceA2639 sourceB2639 sourceC2639 difference raw34421; decide +kernel
    rw [ha]
    exact (canonical34421 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2639 + difference 3 1) (sourceB2639 + difference 1 3) sourceC2639) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4672) := by
    have ha : (tripleCharges (sourceA2639 + difference 3 1) (sourceB2639 + difference 1 3) sourceC2639) = raw37035 := by
      apply Matrix.ext; unfold tripleCharges sourceA2639 sourceB2639 sourceC2639 difference raw37035; decide +kernel
    rw [ha]
    exact (canonical37035 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2639 + difference 3 2) (sourceB2639 + difference 2 3) sourceC2639) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5384) := by
    have ha : (tripleCharges (sourceA2639 + difference 3 2) (sourceB2639 + difference 2 3) sourceC2639) = raw18352 := by
      apply Matrix.ext; unfold tripleCharges sourceA2639 sourceB2639 sourceC2639 difference raw18352; decide +kernel
    rw [ha]
    exact (canonical18352 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2639 + difference 3 4) (sourceB2639 + difference 4 3) sourceC2639) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5384) := by
    have ha : (tripleCharges (sourceA2639 + difference 3 4) (sourceB2639 + difference 4 3) sourceC2639) = raw37036 := by
      apply Matrix.ext; unfold tripleCharges sourceA2639 sourceB2639 sourceC2639 difference raw37036; decide +kernel
    rw [ha]
    exact (canonical37036 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2639 + difference 3 5) (sourceB2639 + difference 5 3) sourceC2639) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5374) := by
    have ha : (tripleCharges (sourceA2639 + difference 3 5) (sourceB2639 + difference 5 3) sourceC2639) = raw37037 := by
      apply Matrix.ext; unfold tripleCharges sourceA2639 sourceB2639 sourceC2639 difference raw37037; decide +kernel
    rw [ha]
    exact (canonical37037 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2639 + difference 4 0) (sourceB2639 + difference 0 4) sourceC2639) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4969) := by
    have ha : (tripleCharges (sourceA2639 + difference 4 0) (sourceB2639 + difference 0 4) sourceC2639) = raw34424 := by
      apply Matrix.ext; unfold tripleCharges sourceA2639 sourceB2639 sourceC2639 difference raw34424; decide +kernel
    rw [ha]
    exact (canonical34424 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2639 + difference 4 1) (sourceB2639 + difference 1 4) sourceC2639) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4672) := by
    have ha : (tripleCharges (sourceA2639 + difference 4 1) (sourceB2639 + difference 1 4) sourceC2639) = raw37038 := by
      apply Matrix.ext; unfold tripleCharges sourceA2639 sourceB2639 sourceC2639 difference raw37038; decide +kernel
    rw [ha]
    exact (canonical37038 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2639 + difference 4 2) (sourceB2639 + difference 2 4) sourceC2639) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5384) := by
    have ha : (tripleCharges (sourceA2639 + difference 4 2) (sourceB2639 + difference 2 4) sourceC2639) = raw18356 := by
      apply Matrix.ext; unfold tripleCharges sourceA2639 sourceB2639 sourceC2639 difference raw18356; decide +kernel
    rw [ha]
    exact (canonical18356 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2639 + difference 4 3) (sourceB2639 + difference 3 4) sourceC2639) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5384) := by
    have ha : (tripleCharges (sourceA2639 + difference 4 3) (sourceB2639 + difference 3 4) sourceC2639) = raw34788 := by
      apply Matrix.ext; unfold tripleCharges sourceA2639 sourceB2639 sourceC2639 difference raw34788; decide +kernel
    rw [ha]
    exact (canonical34788 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2639 + difference 4 5) (sourceB2639 + difference 5 4) sourceC2639) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5374) := by
    have ha : (tripleCharges (sourceA2639 + difference 4 5) (sourceB2639 + difference 5 4) sourceC2639) = raw37039 := by
      apply Matrix.ext; unfold tripleCharges sourceA2639 sourceB2639 sourceC2639 difference raw37039; decide +kernel
    rw [ha]
    exact (canonical37039 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2639 + difference 5 0) (sourceB2639 + difference 0 5) sourceC2639) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4967) := by
    have ha : (tripleCharges (sourceA2639 + difference 5 0) (sourceB2639 + difference 0 5) sourceC2639) = raw32031 := by
      apply Matrix.ext; unfold tripleCharges sourceA2639 sourceB2639 sourceC2639 difference raw32031; decide +kernel
    rw [ha]
    exact (canonical32031 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2639 + difference 5 1) (sourceB2639 + difference 1 5) sourceC2639) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4685) := by
    have ha : (tripleCharges (sourceA2639 + difference 5 1) (sourceB2639 + difference 1 5) sourceC2639) = raw35551 := by
      apply Matrix.ext; unfold tripleCharges sourceA2639 sourceB2639 sourceC2639 difference raw35551; decide +kernel
    rw [ha]
    exact (canonical35551 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2639 + difference 5 2) (sourceB2639 + difference 2 5) sourceC2639) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5387) := by
    have ha : (tripleCharges (sourceA2639 + difference 5 2) (sourceB2639 + difference 2 5) sourceC2639) = raw18303 := by
      apply Matrix.ext; unfold tripleCharges sourceA2639 sourceB2639 sourceC2639 difference raw18303; decide +kernel
    rw [ha]
    exact (canonical18303 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2639 + difference 5 3) (sourceB2639 + difference 3 5) sourceC2639) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5387) := by
    have ha : (tripleCharges (sourceA2639 + difference 5 3) (sourceB2639 + difference 3 5) sourceC2639) = raw18299 := by
      apply Matrix.ext; unfold tripleCharges sourceA2639 sourceB2639 sourceC2639 difference raw18299; decide +kernel
    rw [ha]
    exact (canonical18299 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2639 + difference 5 4) (sourceB2639 + difference 4 5) sourceC2639) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5387) := by
    have ha : (tripleCharges (sourceA2639 + difference 5 4) (sourceB2639 + difference 4 5) sourceC2639) = raw35552 := by
      apply Matrix.ext; unfold tripleCharges sourceA2639 sourceB2639 sourceC2639 difference raw35552; decide +kernel
    rw [ha]
    exact (canonical35552 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2639 sourceB2639 sourceC2639
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2639, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic131
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reindexCheck2099 : Integer.Sparse.reindex keyMap MixedData.row2099 = numericRow2099 := by decide +kernel

theorem numericCheck2099 (x : Master → ℝ) : Integer.Sparse.eval numericRow2099 x =
    (17280 : ℝ) * reducedSource2099 x := by
  norm_num [numericRow2099, reducedSource2099, Integer.Sparse.eval, Sparse.eval, nodeValue4672, nodeValue4685, nodeValue4859, nodeValue4967, nodeValue4969, nodeValue5166, nodeValue5374, nodeValue5383, nodeValue5384, nodeValue5387, nodeValue5437, nodeValue5439, nodeValue5448] <;> ring

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Rows131
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero2099 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource2099 (mixedVector B) = 0 := by
  have h4672 : mixedVector B (Sum.inr 4672) = Sparse.eval nodeValue4672 (mixedVector B) := by
    change mixedMoment B node4672 node4672Labels = _
    exact sound4672 B hB hF
  have h4685 : mixedVector B (Sum.inr 4685) = Sparse.eval nodeValue4685 (mixedVector B) := by
    change mixedMoment B node4685 node4685Labels = _
    exact sound4685 B hB hF
  have h4859 : mixedVector B (Sum.inr 4859) = Sparse.eval nodeValue4859 (mixedVector B) := by
    change mixedMoment B node4859 node4859Labels = _
    exact sound4859 B hB hF
  have h4967 : mixedVector B (Sum.inr 4967) = Sparse.eval nodeValue4967 (mixedVector B) := by
    change mixedMoment B node4967 node4967Labels = _
    exact sound4967 B hB hF
  have h4969 : mixedVector B (Sum.inr 4969) = Sparse.eval nodeValue4969 (mixedVector B) := by
    change mixedMoment B node4969 node4969Labels = _
    exact sound4969 B hB hF
  have h5166 : mixedVector B (Sum.inr 5166) = Sparse.eval nodeValue5166 (mixedVector B) := by
    change mixedMoment B node5166 node5166Labels = _
    exact sound5166 B hB hF
  have h5374 : mixedVector B (Sum.inr 5374) = Sparse.eval nodeValue5374 (mixedVector B) := by
    change mixedMoment B node5374 node5374Labels = _
    exact sound5374 B hB hF
  have h5383 : mixedVector B (Sum.inr 5383) = Sparse.eval nodeValue5383 (mixedVector B) := by
    change mixedMoment B node5383 node5383Labels = _
    exact sound5383 B hB hF
  have h5384 : mixedVector B (Sum.inr 5384) = Sparse.eval nodeValue5384 (mixedVector B) := by
    change mixedMoment B node5384 node5384Labels = _
    exact sound5384 B hB hF
  have h5387 : mixedVector B (Sum.inr 5387) = Sparse.eval nodeValue5387 (mixedVector B) := by
    change mixedMoment B node5387 node5387Labels = _
    exact sound5387_e B hB hF
  have h5437 : mixedVector B (Sum.inr 5437) = Sparse.eval nodeValue5437 (mixedVector B) := by
    change mixedMoment B node5437 node5437Labels = _
    exact sound5437 B hB hF
  have h5439 : mixedVector B (Sum.inr 5439) = Sparse.eval nodeValue5439 (mixedVector B) := by
    change mixedMoment B node5439 node5439Labels = _
    exact sound5439_e B hB hF
  have h5448 : mixedVector B (Sum.inr 5448) = Sparse.eval nodeValue5448 (mixedVector B) := by
    change mixedMoment B node5448 node5448Labels = _
    exact sound5448 B hB hF
  simpa only [sourceForm2639, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4672, h4685, h4859, h4967, h4969, h5166, h5374, h5383, h5384, h5387, h5437, h5439, h5448, reducedSource2099] using sourceEq2639 B hB

theorem rowSound2099_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row2099 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck2099, numericCheck2099, reducedZero2099 B hB hF, mul_zero]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedSourceBridge.rowSound2099_e_oai := @OAI.MUB6.Certificate.MixedSourceBridge.rowSound2099_e_oai
