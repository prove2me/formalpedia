-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedSourceBridge.rowSound982_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T03:13:48.636192+00:00
-- url     : https://prove2.me/submissions/867ce912-67e2-4c11-b927-a6ad7fce4bbf

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E086
import Definitions.Def_OAIQ106E095
import Definitions.Def_OAIQ106E096
import Definitions.Def_OAIQ106E190
import Definitions.Def_OAIQ106E100
import Definitions.Def_OAIQ106E194
import Definitions.Def_OAIQ106E195
import Definitions.Def_OAIQ106E101
import Definitions.Def_OAIQ106E119
import Definitions.Def_OAIQ106E123
import Definitions.Def_OAIQ106E129
import Definitions.Def_OAIQ106E140
import Definitions.Def_OAIQ106E147
import Definitions.Def_OAIQ106E170
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound5482_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound5490_e

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical149
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical19140 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19140 raw19140Labels = mixedMoment B node5257 node5257Labels := by
  calc
    mixedMoment B raw19140 raw19140Labels = mixedMoment B raw19140step0 raw19140step0Labels := by
      have ha : raw19140step0 = (fun i j => raw19140 (permutation283 i) (permutation5 j)) := by apply Matrix.ext; unfold raw19140step0 raw19140; decide +kernel
      have hl : raw19140step0Labels = raw19140Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19140 raw19140Labels permutation283 permutation5
    mixedMoment B raw19140step0 raw19140step0Labels = mixedMoment B raw19140step1 raw19140step1Labels := by
      have ha : raw19140step1 = -raw19140step0 := by apply Matrix.ext; change ∀ i j, raw19140step1 i j = -(raw19140step0 i j); unfold raw19140step1 raw19140step0; decide +kernel
      have hl : raw19140step1Labels = raw19140step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19140step1 raw19140step1Labels = mixedMoment B raw19140step2 raw19140step2Labels := by
      have ha : raw19140step2 = raw19140step1 := by apply Matrix.ext; unfold raw19140step2 raw19140step1; decide +kernel
      have hl : raw19140step1Labels = labelEmbedding8 ∘ raw19140step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19140step1 raw19140step1Labels raw19140step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5257 node5257Labels := by rfl

theorem canonical19141 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19141 raw19141Labels = mixedMoment B node5489 node5489Labels := by
  calc
    mixedMoment B raw19141 raw19141Labels = mixedMoment B raw19141step0 raw19141step0Labels := by
      have ha : raw19141step0 = (fun i j => raw19141 (permutation269 i) (permutation5 j)) := by apply Matrix.ext; unfold raw19141step0 raw19141; decide +kernel
      have hl : raw19141step0Labels = raw19141Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19141 raw19141Labels permutation269 permutation5
    mixedMoment B raw19141step0 raw19141step0Labels = mixedMoment B raw19141step1 raw19141step1Labels := by
      have ha : raw19141step1 = -raw19141step0 := by apply Matrix.ext; change ∀ i j, raw19141step1 i j = -(raw19141step0 i j); unfold raw19141step1 raw19141step0; decide +kernel
      have hl : raw19141step1Labels = raw19141step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19141step1 raw19141step1Labels = mixedMoment B raw19141step2 raw19141step2Labels := by
      have ha : raw19141step2 = raw19141step1 := by apply Matrix.ext; unfold raw19141step2 raw19141step1; decide +kernel
      have hl : raw19141step1Labels = labelEmbedding8 ∘ raw19141step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19141step1 raw19141step1Labels raw19141step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5489 node5489Labels := by rfl

theorem canonical19142 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19142 raw19142Labels = mixedMoment B node5490 node5490Labels := by
  calc
    mixedMoment B raw19142 raw19142Labels = mixedMoment B raw19142step0 raw19142step0Labels := by
      have hz : ∀ j, raw19142 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19142step0 = (fun i j => raw19142 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19142step0 raw19142; decide +kernel
      have hl : raw19142step0Labels = raw19142Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19142 raw19142Labels permutation434 hz
    mixedMoment B raw19142step0 raw19142step0Labels = mixedMoment B raw19142step1 raw19142step1Labels := by
      have ha : raw19142step1 = (fun i j => raw19142step0 (permutation75 i) (permutation4 j)) := by apply Matrix.ext; unfold raw19142step1 raw19142step0; decide +kernel
      have hl : raw19142step1Labels = raw19142step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19142step0 raw19142step0Labels permutation75 permutation4
    mixedMoment B raw19142step1 raw19142step1Labels = mixedMoment B raw19142step2 raw19142step2Labels := by
      have ha : raw19142step2 = -raw19142step1 := by apply Matrix.ext; change ∀ i j, raw19142step2 i j = -(raw19142step1 i j); unfold raw19142step2 raw19142step1; decide +kernel
      have hl : raw19142step2Labels = raw19142step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19142step2 raw19142step2Labels = mixedMoment B raw19142step3 raw19142step3Labels := by
      have ha : raw19142step3 = raw19142step2 := by apply Matrix.ext; unfold raw19142step3 raw19142step2; decide +kernel
      have hl : raw19142step2Labels = labelEmbedding7 ∘ raw19142step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19142step2 raw19142step2Labels raw19142step3Labels labelEmbedding7 hl
    _ = mixedMoment B node5490 node5490Labels := by rfl

theorem canonical19143 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19143 raw19143Labels = mixedMoment B node5490 node5490Labels := by
  calc
    mixedMoment B raw19143 raw19143Labels = mixedMoment B raw19143step0 raw19143step0Labels := by
      have hz : ∀ j, raw19143 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw19143step0 = (fun i j => raw19143 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw19143step0 raw19143; decide +kernel
      have hl : raw19143step0Labels = raw19143Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19143 raw19143Labels permutation520 hz
    mixedMoment B raw19143step0 raw19143step0Labels = mixedMoment B raw19143step1 raw19143step1Labels := by
      have ha : raw19143step1 = (fun i j => raw19143step0 (permutation75 i) (permutation4 j)) := by apply Matrix.ext; unfold raw19143step1 raw19143step0; decide +kernel
      have hl : raw19143step1Labels = raw19143step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19143step0 raw19143step0Labels permutation75 permutation4
    mixedMoment B raw19143step1 raw19143step1Labels = mixedMoment B raw19143step2 raw19143step2Labels := by
      have ha : raw19143step2 = -raw19143step1 := by apply Matrix.ext; change ∀ i j, raw19143step2 i j = -(raw19143step1 i j); unfold raw19143step2 raw19143step1; decide +kernel
      have hl : raw19143step2Labels = raw19143step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19143step2 raw19143step2Labels = mixedMoment B raw19143step3 raw19143step3Labels := by
      have ha : raw19143step3 = raw19143step2 := by apply Matrix.ext; unfold raw19143step3 raw19143step2; decide +kernel
      have hl : raw19143step2Labels = labelEmbedding7 ∘ raw19143step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19143step2 raw19143step2Labels raw19143step3Labels labelEmbedding7 hl
    _ = mixedMoment B node5490 node5490Labels := by rfl

theorem canonical19144 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19144 raw19144Labels = mixedMoment B node5482 node5482Labels := by
  calc
    mixedMoment B raw19144 raw19144Labels = mixedMoment B raw19144step0 raw19144step0Labels := by
      have ha : raw19144step0 = (fun i j => raw19144 (permutation336 i) (permutation4 j)) := by apply Matrix.ext; unfold raw19144step0 raw19144; decide +kernel
      have hl : raw19144step0Labels = raw19144Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19144 raw19144Labels permutation336 permutation4
    mixedMoment B raw19144step0 raw19144step0Labels = mixedMoment B raw19144step1 raw19144step1Labels := by
      have ha : raw19144step1 = -raw19144step0 := by apply Matrix.ext; change ∀ i j, raw19144step1 i j = -(raw19144step0 i j); unfold raw19144step1 raw19144step0; decide +kernel
      have hl : raw19144step1Labels = raw19144step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19144step1 raw19144step1Labels = mixedMoment B raw19144step2 raw19144step2Labels := by
      have ha : raw19144step2 = raw19144step1 := by apply Matrix.ext; unfold raw19144step2 raw19144step1; decide +kernel
      have hl : raw19144step1Labels = labelEmbedding7 ∘ raw19144step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19144step1 raw19144step1Labels raw19144step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5482 node5482Labels := by rfl

theorem canonical19145 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19145 raw19145Labels = mixedMoment B node5257 node5257Labels := by
  calc
    mixedMoment B raw19145 raw19145Labels = mixedMoment B raw19145step0 raw19145step0Labels := by
      have ha : raw19145step0 = (fun i j => raw19145 (permutation156 i) (permutation3 j)) := by apply Matrix.ext; unfold raw19145step0 raw19145; decide +kernel
      have hl : raw19145step0Labels = raw19145Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19145 raw19145Labels permutation156 permutation3
    mixedMoment B raw19145step0 raw19145step0Labels = mixedMoment B raw19145step1 raw19145step1Labels := by
      have ha : raw19145step1 = raw19145step0 := by apply Matrix.ext; unfold raw19145step1 raw19145step0; decide +kernel
      have hl : raw19145step0Labels = labelEmbedding6 ∘ raw19145step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19145step0 raw19145step0Labels raw19145step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5257 node5257Labels := by rfl

theorem canonical19146 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19146 raw19146Labels = mixedMoment B node5482 node5482Labels := by
  calc
    mixedMoment B raw19146 raw19146Labels = mixedMoment B raw19146step0 raw19146step0Labels := by
      have ha : raw19146step0 = (fun i j => raw19146 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19146step0 raw19146; decide +kernel
      have hl : raw19146step0Labels = raw19146Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19146 raw19146Labels permutation176 permutation2
    _ = mixedMoment B node5482 node5482Labels := by rfl

theorem canonical19147 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19147 raw19147Labels = mixedMoment B node5490 node5490Labels := by
  calc
    mixedMoment B raw19147 raw19147Labels = mixedMoment B raw19147step0 raw19147step0Labels := by
      have hz : ∀ j, raw19147 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19147step0 = (fun i j => raw19147 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19147step0 raw19147; decide +kernel
      have hl : raw19147step0Labels = raw19147Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19147 raw19147Labels permutation434 hz
    mixedMoment B raw19147step0 raw19147step0Labels = mixedMoment B raw19147step1 raw19147step1Labels := by
      have ha : raw19147step1 = (fun i j => raw19147step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19147step1 raw19147step0; decide +kernel
      have hl : raw19147step1Labels = raw19147step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19147step0 raw19147step0Labels permutation38 permutation2
    _ = mixedMoment B node5490 node5490Labels := by rfl

theorem canonical19148 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19148 raw19148Labels = mixedMoment B node5490 node5490Labels := by
  calc
    mixedMoment B raw19148 raw19148Labels = mixedMoment B raw19148step0 raw19148step0Labels := by
      have hz : ∀ j, raw19148 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw19148step0 = (fun i j => raw19148 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw19148step0 raw19148; decide +kernel
      have hl : raw19148step0Labels = raw19148Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19148 raw19148Labels permutation520 hz
    mixedMoment B raw19148step0 raw19148step0Labels = mixedMoment B raw19148step1 raw19148step1Labels := by
      have ha : raw19148step1 = (fun i j => raw19148step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19148step1 raw19148step0; decide +kernel
      have hl : raw19148step1Labels = raw19148step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19148step0 raw19148step0Labels permutation38 permutation2
    _ = mixedMoment B node5490 node5490Labels := by rfl

theorem canonical19149 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19149 raw19149Labels = mixedMoment B node5489 node5489Labels := by
  calc
    mixedMoment B raw19149 raw19149Labels = mixedMoment B raw19149step0 raw19149step0Labels := by
      have ha : raw19149step0 = (fun i j => raw19149 (permutation170 i) (permutation3 j)) := by apply Matrix.ext; unfold raw19149step0 raw19149; decide +kernel
      have hl : raw19149step0Labels = raw19149Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19149 raw19149Labels permutation170 permutation3
    mixedMoment B raw19149step0 raw19149step0Labels = mixedMoment B raw19149step1 raw19149step1Labels := by
      have ha : raw19149step1 = raw19149step0 := by apply Matrix.ext; unfold raw19149step1 raw19149step0; decide +kernel
      have hl : raw19149step0Labels = labelEmbedding6 ∘ raw19149step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19149step0 raw19149step0Labels raw19149step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5489 node5489Labels := by rfl

theorem canonical19150 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19150 raw19150Labels = mixedMoment B node5013 node5013Labels := by
  calc
    mixedMoment B raw19150 raw19150Labels = mixedMoment B raw19150step0 raw19150step0Labels := by
      have ha : raw19150step0 = (fun i j => raw19150 (permutation173 i) (permutation3 j)) := by apply Matrix.ext; unfold raw19150step0 raw19150; decide +kernel
      have hl : raw19150step0Labels = raw19150Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19150 raw19150Labels permutation173 permutation3
    mixedMoment B raw19150step0 raw19150step0Labels = mixedMoment B raw19150step1 raw19150step1Labels := by
      have ha : raw19150step1 = raw19150step0 := by apply Matrix.ext; unfold raw19150step1 raw19150step0; decide +kernel
      have hl : raw19150step0Labels = labelEmbedding6 ∘ raw19150step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19150step0 raw19150step0Labels raw19150step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5013 node5013Labels := by rfl

theorem canonical19151 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19151 raw19151Labels = mixedMoment B node4998 node4998Labels := by
  calc
    mixedMoment B raw19151 raw19151Labels = mixedMoment B raw19151step0 raw19151step0Labels := by
      have ha : raw19151step0 = (fun i j => raw19151 (permutation286 i) (permutation5 j)) := by apply Matrix.ext; unfold raw19151step0 raw19151; decide +kernel
      have hl : raw19151step0Labels = raw19151Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19151 raw19151Labels permutation286 permutation5
    mixedMoment B raw19151step0 raw19151step0Labels = mixedMoment B raw19151step1 raw19151step1Labels := by
      have ha : raw19151step1 = -raw19151step0 := by apply Matrix.ext; change ∀ i j, raw19151step1 i j = -(raw19151step0 i j); unfold raw19151step1 raw19151step0; decide +kernel
      have hl : raw19151step1Labels = raw19151step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19151step1 raw19151step1Labels = mixedMoment B raw19151step2 raw19151step2Labels := by
      have ha : raw19151step2 = raw19151step1 := by apply Matrix.ext; unfold raw19151step2 raw19151step1; decide +kernel
      have hl : raw19151step1Labels = labelEmbedding8 ∘ raw19151step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19151step1 raw19151step1Labels raw19151step2Labels labelEmbedding8 hl
    _ = mixedMoment B node4998 node4998Labels := by rfl

theorem canonical19152 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19152 raw19152Labels = mixedMoment B node5473 node5473Labels := by
  calc
    mixedMoment B raw19152 raw19152Labels = mixedMoment B raw19152step0 raw19152step0Labels := by
      have hz : ∀ j, raw19152 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19152step0 = (fun i j => raw19152 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19152step0 raw19152; decide +kernel
      have hl : raw19152step0Labels = raw19152Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19152 raw19152Labels permutation434 hz
    mixedMoment B raw19152step0 raw19152step0Labels = mixedMoment B raw19152step1 raw19152step1Labels := by
      have ha : raw19152step1 = (fun i j => raw19152step0 (permutation61 i) (permutation5 j)) := by apply Matrix.ext; unfold raw19152step1 raw19152step0; decide +kernel
      have hl : raw19152step1Labels = raw19152step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19152step0 raw19152step0Labels permutation61 permutation5
    mixedMoment B raw19152step1 raw19152step1Labels = mixedMoment B raw19152step2 raw19152step2Labels := by
      have ha : raw19152step2 = -raw19152step1 := by apply Matrix.ext; change ∀ i j, raw19152step2 i j = -(raw19152step1 i j); unfold raw19152step2 raw19152step1; decide +kernel
      have hl : raw19152step2Labels = raw19152step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19152step2 raw19152step2Labels = mixedMoment B raw19152step3 raw19152step3Labels := by
      have ha : raw19152step3 = raw19152step2 := by apply Matrix.ext; unfold raw19152step3 raw19152step2; decide +kernel
      have hl : raw19152step2Labels = labelEmbedding8 ∘ raw19152step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19152step2 raw19152step2Labels raw19152step3Labels labelEmbedding8 hl
    _ = mixedMoment B node5473 node5473Labels := by rfl

theorem canonical19153 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19153 raw19153Labels = mixedMoment B node5473 node5473Labels := by
  calc
    mixedMoment B raw19153 raw19153Labels = mixedMoment B raw19153step0 raw19153step0Labels := by
      have hz : ∀ j, raw19153 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw19153step0 = (fun i j => raw19153 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw19153step0 raw19153; decide +kernel
      have hl : raw19153step0Labels = raw19153Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19153 raw19153Labels permutation520 hz
    mixedMoment B raw19153step0 raw19153step0Labels = mixedMoment B raw19153step1 raw19153step1Labels := by
      have ha : raw19153step1 = (fun i j => raw19153step0 (permutation61 i) (permutation5 j)) := by apply Matrix.ext; unfold raw19153step1 raw19153step0; decide +kernel
      have hl : raw19153step1Labels = raw19153step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19153step0 raw19153step0Labels permutation61 permutation5
    mixedMoment B raw19153step1 raw19153step1Labels = mixedMoment B raw19153step2 raw19153step2Labels := by
      have ha : raw19153step2 = -raw19153step1 := by apply Matrix.ext; change ∀ i j, raw19153step2 i j = -(raw19153step1 i j); unfold raw19153step2 raw19153step1; decide +kernel
      have hl : raw19153step2Labels = raw19153step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19153step2 raw19153step2Labels = mixedMoment B raw19153step3 raw19153step3Labels := by
      have ha : raw19153step3 = raw19153step2 := by apply Matrix.ext; unfold raw19153step3 raw19153step2; decide +kernel
      have hl : raw19153step2Labels = labelEmbedding8 ∘ raw19153step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19153step2 raw19153step2Labels raw19153step3Labels labelEmbedding8 hl
    _ = mixedMoment B node5473 node5473Labels := by rfl

theorem canonical19154 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19154 raw19154Labels = mixedMoment B node5469 node5469Labels := by
  calc
    mixedMoment B raw19154 raw19154Labels = mixedMoment B raw19154step0 raw19154step0Labels := by
      have ha : raw19154step0 = (fun i j => raw19154 (permutation286 i) (permutation5 j)) := by apply Matrix.ext; unfold raw19154step0 raw19154; decide +kernel
      have hl : raw19154step0Labels = raw19154Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19154 raw19154Labels permutation286 permutation5
    mixedMoment B raw19154step0 raw19154step0Labels = mixedMoment B raw19154step1 raw19154step1Labels := by
      have ha : raw19154step1 = -raw19154step0 := by apply Matrix.ext; change ∀ i j, raw19154step1 i j = -(raw19154step0 i j); unfold raw19154step1 raw19154step0; decide +kernel
      have hl : raw19154step1Labels = raw19154step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19154step1 raw19154step1Labels = mixedMoment B raw19154step2 raw19154step2Labels := by
      have ha : raw19154step2 = raw19154step1 := by apply Matrix.ext; unfold raw19154step2 raw19154step1; decide +kernel
      have hl : raw19154step1Labels = labelEmbedding8 ∘ raw19154step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19154step1 raw19154step1Labels raw19154step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5469 node5469Labels := by rfl

theorem canonical19155 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19155 raw19155Labels = mixedMoment B node4996 node4996Labels := by
  calc
    mixedMoment B raw19155 raw19155Labels = mixedMoment B raw19155step0 raw19155step0Labels := by
      have ha : raw19155step0 = (fun i j => raw19155 (permutation157 i) (permutation3 j)) := by apply Matrix.ext; unfold raw19155step0 raw19155; decide +kernel
      have hl : raw19155step0Labels = raw19155Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19155 raw19155Labels permutation157 permutation3
    mixedMoment B raw19155step0 raw19155step0Labels = mixedMoment B raw19155step1 raw19155step1Labels := by
      have ha : raw19155step1 = raw19155step0 := by apply Matrix.ext; unfold raw19155step1 raw19155step0; decide +kernel
      have hl : raw19155step0Labels = labelEmbedding6 ∘ raw19155step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19155step0 raw19155step0Labels raw19155step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4996 node4996Labels := by rfl

theorem canonical19156 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19156 raw19156Labels = mixedMoment B node4996 node4996Labels := by
  calc
    mixedMoment B raw19156 raw19156Labels = mixedMoment B raw19156step0 raw19156step0Labels := by
      have ha : raw19156step0 = (fun i j => raw19156 (permutation284 i) (permutation5 j)) := by apply Matrix.ext; unfold raw19156step0 raw19156; decide +kernel
      have hl : raw19156step0Labels = raw19156Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19156 raw19156Labels permutation284 permutation5
    mixedMoment B raw19156step0 raw19156step0Labels = mixedMoment B raw19156step1 raw19156step1Labels := by
      have ha : raw19156step1 = -raw19156step0 := by apply Matrix.ext; change ∀ i j, raw19156step1 i j = -(raw19156step0 i j); unfold raw19156step1 raw19156step0; decide +kernel
      have hl : raw19156step1Labels = raw19156step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19156step1 raw19156step1Labels = mixedMoment B raw19156step2 raw19156step2Labels := by
      have ha : raw19156step2 = raw19156step1 := by apply Matrix.ext; unfold raw19156step2 raw19156step1; decide +kernel
      have hl : raw19156step1Labels = labelEmbedding8 ∘ raw19156step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19156step1 raw19156step1Labels raw19156step2Labels labelEmbedding8 hl
    _ = mixedMoment B node4996 node4996Labels := by rfl

theorem canonical19157 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19157 raw19157Labels = mixedMoment B node5395 node5395Labels := by
  calc
    mixedMoment B raw19157 raw19157Labels = mixedMoment B raw19157step0 raw19157step0Labels := by
      have ha : raw19157step0 = (fun i j => raw19157 (permutation504 i) (permutation3 j)) := by apply Matrix.ext; unfold raw19157step0 raw19157; decide +kernel
      have hl : raw19157step0Labels = raw19157Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19157 raw19157Labels permutation504 permutation3
    mixedMoment B raw19157step0 raw19157step0Labels = mixedMoment B raw19157step1 raw19157step1Labels := by
      have ha : raw19157step1 = -raw19157step0 := by apply Matrix.ext; change ∀ i j, raw19157step1 i j = -(raw19157step0 i j); unfold raw19157step1 raw19157step0; decide +kernel
      have hl : raw19157step1Labels = raw19157step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19157step1 raw19157step1Labels = mixedMoment B raw19157step2 raw19157step2Labels := by
      have ha : raw19157step2 = raw19157step1 := by apply Matrix.ext; unfold raw19157step2 raw19157step1; decide +kernel
      have hl : raw19157step1Labels = labelEmbedding6 ∘ raw19157step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19157step1 raw19157step1Labels raw19157step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5395 node5395Labels := by rfl

theorem canonical19158 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19158 raw19158Labels = mixedMoment B node5428 node5428Labels := by
  calc
    mixedMoment B raw19158 raw19158Labels = mixedMoment B raw19158step0 raw19158step0Labels := by
      have hz : ∀ j, raw19158 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw19158step0 = (fun i j => raw19158 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw19158step0 raw19158; decide +kernel
      have hl : raw19158step0Labels = raw19158Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19158 raw19158Labels permutation520 hz
    mixedMoment B raw19158step0 raw19158step0Labels = mixedMoment B raw19158step1 raw19158step1Labels := by
      have ha : raw19158step1 = (fun i j => raw19158step0 (permutation127 i) (permutation3 j)) := by apply Matrix.ext; unfold raw19158step1 raw19158step0; decide +kernel
      have hl : raw19158step1Labels = raw19158step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19158step0 raw19158step0Labels permutation127 permutation3
    mixedMoment B raw19158step1 raw19158step1Labels = mixedMoment B raw19158step2 raw19158step2Labels := by
      have ha : raw19158step2 = -raw19158step1 := by apply Matrix.ext; change ∀ i j, raw19158step2 i j = -(raw19158step1 i j); unfold raw19158step2 raw19158step1; decide +kernel
      have hl : raw19158step2Labels = raw19158step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19158step2 raw19158step2Labels = mixedMoment B raw19158step3 raw19158step3Labels := by
      have ha : raw19158step3 = raw19158step2 := by apply Matrix.ext; unfold raw19158step3 raw19158step2; decide +kernel
      have hl : raw19158step2Labels = labelEmbedding6 ∘ raw19158step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19158step2 raw19158step2Labels raw19158step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5428 node5428Labels := by rfl

theorem canonical19159 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19159 raw19159Labels = mixedMoment B node5395 node5395Labels := by
  calc
    mixedMoment B raw19159 raw19159Labels = mixedMoment B raw19159step0 raw19159step0Labels := by
      have ha : raw19159step0 = (fun i j => raw19159 (permutation497 i) (permutation5 j)) := by apply Matrix.ext; unfold raw19159step0 raw19159; decide +kernel
      have hl : raw19159step0Labels = raw19159Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19159 raw19159Labels permutation497 permutation5
    mixedMoment B raw19159step0 raw19159step0Labels = mixedMoment B raw19159step1 raw19159step1Labels := by
      have ha : raw19159step1 = raw19159step0 := by apply Matrix.ext; unfold raw19159step1 raw19159step0; decide +kernel
      have hl : raw19159step0Labels = labelEmbedding8 ∘ raw19159step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19159step0 raw19159step0Labels raw19159step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5395 node5395Labels := by rfl

theorem canonical19160 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19160 raw19160Labels = mixedMoment B node4996 node4996Labels := by
  calc
    mixedMoment B raw19160 raw19160Labels = mixedMoment B raw19160step0 raw19160step0Labels := by
      have ha : raw19160step0 = (fun i j => raw19160 (permutation156 i) (permutation3 j)) := by apply Matrix.ext; unfold raw19160step0 raw19160; decide +kernel
      have hl : raw19160step0Labels = raw19160Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19160 raw19160Labels permutation156 permutation3
    mixedMoment B raw19160step0 raw19160step0Labels = mixedMoment B raw19160step1 raw19160step1Labels := by
      have ha : raw19160step1 = raw19160step0 := by apply Matrix.ext; unfold raw19160step1 raw19160step0; decide +kernel
      have hl : raw19160step0Labels = labelEmbedding6 ∘ raw19160step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19160step0 raw19160step0Labels raw19160step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4996 node4996Labels := by rfl

theorem canonical19161 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19161 raw19161Labels = mixedMoment B node4996 node4996Labels := by
  calc
    mixedMoment B raw19161 raw19161Labels = mixedMoment B raw19161step0 raw19161step0Labels := by
      have ha : raw19161step0 = (fun i j => raw19161 (permutation283 i) (permutation5 j)) := by apply Matrix.ext; unfold raw19161step0 raw19161; decide +kernel
      have hl : raw19161step0Labels = raw19161Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19161 raw19161Labels permutation283 permutation5
    mixedMoment B raw19161step0 raw19161step0Labels = mixedMoment B raw19161step1 raw19161step1Labels := by
      have ha : raw19161step1 = -raw19161step0 := by apply Matrix.ext; change ∀ i j, raw19161step1 i j = -(raw19161step0 i j); unfold raw19161step1 raw19161step0; decide +kernel
      have hl : raw19161step1Labels = raw19161step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19161step1 raw19161step1Labels = mixedMoment B raw19161step2 raw19161step2Labels := by
      have ha : raw19161step2 = raw19161step1 := by apply Matrix.ext; unfold raw19161step2 raw19161step1; decide +kernel
      have hl : raw19161step1Labels = labelEmbedding8 ∘ raw19161step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19161step1 raw19161step1Labels raw19161step2Labels labelEmbedding8 hl
    _ = mixedMoment B node4996 node4996Labels := by rfl

theorem canonical19162 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19162 raw19162Labels = mixedMoment B node5395 node5395Labels := by
  calc
    mixedMoment B raw19162 raw19162Labels = mixedMoment B raw19162step0 raw19162step0Labels := by
      have ha : raw19162step0 = (fun i j => raw19162 (permutation568 i) (permutation3 j)) := by apply Matrix.ext; unfold raw19162step0 raw19162; decide +kernel
      have hl : raw19162step0Labels = raw19162Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19162 raw19162Labels permutation568 permutation3
    mixedMoment B raw19162step0 raw19162step0Labels = mixedMoment B raw19162step1 raw19162step1Labels := by
      have ha : raw19162step1 = -raw19162step0 := by apply Matrix.ext; change ∀ i j, raw19162step1 i j = -(raw19162step0 i j); unfold raw19162step1 raw19162step0; decide +kernel
      have hl : raw19162step1Labels = raw19162step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19162step1 raw19162step1Labels = mixedMoment B raw19162step2 raw19162step2Labels := by
      have ha : raw19162step2 = raw19162step1 := by apply Matrix.ext; unfold raw19162step2 raw19162step1; decide +kernel
      have hl : raw19162step1Labels = labelEmbedding6 ∘ raw19162step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19162step1 raw19162step1Labels raw19162step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5395 node5395Labels := by rfl

theorem canonical19163 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19163 raw19163Labels = mixedMoment B node5428 node5428Labels := by
  calc
    mixedMoment B raw19163 raw19163Labels = mixedMoment B raw19163step0 raw19163step0Labels := by
      have hz : ∀ j, raw19163 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19163step0 = (fun i j => raw19163 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19163step0 raw19163; decide +kernel
      have hl : raw19163step0Labels = raw19163Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19163 raw19163Labels permutation434 hz
    mixedMoment B raw19163step0 raw19163step0Labels = mixedMoment B raw19163step1 raw19163step1Labels := by
      have ha : raw19163step1 = (fun i j => raw19163step0 (permutation127 i) (permutation3 j)) := by apply Matrix.ext; unfold raw19163step1 raw19163step0; decide +kernel
      have hl : raw19163step1Labels = raw19163step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19163step0 raw19163step0Labels permutation127 permutation3
    mixedMoment B raw19163step1 raw19163step1Labels = mixedMoment B raw19163step2 raw19163step2Labels := by
      have ha : raw19163step2 = -raw19163step1 := by apply Matrix.ext; change ∀ i j, raw19163step2 i j = -(raw19163step1 i j); unfold raw19163step2 raw19163step1; decide +kernel
      have hl : raw19163step2Labels = raw19163step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19163step2 raw19163step2Labels = mixedMoment B raw19163step3 raw19163step3Labels := by
      have ha : raw19163step3 = raw19163step2 := by apply Matrix.ext; unfold raw19163step3 raw19163step2; decide +kernel
      have hl : raw19163step2Labels = labelEmbedding6 ∘ raw19163step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19163step2 raw19163step2Labels raw19163step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5428 node5428Labels := by rfl

theorem canonical19164 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19164 raw19164Labels = mixedMoment B node5395 node5395Labels := by
  calc
    mixedMoment B raw19164 raw19164Labels = mixedMoment B raw19164step0 raw19164step0Labels := by
      have ha : raw19164step0 = (fun i j => raw19164 (permutation561 i) (permutation5 j)) := by apply Matrix.ext; unfold raw19164step0 raw19164; decide +kernel
      have hl : raw19164step0Labels = raw19164Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19164 raw19164Labels permutation561 permutation5
    mixedMoment B raw19164step0 raw19164step0Labels = mixedMoment B raw19164step1 raw19164step1Labels := by
      have ha : raw19164step1 = raw19164step0 := by apply Matrix.ext; unfold raw19164step1 raw19164step0; decide +kernel
      have hl : raw19164step0Labels = labelEmbedding8 ∘ raw19164step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19164step0 raw19164step0Labels raw19164step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5395 node5395Labels := by rfl

theorem canonical19165 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19165 raw19165Labels = mixedMoment B node4998 node4998Labels := by
  calc
    mixedMoment B raw19165 raw19165Labels = mixedMoment B raw19165step0 raw19165step0Labels := by
      have ha : raw19165step0 = (fun i j => raw19165 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw19165step0 raw19165; decide +kernel
      have hl : raw19165step0Labels = raw19165Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19165 raw19165Labels permutation152 permutation3
    mixedMoment B raw19165step0 raw19165step0Labels = mixedMoment B raw19165step1 raw19165step1Labels := by
      have ha : raw19165step1 = raw19165step0 := by apply Matrix.ext; unfold raw19165step1 raw19165step0; decide +kernel
      have hl : raw19165step0Labels = labelEmbedding6 ∘ raw19165step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19165step0 raw19165step0Labels raw19165step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4998 node4998Labels := by rfl

theorem canonical19166 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19166 raw19166Labels = mixedMoment B node5013 node5013Labels := by
  calc
    mixedMoment B raw19166 raw19166Labels = mixedMoment B raw19166step0 raw19166step0Labels := by
      have ha : raw19166step0 = (fun i j => raw19166 (permutation265 i) (permutation5 j)) := by apply Matrix.ext; unfold raw19166step0 raw19166; decide +kernel
      have hl : raw19166step0Labels = raw19166Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19166 raw19166Labels permutation265 permutation5
    mixedMoment B raw19166step0 raw19166step0Labels = mixedMoment B raw19166step1 raw19166step1Labels := by
      have ha : raw19166step1 = -raw19166step0 := by apply Matrix.ext; change ∀ i j, raw19166step1 i j = -(raw19166step0 i j); unfold raw19166step1 raw19166step0; decide +kernel
      have hl : raw19166step1Labels = raw19166step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19166step1 raw19166step1Labels = mixedMoment B raw19166step2 raw19166step2Labels := by
      have ha : raw19166step2 = raw19166step1 := by apply Matrix.ext; unfold raw19166step2 raw19166step1; decide +kernel
      have hl : raw19166step1Labels = labelEmbedding8 ∘ raw19166step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19166step1 raw19166step1Labels raw19166step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5013 node5013Labels := by rfl

theorem canonical19167 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19167 raw19167Labels = mixedMoment B node5469 node5469Labels := by
  calc
    mixedMoment B raw19167 raw19167Labels = mixedMoment B raw19167step0 raw19167step0Labels := by
      have ha : raw19167step0 = (fun i j => raw19167 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw19167step0 raw19167; decide +kernel
      have hl : raw19167step0Labels = raw19167Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19167 raw19167Labels permutation152 permutation3
    mixedMoment B raw19167step0 raw19167step0Labels = mixedMoment B raw19167step1 raw19167step1Labels := by
      have ha : raw19167step1 = raw19167step0 := by apply Matrix.ext; unfold raw19167step1 raw19167step0; decide +kernel
      have hl : raw19167step0Labels = labelEmbedding6 ∘ raw19167step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19167step0 raw19167step0Labels raw19167step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5469 node5469Labels := by rfl

theorem canonical19168 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19168 raw19168Labels = mixedMoment B node5473 node5473Labels := by
  calc
    mixedMoment B raw19168 raw19168Labels = mixedMoment B raw19168step0 raw19168step0Labels := by
      have hz : ∀ j, raw19168 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19168step0 = (fun i j => raw19168 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19168step0 raw19168; decide +kernel
      have hl : raw19168step0Labels = raw19168Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19168 raw19168Labels permutation434 hz
    mixedMoment B raw19168step0 raw19168step0Labels = mixedMoment B raw19168step1 raw19168step1Labels := by
      have ha : raw19168step1 = (fun i j => raw19168step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw19168step1 raw19168step0; decide +kernel
      have hl : raw19168step1Labels = raw19168step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19168step0 raw19168step0Labels permutation32 permutation3
    mixedMoment B raw19168step1 raw19168step1Labels = mixedMoment B raw19168step2 raw19168step2Labels := by
      have ha : raw19168step2 = raw19168step1 := by apply Matrix.ext; unfold raw19168step2 raw19168step1; decide +kernel
      have hl : raw19168step1Labels = labelEmbedding6 ∘ raw19168step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19168step1 raw19168step1Labels raw19168step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5473 node5473Labels := by rfl

theorem canonical19169 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19169 raw19169Labels = mixedMoment B node5473 node5473Labels := by
  calc
    mixedMoment B raw19169 raw19169Labels = mixedMoment B raw19169step0 raw19169step0Labels := by
      have hz : ∀ j, raw19169 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw19169step0 = (fun i j => raw19169 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw19169step0 raw19169; decide +kernel
      have hl : raw19169step0Labels = raw19169Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19169 raw19169Labels permutation520 hz
    mixedMoment B raw19169step0 raw19169step0Labels = mixedMoment B raw19169step1 raw19169step1Labels := by
      have ha : raw19169step1 = (fun i j => raw19169step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw19169step1 raw19169step0; decide +kernel
      have hl : raw19169step1Labels = raw19169step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19169step0 raw19169step0Labels permutation32 permutation3
    mixedMoment B raw19169step1 raw19169step1Labels = mixedMoment B raw19169step2 raw19169step2Labels := by
      have ha : raw19169step2 = raw19169step1 := by apply Matrix.ext; unfold raw19169step2 raw19169step1; decide +kernel
      have hl : raw19169step1Labels = labelEmbedding6 ∘ raw19169step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19169step1 raw19169step1Labels raw19169step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5473 node5473Labels := by rfl

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

theorem canonical2007 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2007 raw2007Labels = mixedMoment B node4996 node4996Labels := by
  calc
    mixedMoment B raw2007 raw2007Labels = mixedMoment B raw2007step0 raw2007step0Labels := by
      have ha : raw2007step0 = (fun i j => raw2007 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2007step0 raw2007; decide +kernel
      have hl : raw2007step0Labels = raw2007Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2007 raw2007Labels permutation152 permutation4
    mixedMoment B raw2007step0 raw2007step0Labels = mixedMoment B raw2007step1 raw2007step1Labels := by
      have ha : raw2007step1 = raw2007step0 := by apply Matrix.ext; unfold raw2007step1 raw2007step0; decide +kernel
      have hl : raw2007step0Labels = labelEmbedding7 ∘ raw2007step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2007step0 raw2007step0Labels raw2007step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4996 node4996Labels := by rfl

theorem canonical2008 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2008 raw2008Labels = mixedMoment B node2382 node2382Labels := by
  calc
    mixedMoment B raw2008 raw2008Labels = mixedMoment B raw2008step0 raw2008step0Labels := by
      have ha : raw2008step0 = (fun i j => raw2008 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2008step0 raw2008; decide +kernel
      have hl : raw2008step0Labels = raw2008Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2008 raw2008Labels permutation152 permutation4
    _ = mixedMoment B node2382 node2382Labels := by rfl

theorem canonical2009 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2009 raw2009Labels = mixedMoment B node3340 node3340Labels := by
  calc
    mixedMoment B raw2009 raw2009Labels = mixedMoment B raw2009step0 raw2009step0Labels := by
      have ha : raw2009step0 = (fun i j => raw2009 (permutation158 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2009step0 raw2009; decide +kernel
      have hl : raw2009step0Labels = raw2009Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2009 raw2009Labels permutation158 permutation6
    mixedMoment B raw2009step0 raw2009step0Labels = mixedMoment B raw2009step1 raw2009step1Labels := by
      have ha : raw2009step1 = -raw2009step0 := by apply Matrix.ext; change ∀ i j, raw2009step1 i j = -(raw2009step0 i j); unfold raw2009step1 raw2009step0; decide +kernel
      have hl : raw2009step1Labels = raw2009step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2009step1 raw2009step1Labels = mixedMoment B raw2009step2 raw2009step2Labels := by
      have ha : raw2009step2 = raw2009step1 := by apply Matrix.ext; unfold raw2009step2 raw2009step1; decide +kernel
      have hl : raw2009step1Labels = labelEmbedding1 ∘ raw2009step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2009step1 raw2009step1Labels raw2009step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3340 node3340Labels := by rfl

theorem canonical2010 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2010 raw2010Labels = mixedMoment B node4998 node4998Labels := by
  calc
    mixedMoment B raw2010 raw2010Labels = mixedMoment B raw2010step0 raw2010step0Labels := by
      have ha : raw2010step0 = (fun i j => raw2010 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2010step0 raw2010; decide +kernel
      have hl : raw2010step0Labels = raw2010Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2010 raw2010Labels permutation152 permutation4
    mixedMoment B raw2010step0 raw2010step0Labels = mixedMoment B raw2010step1 raw2010step1Labels := by
      have ha : raw2010step1 = raw2010step0 := by apply Matrix.ext; unfold raw2010step1 raw2010step0; decide +kernel
      have hl : raw2010step0Labels = labelEmbedding7 ∘ raw2010step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2010step0 raw2010step0Labels raw2010step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4998 node4998Labels := by rfl

theorem canonical2011 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2011 raw2011Labels = mixedMoment B node2383 node2383Labels := by
  calc
    mixedMoment B raw2011 raw2011Labels = mixedMoment B raw2011step0 raw2011step0Labels := by
      have ha : raw2011step0 = (fun i j => raw2011 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2011step0 raw2011; decide +kernel
      have hl : raw2011step0Labels = raw2011Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2011 raw2011Labels permutation152 permutation4
    _ = mixedMoment B node2383 node2383Labels := by rfl

theorem canonical2012 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2012 raw2012Labels = mixedMoment B node3352 node3352Labels := by
  calc
    mixedMoment B raw2012 raw2012Labels = mixedMoment B raw2012step0 raw2012step0Labels := by
      have ha : raw2012step0 = (fun i j => raw2012 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2012step0 raw2012; decide +kernel
      have hl : raw2012step0Labels = raw2012Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2012 raw2012Labels permutation152 permutation6
    mixedMoment B raw2012step0 raw2012step0Labels = mixedMoment B raw2012step1 raw2012step1Labels := by
      have ha : raw2012step1 = -raw2012step0 := by apply Matrix.ext; change ∀ i j, raw2012step1 i j = -(raw2012step0 i j); unfold raw2012step1 raw2012step0; decide +kernel
      have hl : raw2012step1Labels = raw2012step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2012step1 raw2012step1Labels = mixedMoment B raw2012step2 raw2012step2Labels := by
      have ha : raw2012step2 = raw2012step1 := by apply Matrix.ext; unfold raw2012step2 raw2012step1; decide +kernel
      have hl : raw2012step1Labels = labelEmbedding1 ∘ raw2012step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2012step1 raw2012step1Labels raw2012step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3352 node3352Labels := by rfl

theorem canonical2019 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2019 raw2019Labels = mixedMoment B node5013 node5013Labels := by
  calc
    mixedMoment B raw2019 raw2019Labels = mixedMoment B raw2019step0 raw2019step0Labels := by
      have ha : raw2019step0 = (fun i j => raw2019 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2019step0 raw2019; decide +kernel
      have hl : raw2019step0Labels = raw2019Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2019 raw2019Labels permutation152 permutation4
    mixedMoment B raw2019step0 raw2019step0Labels = mixedMoment B raw2019step1 raw2019step1Labels := by
      have ha : raw2019step1 = raw2019step0 := by apply Matrix.ext; unfold raw2019step1 raw2019step0; decide +kernel
      have hl : raw2019step0Labels = labelEmbedding7 ∘ raw2019step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2019step0 raw2019step0Labels raw2019step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5013 node5013Labels := by rfl

theorem canonical2020 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2020 raw2020Labels = mixedMoment B node2398 node2398Labels := by
  calc
    mixedMoment B raw2020 raw2020Labels = mixedMoment B raw2020step0 raw2020step0Labels := by
      have ha : raw2020step0 = (fun i j => raw2020 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2020step0 raw2020; decide +kernel
      have hl : raw2020step0Labels = raw2020Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2020 raw2020Labels permutation152 permutation4
    _ = mixedMoment B node2398 node2398Labels := by rfl

theorem canonical2021 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2021 raw2021Labels = mixedMoment B node3341 node3341Labels := by
  calc
    mixedMoment B raw2021 raw2021Labels = mixedMoment B raw2021step0 raw2021step0Labels := by
      have ha : raw2021step0 = (fun i j => raw2021 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2021step0 raw2021; decide +kernel
      have hl : raw2021step0Labels = raw2021Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2021 raw2021Labels permutation152 permutation6
    mixedMoment B raw2021step0 raw2021step0Labels = mixedMoment B raw2021step1 raw2021step1Labels := by
      have ha : raw2021step1 = -raw2021step0 := by apply Matrix.ext; change ∀ i j, raw2021step1 i j = -(raw2021step0 i j); unfold raw2021step1 raw2021step0; decide +kernel
      have hl : raw2021step1Labels = raw2021step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2021step1 raw2021step1Labels = mixedMoment B raw2021step2 raw2021step2Labels := by
      have ha : raw2021step2 = raw2021step1 := by apply Matrix.ext; unfold raw2021step2 raw2021step1; decide +kernel
      have hl : raw2021step1Labels = labelEmbedding1 ∘ raw2021step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2021step1 raw2021step1Labels raw2021step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3341 node3341Labels := by rfl

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

theorem canonical2268 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2268 raw2268Labels = mixedMoment B node5257 node5257Labels := by
  calc
    mixedMoment B raw2268 raw2268Labels = mixedMoment B raw2268step0 raw2268step0Labels := by
      have ha : raw2268step0 = (fun i j => raw2268 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2268step0 raw2268; decide +kernel
      have hl : raw2268step0Labels = raw2268Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2268 raw2268Labels permutation152 permutation4
    mixedMoment B raw2268step0 raw2268step0Labels = mixedMoment B raw2268step1 raw2268step1Labels := by
      have ha : raw2268step1 = raw2268step0 := by apply Matrix.ext; unfold raw2268step1 raw2268step0; decide +kernel
      have hl : raw2268step0Labels = labelEmbedding7 ∘ raw2268step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2268step0 raw2268step0Labels raw2268step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5257 node5257Labels := by rfl

theorem canonical2269 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2269 raw2269Labels = mixedMoment B node2721 node2721Labels := by
  calc
    mixedMoment B raw2269 raw2269Labels = mixedMoment B raw2269step0 raw2269step0Labels := by
      have ha : raw2269step0 = (fun i j => raw2269 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2269step0 raw2269; decide +kernel
      have hl : raw2269step0Labels = raw2269Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2269 raw2269Labels permutation152 permutation4
    _ = mixedMoment B node2721 node2721Labels := by rfl

theorem canonical2270 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2270 raw2270Labels = mixedMoment B node3532 node3532Labels := by
  calc
    mixedMoment B raw2270 raw2270Labels = mixedMoment B raw2270step0 raw2270step0Labels := by
      have ha : raw2270step0 = (fun i j => raw2270 (permutation158 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2270step0 raw2270; decide +kernel
      have hl : raw2270step0Labels = raw2270Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2270 raw2270Labels permutation158 permutation6
    mixedMoment B raw2270step0 raw2270step0Labels = mixedMoment B raw2270step1 raw2270step1Labels := by
      have ha : raw2270step1 = -raw2270step0 := by apply Matrix.ext; change ∀ i j, raw2270step1 i j = -(raw2270step0 i j); unfold raw2270step1 raw2270step0; decide +kernel
      have hl : raw2270step1Labels = raw2270step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2270step1 raw2270step1Labels = mixedMoment B raw2270step2 raw2270step2Labels := by
      have ha : raw2270step2 = raw2270step1 := by apply Matrix.ext; unfold raw2270step2 raw2270step1; decide +kernel
      have hl : raw2270step1Labels = labelEmbedding1 ∘ raw2270step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2270step1 raw2270step1Labels raw2270step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3532 node3532Labels := by rfl

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

theorem canonical2463 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2463 raw2463Labels = mixedMoment B node5395 node5395Labels := by
  calc
    mixedMoment B raw2463 raw2463Labels = mixedMoment B raw2463step0 raw2463step0Labels := by
      have ha : raw2463step0 = (fun i j => raw2463 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2463step0 raw2463; decide +kernel
      have hl : raw2463step0Labels = raw2463Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2463 raw2463Labels permutation152 permutation4
    mixedMoment B raw2463step0 raw2463step0Labels = mixedMoment B raw2463step1 raw2463step1Labels := by
      have ha : raw2463step1 = raw2463step0 := by apply Matrix.ext; unfold raw2463step1 raw2463step0; decide +kernel
      have hl : raw2463step0Labels = labelEmbedding7 ∘ raw2463step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2463step0 raw2463step0Labels raw2463step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5395 node5395Labels := by rfl

theorem canonical2464 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2464 raw2464Labels = mixedMoment B node3781 node3781Labels := by
  calc
    mixedMoment B raw2464 raw2464Labels = mixedMoment B raw2464step0 raw2464step0Labels := by
      have ha : raw2464step0 = (fun i j => raw2464 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2464step0 raw2464; decide +kernel
      have hl : raw2464step0Labels = raw2464Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2464 raw2464Labels permutation152 permutation4
    _ = mixedMoment B node3781 node3781Labels := by rfl

theorem canonical2465 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2465 raw2465Labels = mixedMoment B node3794 node3794Labels := by
  calc
    mixedMoment B raw2465 raw2465Labels = mixedMoment B raw2465step0 raw2465step0Labels := by
      have ha : raw2465step0 = (fun i j => raw2465 (permutation153 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2465step0 raw2465; decide +kernel
      have hl : raw2465step0Labels = raw2465Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2465 raw2465Labels permutation153 permutation6
    mixedMoment B raw2465step0 raw2465step0Labels = mixedMoment B raw2465step1 raw2465step1Labels := by
      have ha : raw2465step1 = -raw2465step0 := by apply Matrix.ext; change ∀ i j, raw2465step1 i j = -(raw2465step0 i j); unfold raw2465step1 raw2465step0; decide +kernel
      have hl : raw2465step1Labels = raw2465step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2465step1 raw2465step1Labels = mixedMoment B raw2465step2 raw2465step2Labels := by
      have ha : raw2465step2 = raw2465step1 := by apply Matrix.ext; unfold raw2465step2 raw2465step1; decide +kernel
      have hl : raw2465step1Labels = labelEmbedding1 ∘ raw2465step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2465step1 raw2465step1Labels raw2465step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3794 node3794Labels := by rfl

theorem canonical2517 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2517 raw2517Labels = mixedMoment B node5428 node5428Labels := by
  calc
    mixedMoment B raw2517 raw2517Labels = mixedMoment B raw2517step0 raw2517step0Labels := by
      have ha : raw2517step0 = (fun i j => raw2517 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2517step0 raw2517; decide +kernel
      have hl : raw2517step0Labels = raw2517Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2517 raw2517Labels permutation32 permutation4
    mixedMoment B raw2517step0 raw2517step0Labels = mixedMoment B raw2517step1 raw2517step1Labels := by
      have ha : raw2517step1 = raw2517step0 := by apply Matrix.ext; unfold raw2517step1 raw2517step0; decide +kernel
      have hl : raw2517step0Labels = labelEmbedding7 ∘ raw2517step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2517step0 raw2517step0Labels raw2517step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5428 node5428Labels := by rfl

theorem canonical2518 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2518 raw2518Labels = mixedMoment B node3845 node3845Labels := by
  calc
    mixedMoment B raw2518 raw2518Labels = mixedMoment B raw2518step0 raw2518step0Labels := by
      have ha : raw2518step0 = (fun i j => raw2518 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2518step0 raw2518; decide +kernel
      have hl : raw2518step0Labels = raw2518Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2518 raw2518Labels permutation32 permutation4
    _ = mixedMoment B node3845 node3845Labels := by rfl

theorem canonical2519 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2519 raw2519Labels = mixedMoment B node3845 node3845Labels := by
  calc
    mixedMoment B raw2519 raw2519Labels = mixedMoment B raw2519step0 raw2519step0Labels := by
      have ha : raw2519step0 = (fun i j => raw2519 (permutation39 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2519step0 raw2519; decide +kernel
      have hl : raw2519step0Labels = raw2519Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2519 raw2519Labels permutation39 permutation6
    mixedMoment B raw2519step0 raw2519step0Labels = mixedMoment B raw2519step1 raw2519step1Labels := by
      have ha : raw2519step1 = -raw2519step0 := by apply Matrix.ext; change ∀ i j, raw2519step1 i j = -(raw2519step0 i j); unfold raw2519step1 raw2519step0; decide +kernel
      have hl : raw2519step1Labels = raw2519step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2519step1 raw2519step1Labels = mixedMoment B raw2519step2 raw2519step2Labels := by
      have ha : raw2519step2 = raw2519step1 := by apply Matrix.ext; unfold raw2519step2 raw2519step1; decide +kernel
      have hl : raw2519step1Labels = labelEmbedding1 ∘ raw2519step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2519step1 raw2519step1Labels raw2519step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3845 node3845Labels := by rfl

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

theorem canonical2583 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2583 raw2583Labels = mixedMoment B node5469 node5469Labels := by
  calc
    mixedMoment B raw2583 raw2583Labels = mixedMoment B raw2583step0 raw2583step0Labels := by
      have ha : raw2583step0 = (fun i j => raw2583 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2583step0 raw2583; decide +kernel
      have hl : raw2583step0Labels = raw2583Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2583 raw2583Labels permutation152 permutation4
    mixedMoment B raw2583step0 raw2583step0Labels = mixedMoment B raw2583step1 raw2583step1Labels := by
      have ha : raw2583step1 = raw2583step0 := by apply Matrix.ext; unfold raw2583step1 raw2583step0; decide +kernel
      have hl : raw2583step0Labels = labelEmbedding7 ∘ raw2583step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2583step0 raw2583step0Labels raw2583step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5469 node5469Labels := by rfl

theorem canonical2584 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2584 raw2584Labels = mixedMoment B node3945 node3945Labels := by
  calc
    mixedMoment B raw2584 raw2584Labels = mixedMoment B raw2584step0 raw2584step0Labels := by
      have ha : raw2584step0 = (fun i j => raw2584 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2584step0 raw2584; decide +kernel
      have hl : raw2584step0Labels = raw2584Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2584 raw2584Labels permutation152 permutation4
    _ = mixedMoment B node3945 node3945Labels := by rfl

theorem canonical2585 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2585 raw2585Labels = mixedMoment B node3952 node3952Labels := by
  calc
    mixedMoment B raw2585 raw2585Labels = mixedMoment B raw2585step0 raw2585step0Labels := by
      have ha : raw2585step0 = (fun i j => raw2585 (permutation265 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2585step0 raw2585; decide +kernel
      have hl : raw2585step0Labels = raw2585Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2585 raw2585Labels permutation265 permutation6
    mixedMoment B raw2585step0 raw2585step0Labels = mixedMoment B raw2585step1 raw2585step1Labels := by
      have ha : raw2585step1 = -raw2585step0 := by apply Matrix.ext; change ∀ i j, raw2585step1 i j = -(raw2585step0 i j); unfold raw2585step1 raw2585step0; decide +kernel
      have hl : raw2585step1Labels = raw2585step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2585step1 raw2585step1Labels = mixedMoment B raw2585step2 raw2585step2Labels := by
      have ha : raw2585step2 = raw2585step1 := by apply Matrix.ext; unfold raw2585step2 raw2585step1; decide +kernel
      have hl : raw2585step1Labels = labelEmbedding1 ∘ raw2585step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2585step1 raw2585step1Labels raw2585step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3952 node3952Labels := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons78
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singleton4996 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4996 node4996Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2382 node2382Labels + mixedMoment B node3340 node3340Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2007 singletonSmall4996
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4996) = raw2007Labels := by decide +kernel
  rw [hl, canonical2007 B hB] at h
  have hc0 : mixedMoment B raw2007 (Fin.cases (0 : Fin 2) singletonSmall4996) =
      mixedMoment B node2382 node2382Labels := by
    have ha : raw2007 = raw2008 := by apply Matrix.ext; unfold raw2007 raw2008; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4996 = raw2008Labels := by decide +kernel
    rw [ha, hj, canonical2008 B hB]
  have hc1 : mixedMoment B raw2007 (Fin.cases (1 : Fin 2) singletonSmall4996) =
      mixedMoment B node3340 node3340Labels := by
    have ha : raw2007 = raw2009 := by apply Matrix.ext; unfold raw2007 raw2009; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4996 = raw2009Labels := by decide +kernel
    rw [ha, hj, canonical2009 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4998 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4998 node4998Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2383 node2383Labels + mixedMoment B node3352 node3352Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2010 singletonSmall4998
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4998) = raw2010Labels := by decide +kernel
  rw [hl, canonical2010 B hB] at h
  have hc0 : mixedMoment B raw2010 (Fin.cases (0 : Fin 2) singletonSmall4998) =
      mixedMoment B node2383 node2383Labels := by
    have ha : raw2010 = raw2011 := by apply Matrix.ext; unfold raw2010 raw2011; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4998 = raw2011Labels := by decide +kernel
    rw [ha, hj, canonical2011 B hB]
  have hc1 : mixedMoment B raw2010 (Fin.cases (1 : Fin 2) singletonSmall4998) =
      mixedMoment B node3352 node3352Labels := by
    have ha : raw2010 = raw2012 := by apply Matrix.ext; unfold raw2010 raw2012; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4998 = raw2012Labels := by decide +kernel
    rw [ha, hj, canonical2012 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton5013 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5013 node5013Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2398 node2398Labels + mixedMoment B node3341 node3341Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2019 singletonSmall5013
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5013) = raw2019Labels := by decide +kernel
  rw [hl, canonical2019 B hB] at h
  have hc0 : mixedMoment B raw2019 (Fin.cases (0 : Fin 2) singletonSmall5013) =
      mixedMoment B node2398 node2398Labels := by
    have ha : raw2019 = raw2020 := by apply Matrix.ext; unfold raw2019 raw2020; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5013 = raw2020Labels := by decide +kernel
    rw [ha, hj, canonical2020 B hB]
  have hc1 : mixedMoment B raw2019 (Fin.cases (1 : Fin 2) singletonSmall5013) =
      mixedMoment B node3341 node3341Labels := by
    have ha : raw2019 = raw2021 := by apply Matrix.ext; unfold raw2019 raw2021; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5013 = raw2021Labels := by decide +kernel
    rw [ha, hj, canonical2021 B hB]
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

theorem singleton5257 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5257 node5257Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2721 node2721Labels + mixedMoment B node3532 node3532Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2268 singletonSmall5257
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5257) = raw2268Labels := by decide +kernel
  rw [hl, canonical2268 B hB] at h
  have hc0 : mixedMoment B raw2268 (Fin.cases (0 : Fin 2) singletonSmall5257) =
      mixedMoment B node2721 node2721Labels := by
    have ha : raw2268 = raw2269 := by apply Matrix.ext; unfold raw2268 raw2269; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5257 = raw2269Labels := by decide +kernel
    rw [ha, hj, canonical2269 B hB]
  have hc1 : mixedMoment B raw2268 (Fin.cases (1 : Fin 2) singletonSmall5257) =
      mixedMoment B node3532 node3532Labels := by
    have ha : raw2268 = raw2270 := by apply Matrix.ext; unfold raw2268 raw2270; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5257 = raw2270Labels := by decide +kernel
    rw [ha, hj, canonical2270 B hB]
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

theorem singleton5395 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5395 node5395Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3781 node3781Labels + mixedMoment B node3794 node3794Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2463 singletonSmall5395
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5395) = raw2463Labels := by decide +kernel
  rw [hl, canonical2463 B hB] at h
  have hc0 : mixedMoment B raw2463 (Fin.cases (0 : Fin 2) singletonSmall5395) =
      mixedMoment B node3781 node3781Labels := by
    have ha : raw2463 = raw2464 := by apply Matrix.ext; unfold raw2463 raw2464; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5395 = raw2464Labels := by decide +kernel
    rw [ha, hj, canonical2464 B hB]
  have hc1 : mixedMoment B raw2463 (Fin.cases (1 : Fin 2) singletonSmall5395) =
      mixedMoment B node3794 node3794Labels := by
    have ha : raw2463 = raw2465 := by apply Matrix.ext; unfold raw2463 raw2465; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5395 = raw2465Labels := by decide +kernel
    rw [ha, hj, canonical2465 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton5428 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5428 node5428Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3845 node3845Labels + mixedMoment B node3845 node3845Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2517 singletonSmall5428
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5428) = raw2517Labels := by decide +kernel
  rw [hl, canonical2517 B hB] at h
  have hc0 : mixedMoment B raw2517 (Fin.cases (0 : Fin 2) singletonSmall5428) =
      mixedMoment B node3845 node3845Labels := by
    have ha : raw2517 = raw2518 := by apply Matrix.ext; unfold raw2517 raw2518; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5428 = raw2518Labels := by decide +kernel
    rw [ha, hj, canonical2518 B hB]
  have hc1 : mixedMoment B raw2517 (Fin.cases (1 : Fin 2) singletonSmall5428) =
      mixedMoment B node3845 node3845Labels := by
    have ha : raw2517 = raw2519 := by apply Matrix.ext; unfold raw2517 raw2519; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5428 = raw2519Labels := by decide +kernel
    rw [ha, hj, canonical2519 B hB]
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

theorem singleton5469 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5469 node5469Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3945 node3945Labels + mixedMoment B node3952 node3952Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2583 singletonSmall5469
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5469) = raw2583Labels := by decide +kernel
  rw [hl, canonical2583 B hB] at h
  have hc0 : mixedMoment B raw2583 (Fin.cases (0 : Fin 2) singletonSmall5469) =
      mixedMoment B node3945 node3945Labels := by
    have ha : raw2583 = raw2584 := by apply Matrix.ext; unfold raw2583 raw2584; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5469 = raw2584Labels := by decide +kernel
    rw [ha, hj, canonical2584 B hB]
  have hc1 : mixedMoment B raw2583 (Fin.cases (1 : Fin 2) singletonSmall5469) =
      mixedMoment B node3952 node3952Labels := by
    have ha : raw2583 = raw2585 := by apply Matrix.ext; unfold raw2583 raw2585; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5469 = raw2585Labels := by decide +kernel
    rw [ha, hj, canonical2585 B hB]
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

theorem zero5489 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node5489 node5489Labels = 0 := by
  exact mixedMoment_alpha B hF node5489 node5489Labels 2 permutation152
    (by decide +kernel)

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

theorem sound2382 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2382 node2382Labels = Sparse.eval nodeValue2382 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2382) = mixedMoment B node2382 node2382Labels := rfl
  simpa [nodeValue2382, Sparse.eval] using hc.symm

theorem sound2383 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2383 node2383Labels = Sparse.eval nodeValue2383 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2383) = mixedMoment B node2383 node2383Labels := rfl
  simpa [nodeValue2383, Sparse.eval] using hc.symm

theorem sound2398 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2398 node2398Labels = Sparse.eval nodeValue2398 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2398) = mixedMoment B node2398 node2398Labels := rfl
  simpa [nodeValue2398, Sparse.eval] using hc.symm

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

theorem sound2721 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2721 node2721Labels = Sparse.eval nodeValue2721 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2721) = mixedMoment B node2721 node2721Labels := rfl
  simpa [nodeValue2721, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound52
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound3340 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3340 node3340Labels = Sparse.eval nodeValue3340 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3340) = mixedMoment B node3340 node3340Labels := rfl
  simpa [nodeValue3340, Sparse.eval] using hc.symm

theorem sound3341 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3341 node3341Labels = Sparse.eval nodeValue3341 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3341) = mixedMoment B node3341 node3341Labels := rfl
  simpa [nodeValue3341, Sparse.eval] using hc.symm

theorem sound3352 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3352 node3352Labels = Sparse.eval nodeValue3352 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3352) = mixedMoment B node3352 node3352Labels := rfl
  simpa [nodeValue3352, Sparse.eval] using hc.symm

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

theorem sound3532 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3532 node3532Labels = Sparse.eval nodeValue3532 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3532) = mixedMoment B node3532 node3532Labels := rfl
  simpa [nodeValue3532, Sparse.eval] using hc.symm

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

theorem sound3781 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3781 node3781Labels = Sparse.eval nodeValue3781 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3781) = mixedMoment B node3781 node3781Labels := rfl
  simpa [nodeValue3781, Sparse.eval] using hc.symm

theorem sound3794 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3794 node3794Labels = Sparse.eval nodeValue3794 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3794) = mixedMoment B node3794 node3794Labels := rfl
  simpa [nodeValue3794, Sparse.eval] using hc.symm

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

theorem sound3845 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3845 node3845Labels = Sparse.eval nodeValue3845 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3845) = mixedMoment B node3845 node3845Labels := rfl
  simpa [nodeValue3845, Sparse.eval] using hc.symm

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

theorem sound3945 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3945 node3945Labels = Sparse.eval nodeValue3945 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3945) = mixedMoment B node3945 node3945Labels := rfl
  simpa [nodeValue3945, Sparse.eval] using hc.symm

theorem sound3952 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3952 node3952Labels = Sparse.eval nodeValue3952 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3952) = mixedMoment B node3952 node3952Labels := rfl
  simpa [nodeValue3952, Sparse.eval] using hc.symm

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound78
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound4996 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4996 node4996Labels = Sparse.eval nodeValue4996 (mixedVector B) := by
  have h := singleton4996 B _hB
  rw [sound2382 B _hB _hF, sound3340 B _hB _hF] at h
  norm_num [nodeValue4996, nodeValue2382, nodeValue3340, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4998 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4998 node4998Labels = Sparse.eval nodeValue4998 (mixedVector B) := by
  have h := singleton4998 B _hB
  rw [sound2383 B _hB _hF, sound3352 B _hB _hF] at h
  norm_num [nodeValue4998, nodeValue2383, nodeValue3352, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5013 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5013 node5013Labels = Sparse.eval nodeValue5013 (mixedVector B) := by
  have h := singleton5013 B _hB
  rw [sound2398 B _hB _hF, sound3341 B _hB _hF] at h
  norm_num [nodeValue5013, nodeValue2398, nodeValue3341, Sparse.eval] at h ⊢
  linarith only [h]

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

theorem sound5257 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5257 node5257Labels = Sparse.eval nodeValue5257 (mixedVector B) := by
  have h := singleton5257 B _hB
  rw [sound2721 B _hB _hF, sound3532 B _hB _hF] at h
  norm_num [nodeValue5257, nodeValue2721, nodeValue3532, Sparse.eval] at h ⊢
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

theorem sound5395 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5395 node5395Labels = Sparse.eval nodeValue5395 (mixedVector B) := by
  have h := singleton5395 B _hB
  rw [sound3781 B _hB _hF, sound3794 B _hB _hF] at h
  norm_num [nodeValue5395, nodeValue3781, nodeValue3794, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5428 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5428 node5428Labels = Sparse.eval nodeValue5428 (mixedVector B) := by
  have h := singleton5428 B _hB
  rw [sound3845 B _hB _hF] at h
  norm_num [nodeValue5428, nodeValue3845, Sparse.eval] at h ⊢
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

theorem sound5469 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5469 node5469Labels = Sparse.eval nodeValue5469 (mixedVector B) := by
  have h := singleton5469 B _hB
  rw [sound3945 B _hB _hF, sound3952 B _hB _hF] at h
  norm_num [nodeValue5469, nodeValue3945, nodeValue3952, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5473 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5473 node5473Labels = Sparse.eval nodeValue5473 (mixedVector B) := by
  have h := singleton5473 B _hB
  rw [sound3958 B _hB _hF, sound3961 B _hB _hF] at h
  norm_num [nodeValue5473, nodeValue3958, nodeValue3961, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5489 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5489 node5489Labels = Sparse.eval nodeValue5489 (mixedVector B) := by
  simpa only [nodeValue5489, Sparse.eval_nil] using zero5489 B _hB _hF

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources35
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sourceEq1130 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1130 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1130 + difference 0 1) (sourceB1130 + difference 1 0) sourceC1130) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5257) := by
    have ha : (tripleCharges (sourceA1130 + difference 0 1) (sourceB1130 + difference 1 0) sourceC1130) = raw19140 := by
      apply Matrix.ext; unfold tripleCharges sourceA1130 sourceB1130 sourceC1130 difference raw19140; decide +kernel
    rw [ha]
    exact (canonical19140 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1130 + difference 0 2) (sourceB1130 + difference 2 0) sourceC1130) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5489) := by
    have ha : (tripleCharges (sourceA1130 + difference 0 2) (sourceB1130 + difference 2 0) sourceC1130) = raw19141 := by
      apply Matrix.ext; unfold tripleCharges sourceA1130 sourceB1130 sourceC1130 difference raw19141; decide +kernel
    rw [ha]
    exact (canonical19141 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1130 + difference 0 3) (sourceB1130 + difference 3 0) sourceC1130) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5490) := by
    have ha : (tripleCharges (sourceA1130 + difference 0 3) (sourceB1130 + difference 3 0) sourceC1130) = raw19142 := by
      apply Matrix.ext; unfold tripleCharges sourceA1130 sourceB1130 sourceC1130 difference raw19142; decide +kernel
    rw [ha]
    exact (canonical19142 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1130 + difference 0 4) (sourceB1130 + difference 4 0) sourceC1130) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5490) := by
    have ha : (tripleCharges (sourceA1130 + difference 0 4) (sourceB1130 + difference 4 0) sourceC1130) = raw19143 := by
      apply Matrix.ext; unfold tripleCharges sourceA1130 sourceB1130 sourceC1130 difference raw19143; decide +kernel
    rw [ha]
    exact (canonical19143 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1130 + difference 0 5) (sourceB1130 + difference 5 0) sourceC1130) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5482) := by
    have ha : (tripleCharges (sourceA1130 + difference 0 5) (sourceB1130 + difference 5 0) sourceC1130) = raw19144 := by
      apply Matrix.ext; unfold tripleCharges sourceA1130 sourceB1130 sourceC1130 difference raw19144; decide +kernel
    rw [ha]
    exact (canonical19144 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1130 + difference 1 0) (sourceB1130 + difference 0 1) sourceC1130) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5257) := by
    have ha : (tripleCharges (sourceA1130 + difference 1 0) (sourceB1130 + difference 0 1) sourceC1130) = raw19145 := by
      apply Matrix.ext; unfold tripleCharges sourceA1130 sourceB1130 sourceC1130 difference raw19145; decide +kernel
    rw [ha]
    exact (canonical19145 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1130 + difference 1 2) (sourceB1130 + difference 2 1) sourceC1130) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5482) := by
    have ha : (tripleCharges (sourceA1130 + difference 1 2) (sourceB1130 + difference 2 1) sourceC1130) = raw19146 := by
      apply Matrix.ext; unfold tripleCharges sourceA1130 sourceB1130 sourceC1130 difference raw19146; decide +kernel
    rw [ha]
    exact (canonical19146 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1130 + difference 1 3) (sourceB1130 + difference 3 1) sourceC1130) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5490) := by
    have ha : (tripleCharges (sourceA1130 + difference 1 3) (sourceB1130 + difference 3 1) sourceC1130) = raw19147 := by
      apply Matrix.ext; unfold tripleCharges sourceA1130 sourceB1130 sourceC1130 difference raw19147; decide +kernel
    rw [ha]
    exact (canonical19147 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1130 + difference 1 4) (sourceB1130 + difference 4 1) sourceC1130) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5490) := by
    have ha : (tripleCharges (sourceA1130 + difference 1 4) (sourceB1130 + difference 4 1) sourceC1130) = raw19148 := by
      apply Matrix.ext; unfold tripleCharges sourceA1130 sourceB1130 sourceC1130 difference raw19148; decide +kernel
    rw [ha]
    exact (canonical19148 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1130 + difference 1 5) (sourceB1130 + difference 5 1) sourceC1130) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5489) := by
    have ha : (tripleCharges (sourceA1130 + difference 1 5) (sourceB1130 + difference 5 1) sourceC1130) = raw19149 := by
      apply Matrix.ext; unfold tripleCharges sourceA1130 sourceB1130 sourceC1130 difference raw19149; decide +kernel
    rw [ha]
    exact (canonical19149 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1130 + difference 2 0) (sourceB1130 + difference 0 2) sourceC1130) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5013) := by
    have ha : (tripleCharges (sourceA1130 + difference 2 0) (sourceB1130 + difference 0 2) sourceC1130) = raw19150 := by
      apply Matrix.ext; unfold tripleCharges sourceA1130 sourceB1130 sourceC1130 difference raw19150; decide +kernel
    rw [ha]
    exact (canonical19150 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1130 + difference 2 1) (sourceB1130 + difference 1 2) sourceC1130) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4998) := by
    have ha : (tripleCharges (sourceA1130 + difference 2 1) (sourceB1130 + difference 1 2) sourceC1130) = raw19151 := by
      apply Matrix.ext; unfold tripleCharges sourceA1130 sourceB1130 sourceC1130 difference raw19151; decide +kernel
    rw [ha]
    exact (canonical19151 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1130 + difference 2 3) (sourceB1130 + difference 3 2) sourceC1130) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5473) := by
    have ha : (tripleCharges (sourceA1130 + difference 2 3) (sourceB1130 + difference 3 2) sourceC1130) = raw19152 := by
      apply Matrix.ext; unfold tripleCharges sourceA1130 sourceB1130 sourceC1130 difference raw19152; decide +kernel
    rw [ha]
    exact (canonical19152 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1130 + difference 2 4) (sourceB1130 + difference 4 2) sourceC1130) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5473) := by
    have ha : (tripleCharges (sourceA1130 + difference 2 4) (sourceB1130 + difference 4 2) sourceC1130) = raw19153 := by
      apply Matrix.ext; unfold tripleCharges sourceA1130 sourceB1130 sourceC1130 difference raw19153; decide +kernel
    rw [ha]
    exact (canonical19153 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1130 + difference 2 5) (sourceB1130 + difference 5 2) sourceC1130) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5469) := by
    have ha : (tripleCharges (sourceA1130 + difference 2 5) (sourceB1130 + difference 5 2) sourceC1130) = raw19154 := by
      apply Matrix.ext; unfold tripleCharges sourceA1130 sourceB1130 sourceC1130 difference raw19154; decide +kernel
    rw [ha]
    exact (canonical19154 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1130 + difference 3 0) (sourceB1130 + difference 0 3) sourceC1130) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4996) := by
    have ha : (tripleCharges (sourceA1130 + difference 3 0) (sourceB1130 + difference 0 3) sourceC1130) = raw19155 := by
      apply Matrix.ext; unfold tripleCharges sourceA1130 sourceB1130 sourceC1130 difference raw19155; decide +kernel
    rw [ha]
    exact (canonical19155 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1130 + difference 3 1) (sourceB1130 + difference 1 3) sourceC1130) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4996) := by
    have ha : (tripleCharges (sourceA1130 + difference 3 1) (sourceB1130 + difference 1 3) sourceC1130) = raw19156 := by
      apply Matrix.ext; unfold tripleCharges sourceA1130 sourceB1130 sourceC1130 difference raw19156; decide +kernel
    rw [ha]
    exact (canonical19156 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1130 + difference 3 2) (sourceB1130 + difference 2 3) sourceC1130) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5395) := by
    have ha : (tripleCharges (sourceA1130 + difference 3 2) (sourceB1130 + difference 2 3) sourceC1130) = raw19157 := by
      apply Matrix.ext; unfold tripleCharges sourceA1130 sourceB1130 sourceC1130 difference raw19157; decide +kernel
    rw [ha]
    exact (canonical19157 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1130 + difference 3 4) (sourceB1130 + difference 4 3) sourceC1130) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5428) := by
    have ha : (tripleCharges (sourceA1130 + difference 3 4) (sourceB1130 + difference 4 3) sourceC1130) = raw19158 := by
      apply Matrix.ext; unfold tripleCharges sourceA1130 sourceB1130 sourceC1130 difference raw19158; decide +kernel
    rw [ha]
    exact (canonical19158 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1130 + difference 3 5) (sourceB1130 + difference 5 3) sourceC1130) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5395) := by
    have ha : (tripleCharges (sourceA1130 + difference 3 5) (sourceB1130 + difference 5 3) sourceC1130) = raw19159 := by
      apply Matrix.ext; unfold tripleCharges sourceA1130 sourceB1130 sourceC1130 difference raw19159; decide +kernel
    rw [ha]
    exact (canonical19159 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1130 + difference 4 0) (sourceB1130 + difference 0 4) sourceC1130) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4996) := by
    have ha : (tripleCharges (sourceA1130 + difference 4 0) (sourceB1130 + difference 0 4) sourceC1130) = raw19160 := by
      apply Matrix.ext; unfold tripleCharges sourceA1130 sourceB1130 sourceC1130 difference raw19160; decide +kernel
    rw [ha]
    exact (canonical19160 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1130 + difference 4 1) (sourceB1130 + difference 1 4) sourceC1130) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4996) := by
    have ha : (tripleCharges (sourceA1130 + difference 4 1) (sourceB1130 + difference 1 4) sourceC1130) = raw19161 := by
      apply Matrix.ext; unfold tripleCharges sourceA1130 sourceB1130 sourceC1130 difference raw19161; decide +kernel
    rw [ha]
    exact (canonical19161 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1130 + difference 4 2) (sourceB1130 + difference 2 4) sourceC1130) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5395) := by
    have ha : (tripleCharges (sourceA1130 + difference 4 2) (sourceB1130 + difference 2 4) sourceC1130) = raw19162 := by
      apply Matrix.ext; unfold tripleCharges sourceA1130 sourceB1130 sourceC1130 difference raw19162; decide +kernel
    rw [ha]
    exact (canonical19162 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1130 + difference 4 3) (sourceB1130 + difference 3 4) sourceC1130) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5428) := by
    have ha : (tripleCharges (sourceA1130 + difference 4 3) (sourceB1130 + difference 3 4) sourceC1130) = raw19163 := by
      apply Matrix.ext; unfold tripleCharges sourceA1130 sourceB1130 sourceC1130 difference raw19163; decide +kernel
    rw [ha]
    exact (canonical19163 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1130 + difference 4 5) (sourceB1130 + difference 5 4) sourceC1130) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5395) := by
    have ha : (tripleCharges (sourceA1130 + difference 4 5) (sourceB1130 + difference 5 4) sourceC1130) = raw19164 := by
      apply Matrix.ext; unfold tripleCharges sourceA1130 sourceB1130 sourceC1130 difference raw19164; decide +kernel
    rw [ha]
    exact (canonical19164 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1130 + difference 5 0) (sourceB1130 + difference 0 5) sourceC1130) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4998) := by
    have ha : (tripleCharges (sourceA1130 + difference 5 0) (sourceB1130 + difference 0 5) sourceC1130) = raw19165 := by
      apply Matrix.ext; unfold tripleCharges sourceA1130 sourceB1130 sourceC1130 difference raw19165; decide +kernel
    rw [ha]
    exact (canonical19165 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1130 + difference 5 1) (sourceB1130 + difference 1 5) sourceC1130) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5013) := by
    have ha : (tripleCharges (sourceA1130 + difference 5 1) (sourceB1130 + difference 1 5) sourceC1130) = raw19166 := by
      apply Matrix.ext; unfold tripleCharges sourceA1130 sourceB1130 sourceC1130 difference raw19166; decide +kernel
    rw [ha]
    exact (canonical19166 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1130 + difference 5 2) (sourceB1130 + difference 2 5) sourceC1130) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5469) := by
    have ha : (tripleCharges (sourceA1130 + difference 5 2) (sourceB1130 + difference 2 5) sourceC1130) = raw19167 := by
      apply Matrix.ext; unfold tripleCharges sourceA1130 sourceB1130 sourceC1130 difference raw19167; decide +kernel
    rw [ha]
    exact (canonical19167 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1130 + difference 5 3) (sourceB1130 + difference 3 5) sourceC1130) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5473) := by
    have ha : (tripleCharges (sourceA1130 + difference 5 3) (sourceB1130 + difference 3 5) sourceC1130) = raw19168 := by
      apply Matrix.ext; unfold tripleCharges sourceA1130 sourceB1130 sourceC1130 difference raw19168; decide +kernel
    rw [ha]
    exact (canonical19168 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1130 + difference 5 4) (sourceB1130 + difference 4 5) sourceC1130) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5473) := by
    have ha : (tripleCharges (sourceA1130 + difference 5 4) (sourceB1130 + difference 4 5) sourceC1130) = raw19169 := by
      apply Matrix.ext; unfold tripleCharges sourceA1130 sourceB1130 sourceC1130 difference raw19169; decide +kernel
    rw [ha]
    exact (canonical19169 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1130 sourceB1130 sourceC1130
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1130, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic61
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reindexCheck982 : Integer.Sparse.reindex keyMap MixedData.row982 = numericRow982 := by decide +kernel

theorem numericCheck982 (x : Master → ℝ) : Integer.Sparse.eval numericRow982 x =
    (1728 : ℝ) * reducedSource982 x := by
  norm_num [numericRow982, reducedSource982, Integer.Sparse.eval, Sparse.eval, nodeValue4996, nodeValue4998, nodeValue5013, nodeValue5257, nodeValue5395, nodeValue5428, nodeValue5469, nodeValue5473, nodeValue5482, nodeValue5489, nodeValue5490]
  ring

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Rows61
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero982 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource982 (mixedVector B) = 0 := by
  have h4996 : mixedVector B (Sum.inr 4996) = Sparse.eval nodeValue4996 (mixedVector B) := by
    change mixedMoment B node4996 node4996Labels = _
    exact sound4996 B hB hF
  have h4998 : mixedVector B (Sum.inr 4998) = Sparse.eval nodeValue4998 (mixedVector B) := by
    change mixedMoment B node4998 node4998Labels = _
    exact sound4998 B hB hF
  have h5013 : mixedVector B (Sum.inr 5013) = Sparse.eval nodeValue5013 (mixedVector B) := by
    change mixedMoment B node5013 node5013Labels = _
    exact sound5013 B hB hF
  have h5257 : mixedVector B (Sum.inr 5257) = Sparse.eval nodeValue5257 (mixedVector B) := by
    change mixedMoment B node5257 node5257Labels = _
    exact sound5257 B hB hF
  have h5395 : mixedVector B (Sum.inr 5395) = Sparse.eval nodeValue5395 (mixedVector B) := by
    change mixedMoment B node5395 node5395Labels = _
    exact sound5395 B hB hF
  have h5428 : mixedVector B (Sum.inr 5428) = Sparse.eval nodeValue5428 (mixedVector B) := by
    change mixedMoment B node5428 node5428Labels = _
    exact sound5428 B hB hF
  have h5469 : mixedVector B (Sum.inr 5469) = Sparse.eval nodeValue5469 (mixedVector B) := by
    change mixedMoment B node5469 node5469Labels = _
    exact sound5469 B hB hF
  have h5473 : mixedVector B (Sum.inr 5473) = Sparse.eval nodeValue5473 (mixedVector B) := by
    change mixedMoment B node5473 node5473Labels = _
    exact sound5473 B hB hF
  have h5482 : mixedVector B (Sum.inr 5482) = Sparse.eval nodeValue5482 (mixedVector B) := by
    change mixedMoment B node5482 node5482Labels = _
    exact sound5482_e B hB hF
  have h5489 : mixedVector B (Sum.inr 5489) = Sparse.eval nodeValue5489 (mixedVector B) := by
    change mixedMoment B node5489 node5489Labels = _
    exact sound5489 B hB hF
  have h5490 : mixedVector B (Sum.inr 5490) = Sparse.eval nodeValue5490 (mixedVector B) := by
    change mixedMoment B node5490 node5490Labels = _
    exact sound5490_e B hB hF
  simpa only [sourceForm1130, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4996, h4998, h5013, h5257, h5395, h5428, h5469, h5473, h5482, h5489, h5490, reducedSource982] using sourceEq1130 B hB

theorem rowSound982_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row982 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck982, numericCheck982, reducedZero982 B hB hF, mul_zero]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedSourceBridge.rowSound982_e_oai := @OAI.MUB6.Certificate.MixedSourceBridge.rowSound982_e_oai
