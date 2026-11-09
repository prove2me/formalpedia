-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedSourceBridge.rowSound792_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T02:27:59.379956+00:00
-- url     : https://prove2.me/submissions/e8611efb-66f3-4ff6-912e-eb1edefe6a40

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E070
import Definitions.Def_OAIQ106E086
import Definitions.Def_OAIQ106E091
import Definitions.Def_OAIQ106E102
import Definitions.Def_OAIQ106E103
import Definitions.Def_OAIQ106E110
import Definitions.Def_OAIQ106E115
import Definitions.Def_OAIQ106E119
import Definitions.Def_OAIQ106E123
import Definitions.Def_OAIQ106E128
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
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound3853_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound4003_e

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical115
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical14763 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14763 raw14763Labels = mixedMoment B node3876 node3876Labels := by
  calc
    mixedMoment B raw14763 raw14763Labels = mixedMoment B raw14763step0 raw14763step0Labels := by
      have hz : ∀ j, raw14763 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw14763step0 = (fun i j => raw14763 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw14763step0 raw14763; decide +kernel
      have hl : raw14763step0Labels = raw14763Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14763 raw14763Labels permutation434 hz
    mixedMoment B raw14763step0 raw14763step0Labels = mixedMoment B raw14763step1 raw14763step1Labels := by
      have ha : raw14763step1 = (fun i j => raw14763step0 (permutation151 i) (permutation7 j)) := by apply Matrix.ext; unfold raw14763step1 raw14763step0; decide +kernel
      have hl : raw14763step1Labels = raw14763step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14763step0 raw14763step0Labels permutation151 permutation7
    mixedMoment B raw14763step1 raw14763step1Labels = mixedMoment B raw14763step2 raw14763step2Labels := by
      have ha : raw14763step2 = -raw14763step1 := by apply Matrix.ext; change ∀ i j, raw14763step2 i j = -(raw14763step1 i j); unfold raw14763step2 raw14763step1; decide +kernel
      have hl : raw14763step2Labels = raw14763step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw14763step2 raw14763step2Labels = mixedMoment B raw14763step3 raw14763step3Labels := by
      have ha : raw14763step3 = raw14763step2 := by apply Matrix.ext; unfold raw14763step3 raw14763step2; decide +kernel
      have hl : raw14763step2Labels = labelEmbedding1 ∘ raw14763step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14763step2 raw14763step2Labels raw14763step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3876 node3876Labels := by rfl

theorem canonical14768 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14768 raw14768Labels = mixedMoment B node3877 node3877Labels := by
  calc
    mixedMoment B raw14768 raw14768Labels = mixedMoment B raw14768step0 raw14768step0Labels := by
      have hz : ∀ j, raw14768 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw14768step0 = (fun i j => raw14768 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw14768step0 raw14768; decide +kernel
      have hl : raw14768step0Labels = raw14768Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14768 raw14768Labels permutation434 hz
    mixedMoment B raw14768step0 raw14768step0Labels = mixedMoment B raw14768step1 raw14768step1Labels := by
      have ha : raw14768step1 = (fun i j => raw14768step0 (permutation151 i) (permutation7 j)) := by apply Matrix.ext; unfold raw14768step1 raw14768step0; decide +kernel
      have hl : raw14768step1Labels = raw14768step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14768step0 raw14768step0Labels permutation151 permutation7
    mixedMoment B raw14768step1 raw14768step1Labels = mixedMoment B raw14768step2 raw14768step2Labels := by
      have ha : raw14768step2 = -raw14768step1 := by apply Matrix.ext; change ∀ i j, raw14768step2 i j = -(raw14768step1 i j); unfold raw14768step2 raw14768step1; decide +kernel
      have hl : raw14768step2Labels = raw14768step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw14768step2 raw14768step2Labels = mixedMoment B raw14768step3 raw14768step3Labels := by
      have ha : raw14768step3 = raw14768step2 := by apply Matrix.ext; unfold raw14768step3 raw14768step2; decide +kernel
      have hl : raw14768step2Labels = labelEmbedding1 ∘ raw14768step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14768step2 raw14768step2Labels raw14768step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3877 node3877Labels := by rfl

theorem canonical14771 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14771 raw14771Labels = mixedMoment B node3039 node3039Labels := by
  calc
    mixedMoment B raw14771 raw14771Labels = mixedMoment B raw14771step0 raw14771step0Labels := by
      have hz : ∀ j, raw14771 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw14771step0 = (fun i j => raw14771 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw14771step0 raw14771; decide +kernel
      have hl : raw14771step0Labels = raw14771Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14771 raw14771Labels permutation346 hz
    mixedMoment B raw14771step0 raw14771step0Labels = mixedMoment B raw14771step1 raw14771step1Labels := by
      have ha : raw14771step1 = (fun i j => raw14771step0 (permutation50 i) (permutation5 j)) := by apply Matrix.ext; unfold raw14771step1 raw14771step0; decide +kernel
      have hl : raw14771step1Labels = raw14771step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14771step0 raw14771step0Labels permutation50 permutation5
    mixedMoment B raw14771step1 raw14771step1Labels = mixedMoment B raw14771step2 raw14771step2Labels := by
      have ha : raw14771step2 = -raw14771step1 := by apply Matrix.ext; change ∀ i j, raw14771step2 i j = -(raw14771step1 i j); unfold raw14771step2 raw14771step1; decide +kernel
      have hl : raw14771step2Labels = raw14771step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw14771step2 raw14771step2Labels = mixedMoment B raw14771step3 raw14771step3Labels := by
      have ha : raw14771step3 = raw14771step2 := by apply Matrix.ext; unfold raw14771step3 raw14771step2; decide +kernel
      have hl : raw14771step2Labels = labelEmbedding1 ∘ raw14771step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14771step2 raw14771step2Labels raw14771step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3039 node3039Labels := by rfl

theorem canonical14772 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14772 raw14772Labels = mixedMoment B node3883 node3883Labels := by
  calc
    mixedMoment B raw14772 raw14772Labels = mixedMoment B raw14772step0 raw14772step0Labels := by
      have hz : ∀ j, raw14772 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw14772step0 = (fun i j => raw14772 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw14772step0 raw14772; decide +kernel
      have hl : raw14772step0Labels = raw14772Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14772 raw14772Labels permutation346 hz
    mixedMoment B raw14772step0 raw14772step0Labels = mixedMoment B raw14772step1 raw14772step1Labels := by
      have ha : raw14772step1 = (fun i j => raw14772step0 (permutation151 i) (permutation7 j)) := by apply Matrix.ext; unfold raw14772step1 raw14772step0; decide +kernel
      have hl : raw14772step1Labels = raw14772step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14772step0 raw14772step0Labels permutation151 permutation7
    mixedMoment B raw14772step1 raw14772step1Labels = mixedMoment B raw14772step2 raw14772step2Labels := by
      have ha : raw14772step2 = -raw14772step1 := by apply Matrix.ext; change ∀ i j, raw14772step2 i j = -(raw14772step1 i j); unfold raw14772step2 raw14772step1; decide +kernel
      have hl : raw14772step2Labels = raw14772step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw14772step2 raw14772step2Labels = mixedMoment B raw14772step3 raw14772step3Labels := by
      have ha : raw14772step3 = raw14772step2 := by apply Matrix.ext; unfold raw14772step3 raw14772step2; decide +kernel
      have hl : raw14772step2Labels = labelEmbedding1 ∘ raw14772step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14772step2 raw14772step2Labels raw14772step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3883 node3883Labels := by rfl

theorem canonical14774 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14774 raw14774Labels = mixedMoment B node3853 node3853Labels := by
  calc
    mixedMoment B raw14774 raw14774Labels = mixedMoment B raw14774step0 raw14774step0Labels := by
      have hz : ∀ j, raw14774 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw14774step0 = (fun i j => raw14774 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw14774step0 raw14774; decide +kernel
      have hl : raw14774step0Labels = raw14774Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14774 raw14774Labels permutation346 hz
    mixedMoment B raw14774step0 raw14774step0Labels = mixedMoment B raw14774step1 raw14774step1Labels := by
      have ha : raw14774step1 = (fun i j => raw14774step0 (permutation151 i) (permutation7 j)) := by apply Matrix.ext; unfold raw14774step1 raw14774step0; decide +kernel
      have hl : raw14774step1Labels = raw14774step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14774step0 raw14774step0Labels permutation151 permutation7
    mixedMoment B raw14774step1 raw14774step1Labels = mixedMoment B raw14774step2 raw14774step2Labels := by
      have ha : raw14774step2 = -raw14774step1 := by apply Matrix.ext; change ∀ i j, raw14774step2 i j = -(raw14774step1 i j); unfold raw14774step2 raw14774step1; decide +kernel
      have hl : raw14774step2Labels = raw14774step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw14774step2 raw14774step2Labels = mixedMoment B raw14774step3 raw14774step3Labels := by
      have ha : raw14774step3 = raw14774step2 := by apply Matrix.ext; unfold raw14774step3 raw14774step2; decide +kernel
      have hl : raw14774step2Labels = labelEmbedding1 ∘ raw14774step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14774step2 raw14774step2Labels raw14774step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3853 node3853Labels := by rfl

theorem canonical14775 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14775 raw14775Labels = mixedMoment B node3573 node3573Labels := by
  calc
    mixedMoment B raw14775 raw14775Labels = mixedMoment B raw14775step0 raw14775step0Labels := by
      have hz : ∀ j, raw14775 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw14775step0 = (fun i j => raw14775 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw14775step0 raw14775; decide +kernel
      have hl : raw14775step0Labels = raw14775Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14775 raw14775Labels permutation346 hz
    mixedMoment B raw14775step0 raw14775step0Labels = mixedMoment B raw14775step1 raw14775step1Labels := by
      have ha : raw14775step1 = (fun i j => raw14775step0 (permutation151 i) (permutation7 j)) := by apply Matrix.ext; unfold raw14775step1 raw14775step0; decide +kernel
      have hl : raw14775step1Labels = raw14775step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14775step0 raw14775step0Labels permutation151 permutation7
    mixedMoment B raw14775step1 raw14775step1Labels = mixedMoment B raw14775step2 raw14775step2Labels := by
      have ha : raw14775step2 = -raw14775step1 := by apply Matrix.ext; change ∀ i j, raw14775step2 i j = -(raw14775step1 i j); unfold raw14775step2 raw14775step1; decide +kernel
      have hl : raw14775step2Labels = raw14775step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw14775step2 raw14775step2Labels = mixedMoment B raw14775step3 raw14775step3Labels := by
      have ha : raw14775step3 = raw14775step2 := by apply Matrix.ext; unfold raw14775step3 raw14775step2; decide +kernel
      have hl : raw14775step2Labels = labelEmbedding1 ∘ raw14775step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14775step2 raw14775step2Labels raw14775step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3573 node3573Labels := by rfl

theorem canonical14784 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14784 raw14784Labels = mixedMoment B node2732 node2732Labels := by
  calc
    mixedMoment B raw14784 raw14784Labels = mixedMoment B raw14784step0 raw14784step0Labels := by
      have hz : ∀ j, raw14784 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw14784step0 = (fun i j => raw14784 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw14784step0 raw14784; decide +kernel
      have hl : raw14784step0Labels = raw14784Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14784 raw14784Labels permutation434 hz
    mixedMoment B raw14784step0 raw14784step0Labels = mixedMoment B raw14784step1 raw14784step1Labels := by
      have ha : raw14784step1 = (fun i j => raw14784step0 (permutation115 i) (permutation5 j)) := by apply Matrix.ext; unfold raw14784step1 raw14784step0; decide +kernel
      have hl : raw14784step1Labels = raw14784step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14784step0 raw14784step0Labels permutation115 permutation5
    mixedMoment B raw14784step1 raw14784step1Labels = mixedMoment B raw14784step2 raw14784step2Labels := by
      have ha : raw14784step2 = raw14784step1 := by apply Matrix.ext; unfold raw14784step2 raw14784step1; decide +kernel
      have hl : raw14784step1Labels = labelEmbedding1 ∘ raw14784step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14784step1 raw14784step1Labels raw14784step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2732 node2732Labels := by rfl

theorem canonical14789 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14789 raw14789Labels = mixedMoment B node4003 node4003Labels := by
  calc
    mixedMoment B raw14789 raw14789Labels = mixedMoment B raw14789step0 raw14789step0Labels := by
      have hz : ∀ j, raw14789 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw14789step0 = (fun i j => raw14789 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw14789step0 raw14789; decide +kernel
      have hl : raw14789step0Labels = raw14789Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14789 raw14789Labels permutation434 hz
    mixedMoment B raw14789step0 raw14789step0Labels = mixedMoment B raw14789step1 raw14789step1Labels := by
      have ha : raw14789step1 = (fun i j => raw14789step0 (permutation125 i) (permutation5 j)) := by apply Matrix.ext; unfold raw14789step1 raw14789step0; decide +kernel
      have hl : raw14789step1Labels = raw14789step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14789step0 raw14789step0Labels permutation125 permutation5
    mixedMoment B raw14789step1 raw14789step1Labels = mixedMoment B raw14789step2 raw14789step2Labels := by
      have ha : raw14789step2 = raw14789step1 := by apply Matrix.ext; unfold raw14789step2 raw14789step1; decide +kernel
      have hl : raw14789step1Labels = labelEmbedding1 ∘ raw14789step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14789step1 raw14789step1Labels raw14789step2Labels labelEmbedding1 hl
    _ = mixedMoment B node4003 node4003Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical117
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical14995 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14995 raw14995Labels = mixedMoment B node3888 node3888Labels := by
  calc
    mixedMoment B raw14995 raw14995Labels = mixedMoment B raw14995step0 raw14995step0Labels := by
      have hz : ∀ j, raw14995 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw14995step0 = (fun i j => raw14995 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw14995step0 raw14995; decide +kernel
      have hl : raw14995step0Labels = raw14995Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14995 raw14995Labels permutation434 hz
    mixedMoment B raw14995step0 raw14995step0Labels = mixedMoment B raw14995step1 raw14995step1Labels := by
      have hz : ∀ j, raw14995step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw14995step1 = (fun i j => raw14995step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw14995step1 raw14995step0; decide +kernel
      have hl : raw14995step1Labels = raw14995step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14995step0 raw14995step0Labels permutation80 hz
    mixedMoment B raw14995step1 raw14995step1Labels = mixedMoment B raw14995step2 raw14995step2Labels := by
      have ha : raw14995step2 = (fun i j => raw14995step1 (permutation31 i) (permutation7 j)) := by apply Matrix.ext; unfold raw14995step2 raw14995step1; decide +kernel
      have hl : raw14995step2Labels = raw14995step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14995step1 raw14995step1Labels permutation31 permutation7
    mixedMoment B raw14995step2 raw14995step2Labels = mixedMoment B raw14995step3 raw14995step3Labels := by
      have ha : raw14995step3 = -raw14995step2 := by apply Matrix.ext; change ∀ i j, raw14995step3 i j = -(raw14995step2 i j); unfold raw14995step3 raw14995step2; decide +kernel
      have hl : raw14995step3Labels = raw14995step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw14995step3 raw14995step3Labels = mixedMoment B raw14995step4 raw14995step4Labels := by
      have ha : raw14995step4 = raw14995step3 := by apply Matrix.ext; unfold raw14995step4 raw14995step3; decide +kernel
      have hl : raw14995step3Labels = labelEmbedding1 ∘ raw14995step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14995step3 raw14995step3Labels raw14995step4Labels labelEmbedding1 hl
    _ = mixedMoment B node3888 node3888Labels := by rfl

theorem canonical14996 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14996 raw14996Labels = mixedMoment B node3876 node3876Labels := by
  calc
    mixedMoment B raw14996 raw14996Labels = mixedMoment B raw14996step0 raw14996step0Labels := by
      have hz : ∀ j, raw14996 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw14996step0 = (fun i j => raw14996 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw14996step0 raw14996; decide +kernel
      have hl : raw14996step0Labels = raw14996Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14996 raw14996Labels permutation346 hz
    mixedMoment B raw14996step0 raw14996step0Labels = mixedMoment B raw14996step1 raw14996step1Labels := by
      have ha : raw14996step1 = (fun i j => raw14996step0 (permutation151 i) (permutation7 j)) := by apply Matrix.ext; unfold raw14996step1 raw14996step0; decide +kernel
      have hl : raw14996step1Labels = raw14996step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14996step0 raw14996step0Labels permutation151 permutation7
    mixedMoment B raw14996step1 raw14996step1Labels = mixedMoment B raw14996step2 raw14996step2Labels := by
      have ha : raw14996step2 = -raw14996step1 := by apply Matrix.ext; change ∀ i j, raw14996step2 i j = -(raw14996step1 i j); unfold raw14996step2 raw14996step1; decide +kernel
      have hl : raw14996step2Labels = raw14996step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw14996step2 raw14996step2Labels = mixedMoment B raw14996step3 raw14996step3Labels := by
      have ha : raw14996step3 = raw14996step2 := by apply Matrix.ext; unfold raw14996step3 raw14996step2; decide +kernel
      have hl : raw14996step2Labels = labelEmbedding1 ∘ raw14996step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14996step2 raw14996step2Labels raw14996step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3876 node3876Labels := by rfl

theorem canonical14997 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14997 raw14997Labels = mixedMoment B node3861 node3861Labels := by
  calc
    mixedMoment B raw14997 raw14997Labels = mixedMoment B raw14997step0 raw14997step0Labels := by
      have hz : ∀ j, raw14997 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw14997step0 = (fun i j => raw14997 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw14997step0 raw14997; decide +kernel
      have hl : raw14997step0Labels = raw14997Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14997 raw14997Labels permutation434 hz
    mixedMoment B raw14997step0 raw14997step0Labels = mixedMoment B raw14997step1 raw14997step1Labels := by
      have hz : ∀ j, raw14997step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw14997step1 = (fun i j => raw14997step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw14997step1 raw14997step0; decide +kernel
      have hl : raw14997step1Labels = raw14997step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14997step0 raw14997step0Labels permutation80 hz
    mixedMoment B raw14997step1 raw14997step1Labels = mixedMoment B raw14997step2 raw14997step2Labels := by
      have ha : raw14997step2 = (fun i j => raw14997step1 (permutation31 i) (permutation7 j)) := by apply Matrix.ext; unfold raw14997step2 raw14997step1; decide +kernel
      have hl : raw14997step2Labels = raw14997step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14997step1 raw14997step1Labels permutation31 permutation7
    mixedMoment B raw14997step2 raw14997step2Labels = mixedMoment B raw14997step3 raw14997step3Labels := by
      have ha : raw14997step3 = -raw14997step2 := by apply Matrix.ext; change ∀ i j, raw14997step3 i j = -(raw14997step2 i j); unfold raw14997step3 raw14997step2; decide +kernel
      have hl : raw14997step3Labels = raw14997step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw14997step3 raw14997step3Labels = mixedMoment B raw14997step4 raw14997step4Labels := by
      have ha : raw14997step4 = raw14997step3 := by apply Matrix.ext; unfold raw14997step4 raw14997step3; decide +kernel
      have hl : raw14997step3Labels = labelEmbedding1 ∘ raw14997step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14997step3 raw14997step3Labels raw14997step4Labels labelEmbedding1 hl
    _ = mixedMoment B node3861 node3861Labels := by rfl

theorem canonical14998 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14998 raw14998Labels = mixedMoment B node3583 node3583Labels := by
  calc
    mixedMoment B raw14998 raw14998Labels = mixedMoment B raw14998step0 raw14998step0Labels := by
      have hz : ∀ j, raw14998 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw14998step0 = (fun i j => raw14998 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw14998step0 raw14998; decide +kernel
      have hl : raw14998step0Labels = raw14998Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14998 raw14998Labels permutation434 hz
    mixedMoment B raw14998step0 raw14998step0Labels = mixedMoment B raw14998step1 raw14998step1Labels := by
      have hz : ∀ j, raw14998step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw14998step1 = (fun i j => raw14998step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw14998step1 raw14998step0; decide +kernel
      have hl : raw14998step1Labels = raw14998step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14998step0 raw14998step0Labels permutation80 hz
    mixedMoment B raw14998step1 raw14998step1Labels = mixedMoment B raw14998step2 raw14998step2Labels := by
      have ha : raw14998step2 = (fun i j => raw14998step1 (permutation31 i) (permutation7 j)) := by apply Matrix.ext; unfold raw14998step2 raw14998step1; decide +kernel
      have hl : raw14998step2Labels = raw14998step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14998step1 raw14998step1Labels permutation31 permutation7
    mixedMoment B raw14998step2 raw14998step2Labels = mixedMoment B raw14998step3 raw14998step3Labels := by
      have ha : raw14998step3 = -raw14998step2 := by apply Matrix.ext; change ∀ i j, raw14998step3 i j = -(raw14998step2 i j); unfold raw14998step3 raw14998step2; decide +kernel
      have hl : raw14998step3Labels = raw14998step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw14998step3 raw14998step3Labels = mixedMoment B raw14998step4 raw14998step4Labels := by
      have ha : raw14998step4 = raw14998step3 := by apply Matrix.ext; unfold raw14998step4 raw14998step3; decide +kernel
      have hl : raw14998step3Labels = labelEmbedding1 ∘ raw14998step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14998step3 raw14998step3Labels raw14998step4Labels labelEmbedding1 hl
    _ = mixedMoment B node3583 node3583Labels := by rfl

theorem canonical14999 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14999 raw14999Labels = mixedMoment B node3055 node3055Labels := by
  calc
    mixedMoment B raw14999 raw14999Labels = mixedMoment B raw14999step0 raw14999step0Labels := by
      have hz : ∀ j, raw14999 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw14999step0 = (fun i j => raw14999 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw14999step0 raw14999; decide +kernel
      have hl : raw14999step0Labels = raw14999Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14999 raw14999Labels permutation434 hz
    mixedMoment B raw14999step0 raw14999step0Labels = mixedMoment B raw14999step1 raw14999step1Labels := by
      have hz : ∀ j, raw14999step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw14999step1 = (fun i j => raw14999step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw14999step1 raw14999step0; decide +kernel
      have hl : raw14999step1Labels = raw14999step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14999step0 raw14999step0Labels permutation80 hz
    mixedMoment B raw14999step1 raw14999step1Labels = mixedMoment B raw14999step2 raw14999step2Labels := by
      have ha : raw14999step2 = (fun i j => raw14999step1 (permutation12 i) (permutation5 j)) := by apply Matrix.ext; unfold raw14999step2 raw14999step1; decide +kernel
      have hl : raw14999step2Labels = raw14999step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14999step1 raw14999step1Labels permutation12 permutation5
    mixedMoment B raw14999step2 raw14999step2Labels = mixedMoment B raw14999step3 raw14999step3Labels := by
      have ha : raw14999step3 = -raw14999step2 := by apply Matrix.ext; change ∀ i j, raw14999step3 i j = -(raw14999step2 i j); unfold raw14999step3 raw14999step2; decide +kernel
      have hl : raw14999step3Labels = raw14999step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw14999step3 raw14999step3Labels = mixedMoment B raw14999step4 raw14999step4Labels := by
      have ha : raw14999step4 = raw14999step3 := by apply Matrix.ext; unfold raw14999step4 raw14999step3; decide +kernel
      have hl : raw14999step3Labels = labelEmbedding1 ∘ raw14999step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14999step3 raw14999step3Labels raw14999step4Labels labelEmbedding1 hl
    _ = mixedMoment B node3055 node3055Labels := by rfl

theorem canonical15000 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15000 raw15000Labels = mixedMoment B node3877 node3877Labels := by
  calc
    mixedMoment B raw15000 raw15000Labels = mixedMoment B raw15000step0 raw15000step0Labels := by
      have hz : ∀ j, raw15000 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15000step0 = (fun i j => raw15000 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15000step0 raw15000; decide +kernel
      have hl : raw15000step0Labels = raw15000Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15000 raw15000Labels permutation346 hz
    mixedMoment B raw15000step0 raw15000step0Labels = mixedMoment B raw15000step1 raw15000step1Labels := by
      have ha : raw15000step1 = (fun i j => raw15000step0 (permutation151 i) (permutation7 j)) := by apply Matrix.ext; unfold raw15000step1 raw15000step0; decide +kernel
      have hl : raw15000step1Labels = raw15000step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15000step0 raw15000step0Labels permutation151 permutation7
    mixedMoment B raw15000step1 raw15000step1Labels = mixedMoment B raw15000step2 raw15000step2Labels := by
      have ha : raw15000step2 = -raw15000step1 := by apply Matrix.ext; change ∀ i j, raw15000step2 i j = -(raw15000step1 i j); unfold raw15000step2 raw15000step1; decide +kernel
      have hl : raw15000step2Labels = raw15000step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15000step2 raw15000step2Labels = mixedMoment B raw15000step3 raw15000step3Labels := by
      have ha : raw15000step3 = raw15000step2 := by apply Matrix.ext; unfold raw15000step3 raw15000step2; decide +kernel
      have hl : raw15000step2Labels = labelEmbedding1 ∘ raw15000step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15000step2 raw15000step2Labels raw15000step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3877 node3877Labels := by rfl

theorem canonical15001 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15001 raw15001Labels = mixedMoment B node3862 node3862Labels := by
  calc
    mixedMoment B raw15001 raw15001Labels = mixedMoment B raw15001step0 raw15001step0Labels := by
      have hz : ∀ j, raw15001 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw15001step0 = (fun i j => raw15001 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw15001step0 raw15001; decide +kernel
      have hl : raw15001step0Labels = raw15001Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15001 raw15001Labels permutation434 hz
    mixedMoment B raw15001step0 raw15001step0Labels = mixedMoment B raw15001step1 raw15001step1Labels := by
      have hz : ∀ j, raw15001step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw15001step1 = (fun i j => raw15001step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw15001step1 raw15001step0; decide +kernel
      have hl : raw15001step1Labels = raw15001step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15001step0 raw15001step0Labels permutation80 hz
    mixedMoment B raw15001step1 raw15001step1Labels = mixedMoment B raw15001step2 raw15001step2Labels := by
      have ha : raw15001step2 = (fun i j => raw15001step1 (permutation31 i) (permutation7 j)) := by apply Matrix.ext; unfold raw15001step2 raw15001step1; decide +kernel
      have hl : raw15001step2Labels = raw15001step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15001step1 raw15001step1Labels permutation31 permutation7
    mixedMoment B raw15001step2 raw15001step2Labels = mixedMoment B raw15001step3 raw15001step3Labels := by
      have ha : raw15001step3 = -raw15001step2 := by apply Matrix.ext; change ∀ i j, raw15001step3 i j = -(raw15001step2 i j); unfold raw15001step3 raw15001step2; decide +kernel
      have hl : raw15001step3Labels = raw15001step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15001step3 raw15001step3Labels = mixedMoment B raw15001step4 raw15001step4Labels := by
      have ha : raw15001step4 = raw15001step3 := by apply Matrix.ext; unfold raw15001step4 raw15001step3; decide +kernel
      have hl : raw15001step3Labels = labelEmbedding1 ∘ raw15001step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15001step3 raw15001step3Labels raw15001step4Labels labelEmbedding1 hl
    _ = mixedMoment B node3862 node3862Labels := by rfl

theorem canonical15002 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15002 raw15002Labels = mixedMoment B node3584 node3584Labels := by
  calc
    mixedMoment B raw15002 raw15002Labels = mixedMoment B raw15002step0 raw15002step0Labels := by
      have hz : ∀ j, raw15002 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw15002step0 = (fun i j => raw15002 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw15002step0 raw15002; decide +kernel
      have hl : raw15002step0Labels = raw15002Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15002 raw15002Labels permutation434 hz
    mixedMoment B raw15002step0 raw15002step0Labels = mixedMoment B raw15002step1 raw15002step1Labels := by
      have hz : ∀ j, raw15002step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw15002step1 = (fun i j => raw15002step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw15002step1 raw15002step0; decide +kernel
      have hl : raw15002step1Labels = raw15002step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15002step0 raw15002step0Labels permutation80 hz
    mixedMoment B raw15002step1 raw15002step1Labels = mixedMoment B raw15002step2 raw15002step2Labels := by
      have ha : raw15002step2 = (fun i j => raw15002step1 (permutation31 i) (permutation7 j)) := by apply Matrix.ext; unfold raw15002step2 raw15002step1; decide +kernel
      have hl : raw15002step2Labels = raw15002step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15002step1 raw15002step1Labels permutation31 permutation7
    mixedMoment B raw15002step2 raw15002step2Labels = mixedMoment B raw15002step3 raw15002step3Labels := by
      have ha : raw15002step3 = -raw15002step2 := by apply Matrix.ext; change ∀ i j, raw15002step3 i j = -(raw15002step2 i j); unfold raw15002step3 raw15002step2; decide +kernel
      have hl : raw15002step3Labels = raw15002step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15002step3 raw15002step3Labels = mixedMoment B raw15002step4 raw15002step4Labels := by
      have ha : raw15002step4 = raw15002step3 := by apply Matrix.ext; unfold raw15002step4 raw15002step3; decide +kernel
      have hl : raw15002step3Labels = labelEmbedding1 ∘ raw15002step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15002step3 raw15002step3Labels raw15002step4Labels labelEmbedding1 hl
    _ = mixedMoment B node3584 node3584Labels := by rfl

theorem canonical15003 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15003 raw15003Labels = mixedMoment B node3039 node3039Labels := by
  calc
    mixedMoment B raw15003 raw15003Labels = mixedMoment B raw15003step0 raw15003step0Labels := by
      have hz : ∀ j, raw15003 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw15003step0 = (fun i j => raw15003 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw15003step0 raw15003; decide +kernel
      have hl : raw15003step0Labels = raw15003Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15003 raw15003Labels permutation434 hz
    mixedMoment B raw15003step0 raw15003step0Labels = mixedMoment B raw15003step1 raw15003step1Labels := by
      have ha : raw15003step1 = (fun i j => raw15003step0 (permutation50 i) (permutation5 j)) := by apply Matrix.ext; unfold raw15003step1 raw15003step0; decide +kernel
      have hl : raw15003step1Labels = raw15003step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15003step0 raw15003step0Labels permutation50 permutation5
    mixedMoment B raw15003step1 raw15003step1Labels = mixedMoment B raw15003step2 raw15003step2Labels := by
      have ha : raw15003step2 = -raw15003step1 := by apply Matrix.ext; change ∀ i j, raw15003step2 i j = -(raw15003step1 i j); unfold raw15003step2 raw15003step1; decide +kernel
      have hl : raw15003step2Labels = raw15003step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15003step2 raw15003step2Labels = mixedMoment B raw15003step3 raw15003step3Labels := by
      have ha : raw15003step3 = raw15003step2 := by apply Matrix.ext; unfold raw15003step3 raw15003step2; decide +kernel
      have hl : raw15003step2Labels = labelEmbedding1 ∘ raw15003step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15003step2 raw15003step2Labels raw15003step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3039 node3039Labels := by rfl

theorem canonical15004 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15004 raw15004Labels = mixedMoment B node3883 node3883Labels := by
  calc
    mixedMoment B raw15004 raw15004Labels = mixedMoment B raw15004step0 raw15004step0Labels := by
      have hz : ∀ j, raw15004 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw15004step0 = (fun i j => raw15004 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw15004step0 raw15004; decide +kernel
      have hl : raw15004step0Labels = raw15004Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15004 raw15004Labels permutation434 hz
    mixedMoment B raw15004step0 raw15004step0Labels = mixedMoment B raw15004step1 raw15004step1Labels := by
      have ha : raw15004step1 = (fun i j => raw15004step0 (permutation151 i) (permutation7 j)) := by apply Matrix.ext; unfold raw15004step1 raw15004step0; decide +kernel
      have hl : raw15004step1Labels = raw15004step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15004step0 raw15004step0Labels permutation151 permutation7
    mixedMoment B raw15004step1 raw15004step1Labels = mixedMoment B raw15004step2 raw15004step2Labels := by
      have ha : raw15004step2 = -raw15004step1 := by apply Matrix.ext; change ∀ i j, raw15004step2 i j = -(raw15004step1 i j); unfold raw15004step2 raw15004step1; decide +kernel
      have hl : raw15004step2Labels = raw15004step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15004step2 raw15004step2Labels = mixedMoment B raw15004step3 raw15004step3Labels := by
      have ha : raw15004step3 = raw15004step2 := by apply Matrix.ext; unfold raw15004step3 raw15004step2; decide +kernel
      have hl : raw15004step2Labels = labelEmbedding1 ∘ raw15004step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15004step2 raw15004step2Labels raw15004step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3883 node3883Labels := by rfl

theorem canonical15005 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15005 raw15005Labels = mixedMoment B node3872 node3872Labels := by
  calc
    mixedMoment B raw15005 raw15005Labels = mixedMoment B raw15005step0 raw15005step0Labels := by
      have ha : raw15005step0 = (fun i j => raw15005 (permutation688 i) (permutation7 j)) := by apply Matrix.ext; unfold raw15005step0 raw15005; decide +kernel
      have hl : raw15005step0Labels = raw15005Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15005 raw15005Labels permutation688 permutation7
    mixedMoment B raw15005step0 raw15005step0Labels = mixedMoment B raw15005step1 raw15005step1Labels := by
      have ha : raw15005step1 = -raw15005step0 := by apply Matrix.ext; change ∀ i j, raw15005step1 i j = -(raw15005step0 i j); unfold raw15005step1 raw15005step0; decide +kernel
      have hl : raw15005step1Labels = raw15005step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15005step1 raw15005step1Labels = mixedMoment B raw15005step2 raw15005step2Labels := by
      have ha : raw15005step2 = raw15005step1 := by apply Matrix.ext; unfold raw15005step2 raw15005step1; decide +kernel
      have hl : raw15005step1Labels = labelEmbedding1 ∘ raw15005step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15005step1 raw15005step1Labels raw15005step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3872 node3872Labels := by rfl

theorem canonical15006 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15006 raw15006Labels = mixedMoment B node3853 node3853Labels := by
  calc
    mixedMoment B raw15006 raw15006Labels = mixedMoment B raw15006step0 raw15006step0Labels := by
      have hz : ∀ j, raw15006 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw15006step0 = (fun i j => raw15006 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw15006step0 raw15006; decide +kernel
      have hl : raw15006step0Labels = raw15006Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15006 raw15006Labels permutation434 hz
    mixedMoment B raw15006step0 raw15006step0Labels = mixedMoment B raw15006step1 raw15006step1Labels := by
      have ha : raw15006step1 = (fun i j => raw15006step0 (permutation151 i) (permutation7 j)) := by apply Matrix.ext; unfold raw15006step1 raw15006step0; decide +kernel
      have hl : raw15006step1Labels = raw15006step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15006step0 raw15006step0Labels permutation151 permutation7
    mixedMoment B raw15006step1 raw15006step1Labels = mixedMoment B raw15006step2 raw15006step2Labels := by
      have ha : raw15006step2 = -raw15006step1 := by apply Matrix.ext; change ∀ i j, raw15006step2 i j = -(raw15006step1 i j); unfold raw15006step2 raw15006step1; decide +kernel
      have hl : raw15006step2Labels = raw15006step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15006step2 raw15006step2Labels = mixedMoment B raw15006step3 raw15006step3Labels := by
      have ha : raw15006step3 = raw15006step2 := by apply Matrix.ext; unfold raw15006step3 raw15006step2; decide +kernel
      have hl : raw15006step2Labels = labelEmbedding1 ∘ raw15006step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15006step2 raw15006step2Labels raw15006step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3853 node3853Labels := by rfl

theorem canonical15007 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15007 raw15007Labels = mixedMoment B node3573 node3573Labels := by
  calc
    mixedMoment B raw15007 raw15007Labels = mixedMoment B raw15007step0 raw15007step0Labels := by
      have hz : ∀ j, raw15007 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw15007step0 = (fun i j => raw15007 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw15007step0 raw15007; decide +kernel
      have hl : raw15007step0Labels = raw15007Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15007 raw15007Labels permutation434 hz
    mixedMoment B raw15007step0 raw15007step0Labels = mixedMoment B raw15007step1 raw15007step1Labels := by
      have ha : raw15007step1 = (fun i j => raw15007step0 (permutation151 i) (permutation7 j)) := by apply Matrix.ext; unfold raw15007step1 raw15007step0; decide +kernel
      have hl : raw15007step1Labels = raw15007step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15007step0 raw15007step0Labels permutation151 permutation7
    mixedMoment B raw15007step1 raw15007step1Labels = mixedMoment B raw15007step2 raw15007step2Labels := by
      have ha : raw15007step2 = -raw15007step1 := by apply Matrix.ext; change ∀ i j, raw15007step2 i j = -(raw15007step1 i j); unfold raw15007step2 raw15007step1; decide +kernel
      have hl : raw15007step2Labels = raw15007step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15007step2 raw15007step2Labels = mixedMoment B raw15007step3 raw15007step3Labels := by
      have ha : raw15007step3 = raw15007step2 := by apply Matrix.ext; unfold raw15007step3 raw15007step2; decide +kernel
      have hl : raw15007step2Labels = labelEmbedding1 ∘ raw15007step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15007step2 raw15007step2Labels raw15007step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3573 node3573Labels := by rfl

theorem canonical15008 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15008 raw15008Labels = mixedMoment B node3872 node3872Labels := by
  calc
    mixedMoment B raw15008 raw15008Labels = mixedMoment B raw15008step0 raw15008step0Labels := by
      have ha : raw15008step0 = (fun i j => raw15008 (permutation682 i) (permutation7 j)) := by apply Matrix.ext; unfold raw15008step0 raw15008; decide +kernel
      have hl : raw15008step0Labels = raw15008Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15008 raw15008Labels permutation682 permutation7
    mixedMoment B raw15008step0 raw15008step0Labels = mixedMoment B raw15008step1 raw15008step1Labels := by
      have ha : raw15008step1 = -raw15008step0 := by apply Matrix.ext; change ∀ i j, raw15008step1 i j = -(raw15008step0 i j); unfold raw15008step1 raw15008step0; decide +kernel
      have hl : raw15008step1Labels = raw15008step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15008step1 raw15008step1Labels = mixedMoment B raw15008step2 raw15008step2Labels := by
      have ha : raw15008step2 = raw15008step1 := by apply Matrix.ext; unfold raw15008step2 raw15008step1; decide +kernel
      have hl : raw15008step1Labels = labelEmbedding1 ∘ raw15008step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15008step1 raw15008step1Labels raw15008step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3872 node3872Labels := by rfl

theorem canonical15009 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15009 raw15009Labels = mixedMoment B node2734 node2734Labels := by
  calc
    mixedMoment B raw15009 raw15009Labels = mixedMoment B raw15009step0 raw15009step0Labels := by
      have hz : ∀ j, raw15009 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw15009step0 = (fun i j => raw15009 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw15009step0 raw15009; decide +kernel
      have hl : raw15009step0Labels = raw15009Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15009 raw15009Labels permutation434 hz
    mixedMoment B raw15009step0 raw15009step0Labels = mixedMoment B raw15009step1 raw15009step1Labels := by
      have hz : ∀ j, raw15009step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw15009step1 = (fun i j => raw15009step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw15009step1 raw15009step0; decide +kernel
      have hl : raw15009step1Labels = raw15009step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15009step0 raw15009step0Labels permutation80 hz
    mixedMoment B raw15009step1 raw15009step1Labels = mixedMoment B raw15009step2 raw15009step2Labels := by
      have ha : raw15009step2 = (fun i j => raw15009step1 (permutation23 i) (permutation5 j)) := by apply Matrix.ext; unfold raw15009step2 raw15009step1; decide +kernel
      have hl : raw15009step2Labels = raw15009step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15009step1 raw15009step1Labels permutation23 permutation5
    mixedMoment B raw15009step2 raw15009step2Labels = mixedMoment B raw15009step3 raw15009step3Labels := by
      have ha : raw15009step3 = raw15009step2 := by apply Matrix.ext; unfold raw15009step3 raw15009step2; decide +kernel
      have hl : raw15009step2Labels = labelEmbedding1 ∘ raw15009step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15009step2 raw15009step2Labels raw15009step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2734 node2734Labels := by rfl

theorem canonical15010 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15010 raw15010Labels = mixedMoment B node2776 node2776Labels := by
  calc
    mixedMoment B raw15010 raw15010Labels = mixedMoment B raw15010step0 raw15010step0Labels := by
      have hz : ∀ j, raw15010 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw15010step0 = (fun i j => raw15010 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw15010step0 raw15010; decide +kernel
      have hl : raw15010step0Labels = raw15010Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15010 raw15010Labels permutation434 hz
    mixedMoment B raw15010step0 raw15010step0Labels = mixedMoment B raw15010step1 raw15010step1Labels := by
      have hz : ∀ j, raw15010step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw15010step1 = (fun i j => raw15010step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw15010step1 raw15010step0; decide +kernel
      have hl : raw15010step1Labels = raw15010step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15010step0 raw15010step0Labels permutation80 hz
    mixedMoment B raw15010step1 raw15010step1Labels = mixedMoment B raw15010step2 raw15010step2Labels := by
      have ha : raw15010step2 = (fun i j => raw15010step1 (permutation25 i) (permutation5 j)) := by apply Matrix.ext; unfold raw15010step2 raw15010step1; decide +kernel
      have hl : raw15010step2Labels = raw15010step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15010step1 raw15010step1Labels permutation25 permutation5
    mixedMoment B raw15010step2 raw15010step2Labels = mixedMoment B raw15010step3 raw15010step3Labels := by
      have ha : raw15010step3 = raw15010step2 := by apply Matrix.ext; unfold raw15010step3 raw15010step2; decide +kernel
      have hl : raw15010step2Labels = labelEmbedding1 ∘ raw15010step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15010step2 raw15010step2Labels raw15010step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2776 node2776Labels := by rfl

theorem canonical15011 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15011 raw15011Labels = mixedMoment B node2732 node2732Labels := by
  calc
    mixedMoment B raw15011 raw15011Labels = mixedMoment B raw15011step0 raw15011step0Labels := by
      have hz : ∀ j, raw15011 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15011step0 = (fun i j => raw15011 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15011step0 raw15011; decide +kernel
      have hl : raw15011step0Labels = raw15011Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15011 raw15011Labels permutation346 hz
    mixedMoment B raw15011step0 raw15011step0Labels = mixedMoment B raw15011step1 raw15011step1Labels := by
      have ha : raw15011step1 = (fun i j => raw15011step0 (permutation115 i) (permutation5 j)) := by apply Matrix.ext; unfold raw15011step1 raw15011step0; decide +kernel
      have hl : raw15011step1Labels = raw15011step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15011step0 raw15011step0Labels permutation115 permutation5
    mixedMoment B raw15011step1 raw15011step1Labels = mixedMoment B raw15011step2 raw15011step2Labels := by
      have ha : raw15011step2 = raw15011step1 := by apply Matrix.ext; unfold raw15011step2 raw15011step1; decide +kernel
      have hl : raw15011step1Labels = labelEmbedding1 ∘ raw15011step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15011step1 raw15011step1Labels raw15011step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2732 node2732Labels := by rfl

theorem canonical15012 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15012 raw15012Labels = mixedMoment B node2744 node2744Labels := by
  calc
    mixedMoment B raw15012 raw15012Labels = mixedMoment B raw15012step0 raw15012step0Labels := by
      have hz : ∀ j, raw15012 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw15012step0 = (fun i j => raw15012 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw15012step0 raw15012; decide +kernel
      have hl : raw15012step0Labels = raw15012Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15012 raw15012Labels permutation434 hz
    mixedMoment B raw15012step0 raw15012step0Labels = mixedMoment B raw15012step1 raw15012step1Labels := by
      have hz : ∀ j, raw15012step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw15012step1 = (fun i j => raw15012step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw15012step1 raw15012step0; decide +kernel
      have hl : raw15012step1Labels = raw15012step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15012step0 raw15012step0Labels permutation80 hz
    mixedMoment B raw15012step1 raw15012step1Labels = mixedMoment B raw15012step2 raw15012step2Labels := by
      have ha : raw15012step2 = (fun i j => raw15012step1 (permutation23 i) (permutation5 j)) := by apply Matrix.ext; unfold raw15012step2 raw15012step1; decide +kernel
      have hl : raw15012step2Labels = raw15012step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15012step1 raw15012step1Labels permutation23 permutation5
    mixedMoment B raw15012step2 raw15012step2Labels = mixedMoment B raw15012step3 raw15012step3Labels := by
      have ha : raw15012step3 = raw15012step2 := by apply Matrix.ext; unfold raw15012step3 raw15012step2; decide +kernel
      have hl : raw15012step2Labels = labelEmbedding1 ∘ raw15012step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15012step2 raw15012step2Labels raw15012step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2744 node2744Labels := by rfl

theorem canonical15013 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15013 raw15013Labels = mixedMoment B node3110 node3110Labels := by
  calc
    mixedMoment B raw15013 raw15013Labels = mixedMoment B raw15013step0 raw15013step0Labels := by
      have hz : ∀ j, raw15013 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw15013step0 = (fun i j => raw15013 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw15013step0 raw15013; decide +kernel
      have hl : raw15013step0Labels = raw15013Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15013 raw15013Labels permutation434 hz
    mixedMoment B raw15013step0 raw15013step0Labels = mixedMoment B raw15013step1 raw15013step1Labels := by
      have hz : ∀ j, raw15013step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw15013step1 = (fun i j => raw15013step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw15013step1 raw15013step0; decide +kernel
      have hl : raw15013step1Labels = raw15013step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15013step0 raw15013step0Labels permutation80 hz
    mixedMoment B raw15013step1 raw15013step1Labels = mixedMoment B raw15013step2 raw15013step2Labels := by
      have ha : raw15013step2 = (fun i j => raw15013step1 (permutation9 i) (permutation5 j)) := by apply Matrix.ext; unfold raw15013step2 raw15013step1; decide +kernel
      have hl : raw15013step2Labels = raw15013step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15013step1 raw15013step1Labels permutation9 permutation5
    mixedMoment B raw15013step2 raw15013step2Labels = mixedMoment B raw15013step3 raw15013step3Labels := by
      have ha : raw15013step3 = -raw15013step2 := by apply Matrix.ext; change ∀ i j, raw15013step3 i j = -(raw15013step2 i j); unfold raw15013step3 raw15013step2; decide +kernel
      have hl : raw15013step3Labels = raw15013step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15013step3 raw15013step3Labels = mixedMoment B raw15013step4 raw15013step4Labels := by
      have ha : raw15013step4 = raw15013step3 := by apply Matrix.ext; unfold raw15013step4 raw15013step3; decide +kernel
      have hl : raw15013step3Labels = labelEmbedding1 ∘ raw15013step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15013step3 raw15013step3Labels raw15013step4Labels labelEmbedding1 hl
    _ = mixedMoment B node3110 node3110Labels := by rfl

theorem canonical15014 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15014 raw15014Labels = mixedMoment B node4006 node4006Labels := by
  calc
    mixedMoment B raw15014 raw15014Labels = mixedMoment B raw15014step0 raw15014step0Labels := by
      have hz : ∀ j, raw15014 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw15014step0 = (fun i j => raw15014 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw15014step0 raw15014; decide +kernel
      have hl : raw15014step0Labels = raw15014Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15014 raw15014Labels permutation434 hz
    mixedMoment B raw15014step0 raw15014step0Labels = mixedMoment B raw15014step1 raw15014step1Labels := by
      have hz : ∀ j, raw15014step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw15014step1 = (fun i j => raw15014step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw15014step1 raw15014step0; decide +kernel
      have hl : raw15014step1Labels = raw15014step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15014step0 raw15014step0Labels permutation80 hz
    mixedMoment B raw15014step1 raw15014step1Labels = mixedMoment B raw15014step2 raw15014step2Labels := by
      have ha : raw15014step2 = (fun i j => raw15014step1 (permutation25 i) (permutation5 j)) := by apply Matrix.ext; unfold raw15014step2 raw15014step1; decide +kernel
      have hl : raw15014step2Labels = raw15014step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15014step1 raw15014step1Labels permutation25 permutation5
    mixedMoment B raw15014step2 raw15014step2Labels = mixedMoment B raw15014step3 raw15014step3Labels := by
      have ha : raw15014step3 = raw15014step2 := by apply Matrix.ext; unfold raw15014step3 raw15014step2; decide +kernel
      have hl : raw15014step2Labels = labelEmbedding1 ∘ raw15014step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15014step2 raw15014step2Labels raw15014step3Labels labelEmbedding1 hl
    _ = mixedMoment B node4006 node4006Labels := by rfl

theorem canonical15015 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15015 raw15015Labels = mixedMoment B node4003 node4003Labels := by
  calc
    mixedMoment B raw15015 raw15015Labels = mixedMoment B raw15015step0 raw15015step0Labels := by
      have hz : ∀ j, raw15015 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15015step0 = (fun i j => raw15015 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15015step0 raw15015; decide +kernel
      have hl : raw15015step0Labels = raw15015Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15015 raw15015Labels permutation346 hz
    mixedMoment B raw15015step0 raw15015step0Labels = mixedMoment B raw15015step1 raw15015step1Labels := by
      have ha : raw15015step1 = (fun i j => raw15015step0 (permutation125 i) (permutation5 j)) := by apply Matrix.ext; unfold raw15015step1 raw15015step0; decide +kernel
      have hl : raw15015step1Labels = raw15015step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15015step0 raw15015step0Labels permutation125 permutation5
    mixedMoment B raw15015step1 raw15015step1Labels = mixedMoment B raw15015step2 raw15015step2Labels := by
      have ha : raw15015step2 = raw15015step1 := by apply Matrix.ext; unfold raw15015step2 raw15015step1; decide +kernel
      have hl : raw15015step1Labels = labelEmbedding1 ∘ raw15015step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15015step1 raw15015step1Labels raw15015step2Labels labelEmbedding1 hl
    _ = mixedMoment B node4003 node4003Labels := by rfl

theorem canonical15016 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15016 raw15016Labels = mixedMoment B node4001 node4001Labels := by
  calc
    mixedMoment B raw15016 raw15016Labels = mixedMoment B raw15016step0 raw15016step0Labels := by
      have hz : ∀ j, raw15016 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw15016step0 = (fun i j => raw15016 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw15016step0 raw15016; decide +kernel
      have hl : raw15016step0Labels = raw15016Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15016 raw15016Labels permutation434 hz
    mixedMoment B raw15016step0 raw15016step0Labels = mixedMoment B raw15016step1 raw15016step1Labels := by
      have hz : ∀ j, raw15016step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw15016step1 = (fun i j => raw15016step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw15016step1 raw15016step0; decide +kernel
      have hl : raw15016step1Labels = raw15016step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15016step0 raw15016step0Labels permutation80 hz
    mixedMoment B raw15016step1 raw15016step1Labels = mixedMoment B raw15016step2 raw15016step2Labels := by
      have ha : raw15016step2 = (fun i j => raw15016step1 (permutation31 i) (permutation7 j)) := by apply Matrix.ext; unfold raw15016step2 raw15016step1; decide +kernel
      have hl : raw15016step2Labels = raw15016step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15016step1 raw15016step1Labels permutation31 permutation7
    mixedMoment B raw15016step2 raw15016step2Labels = mixedMoment B raw15016step3 raw15016step3Labels := by
      have ha : raw15016step3 = -raw15016step2 := by apply Matrix.ext; change ∀ i j, raw15016step3 i j = -(raw15016step2 i j); unfold raw15016step3 raw15016step2; decide +kernel
      have hl : raw15016step3Labels = raw15016step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15016step3 raw15016step3Labels = mixedMoment B raw15016step4 raw15016step4Labels := by
      have ha : raw15016step4 = raw15016step3 := by apply Matrix.ext; unfold raw15016step4 raw15016step3; decide +kernel
      have hl : raw15016step3Labels = labelEmbedding1 ∘ raw15016step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15016step3 raw15016step3Labels raw15016step4Labels labelEmbedding1 hl
    _ = mixedMoment B node4001 node4001Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical278 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw278 raw278Labels = mixedMoment B node2776 node2776Labels := by
  calc
    mixedMoment B raw278 raw278Labels = mixedMoment B raw278step0 raw278step0Labels := by
      have ha : raw278step0 = (fun i j => raw278 (permutation8 i) (permutation5 j)) := by apply Matrix.ext; unfold raw278step0 raw278; decide +kernel
      have hl : raw278step0Labels = raw278Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw278 raw278Labels permutation8 permutation5
    mixedMoment B raw278step0 raw278step0Labels = mixedMoment B raw278step1 raw278step1Labels := by
      have ha : raw278step1 = raw278step0 := by apply Matrix.ext; unfold raw278step1 raw278step0; decide +kernel
      have hl : raw278step0Labels = labelEmbedding1 ∘ raw278step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw278step0 raw278step0Labels raw278step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2776 node2776Labels := by rfl

theorem canonical279 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw279 raw279Labels = mixedMoment B node412 node412Labels := by
  calc
    mixedMoment B raw279 raw279Labels = mixedMoment B raw279step0 raw279step0Labels := by
      have ha : raw279step0 = (fun i j => raw279 (permutation8 i) (permutation5 j)) := by apply Matrix.ext; unfold raw279step0 raw279; decide +kernel
      have hl : raw279step0Labels = raw279Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw279 raw279Labels permutation8 permutation5
    _ = mixedMoment B node412 node412Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical3
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical392 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw392 raw392Labels = mixedMoment B node3110 node3110Labels := by
  calc
    mixedMoment B raw392 raw392Labels = mixedMoment B raw392step0 raw392step0Labels := by
      have ha : raw392step0 = (fun i j => raw392 (permutation8 i) (permutation5 j)) := by apply Matrix.ext; unfold raw392step0 raw392; decide +kernel
      have hl : raw392step0Labels = raw392Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw392 raw392Labels permutation8 permutation5
    mixedMoment B raw392step0 raw392step0Labels = mixedMoment B raw392step1 raw392step1Labels := by
      have ha : raw392step1 = raw392step0 := by apply Matrix.ext; unfold raw392step1 raw392step0; decide +kernel
      have hl : raw392step0Labels = labelEmbedding1 ∘ raw392step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw392step0 raw392step0Labels raw392step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3110 node3110Labels := by rfl

theorem canonical393 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw393 raw393Labels = mixedMoment B node390 node390Labels := by
  calc
    mixedMoment B raw393 raw393Labels = mixedMoment B raw393step0 raw393step0Labels := by
      have ha : raw393step0 = (fun i j => raw393 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw393step0 raw393; decide +kernel
      have hl : raw393step0Labels = raw393Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw393 raw393Labels permutation8 permutation4
    _ = mixedMoment B node390 node390Labels := by rfl

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

theorem canonical536 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw536 raw536Labels = mixedMoment B node3862 node3862Labels := by
  calc
    mixedMoment B raw536 raw536Labels = mixedMoment B raw536step0 raw536step0Labels := by
      have ha : raw536step0 = (fun i j => raw536 (permutation8 i) (permutation5 j)) := by apply Matrix.ext; unfold raw536step0 raw536; decide +kernel
      have hl : raw536step0Labels = raw536Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw536 raw536Labels permutation8 permutation5
    mixedMoment B raw536step0 raw536step0Labels = mixedMoment B raw536step1 raw536step1Labels := by
      have ha : raw536step1 = raw536step0 := by apply Matrix.ext; unfold raw536step1 raw536step0; decide +kernel
      have hl : raw536step0Labels = labelEmbedding1 ∘ raw536step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw536step0 raw536step0Labels raw536step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3862 node3862Labels := by rfl

theorem canonical537 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw537 raw537Labels = mixedMoment B node496 node496Labels := by
  calc
    mixedMoment B raw537 raw537Labels = mixedMoment B raw537step0 raw537step0Labels := by
      have ha : raw537step0 = (fun i j => raw537 (permutation8 i) (permutation5 j)) := by apply Matrix.ext; unfold raw537step0 raw537; decide +kernel
      have hl : raw537step0Labels = raw537Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw537 raw537Labels permutation8 permutation5
    _ = mixedMoment B node496 node496Labels := by rfl

theorem canonical540 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw540 raw540Labels = mixedMoment B node3883 node3883Labels := by
  calc
    mixedMoment B raw540 raw540Labels = mixedMoment B raw540step0 raw540step0Labels := by
      have ha : raw540step0 = (fun i j => raw540 (permutation32 i) (permutation5 j)) := by apply Matrix.ext; unfold raw540step0 raw540; decide +kernel
      have hl : raw540step0Labels = raw540Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw540 raw540Labels permutation32 permutation5
    mixedMoment B raw540step0 raw540step0Labels = mixedMoment B raw540step1 raw540step1Labels := by
      have ha : raw540step1 = raw540step0 := by apply Matrix.ext; unfold raw540step1 raw540step0; decide +kernel
      have hl : raw540step0Labels = labelEmbedding1 ∘ raw540step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw540step0 raw540step0Labels raw540step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3883 node3883Labels := by rfl

theorem canonical541 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw541 raw541Labels = mixedMoment B node467 node467Labels := by
  calc
    mixedMoment B raw541 raw541Labels = mixedMoment B raw541step0 raw541step0Labels := by
      have ha : raw541step0 = (fun i j => raw541 (permutation151 i) (permutation4 j)) := by apply Matrix.ext; unfold raw541step0 raw541; decide +kernel
      have hl : raw541step0Labels = raw541Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw541 raw541Labels permutation151 permutation4
    mixedMoment B raw541step0 raw541step0Labels = mixedMoment B raw541step1 raw541step1Labels := by
      have ha : raw541step1 = -raw541step0 := by apply Matrix.ext; change ∀ i j, raw541step1 i j = -(raw541step0 i j); unfold raw541step1 raw541step0; decide +kernel
      have hl : raw541step1Labels = raw541step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node467 node467Labels := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical160
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical5128 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5128 = injectiveMoment H node46 := by
  calc
    injectiveMoment H raw5128 = injectiveMoment H raw5128step0 := by
      have hz : ∀ j, raw5128 (permutation80 0) j = 0 := by decide +kernel
      have heq : raw5128step0 = (fun i j => raw5128 (permutation80 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw5128 permutation80 hz
    _ = injectiveMoment H node46 := by rfl

theorem canonical5141 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5141 = injectiveMoment H node46 := by
  rfl

theorem canonical5142 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5142 = injectiveMoment H node46 := by
  calc
    injectiveMoment H raw5142 = injectiveMoment H raw5142step0 := by
      have hz : ∀ j, raw5142 (permutation128 0) j = 0 := by decide +kernel
      have heq : raw5142step0 = (fun i j => raw5142 (permutation128 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw5142 permutation128 hz
    _ = injectiveMoment H node46 := by rfl

theorem canonical5149 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5149 = injectiveMoment H node46 := by
  calc
    injectiveMoment H raw5149 = injectiveMoment H raw5149step0 := by
      have heq : raw5149step0 = (fun i j => raw5149 (permutation10 i) (permutation1 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5149 permutation10 permutation1
    _ = injectiveMoment H node46 := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical23
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical750 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw750 = injectiveMoment H node261 := by
  calc
    injectiveMoment H raw750 = injectiveMoment H raw750step0 := by
      have heq : raw750step0 = -raw750 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw750).symm
    injectiveMoment H raw750step0 = injectiveMoment H raw750step1 := by
      have heq : raw750step1 = (fun i j => raw750step0 (permutation11 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw750step0 permutation11 permutation6
    _ = injectiveMoment H node261 := by rfl

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

theorem canonical7731 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7731 = injectiveMoment H node65 := by
  calc
    injectiveMoment H raw7731 = injectiveMoment H raw7731step0 := by
      have heq : raw7731step0 = (fun i j => raw7731 (permutation11 i) (permutation1 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7731 permutation11 permutation1
    _ = injectiveMoment H node65 := by rfl

theorem canonical7735 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7735 = injectiveMoment H node5 := by
  calc
    injectiveMoment H raw7735 = injectiveMoment H raw7735step0 := by
      have hz : ∀ j, raw7735 (permutation7 0) j = 0 := by decide +kernel
      have heq : raw7735step0 = (fun i j => raw7735 (permutation7 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7735 permutation7 hz
    _ = injectiveMoment H node5 := by rfl

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

theorem canonical7977 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7977 = injectiveMoment H node10 := by
  calc
    injectiveMoment H raw7977 = injectiveMoment H raw7977step0 := by
      have heq : raw7977step0 = raw7977.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7977).symm
    injectiveMoment H raw7977step0 = injectiveMoment H raw7977step1 := by
      have heq : raw7977step1 = (fun i j => raw7977step0 (permutation5 i) (permutation2 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7977step0 permutation5 permutation2
    _ = injectiveMoment H node10 := by rfl

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

theorem canonical7981 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7981 = injectiveMoment H node0 := by
  calc
    injectiveMoment H raw7981 = injectiveMoment H raw7981step0 := by
      have hz : ∀ j, raw7981 (permutation128 0) j = 0 := by decide +kernel
      have heq : raw7981step0 = (fun i j => raw7981 (permutation128 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7981 permutation128 hz
    injectiveMoment H raw7981step0 = injectiveMoment H raw7981step1 := by
      have hz : ∀ j, raw7981step0 (permutation27 0) j = 0 := by decide +kernel
      have heq : raw7981step1 = (fun i j => raw7981step0 (permutation27 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7981step0 permutation27 hz
    injectiveMoment H raw7981step1 = injectiveMoment H raw7981step2 := by
      have hz : ∀ j, raw7981step1 (permutation7 0) j = 0 := by decide +kernel
      have heq : raw7981step2 = (fun i j => raw7981step1 (permutation7 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7981step1 permutation7 hz
    injectiveMoment H raw7981step2 = injectiveMoment H raw7981step3 := by
      have hz : ∀ j, raw7981step2 (permutation2 0) j = 0 := by decide +kernel
      have heq : raw7981step3 = (fun i j => raw7981step2 (permutation2 i.succ) j) := by ext i j; fin_cases i; fin_cases j; decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7981step2 permutation2 hz
    injectiveMoment H raw7981step3 = injectiveMoment H raw7981step4 := by
      have hz : ∀ j, raw7981step3 (permutation0 0) j = 0 := by decide +kernel
      have heq : raw7981step4 = (fun i j => raw7981step3 (permutation0 i.succ) j) := by ext i j; fin_cases i
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7981step3 permutation0 hz
    injectiveMoment H raw7981step4 = injectiveMoment H raw7981step5 := by
      have hz : ∀ i, raw7981step4 i (permutation0 0) = 0 := by decide +kernel
      have heq : raw7981step5 = (fun i j => raw7981step4 i (permutation0 j.succ)) := by ext i j; fin_cases i
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw7981step4 permutation0 hz
    _ = injectiveMoment H node0 := by rfl

theorem canonical7995 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7995 = injectiveMoment H node63 := by
  calc
    injectiveMoment H raw7995 = injectiveMoment H raw7995step0 := by
      have heq : raw7995step0 = (fun i j => raw7995 (permutation5 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7995 permutation5 permutation4
    _ = injectiveMoment H node63 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical27
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical895 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw895 = injectiveMoment H node10 := by
  calc
    injectiveMoment H raw895 = injectiveMoment H raw895step0 := by
      have hz : ∀ j, raw895 (permutation15 0) j = 0 := by decide +kernel
      have heq : raw895step0 = (fun i j => raw895 (permutation15 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw895 permutation15 hz
    _ = injectiveMoment H node10 := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical162
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical5185 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5185 = injectiveMoment H node4 := by
  calc
    injectiveMoment H raw5185 = injectiveMoment H raw5185step0 := by
      have hz : ∀ j, raw5185 (permutation27 0) j = 0 := by decide +kernel
      have heq : raw5185step0 = (fun i j => raw5185 (permutation27 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw5185 permutation27 hz
    injectiveMoment H raw5185step0 = injectiveMoment H raw5185step1 := by
      have hz : ∀ j, raw5185step0 (permutation5 0) j = 0 := by decide +kernel
      have heq : raw5185step1 = (fun i j => raw5185step0 (permutation5 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw5185step0 permutation5 hz
    _ = injectiveMoment H node4 := by rfl

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

theorem canonical5215 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5215 = injectiveMoment H node4 := by
  calc
    injectiveMoment H raw5215 = injectiveMoment H raw5215step0 := by
      have hz : ∀ j, raw5215 (permutation27 0) j = 0 := by decide +kernel
      have heq : raw5215step0 = (fun i j => raw5215 (permutation27 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw5215 permutation27 hz
    injectiveMoment H raw5215step0 = injectiveMoment H raw5215step1 := by
      have hz : ∀ j, raw5215step0 (permutation7 0) j = 0 := by decide +kernel
      have heq : raw5215step1 = (fun i j => raw5215step0 (permutation7 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw5215step0 permutation7 hz
    _ = injectiveMoment H node4 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical170
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical5458 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5458 = injectiveMoment H node10 := by
  calc
    injectiveMoment H raw5458 = injectiveMoment H raw5458step0 := by
      have heq : raw5458step0 = raw5458.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5458).symm
    injectiveMoment H raw5458step0 = injectiveMoment H raw5458step1 := by
      have heq : raw5458step1 = (fun i j => raw5458step0 (permutation6 i) (permutation2 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5458step0 permutation6 permutation2
    _ = injectiveMoment H node10 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical187
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical5990 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5990 = injectiveMoment H node10 := by
  calc
    injectiveMoment H raw5990 = injectiveMoment H raw5990step0 := by
      have heq : raw5990step0 = raw5990.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5990).symm
    injectiveMoment H raw5990step0 = injectiveMoment H raw5990step1 := by
      have heq : raw5990step1 = (fun i j => raw5990step0 (permutation7 i) (permutation2 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5990step0 permutation7 permutation2
    _ = injectiveMoment H node10 := by rfl

end MUB6.Certificate.PairSemantics

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

theorem sound37 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node37 = Sparse.eval value37 (momentVector H) := by
  have hc : momentVector H 13 = injectiveMoment H node37 := rfl
  simp [value37, Sparse.eval, hc]

theorem sound41 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node41 = Sparse.eval value41 (momentVector H) := by
  have hc : momentVector H 12 = injectiveMoment H node41 := rfl
  simp [value41, Sparse.eval, hc]

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

theorem sound56 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node56 = Sparse.eval value56 (momentVector H) := by
  have heq : pivotMatrix56 = (fun u v => node56 (pivotPermutation56 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node56 = injectiveMoment H pivotMatrix56 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix56 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 2 < 6) hH pivotMatrix56 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix56 (0 : Fin 2)) =
      Sparse.eval value11 (momentVector H) := by
    have heq : mergeFirst pivotMatrix56 (0 : Fin 2) = raw6885 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical6885 hH).trans (sound11 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix56 (1 : Fin 2)) =
      Sparse.eval value10 (momentVector H) := by
    have heq : mergeFirst pivotMatrix56 (1 : Fin 2) = raw5990 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical5990 hH).trans (sound10 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (4 : ℝ) * injectiveMoment H node56 + (injectiveMoment H (mergeFirst pivotMatrix56 (0 : Fin 2)) + (injectiveMoment H (mergeFirst pivotMatrix56 (1 : Fin 2)))) = 0 at hc
  rw [hm0, hm1] at hc
  norm_num [value56, value10, value11, Sparse.eval] at hc ⊢
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

theorem sound63 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node63 = Sparse.eval value63 (momentVector H) := by
  have heq : pivotMatrix63 = (fun u v => node63.transpose (pivotPermutation63 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node63 = injectiveMoment H pivotMatrix63 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix63 0 = Pi.single (2 : Fin 3) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 2 < 6) hH pivotMatrix63 2 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix63 (0 : Fin 2)) =
      Sparse.eval value10 (momentVector H) := by
    have heq : mergeFirst pivotMatrix63 (0 : Fin 2) = raw5458 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical5458 hH).trans (sound10 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix63 (1 : Fin 2)) =
      Sparse.eval value10 (momentVector H) := by
    have heq : mergeFirst pivotMatrix63 (1 : Fin 2) = raw7977 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical7977 hH).trans (sound10 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (4 : ℝ) * injectiveMoment H node63 + (injectiveMoment H (mergeFirst pivotMatrix63 (0 : Fin 2)) + (injectiveMoment H (mergeFirst pivotMatrix63 (1 : Fin 2)))) = 0 at hc
  rw [hm0, hm1] at hc
  norm_num [value63, value10, Sparse.eval] at hc ⊢
  linarith

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

theorem canonical4134 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4134 = injectiveMoment H node62 := by
  calc
    injectiveMoment H raw4134 = injectiveMoment H raw4134step0 := by
      have heq : raw4134step0 = (fun i j => raw4134 (permutation7 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4134 permutation7 permutation6
    _ = injectiveMoment H node62 := by rfl

theorem canonical4139 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4139 = injectiveMoment H node203 := by
  calc
    injectiveMoment H raw4139 = injectiveMoment H raw4139step0 := by
      have heq : raw4139step0 = -raw4139 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4139).symm
    injectiveMoment H raw4139step0 = injectiveMoment H raw4139step1 := by
      have heq : raw4139step1 = (fun i j => raw4139step0 (permutation19 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4139step0 permutation19 permutation5
    _ = injectiveMoment H node203 := by rfl

theorem canonical4140 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4140 = injectiveMoment H node207 := by
  calc
    injectiveMoment H raw4140 = injectiveMoment H raw4140step0 := by
      have heq : raw4140step0 = (fun i j => raw4140 (permutation18 i) (permutation7 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4140 permutation18 permutation7
    _ = injectiveMoment H node207 := by rfl

theorem canonical4141 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4141 = injectiveMoment H node41 := by
  rfl

theorem canonical4145 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4145 = injectiveMoment H node215 := by
  rfl

theorem canonical4147 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4147 = injectiveMoment H node37 := by
  calc
    injectiveMoment H raw4147 = injectiveMoment H raw4147step0 := by
      have heq : raw4147step0 = -raw4147 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4147).symm
    injectiveMoment H raw4147step0 = injectiveMoment H raw4147step1 := by
      have heq : raw4147step1 = (fun i j => raw4147step0 (permutation8 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4147step0 permutation8 permutation4
    _ = injectiveMoment H node37 := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical24
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical792 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw792 = injectiveMoment H node177 := by
  calc
    injectiveMoment H raw792 = injectiveMoment H raw792step0 := by
      have heq : raw792step0 = -raw792 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw792).symm
    injectiveMoment H raw792step0 = injectiveMoment H raw792step1 := by
      have heq : raw792step1 = (fun i j => raw792step0 (permutation12 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw792step0 permutation12 permutation8
    _ = injectiveMoment H node177 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical240
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical7709 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7709 = injectiveMoment H node5 := by
  calc
    injectiveMoment H raw7709 = injectiveMoment H raw7709step0 := by
      have hz : ∀ j, raw7709 (permutation5 0) j = 0 := by decide +kernel
      have heq : raw7709step0 = (fun i j => raw7709 (permutation5 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7709 permutation5 hz
    _ = injectiveMoment H node5 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical89
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical2849 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2849 = injectiveMoment H node37 := by
  rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound1
attribute [-simp] _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_toRational _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

theorem sound65 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node65 = Sparse.eval value65 (momentVector H) := by
  have heq : pivotMatrix65 = (fun u v => node65 (pivotPermutation65 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node65 = injectiveMoment H pivotMatrix65 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix65 0 = Pi.single (1 : Fin 2) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix65 1 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix65 (0 : Fin 3)) =
      Sparse.eval value11 (momentVector H) := by
    have heq : mergeFirst pivotMatrix65 (0 : Fin 3) = raw5199 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical5199 hH).trans (sound11 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix65 (1 : Fin 3)) =
      Sparse.eval value5 (momentVector H) := by
    have heq : mergeFirst pivotMatrix65 (1 : Fin 3) = raw7709 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical7709 hH).trans (sound5 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix65 (2 : Fin 3)) =
      Sparse.eval value5 (momentVector H) := by
    have heq : mergeFirst pivotMatrix65 (2 : Fin 3) = raw7735 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical7735 hH).trans (sound5 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node65 + (injectiveMoment H (mergeFirst pivotMatrix65 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix65 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix65 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value65, value11, value5, Sparse.eval] at hc ⊢
  linarith

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

theorem canonical4161 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4161 = injectiveMoment H node36 := by
  calc
    injectiveMoment H raw4161 = injectiveMoment H raw4161step0 := by
      have heq : raw4161step0 = -raw4161 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4161).symm
    injectiveMoment H raw4161step0 = injectiveMoment H raw4161step1 := by
      have heq : raw4161step1 = (fun i j => raw4161step0 (permutation5 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4161step0 permutation5 permutation5
    _ = injectiveMoment H node36 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical154
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical4956 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4956 = injectiveMoment H node62 := by
  calc
    injectiveMoment H raw4956 = injectiveMoment H raw4956step0 := by
      have heq : raw4956step0 = -raw4956 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4956).symm
    injectiveMoment H raw4956step0 = injectiveMoment H raw4956step1 := by
      have heq : raw4956step1 = (fun i j => raw4956step0 (permutation4 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4956step0 permutation4 permutation8
    _ = injectiveMoment H node62 := by rfl

theorem canonical4958 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4958 = injectiveMoment H node210 := by
  calc
    injectiveMoment H raw4958 = injectiveMoment H raw4958step0 := by
      have heq : raw4958step0 = (fun i j => raw4958 (permutation19 i) (permutation7 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4958 permutation19 permutation7
    _ = injectiveMoment H node210 := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical184
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical5891 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5891 = injectiveMoment H node36 := by
  calc
    injectiveMoment H raw5891 = injectiveMoment H raw5891step0 := by
      have heq : raw5891step0 = (fun i j => raw5891 (permutation4 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5891 permutation4 permutation5
    _ = injectiveMoment H node36 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical186
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical5972 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5972 = injectiveMoment H node56 := by
  rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical238
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical7636 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7636 = injectiveMoment H node46 := by
  calc
    injectiveMoment H raw7636 = injectiveMoment H raw7636step0 := by
      have heq : raw7636step0 = (fun i j => raw7636 (permutation15 i) (permutation1 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7636 permutation15 permutation1
    _ = injectiveMoment H node46 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical214
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical6870 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6870 = injectiveMoment H node63 := by
  rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical88
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical2845 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2845 = injectiveMoment H node36 := by
  rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound2
attribute [-simp] _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_toRational _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

theorem sound177 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node177 = Sparse.eval value177 (momentVector H) := by
  have heq : pivotMatrix177 = (fun u v => node177 (pivotPermutation177 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node177 = injectiveMoment H pivotMatrix177 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix177 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix177 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix177 (0 : Fin 3)) =
      Sparse.eval value41 (momentVector H) := by
    have heq : mergeFirst pivotMatrix177 (0 : Fin 3) = raw4141 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical4141 hH).trans (sound41 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix177 (1 : Fin 3)) =
      Sparse.eval value37 (momentVector H) := by
    have heq : mergeFirst pivotMatrix177 (1 : Fin 3) = raw2849 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical2849 hH).trans (sound37 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix177 (2 : Fin 3)) =
      Sparse.eval value36 (momentVector H) := by
    have heq : mergeFirst pivotMatrix177 (2 : Fin 3) = raw2845 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical2845 hH).trans (sound36 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node177 + (injectiveMoment H (mergeFirst pivotMatrix177 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix177 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix177 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value177, value36, value37, value41, Sparse.eval] at hc ⊢
  linarith

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

theorem sound203 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node203 = Sparse.eval value203 (momentVector H) := by
  have heq : pivotMatrix203 = (fun u v => node203 (pivotPermutation203 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node203 = injectiveMoment H pivotMatrix203 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix203 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix203 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix203 (0 : Fin 3)) =
      Sparse.eval value36 (momentVector H) := by
    have heq : mergeFirst pivotMatrix203 (0 : Fin 3) = raw2845 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical2845 hH).trans (sound36 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix203 (1 : Fin 3)) =
      Sparse.eval value62 (momentVector H) := by
    have heq : mergeFirst pivotMatrix203 (1 : Fin 3) = raw4134 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical4134 hH).trans (sound62 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix203 (2 : Fin 3)) =
      Sparse.eval value41 (momentVector H) := by
    have heq : mergeFirst pivotMatrix203 (2 : Fin 3) = raw4141 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical4141 hH).trans (sound41 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node203 + (injectiveMoment H (mergeFirst pivotMatrix203 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix203 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix203 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value203, value36, value41, value62, Sparse.eval] at hc ⊢
  linarith

theorem sound207 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node207 = Sparse.eval value207 (momentVector H) := by
  have heq : pivotMatrix207 = (fun u v => node207 (pivotPermutation207 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node207 = injectiveMoment H pivotMatrix207 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix207 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix207 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix207 (0 : Fin 3)) =
      Sparse.eval value62 (momentVector H) := by
    have heq : mergeFirst pivotMatrix207 (0 : Fin 3) = raw4956 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical4956 hH).trans (sound62 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix207 (1 : Fin 3)) =
      Sparse.eval value41 (momentVector H) := by
    have heq : mergeFirst pivotMatrix207 (1 : Fin 3) = raw4141 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical4141 hH).trans (sound41 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix207 (2 : Fin 3)) =
      Sparse.eval value62 (momentVector H) := by
    have heq : mergeFirst pivotMatrix207 (2 : Fin 3) = raw4134 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical4134 hH).trans (sound62 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node207 + (injectiveMoment H (mergeFirst pivotMatrix207 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix207 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix207 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value207, value41, value62, Sparse.eval] at hc ⊢
  linarith

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

theorem sound215 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node215 = Sparse.eval value215 (momentVector H) := by
  have heq : pivotMatrix215 = (fun u v => node215 (pivotPermutation215 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node215 = injectiveMoment H pivotMatrix215 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix215 0 = Pi.single (0 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix215 0 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix215 (0 : Fin 3)) =
      Sparse.eval value63 (momentVector H) := by
    have heq : mergeFirst pivotMatrix215 (0 : Fin 3) = raw6870 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical6870 hH).trans (sound63 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix215 (1 : Fin 3)) =
      Sparse.eval value36 (momentVector H) := by
    have heq : mergeFirst pivotMatrix215 (1 : Fin 3) = raw4161 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical4161 hH).trans (sound36 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix215 (2 : Fin 3)) =
      Sparse.eval value37 (momentVector H) := by
    have heq : mergeFirst pivotMatrix215 (2 : Fin 3) = raw4147 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical4147 hH).trans (sound37 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node215 + (injectiveMoment H (mergeFirst pivotMatrix215 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix215 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix215 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value215, value36, value37, value63, Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound4
attribute [-simp] _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_toRational _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

theorem sound261 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node261 = Sparse.eval value261 (momentVector H) := by
  have heq : pivotMatrix261 = (fun u v => node261 (pivotPermutation261 u) v) := by apply Matrix.ext; unfold pivotMatrix261 node261 pivotPermutation261; decide +kernel
  have hmoment : injectiveMoment H node261 = injectiveMoment H pivotMatrix261 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix261 0 = Pi.single (0 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix261 0 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix261 (0 : Fin 3)) =
      Sparse.eval value63 (momentVector H) := by
    have heq : mergeFirst pivotMatrix261 (0 : Fin 3) = raw7995 := by apply Matrix.ext; unfold mergeFirst pivotMatrix261 raw7995; decide +kernel
    rw [heq]
    exact (canonical7995 hH).trans (sound63 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix261 (1 : Fin 3)) =
      Sparse.eval value56 (momentVector H) := by
    have heq : mergeFirst pivotMatrix261 (1 : Fin 3) = raw5972 := by apply Matrix.ext; unfold mergeFirst pivotMatrix261 raw5972; decide +kernel
    rw [heq]
    exact (canonical5972 hH).trans (sound56 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix261 (2 : Fin 3)) =
      Sparse.eval value36 (momentVector H) := by
    have heq : mergeFirst pivotMatrix261 (2 : Fin 3) = raw5891 := by apply Matrix.ext; unfold mergeFirst pivotMatrix261 raw5891; decide +kernel
    rw [heq]
    exact (canonical5891 hH).trans (sound36 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node261 + (injectiveMoment H (mergeFirst pivotMatrix261 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix261 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix261 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value261, value36, value56, value63, Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound10
attribute [-simp] _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_toRational _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

theorem sound670 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node670 = Sparse.eval value670 (momentVector H) := by
  have heq : pivotMatrix670 = (fun u v => node670 (pivotPermutation670 u) v) := by apply Matrix.ext; unfold pivotMatrix670 node670 pivotPermutation670; decide +kernel
  have hmoment : injectiveMoment H node670 = injectiveMoment H pivotMatrix670 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix670 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix670 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix670 (0 : Fin 4)) =
      Sparse.eval value210 (momentVector H) := by
    have heq : mergeFirst pivotMatrix670 (0 : Fin 4) = raw4958 := by apply Matrix.ext; unfold mergeFirst pivotMatrix670 raw4958; decide +kernel
    rw [heq]
    exact (canonical4958 hH).trans (sound210 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix670 (1 : Fin 4)) =
      Sparse.eval value215 (momentVector H) := by
    have heq : mergeFirst pivotMatrix670 (1 : Fin 4) = raw4145 := by apply Matrix.ext; unfold mergeFirst pivotMatrix670 raw4145; decide +kernel
    rw [heq]
    exact (canonical4145 hH).trans (sound215 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix670 (2 : Fin 4)) =
      Sparse.eval value207 (momentVector H) := by
    have heq : mergeFirst pivotMatrix670 (2 : Fin 4) = raw4140 := by apply Matrix.ext; unfold mergeFirst pivotMatrix670 raw4140; decide +kernel
    rw [heq]
    exact (canonical4140 hH).trans (sound207 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix670 (3 : Fin 4)) =
      Sparse.eval value203 (momentVector H) := by
    have heq : mergeFirst pivotMatrix670 (3 : Fin 4) = raw4139 := by apply Matrix.ext; unfold mergeFirst pivotMatrix670 raw4139; decide +kernel
    rw [heq]
    exact (canonical4139 hH).trans (sound203 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node670 + (injectiveMoment H (mergeFirst pivotMatrix670 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix670 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix670 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix670 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value670, value203, value207, value210, value215, Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical122
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical3926 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3926 = injectiveMoment H node670 := by
  calc
    injectiveMoment H raw3926 = injectiveMoment H raw3926step0 := by
      have heq : raw3926step0 = (fun i j => raw3926 (permutation134 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3926 permutation134 permutation6
    _ = injectiveMoment H node670 := by rfl

end MUB6.Certificate.PairSemantics

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_SingleGroup23
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singlePair390 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node390 node390Labels = Sparse.eval singlePairValue390 (familyPairVector B) := by
  have hp := single_label_three B hB node390
  have hl : node390Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node390 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node390 (EqualityPatterns.family3.label 0) = PairSemantics.raw7980 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node390 PairSemantics.raw7980; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7980 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node390 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value46 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node390 (EqualityPatterns.family3.label 1) = PairSemantics.raw5149 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node390 PairSemantics.raw5149; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5149 hH).trans (PairSemantics.sound46 hH)
  have hm2 : familyPairMoment B (groupedColumns node390 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value65 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node390 (EqualityPatterns.family3.label 2) = PairSemantics.raw7731 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node390 PairSemantics.raw7731; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7731 hH).trans (PairSemantics.sound65 hH)
  have hm3 : familyPairMoment B (groupedColumns node390 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value10 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node390 (EqualityPatterns.family3.label 3) = PairSemantics.raw895 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node390 PairSemantics.raw895; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical895 hH).trans (PairSemantics.sound10 hH)
  have hm4 : familyPairMoment B (groupedColumns node390 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value261 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node390 (EqualityPatterns.family3.label 4) = PairSemantics.raw750 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node390 PairSemantics.raw750; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical750 hH).trans (PairSemantics.sound261 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue390, PairSemantics.value0, PairSemantics.value10, PairSemantics.value46, PairSemantics.value65, PairSemantics.value261, Sparse.eval] at hp ⊢
  linarith only [hp]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical281
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical9013 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9013 = injectiveMoment H node11 := by
  calc
    injectiveMoment H raw9013 = injectiveMoment H raw9013step0 := by
      have hz : ∀ j, raw9013 (permutation9 0) j = 0 := by decide +kernel
      have heq : raw9013step0 = (fun i j => raw9013 (permutation9 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw9013 permutation9 hz
    injectiveMoment H raw9013step0 = injectiveMoment H raw9013step1 := by
      have heq : raw9013step1 = (fun i j => raw9013step0 (permutation7 i) (permutation2 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9013step0 permutation7 permutation2
    _ = injectiveMoment H node11 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_SingleGroup25
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singlePair412 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node412 node412Labels = Sparse.eval singlePairValue412 (familyPairVector B) := by
  have hp := single_label_three B hB node412
  have hl : node412Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node412 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node412 (EqualityPatterns.family3.label 0) = PairSemantics.raw7980 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node412 PairSemantics.raw7980; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7980 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node412 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value4 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node412 (EqualityPatterns.family3.label 1) = PairSemantics.raw5215 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node412 PairSemantics.raw5215; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5215 hH).trans (PairSemantics.sound4 hH)
  have hm2 : familyPairMoment B (groupedColumns node412 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value46 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node412 (EqualityPatterns.family3.label 2) = PairSemantics.raw7636 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node412 PairSemantics.raw7636; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7636 hH).trans (PairSemantics.sound46 hH)
  have hm3 : familyPairMoment B (groupedColumns node412 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value10 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node412 (EqualityPatterns.family3.label 3) = PairSemantics.raw895 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node412 PairSemantics.raw895; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical895 hH).trans (PairSemantics.sound10 hH)
  have hm4 : familyPairMoment B (groupedColumns node412 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value177 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node412 (EqualityPatterns.family3.label 4) = PairSemantics.raw792 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node412 PairSemantics.raw792; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical792 hH).trans (PairSemantics.sound177 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue412, PairSemantics.value0, PairSemantics.value4, PairSemantics.value10, PairSemantics.value46, PairSemantics.value177, Sparse.eval] at hp ⊢
  linarith only [hp]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical282
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical9045 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9045 = injectiveMoment H node11 := by
  calc
    injectiveMoment H raw9045 = injectiveMoment H raw9045step0 := by
      have hz : ∀ j, raw9045 (permutation57 0) j = 0 := by decide +kernel
      have heq : raw9045step0 = (fun i j => raw9045 (permutation57 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw9045 permutation57 hz
    injectiveMoment H raw9045step0 = injectiveMoment H raw9045step1 := by
      have hz : ∀ j, raw9045step0 (permutation9 0) j = 0 := by decide +kernel
      have heq : raw9045step1 = (fun i j => raw9045step0 (permutation9 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw9045step0 permutation9 hz
    injectiveMoment H raw9045step1 = injectiveMoment H raw9045step2 := by
      have heq : raw9045step2 = (fun i j => raw9045step1 (permutation7 i) (permutation2 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9045step1 permutation7 permutation2
    _ = injectiveMoment H node11 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical123
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical3963 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3963 = injectiveMoment H node203 := by
  calc
    injectiveMoment H raw3963 = injectiveMoment H raw3963step0 := by
      have heq : raw3963step0 = -raw3963 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3963).symm
    injectiveMoment H raw3963step0 = injectiveMoment H raw3963step1 := by
      have heq : raw3963step1 = (fun i j => raw3963step0 (permutation10 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3963step0 permutation10 permutation8
    _ = injectiveMoment H node203 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_SingleGroup28
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singlePair467 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node467 node467Labels = Sparse.eval singlePairValue467 (familyPairVector B) := by
  have hp := single_label_three B hB node467
  have hl : node467Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node467 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node467 (EqualityPatterns.family3.label 0) = PairSemantics.raw7981 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node467 PairSemantics.raw7981; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7981 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node467 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value46 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node467 (EqualityPatterns.family3.label 1) = PairSemantics.raw5142 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node467 PairSemantics.raw5142; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5142 hH).trans (PairSemantics.sound46 hH)
  have hm2 : familyPairMoment B (groupedColumns node467 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value11 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node467 (EqualityPatterns.family3.label 2) = PairSemantics.raw9045 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node467 PairSemantics.raw9045; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical9045 hH).trans (PairSemantics.sound11 hH)
  have hm3 : familyPairMoment B (groupedColumns node467 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value46 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node467 (EqualityPatterns.family3.label 3) = PairSemantics.raw5128 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node467 PairSemantics.raw5128; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5128 hH).trans (PairSemantics.sound46 hH)
  have hm4 : familyPairMoment B (groupedColumns node467 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value670 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node467 (EqualityPatterns.family3.label 4) = PairSemantics.raw3926 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node467 PairSemantics.raw3926; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical3926 hH).trans (PairSemantics.sound670 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue467, PairSemantics.value0, PairSemantics.value11, PairSemantics.value46, PairSemantics.value670, Sparse.eval] at hp ⊢
  linarith only [hp]

end MUB6.Certificate.MixedSemantics

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_SinglePriority
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singlePair496 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node496 node496Labels = Sparse.eval singlePairValue496 (familyPairVector B) := by
  have hp := single_label_three B hB node496
  have hl : node496Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node496 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node496 (EqualityPatterns.family3.label 0) = PairSemantics.raw7980 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node496 PairSemantics.raw7980; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7980 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node496 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value4 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node496 (EqualityPatterns.family3.label 1) = PairSemantics.raw5185 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node496 PairSemantics.raw5185; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5185 hH).trans (PairSemantics.sound4 hH)
  have hm2 : familyPairMoment B (groupedColumns node496 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value11 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node496 (EqualityPatterns.family3.label 2) = PairSemantics.raw9013 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node496 PairSemantics.raw9013; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical9013 hH).trans (PairSemantics.sound11 hH)
  have hm3 : familyPairMoment B (groupedColumns node496 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value46 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node496 (EqualityPatterns.family3.label 3) = PairSemantics.raw5141 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node496 PairSemantics.raw5141; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5141 hH).trans (PairSemantics.sound46 hH)
  have hm4 : familyPairMoment B (groupedColumns node496 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value203 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node496 (EqualityPatterns.family3.label 4) = PairSemantics.raw3963 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node496 PairSemantics.raw3963; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical3963 hH).trans (PairSemantics.sound203 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue496, PairSemantics.value0, PairSemantics.value4, PairSemantics.value11, PairSemantics.value46, PairSemantics.value203, Sparse.eval] at hp ⊢
  linarith only [hp]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons43
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singleton2776 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node2776 node2776Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node412 node412Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw278 singletonSmall2776
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall2776) = raw278Labels := by decide +kernel
  rw [hl, canonical278 B hB] at h
  have hc0 : mixedMoment B raw278 (Fin.cases (0 : Fin 1) singletonSmall2776) =
      mixedMoment B node412 node412Labels := by
    have ha : raw278 = raw279 := by apply Matrix.ext; unfold raw278 raw279; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall2776 = raw279Labels := by decide +kernel
    rw [ha, hj, canonical279 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons48
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singleton3110 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node3110 node3110Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node390 node390Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw392 singletonSmall3110
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall3110) = raw392Labels := by decide +kernel
  rw [hl, canonical392 B hB] at h
  have hc0 : mixedMoment B raw392 (Fin.cases (0 : Fin 1) singletonSmall3110) =
      mixedMoment B node390 node390Labels := by
    have ha : raw392 = raw393 := by apply Matrix.ext; unfold raw392 raw393; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall3110 = raw393Labels := by decide +kernel
    rw [ha, hj, canonical393 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

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

theorem singleton3862 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node3862 node3862Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node496 node496Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw536 singletonSmall3862
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall3862) = raw536Labels := by decide +kernel
  rw [hl, canonical536 B hB] at h
  have hc0 : mixedMoment B raw536 (Fin.cases (0 : Fin 1) singletonSmall3862) =
      mixedMoment B node496 node496Labels := by
    have ha : raw536 = raw537 := by apply Matrix.ext; unfold raw536 raw537; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall3862 = raw537Labels := by decide +kernel
    rw [ha, hj, canonical537 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

theorem singleton3883 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node3883 node3883Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node467 node467Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw540 singletonSmall3883
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall3883) = raw540Labels := by decide +kernel
  rw [hl, canonical540 B hB] at h
  have hc0 : mixedMoment B raw540 (Fin.cases (0 : Fin 1) singletonSmall3883) =
      mixedMoment B node467 node467Labels := by
    have ha : raw540 = raw541 := by apply Matrix.ext; unfold raw540 raw541; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall3883 = raw541Labels := by decide +kernel
    rw [ha, hj, canonical541 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_SoundPriority
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound496 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node496 node496Labels = Sparse.eval nodeValue496 (mixedVector B) := by
  calc
    _ = Sparse.eval singlePairValue496 (familyPairVector B) := singlePair496 B _hB
    _ = _ := by norm_num [singlePairValue496, nodeValue496, Sparse.eval, mixedVector] <;> ring

theorem sound3862 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3862 node3862Labels = Sparse.eval nodeValue3862 (mixedVector B) := by
  have h := singleton3862 B _hB
  rw [sound496 B _hB _hF] at h
  norm_num [nodeValue3862, nodeValue496, Sparse.eval] at h ⊢
  linarith only [h]

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

theorem sound2732 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2732 node2732Labels = Sparse.eval nodeValue2732 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2732) = mixedMoment B node2732 node2732Labels := rfl
  simpa [nodeValue2732, Sparse.eval] using hc.symm

theorem sound2734 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2734 node2734Labels = Sparse.eval nodeValue2734 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2734) = mixedMoment B node2734 node2734Labels := rfl
  simpa [nodeValue2734, Sparse.eval] using hc.symm

theorem sound2744 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2744 node2744Labels = Sparse.eval nodeValue2744 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2744) = mixedMoment B node2744 node2744Labels := rfl
  simpa [nodeValue2744, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound6
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound390 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node390 node390Labels = Sparse.eval nodeValue390 (mixedVector B) := by
  calc
    _ = Sparse.eval singlePairValue390 (familyPairVector B) := singlePair390 B _hB
    _ = _ := by
      norm_num [singlePairValue390, nodeValue390, Sparse.eval, mixedVector]
      ring

theorem sound412 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node412 node412Labels = Sparse.eval nodeValue412 (mixedVector B) := by
  calc
    _ = Sparse.eval singlePairValue412 (familyPairVector B) := singlePair412 B _hB
    _ = _ := by
      norm_num [singlePairValue412, nodeValue412, Sparse.eval, mixedVector]
      ring

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

theorem sound2776 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2776 node2776Labels = Sparse.eval nodeValue2776 (mixedVector B) := by
  have h := singleton2776 B _hB
  rw [sound412 B _hB _hF] at h
  norm_num [nodeValue2776, nodeValue412, Sparse.eval] at h ⊢
  linarith only [h]

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

theorem sound3039 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3039 node3039Labels = Sparse.eval nodeValue3039 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3039) = mixedMoment B node3039 node3039Labels := rfl
  simpa [nodeValue3039, Sparse.eval] using hc.symm

theorem sound3055 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3055 node3055Labels = Sparse.eval nodeValue3055 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3055) = mixedMoment B node3055 node3055Labels := rfl
  simpa [nodeValue3055, Sparse.eval] using hc.symm

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

theorem sound3110 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3110 node3110Labels = Sparse.eval nodeValue3110 (mixedVector B) := by
  have h := singleton3110 B _hB
  rw [sound390 B _hB _hF] at h
  norm_num [nodeValue3110, nodeValue390, Sparse.eval] at h ⊢
  linarith only [h]

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

theorem sound3573 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3573 node3573Labels = Sparse.eval nodeValue3573 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3573) = mixedMoment B node3573 node3573Labels := rfl
  simpa [nodeValue3573, Sparse.eval] using hc.symm

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

theorem sound3584 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3584 node3584Labels = Sparse.eval nodeValue3584 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3584) = mixedMoment B node3584 node3584Labels := rfl
  simpa [nodeValue3584, Sparse.eval] using hc.symm

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

theorem sound467 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node467 node467Labels = Sparse.eval nodeValue467 (mixedVector B) := by
  calc
    _ = Sparse.eval singlePairValue467 (familyPairVector B) := singlePair467 B _hB
    _ = _ := by norm_num [singlePairValue467, nodeValue467, Sparse.eval, mixedVector] <;> ring

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

theorem zero3861 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3861 node3861Labels = 0 := by
  exact mixedMoment_order_one B hB node3861 node3861Labels 1
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

theorem sound3861 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3861 node3861Labels = Sparse.eval nodeValue3861 (mixedVector B) := by
  simpa only [nodeValue3861, Sparse.eval_nil] using zero3861 B _hB _hF

theorem sound3872 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3872 node3872Labels = Sparse.eval nodeValue3872 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3872) = mixedMoment B node3872 node3872Labels := rfl
  simpa [nodeValue3872, Sparse.eval] using hc.symm

theorem sound3876 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3876 node3876Labels = Sparse.eval nodeValue3876 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3876) = mixedMoment B node3876 node3876Labels := rfl
  simpa [nodeValue3876, Sparse.eval] using hc.symm

theorem sound3877 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3877 node3877Labels = Sparse.eval nodeValue3877 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3877) = mixedMoment B node3877 node3877Labels := rfl
  simpa [nodeValue3877, Sparse.eval] using hc.symm

theorem sound3883 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3883 node3883Labels = Sparse.eval nodeValue3883 (mixedVector B) := by
  have h := singleton3883 B _hB
  rw [sound467 B _hB _hF] at h
  norm_num [nodeValue3883, nodeValue467, Sparse.eval] at h ⊢
  linarith only [h]

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros62
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero4001 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4001 node4001Labels = 0 := by
  exact mixedMoment_order_one B hB node4001 node4001Labels 2
    (by decide +kernel) (by decide +kernel)

theorem zero4006 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4006 node4006Labels = 0 := by
  exact mixedMoment_order_one B hB node4006 node4006Labels 2
    (by decide +kernel) (by decide +kernel)

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

theorem sound4001 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4001 node4001Labels = Sparse.eval nodeValue4001 (mixedVector B) := by
  simpa only [nodeValue4001, Sparse.eval_nil] using zero4001 B _hB _hF

theorem sound4006 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4006 node4006Labels = Sparse.eval nodeValue4006 (mixedVector B) := by
  simpa only [nodeValue4006, Sparse.eval_nil] using zero4006 B _hB _hF

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources28
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sourceEq908 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm908 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA908 + difference 0 1) (sourceB908 + difference 1 0) sourceC908) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3888) := by
    have ha : (tripleCharges (sourceA908 + difference 0 1) (sourceB908 + difference 1 0) sourceC908) = raw14995 := by
      apply Matrix.ext; unfold tripleCharges sourceA908 sourceB908 sourceC908 difference raw14995; decide +kernel
    rw [ha]
    exact (canonical14995 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA908 + difference 0 2) (sourceB908 + difference 2 0) sourceC908) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3876) := by
    have ha : (tripleCharges (sourceA908 + difference 0 2) (sourceB908 + difference 2 0) sourceC908) = raw14763 := by
      apply Matrix.ext; unfold tripleCharges sourceA908 sourceB908 sourceC908 difference raw14763; decide +kernel
    rw [ha]
    exact (canonical14763 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA908 + difference 0 3) (sourceB908 + difference 3 0) sourceC908) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3876) := by
    have ha : (tripleCharges (sourceA908 + difference 0 3) (sourceB908 + difference 3 0) sourceC908) = raw14996 := by
      apply Matrix.ext; unfold tripleCharges sourceA908 sourceB908 sourceC908 difference raw14996; decide +kernel
    rw [ha]
    exact (canonical14996 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA908 + difference 0 4) (sourceB908 + difference 4 0) sourceC908) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3861) := by
    have ha : (tripleCharges (sourceA908 + difference 0 4) (sourceB908 + difference 4 0) sourceC908) = raw14997 := by
      apply Matrix.ext; unfold tripleCharges sourceA908 sourceB908 sourceC908 difference raw14997; decide +kernel
    rw [ha]
    exact (canonical14997 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA908 + difference 0 5) (sourceB908 + difference 5 0) sourceC908) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3583) := by
    have ha : (tripleCharges (sourceA908 + difference 0 5) (sourceB908 + difference 5 0) sourceC908) = raw14998 := by
      apply Matrix.ext; unfold tripleCharges sourceA908 sourceB908 sourceC908 difference raw14998; decide +kernel
    rw [ha]
    exact (canonical14998 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA908 + difference 1 0) (sourceB908 + difference 0 1) sourceC908) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3055) := by
    have ha : (tripleCharges (sourceA908 + difference 1 0) (sourceB908 + difference 0 1) sourceC908) = raw14999 := by
      apply Matrix.ext; unfold tripleCharges sourceA908 sourceB908 sourceC908 difference raw14999; decide +kernel
    rw [ha]
    exact (canonical14999 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA908 + difference 1 2) (sourceB908 + difference 2 1) sourceC908) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3877) := by
    have ha : (tripleCharges (sourceA908 + difference 1 2) (sourceB908 + difference 2 1) sourceC908) = raw14768 := by
      apply Matrix.ext; unfold tripleCharges sourceA908 sourceB908 sourceC908 difference raw14768; decide +kernel
    rw [ha]
    exact (canonical14768 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA908 + difference 1 3) (sourceB908 + difference 3 1) sourceC908) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3877) := by
    have ha : (tripleCharges (sourceA908 + difference 1 3) (sourceB908 + difference 3 1) sourceC908) = raw15000 := by
      apply Matrix.ext; unfold tripleCharges sourceA908 sourceB908 sourceC908 difference raw15000; decide +kernel
    rw [ha]
    exact (canonical15000 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA908 + difference 1 4) (sourceB908 + difference 4 1) sourceC908) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3862) := by
    have ha : (tripleCharges (sourceA908 + difference 1 4) (sourceB908 + difference 4 1) sourceC908) = raw15001 := by
      apply Matrix.ext; unfold tripleCharges sourceA908 sourceB908 sourceC908 difference raw15001; decide +kernel
    rw [ha]
    exact (canonical15001 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA908 + difference 1 5) (sourceB908 + difference 5 1) sourceC908) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3584) := by
    have ha : (tripleCharges (sourceA908 + difference 1 5) (sourceB908 + difference 5 1) sourceC908) = raw15002 := by
      apply Matrix.ext; unfold tripleCharges sourceA908 sourceB908 sourceC908 difference raw15002; decide +kernel
    rw [ha]
    exact (canonical15002 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA908 + difference 2 0) (sourceB908 + difference 0 2) sourceC908) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3039) := by
    have ha : (tripleCharges (sourceA908 + difference 2 0) (sourceB908 + difference 0 2) sourceC908) = raw15003 := by
      apply Matrix.ext; unfold tripleCharges sourceA908 sourceB908 sourceC908 difference raw15003; decide +kernel
    rw [ha]
    exact (canonical15003 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA908 + difference 2 1) (sourceB908 + difference 1 2) sourceC908) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3883) := by
    have ha : (tripleCharges (sourceA908 + difference 2 1) (sourceB908 + difference 1 2) sourceC908) = raw15004 := by
      apply Matrix.ext; unfold tripleCharges sourceA908 sourceB908 sourceC908 difference raw15004; decide +kernel
    rw [ha]
    exact (canonical15004 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA908 + difference 2 3) (sourceB908 + difference 3 2) sourceC908) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3872) := by
    have ha : (tripleCharges (sourceA908 + difference 2 3) (sourceB908 + difference 3 2) sourceC908) = raw15005 := by
      apply Matrix.ext; unfold tripleCharges sourceA908 sourceB908 sourceC908 difference raw15005; decide +kernel
    rw [ha]
    exact (canonical15005 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA908 + difference 2 4) (sourceB908 + difference 4 2) sourceC908) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3853) := by
    have ha : (tripleCharges (sourceA908 + difference 2 4) (sourceB908 + difference 4 2) sourceC908) = raw15006 := by
      apply Matrix.ext; unfold tripleCharges sourceA908 sourceB908 sourceC908 difference raw15006; decide +kernel
    rw [ha]
    exact (canonical15006 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA908 + difference 2 5) (sourceB908 + difference 5 2) sourceC908) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3573) := by
    have ha : (tripleCharges (sourceA908 + difference 2 5) (sourceB908 + difference 5 2) sourceC908) = raw15007 := by
      apply Matrix.ext; unfold tripleCharges sourceA908 sourceB908 sourceC908 difference raw15007; decide +kernel
    rw [ha]
    exact (canonical15007 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA908 + difference 3 0) (sourceB908 + difference 0 3) sourceC908) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3039) := by
    have ha : (tripleCharges (sourceA908 + difference 3 0) (sourceB908 + difference 0 3) sourceC908) = raw14771 := by
      apply Matrix.ext; unfold tripleCharges sourceA908 sourceB908 sourceC908 difference raw14771; decide +kernel
    rw [ha]
    exact (canonical14771 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA908 + difference 3 1) (sourceB908 + difference 1 3) sourceC908) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3883) := by
    have ha : (tripleCharges (sourceA908 + difference 3 1) (sourceB908 + difference 1 3) sourceC908) = raw14772 := by
      apply Matrix.ext; unfold tripleCharges sourceA908 sourceB908 sourceC908 difference raw14772; decide +kernel
    rw [ha]
    exact (canonical14772 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA908 + difference 3 2) (sourceB908 + difference 2 3) sourceC908) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3872) := by
    have ha : (tripleCharges (sourceA908 + difference 3 2) (sourceB908 + difference 2 3) sourceC908) = raw15008 := by
      apply Matrix.ext; unfold tripleCharges sourceA908 sourceB908 sourceC908 difference raw15008; decide +kernel
    rw [ha]
    exact (canonical15008 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA908 + difference 3 4) (sourceB908 + difference 4 3) sourceC908) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3853) := by
    have ha : (tripleCharges (sourceA908 + difference 3 4) (sourceB908 + difference 4 3) sourceC908) = raw14774 := by
      apply Matrix.ext; unfold tripleCharges sourceA908 sourceB908 sourceC908 difference raw14774; decide +kernel
    rw [ha]
    exact (canonical14774 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA908 + difference 3 5) (sourceB908 + difference 5 3) sourceC908) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3573) := by
    have ha : (tripleCharges (sourceA908 + difference 3 5) (sourceB908 + difference 5 3) sourceC908) = raw14775 := by
      apply Matrix.ext; unfold tripleCharges sourceA908 sourceB908 sourceC908 difference raw14775; decide +kernel
    rw [ha]
    exact (canonical14775 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA908 + difference 4 0) (sourceB908 + difference 0 4) sourceC908) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2734) := by
    have ha : (tripleCharges (sourceA908 + difference 4 0) (sourceB908 + difference 0 4) sourceC908) = raw15009 := by
      apply Matrix.ext; unfold tripleCharges sourceA908 sourceB908 sourceC908 difference raw15009; decide +kernel
    rw [ha]
    exact (canonical15009 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA908 + difference 4 1) (sourceB908 + difference 1 4) sourceC908) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2776) := by
    have ha : (tripleCharges (sourceA908 + difference 4 1) (sourceB908 + difference 1 4) sourceC908) = raw15010 := by
      apply Matrix.ext; unfold tripleCharges sourceA908 sourceB908 sourceC908 difference raw15010; decide +kernel
    rw [ha]
    exact (canonical15010 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA908 + difference 4 2) (sourceB908 + difference 2 4) sourceC908) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2732) := by
    have ha : (tripleCharges (sourceA908 + difference 4 2) (sourceB908 + difference 2 4) sourceC908) = raw14784 := by
      apply Matrix.ext; unfold tripleCharges sourceA908 sourceB908 sourceC908 difference raw14784; decide +kernel
    rw [ha]
    exact (canonical14784 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA908 + difference 4 3) (sourceB908 + difference 3 4) sourceC908) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2732) := by
    have ha : (tripleCharges (sourceA908 + difference 4 3) (sourceB908 + difference 3 4) sourceC908) = raw15011 := by
      apply Matrix.ext; unfold tripleCharges sourceA908 sourceB908 sourceC908 difference raw15011; decide +kernel
    rw [ha]
    exact (canonical15011 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA908 + difference 4 5) (sourceB908 + difference 5 4) sourceC908) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2744) := by
    have ha : (tripleCharges (sourceA908 + difference 4 5) (sourceB908 + difference 5 4) sourceC908) = raw15012 := by
      apply Matrix.ext; unfold tripleCharges sourceA908 sourceB908 sourceC908 difference raw15012; decide +kernel
    rw [ha]
    exact (canonical15012 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA908 + difference 5 0) (sourceB908 + difference 0 5) sourceC908) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3110) := by
    have ha : (tripleCharges (sourceA908 + difference 5 0) (sourceB908 + difference 0 5) sourceC908) = raw15013 := by
      apply Matrix.ext; unfold tripleCharges sourceA908 sourceB908 sourceC908 difference raw15013; decide +kernel
    rw [ha]
    exact (canonical15013 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA908 + difference 5 1) (sourceB908 + difference 1 5) sourceC908) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4006) := by
    have ha : (tripleCharges (sourceA908 + difference 5 1) (sourceB908 + difference 1 5) sourceC908) = raw15014 := by
      apply Matrix.ext; unfold tripleCharges sourceA908 sourceB908 sourceC908 difference raw15014; decide +kernel
    rw [ha]
    exact (canonical15014 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA908 + difference 5 2) (sourceB908 + difference 2 5) sourceC908) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4003) := by
    have ha : (tripleCharges (sourceA908 + difference 5 2) (sourceB908 + difference 2 5) sourceC908) = raw14789 := by
      apply Matrix.ext; unfold tripleCharges sourceA908 sourceB908 sourceC908 difference raw14789; decide +kernel
    rw [ha]
    exact (canonical14789 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA908 + difference 5 3) (sourceB908 + difference 3 5) sourceC908) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4003) := by
    have ha : (tripleCharges (sourceA908 + difference 5 3) (sourceB908 + difference 3 5) sourceC908) = raw15015 := by
      apply Matrix.ext; unfold tripleCharges sourceA908 sourceB908 sourceC908 difference raw15015; decide +kernel
    rw [ha]
    exact (canonical15015 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA908 + difference 5 4) (sourceB908 + difference 4 5) sourceC908) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4001) := by
    have ha : (tripleCharges (sourceA908 + difference 5 4) (sourceB908 + difference 4 5) sourceC908) = raw15016 := by
      apply Matrix.ext; unfold tripleCharges sourceA908 sourceB908 sourceC908 difference raw15016; decide +kernel
    rw [ha]
    exact (canonical15016 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA908 sourceB908 sourceC908
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm908, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic49
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reindexCheck792 : Integer.Sparse.reindex keyMap MixedData.row792 = numericRow792 := by decide +kernel

theorem numericCheck792 (x : Master → ℝ) : Integer.Sparse.eval numericRow792 x =
    (720 : ℝ) * reducedSource792 x := by
  norm_num [numericRow792, reducedSource792, Integer.Sparse.eval, Sparse.eval, nodeValue2732, nodeValue2734, nodeValue2744, nodeValue2776, nodeValue3039, nodeValue3055, nodeValue3110, nodeValue3573, nodeValue3583, nodeValue3584, nodeValue3853, nodeValue3861, nodeValue3862, nodeValue3872, nodeValue3876, nodeValue3877, nodeValue3883, nodeValue3888, nodeValue4001, nodeValue4003, nodeValue4006] <;> ring

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Rows49
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero792 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource792 (mixedVector B) = 0 := by
  have h2732 : mixedVector B (Sum.inr 2732) = Sparse.eval nodeValue2732 (mixedVector B) := by
    change mixedMoment B node2732 node2732Labels = _
    exact sound2732 B hB hF
  have h2734 : mixedVector B (Sum.inr 2734) = Sparse.eval nodeValue2734 (mixedVector B) := by
    change mixedMoment B node2734 node2734Labels = _
    exact sound2734 B hB hF
  have h2744 : mixedVector B (Sum.inr 2744) = Sparse.eval nodeValue2744 (mixedVector B) := by
    change mixedMoment B node2744 node2744Labels = _
    exact sound2744 B hB hF
  have h2776 : mixedVector B (Sum.inr 2776) = Sparse.eval nodeValue2776 (mixedVector B) := by
    change mixedMoment B node2776 node2776Labels = _
    exact sound2776 B hB hF
  have h3039 : mixedVector B (Sum.inr 3039) = Sparse.eval nodeValue3039 (mixedVector B) := by
    change mixedMoment B node3039 node3039Labels = _
    exact sound3039 B hB hF
  have h3055 : mixedVector B (Sum.inr 3055) = Sparse.eval nodeValue3055 (mixedVector B) := by
    change mixedMoment B node3055 node3055Labels = _
    exact sound3055 B hB hF
  have h3110 : mixedVector B (Sum.inr 3110) = Sparse.eval nodeValue3110 (mixedVector B) := by
    change mixedMoment B node3110 node3110Labels = _
    exact sound3110 B hB hF
  have h3573 : mixedVector B (Sum.inr 3573) = Sparse.eval nodeValue3573 (mixedVector B) := by
    change mixedMoment B node3573 node3573Labels = _
    exact sound3573 B hB hF
  have h3583 : mixedVector B (Sum.inr 3583) = Sparse.eval nodeValue3583 (mixedVector B) := by
    change mixedMoment B node3583 node3583Labels = _
    exact sound3583 B hB hF
  have h3584 : mixedVector B (Sum.inr 3584) = Sparse.eval nodeValue3584 (mixedVector B) := by
    change mixedMoment B node3584 node3584Labels = _
    exact sound3584 B hB hF
  have h3853 : mixedVector B (Sum.inr 3853) = Sparse.eval nodeValue3853 (mixedVector B) := by
    change mixedMoment B node3853 node3853Labels = _
    exact sound3853_e B hB hF
  have h3861 : mixedVector B (Sum.inr 3861) = Sparse.eval nodeValue3861 (mixedVector B) := by
    change mixedMoment B node3861 node3861Labels = _
    exact sound3861 B hB hF
  have h3862 : mixedVector B (Sum.inr 3862) = Sparse.eval nodeValue3862 (mixedVector B) := by
    change mixedMoment B node3862 node3862Labels = _
    exact sound3862 B hB hF
  have h3872 : mixedVector B (Sum.inr 3872) = Sparse.eval nodeValue3872 (mixedVector B) := by
    change mixedMoment B node3872 node3872Labels = _
    exact sound3872 B hB hF
  have h3876 : mixedVector B (Sum.inr 3876) = Sparse.eval nodeValue3876 (mixedVector B) := by
    change mixedMoment B node3876 node3876Labels = _
    exact sound3876 B hB hF
  have h3877 : mixedVector B (Sum.inr 3877) = Sparse.eval nodeValue3877 (mixedVector B) := by
    change mixedMoment B node3877 node3877Labels = _
    exact sound3877 B hB hF
  have h3883 : mixedVector B (Sum.inr 3883) = Sparse.eval nodeValue3883 (mixedVector B) := by
    change mixedMoment B node3883 node3883Labels = _
    exact sound3883 B hB hF
  have h3888 : mixedVector B (Sum.inr 3888) = Sparse.eval nodeValue3888 (mixedVector B) := by
    change mixedMoment B node3888 node3888Labels = _
    exact sound3888 B hB hF
  have h4001 : mixedVector B (Sum.inr 4001) = Sparse.eval nodeValue4001 (mixedVector B) := by
    change mixedMoment B node4001 node4001Labels = _
    exact sound4001 B hB hF
  have h4003 : mixedVector B (Sum.inr 4003) = Sparse.eval nodeValue4003 (mixedVector B) := by
    change mixedMoment B node4003 node4003Labels = _
    exact sound4003_e B hB hF
  have h4006 : mixedVector B (Sum.inr 4006) = Sparse.eval nodeValue4006 (mixedVector B) := by
    change mixedMoment B node4006 node4006Labels = _
    exact sound4006 B hB hF
  simpa only [sourceForm908, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2732, h2734, h2744, h2776, h3039, h3055, h3110, h3573, h3583, h3584, h3853, h3861, h3862, h3872, h3876, h3877, h3883, h3888, h4001, h4003, h4006, reducedSource792] using sourceEq908 B hB

theorem rowSound792_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row792 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck792, numericCheck792, reducedZero792 B hB hF, mul_zero]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedSourceBridge.rowSound792_e_oai := @OAI.MUB6.Certificate.MixedSourceBridge.rowSound792_e_oai
