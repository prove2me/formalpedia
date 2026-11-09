-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedSourceBridge.rowSound956_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T03:04:16.494679+00:00
-- url     : https://prove2.me/submissions/bba03b1a-496a-49a6-a3ec-8cd36646eecc

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E086
import Definitions.Def_OAIQ106E093
import Definitions.Def_OAIQ106E094
import Definitions.Def_OAIQ106E194
import Definitions.Def_OAIQ106E195
import Definitions.Def_OAIQ106E101
import Definitions.Def_OAIQ106E115
import Definitions.Def_OAIQ106E119
import Definitions.Def_OAIQ106E123
import Definitions.Def_OAIQ106E129
import Definitions.Def_OAIQ106E140
import Definitions.Def_OAIQ106E141
import Definitions.Def_OAIQ106E142
import Definitions.Def_OAIQ106E144
import Definitions.Def_OAIQ106E145
import Definitions.Def_OAIQ106E146
import Definitions.Def_OAIQ106E147
import Definitions.Def_OAIQ106E148
import Definitions.Def_OAIQ106E170
import Definitions.Def_OAIQ106E171
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound5386_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound5387_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound5388_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound5435_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound5450_e
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical13
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical142
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical18186 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18186 raw18186Labels = mixedMoment B node5490 node5490Labels := by
  calc
    mixedMoment B raw18186 raw18186Labels = mixedMoment B raw18186step0 raw18186step0Labels := by
      have hz : ∀ j, raw18186 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18186step0 = (fun i j => raw18186 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18186step0 raw18186; decide +kernel
      have hl : raw18186step0Labels = raw18186Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18186 raw18186Labels permutation346 hz
    mixedMoment B raw18186step0 raw18186step0Labels = mixedMoment B raw18186step1 raw18186step1Labels := by
      have ha : raw18186step1 = (fun i j => raw18186step0 (permutation75 i) (permutation6 j)) := by apply Matrix.ext; unfold raw18186step1 raw18186step0; decide +kernel
      have hl : raw18186step1Labels = raw18186step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18186step0 raw18186step0Labels permutation75 permutation6
    mixedMoment B raw18186step1 raw18186step1Labels = mixedMoment B raw18186step2 raw18186step2Labels := by
      have ha : raw18186step2 = -raw18186step1 := by apply Matrix.ext; change ∀ i j, raw18186step2 i j = -(raw18186step1 i j); unfold raw18186step2 raw18186step1; decide +kernel
      have hl : raw18186step2Labels = raw18186step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18186step2 raw18186step2Labels = mixedMoment B raw18186step3 raw18186step3Labels := by
      have ha : raw18186step3 = raw18186step2 := by apply Matrix.ext; unfold raw18186step3 raw18186step2; decide +kernel
      have hl : raw18186step2Labels = labelEmbedding9 ∘ raw18186step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18186step2 raw18186step2Labels raw18186step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5490 node5490Labels := by rfl

theorem canonical18191 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18191 raw18191Labels = mixedMoment B node5435 node5435Labels := by
  calc
    mixedMoment B raw18191 raw18191Labels = mixedMoment B raw18191step0 raw18191step0Labels := by
      have hz : ∀ j, raw18191 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18191step0 = (fun i j => raw18191 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18191step0 raw18191; decide +kernel
      have hl : raw18191step0Labels = raw18191Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18191 raw18191Labels permutation346 hz
    mixedMoment B raw18191step0 raw18191step0Labels = mixedMoment B raw18191step1 raw18191step1Labels := by
      have ha : raw18191step1 = (fun i j => raw18191step0 (permutation79 i) (permutation4 j)) := by apply Matrix.ext; unfold raw18191step1 raw18191step0; decide +kernel
      have hl : raw18191step1Labels = raw18191step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18191step0 raw18191step0Labels permutation79 permutation4
    mixedMoment B raw18191step1 raw18191step1Labels = mixedMoment B raw18191step2 raw18191step2Labels := by
      have ha : raw18191step2 = raw18191step1 := by apply Matrix.ext; unfold raw18191step2 raw18191step1; decide +kernel
      have hl : raw18191step1Labels = labelEmbedding7 ∘ raw18191step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18191step1 raw18191step1Labels raw18191step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5435 node5435Labels := by rfl

theorem canonical18196 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18196 raw18196Labels = mixedMoment B node5431 node5431Labels := by
  calc
    mixedMoment B raw18196 raw18196Labels = mixedMoment B raw18196step0 raw18196step0Labels := by
      have ha : raw18196step0 = (fun i j => raw18196 (permutation212 i) (permutation5 j)) := by apply Matrix.ext; unfold raw18196step0 raw18196; decide +kernel
      have hl : raw18196step0Labels = raw18196Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18196 raw18196Labels permutation212 permutation5
    mixedMoment B raw18196step0 raw18196step0Labels = mixedMoment B raw18196step1 raw18196step1Labels := by
      have ha : raw18196step1 = -raw18196step0 := by apply Matrix.ext; change ∀ i j, raw18196step1 i j = -(raw18196step0 i j); unfold raw18196step1 raw18196step0; decide +kernel
      have hl : raw18196step1Labels = raw18196step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18196step1 raw18196step1Labels = mixedMoment B raw18196step2 raw18196step2Labels := by
      have ha : raw18196step2 = raw18196step1 := by apply Matrix.ext; unfold raw18196step2 raw18196step1; decide +kernel
      have hl : raw18196step1Labels = labelEmbedding8 ∘ raw18196step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18196step1 raw18196step1Labels raw18196step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5431 node5431Labels := by rfl

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

theorem canonical18206 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18206 raw18206Labels = mixedMoment B node5438 node5438Labels := by
  calc
    mixedMoment B raw18206 raw18206Labels = mixedMoment B raw18206step0 raw18206step0Labels := by
      have hz : ∀ j, raw18206 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18206step0 = (fun i j => raw18206 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18206step0 raw18206; decide +kernel
      have hl : raw18206step0Labels = raw18206Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18206 raw18206Labels permutation346 hz
    mixedMoment B raw18206step0 raw18206step0Labels = mixedMoment B raw18206step1 raw18206step1Labels := by
      have ha : raw18206step1 = (fun i j => raw18206step0 (permutation39 i) (permutation5 j)) := by apply Matrix.ext; unfold raw18206step1 raw18206step0; decide +kernel
      have hl : raw18206step1Labels = raw18206step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18206step0 raw18206step0Labels permutation39 permutation5
    mixedMoment B raw18206step1 raw18206step1Labels = mixedMoment B raw18206step2 raw18206step2Labels := by
      have ha : raw18206step2 = -raw18206step1 := by apply Matrix.ext; change ∀ i j, raw18206step2 i j = -(raw18206step1 i j); unfold raw18206step2 raw18206step1; decide +kernel
      have hl : raw18206step2Labels = raw18206step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18206step2 raw18206step2Labels = mixedMoment B raw18206step3 raw18206step3Labels := by
      have ha : raw18206step3 = raw18206step2 := by apply Matrix.ext; unfold raw18206step3 raw18206step2; decide +kernel
      have hl : raw18206step2Labels = labelEmbedding8 ∘ raw18206step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18206step2 raw18206step2Labels raw18206step3Labels labelEmbedding8 hl
    _ = mixedMoment B node5438 node5438Labels := by rfl

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

theorem canonical18486 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18486 raw18486Labels = mixedMoment B node5489 node5489Labels := by
  calc
    mixedMoment B raw18486 raw18486Labels = mixedMoment B raw18486step0 raw18486step0Labels := by
      have ha : raw18486step0 = (fun i j => raw18486 (permutation269 i) (permutation7 j)) := by apply Matrix.ext; unfold raw18486step0 raw18486; decide +kernel
      have hl : raw18486step0Labels = raw18486Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18486 raw18486Labels permutation269 permutation7
    mixedMoment B raw18486step0 raw18486step0Labels = mixedMoment B raw18486step1 raw18486step1Labels := by
      have ha : raw18486step1 = -raw18486step0 := by apply Matrix.ext; change ∀ i j, raw18486step1 i j = -(raw18486step0 i j); unfold raw18486step1 raw18486step0; decide +kernel
      have hl : raw18486step1Labels = raw18486step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18486step1 raw18486step1Labels = mixedMoment B raw18486step2 raw18486step2Labels := by
      have ha : raw18486step2 = raw18486step1 := by apply Matrix.ext; unfold raw18486step2 raw18486step1; decide +kernel
      have hl : raw18486step1Labels = labelEmbedding10 ∘ raw18486step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18486step1 raw18486step1Labels raw18486step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5489 node5489Labels := by rfl

theorem canonical18487 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18487 raw18487Labels = mixedMoment B node5490 node5490Labels := by
  calc
    mixedMoment B raw18487 raw18487Labels = mixedMoment B raw18487step0 raw18487step0Labels := by
      have hz : ∀ j, raw18487 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18487step0 = (fun i j => raw18487 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18487step0 raw18487; decide +kernel
      have hl : raw18487step0Labels = raw18487Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18487 raw18487Labels permutation346 hz
    mixedMoment B raw18487step0 raw18487step0Labels = mixedMoment B raw18487step1 raw18487step1Labels := by
      have ha : raw18487step1 = (fun i j => raw18487step0 (permutation74 i) (permutation6 j)) := by apply Matrix.ext; unfold raw18487step1 raw18487step0; decide +kernel
      have hl : raw18487step1Labels = raw18487step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18487step0 raw18487step0Labels permutation74 permutation6
    mixedMoment B raw18487step1 raw18487step1Labels = mixedMoment B raw18487step2 raw18487step2Labels := by
      have ha : raw18487step2 = -raw18487step1 := by apply Matrix.ext; change ∀ i j, raw18487step2 i j = -(raw18487step1 i j); unfold raw18487step2 raw18487step1; decide +kernel
      have hl : raw18487step2Labels = raw18487step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18487step2 raw18487step2Labels = mixedMoment B raw18487step3 raw18487step3Labels := by
      have ha : raw18487step3 = raw18487step2 := by apply Matrix.ext; unfold raw18487step3 raw18487step2; decide +kernel
      have hl : raw18487step2Labels = labelEmbedding9 ∘ raw18487step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18487step2 raw18487step2Labels raw18487step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5490 node5490Labels := by rfl

theorem canonical18488 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18488 raw18488Labels = mixedMoment B node5493 node5493Labels := by
  calc
    mixedMoment B raw18488 raw18488Labels = mixedMoment B raw18488step0 raw18488step0Labels := by
      have hz : ∀ j, raw18488 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw18488step0 = (fun i j => raw18488 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw18488step0 raw18488; decide +kernel
      have hl : raw18488step0Labels = raw18488Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18488 raw18488Labels permutation590 hz
    mixedMoment B raw18488step0 raw18488step0Labels = mixedMoment B raw18488step1 raw18488step1Labels := by
      have hz : ∀ j, raw18488step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw18488step1 = (fun i j => raw18488step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw18488step1 raw18488step0; decide +kernel
      have hl : raw18488step1Labels = raw18488step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18488step0 raw18488step0Labels permutation80 hz
    mixedMoment B raw18488step1 raw18488step1Labels = mixedMoment B raw18488step2 raw18488step2Labels := by
      have ha : raw18488step2 = (fun i j => raw18488step1 (permutation14 i) (permutation7 j)) := by apply Matrix.ext; unfold raw18488step2 raw18488step1; decide +kernel
      have hl : raw18488step2Labels = raw18488step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18488step1 raw18488step1Labels permutation14 permutation7
    mixedMoment B raw18488step2 raw18488step2Labels = mixedMoment B raw18488step3 raw18488step3Labels := by
      have ha : raw18488step3 = -raw18488step2 := by apply Matrix.ext; change ∀ i j, raw18488step3 i j = -(raw18488step2 i j); unfold raw18488step3 raw18488step2; decide +kernel
      have hl : raw18488step3Labels = raw18488step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18488step3 raw18488step3Labels = mixedMoment B raw18488step4 raw18488step4Labels := by
      have ha : raw18488step4 = raw18488step3 := by apply Matrix.ext; unfold raw18488step4 raw18488step3; decide +kernel
      have hl : raw18488step3Labels = labelEmbedding10 ∘ raw18488step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18488step3 raw18488step3Labels raw18488step4Labels labelEmbedding10 hl
    _ = mixedMoment B node5493 node5493Labels := by rfl

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

theorem canonical18490 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18490 raw18490Labels = mixedMoment B node5406 node5406Labels := by
  calc
    mixedMoment B raw18490 raw18490Labels = mixedMoment B raw18490step0 raw18490step0Labels := by
      have ha : raw18490step0 = (fun i j => raw18490 (permutation185 i) (permutation5 j)) := by apply Matrix.ext; unfold raw18490step0 raw18490; decide +kernel
      have hl : raw18490step0Labels = raw18490Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18490 raw18490Labels permutation185 permutation5
    mixedMoment B raw18490step0 raw18490step0Labels = mixedMoment B raw18490step1 raw18490step1Labels := by
      have ha : raw18490step1 = -raw18490step0 := by apply Matrix.ext; change ∀ i j, raw18490step1 i j = -(raw18490step0 i j); unfold raw18490step1 raw18490step0; decide +kernel
      have hl : raw18490step1Labels = raw18490step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18490step1 raw18490step1Labels = mixedMoment B raw18490step2 raw18490step2Labels := by
      have ha : raw18490step2 = raw18490step1 := by apply Matrix.ext; unfold raw18490step2 raw18490step1; decide +kernel
      have hl : raw18490step1Labels = labelEmbedding8 ∘ raw18490step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18490step1 raw18490step1Labels raw18490step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5406 node5406Labels := by rfl

theorem canonical18491 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18491 raw18491Labels = mixedMoment B node5435 node5435Labels := by
  calc
    mixedMoment B raw18491 raw18491Labels = mixedMoment B raw18491step0 raw18491step0Labels := by
      have hz : ∀ j, raw18491 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18491step0 = (fun i j => raw18491 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18491step0 raw18491; decide +kernel
      have hl : raw18491step0Labels = raw18491Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18491 raw18491Labels permutation346 hz
    mixedMoment B raw18491step0 raw18491step0Labels = mixedMoment B raw18491step1 raw18491step1Labels := by
      have ha : raw18491step1 = (fun i j => raw18491step0 (permutation77 i) (permutation4 j)) := by apply Matrix.ext; unfold raw18491step1 raw18491step0; decide +kernel
      have hl : raw18491step1Labels = raw18491step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18491step0 raw18491step0Labels permutation77 permutation4
    mixedMoment B raw18491step1 raw18491step1Labels = mixedMoment B raw18491step2 raw18491step2Labels := by
      have ha : raw18491step2 = raw18491step1 := by apply Matrix.ext; unfold raw18491step2 raw18491step1; decide +kernel
      have hl : raw18491step1Labels = labelEmbedding7 ∘ raw18491step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18491step1 raw18491step1Labels raw18491step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5435 node5435Labels := by rfl

theorem canonical18492 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18492 raw18492Labels = mixedMoment B node5453 node5453Labels := by
  calc
    mixedMoment B raw18492 raw18492Labels = mixedMoment B raw18492step0 raw18492step0Labels := by
      have hz : ∀ j, raw18492 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw18492step0 = (fun i j => raw18492 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw18492step0 raw18492; decide +kernel
      have hl : raw18492step0Labels = raw18492Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18492 raw18492Labels permutation590 hz
    mixedMoment B raw18492step0 raw18492step0Labels = mixedMoment B raw18492step1 raw18492step1Labels := by
      have hz : ∀ j, raw18492step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw18492step1 = (fun i j => raw18492step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw18492step1 raw18492step0; decide +kernel
      have hl : raw18492step1Labels = raw18492step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18492step0 raw18492step0Labels permutation80 hz
    mixedMoment B raw18492step1 raw18492step1Labels = mixedMoment B raw18492step2 raw18492step2Labels := by
      have ha : raw18492step2 = (fun i j => raw18492step1 (permutation17 i) (permutation4 j)) := by apply Matrix.ext; unfold raw18492step2 raw18492step1; decide +kernel
      have hl : raw18492step2Labels = raw18492step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18492step1 raw18492step1Labels permutation17 permutation4
    mixedMoment B raw18492step2 raw18492step2Labels = mixedMoment B raw18492step3 raw18492step3Labels := by
      have ha : raw18492step3 = raw18492step2 := by apply Matrix.ext; unfold raw18492step3 raw18492step2; decide +kernel
      have hl : raw18492step2Labels = labelEmbedding7 ∘ raw18492step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18492step2 raw18492step2Labels raw18492step3Labels labelEmbedding7 hl
    _ = mixedMoment B node5453 node5453Labels := by rfl

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

theorem canonical18494 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18494 raw18494Labels = mixedMoment B node5386 node5386Labels := by
  calc
    mixedMoment B raw18494 raw18494Labels = mixedMoment B raw18494step0 raw18494step0Labels := by
      have ha : raw18494step0 = (fun i j => raw18494 (permutation269 i) (permutation2 j)) := by apply Matrix.ext; unfold raw18494step0 raw18494; decide +kernel
      have hl : raw18494step0Labels = raw18494Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18494 raw18494Labels permutation269 permutation2
    _ = mixedMoment B node5386 node5386Labels := by rfl

theorem canonical18495 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18495 raw18495Labels = mixedMoment B node5431 node5431Labels := by
  calc
    mixedMoment B raw18495 raw18495Labels = mixedMoment B raw18495step0 raw18495step0Labels := by
      have ha : raw18495step0 = (fun i j => raw18495 (permutation234 i) (permutation5 j)) := by apply Matrix.ext; unfold raw18495step0 raw18495; decide +kernel
      have hl : raw18495step0Labels = raw18495Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18495 raw18495Labels permutation234 permutation5
    mixedMoment B raw18495step0 raw18495step0Labels = mixedMoment B raw18495step1 raw18495step1Labels := by
      have ha : raw18495step1 = -raw18495step0 := by apply Matrix.ext; change ∀ i j, raw18495step1 i j = -(raw18495step0 i j); unfold raw18495step1 raw18495step0; decide +kernel
      have hl : raw18495step1Labels = raw18495step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18495step1 raw18495step1Labels = mixedMoment B raw18495step2 raw18495step2Labels := by
      have ha : raw18495step2 = raw18495step1 := by apply Matrix.ext; unfold raw18495step2 raw18495step1; decide +kernel
      have hl : raw18495step1Labels = labelEmbedding8 ∘ raw18495step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18495step1 raw18495step1Labels raw18495step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5431 node5431Labels := by rfl

theorem canonical18496 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18496 raw18496Labels = mixedMoment B node5450 node5450Labels := by
  calc
    mixedMoment B raw18496 raw18496Labels = mixedMoment B raw18496step0 raw18496step0Labels := by
      have hz : ∀ j, raw18496 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw18496step0 = (fun i j => raw18496 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw18496step0 raw18496; decide +kernel
      have hl : raw18496step0Labels = raw18496Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18496 raw18496Labels permutation590 hz
    mixedMoment B raw18496step0 raw18496step0Labels = mixedMoment B raw18496step1 raw18496step1Labels := by
      have ha : raw18496step1 = (fun i j => raw18496step0 (permutation35 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18496step1 raw18496step0; decide +kernel
      have hl : raw18496step1Labels = raw18496step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18496step0 raw18496step0Labels permutation35 permutation3
    mixedMoment B raw18496step1 raw18496step1Labels = mixedMoment B raw18496step2 raw18496step2Labels := by
      have ha : raw18496step2 = raw18496step1 := by apply Matrix.ext; unfold raw18496step2 raw18496step1; decide +kernel
      have hl : raw18496step1Labels = labelEmbedding6 ∘ raw18496step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18496step1 raw18496step1Labels raw18496step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5450 node5450Labels := by rfl

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

theorem canonical18499 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18499 raw18499Labels = mixedMoment B node5401 node5401Labels := by
  calc
    mixedMoment B raw18499 raw18499Labels = mixedMoment B raw18499step0 raw18499step0Labels := by
      have ha : raw18499step0 = (fun i j => raw18499 (permutation179 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18499step0 raw18499; decide +kernel
      have hl : raw18499step0Labels = raw18499Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18499 raw18499Labels permutation179 permutation3
    mixedMoment B raw18499step0 raw18499step0Labels = mixedMoment B raw18499step1 raw18499step1Labels := by
      have ha : raw18499step1 = raw18499step0 := by apply Matrix.ext; unfold raw18499step1 raw18499step0; decide +kernel
      have hl : raw18499step0Labels = labelEmbedding6 ∘ raw18499step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18499step0 raw18499step0Labels raw18499step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5401 node5401Labels := by rfl

theorem canonical18500 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18500 raw18500Labels = mixedMoment B node5438 node5438Labels := by
  calc
    mixedMoment B raw18500 raw18500Labels = mixedMoment B raw18500step0 raw18500step0Labels := by
      have hz : ∀ j, raw18500 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18500step0 = (fun i j => raw18500 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18500step0 raw18500; decide +kernel
      have hl : raw18500step0Labels = raw18500Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18500 raw18500Labels permutation346 hz
    mixedMoment B raw18500step0 raw18500step0Labels = mixedMoment B raw18500step1 raw18500step1Labels := by
      have ha : raw18500step1 = (fun i j => raw18500step0 (permutation45 i) (permutation5 j)) := by apply Matrix.ext; unfold raw18500step1 raw18500step0; decide +kernel
      have hl : raw18500step1Labels = raw18500step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18500step0 raw18500step0Labels permutation45 permutation5
    mixedMoment B raw18500step1 raw18500step1Labels = mixedMoment B raw18500step2 raw18500step2Labels := by
      have ha : raw18500step2 = -raw18500step1 := by apply Matrix.ext; change ∀ i j, raw18500step2 i j = -(raw18500step1 i j); unfold raw18500step2 raw18500step1; decide +kernel
      have hl : raw18500step2Labels = raw18500step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18500step2 raw18500step2Labels = mixedMoment B raw18500step3 raw18500step3Labels := by
      have ha : raw18500step3 = raw18500step2 := by apply Matrix.ext; unfold raw18500step3 raw18500step2; decide +kernel
      have hl : raw18500step2Labels = labelEmbedding8 ∘ raw18500step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18500step2 raw18500step2Labels raw18500step3Labels labelEmbedding8 hl
    _ = mixedMoment B node5438 node5438Labels := by rfl

theorem canonical18501 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18501 raw18501Labels = mixedMoment B node5451 node5451Labels := by
  calc
    mixedMoment B raw18501 raw18501Labels = mixedMoment B raw18501step0 raw18501step0Labels := by
      have hz : ∀ j, raw18501 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw18501step0 = (fun i j => raw18501 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw18501step0 raw18501; decide +kernel
      have hl : raw18501step0Labels = raw18501Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18501 raw18501Labels permutation590 hz
    mixedMoment B raw18501step0 raw18501step0Labels = mixedMoment B raw18501step1 raw18501step1Labels := by
      have hz : ∀ j, raw18501step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw18501step1 = (fun i j => raw18501step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw18501step1 raw18501step0; decide +kernel
      have hl : raw18501step1Labels = raw18501step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18501step0 raw18501step0Labels permutation80 hz
    mixedMoment B raw18501step1 raw18501step1Labels = mixedMoment B raw18501step2 raw18501step2Labels := by
      have ha : raw18501step2 = (fun i j => raw18501step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18501step2 raw18501step1; decide +kernel
      have hl : raw18501step2Labels = raw18501step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18501step1 raw18501step1Labels permutation9 permutation3
    mixedMoment B raw18501step2 raw18501step2Labels = mixedMoment B raw18501step3 raw18501step3Labels := by
      have ha : raw18501step3 = raw18501step2 := by apply Matrix.ext; unfold raw18501step3 raw18501step2; decide +kernel
      have hl : raw18501step2Labels = labelEmbedding6 ∘ raw18501step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18501step2 raw18501step2Labels raw18501step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5451 node5451Labels := by rfl

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

theorem canonical18504 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18504 raw18504Labels = mixedMoment B node5401 node5401Labels := by
  calc
    mixedMoment B raw18504 raw18504Labels = mixedMoment B raw18504step0 raw18504step0Labels := by
      have ha : raw18504step0 = (fun i j => raw18504 (permutation177 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18504step0 raw18504; decide +kernel
      have hl : raw18504step0Labels = raw18504Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18504 raw18504Labels permutation177 permutation3
    mixedMoment B raw18504step0 raw18504step0Labels = mixedMoment B raw18504step1 raw18504step1Labels := by
      have ha : raw18504step1 = raw18504step0 := by apply Matrix.ext; unfold raw18504step1 raw18504step0; decide +kernel
      have hl : raw18504step0Labels = labelEmbedding6 ∘ raw18504step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18504step0 raw18504step0Labels raw18504step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5401 node5401Labels := by rfl

theorem canonical18505 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18505 raw18505Labels = mixedMoment B node5451 node5451Labels := by
  calc
    mixedMoment B raw18505 raw18505Labels = mixedMoment B raw18505step0 raw18505step0Labels := by
      have hz : ∀ j, raw18505 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw18505step0 = (fun i j => raw18505 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw18505step0 raw18505; decide +kernel
      have hl : raw18505step0Labels = raw18505Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18505 raw18505Labels permutation590 hz
    mixedMoment B raw18505step0 raw18505step0Labels = mixedMoment B raw18505step1 raw18505step1Labels := by
      have hz : ∀ j, raw18505step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw18505step1 = (fun i j => raw18505step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw18505step1 raw18505step0; decide +kernel
      have hl : raw18505step1Labels = raw18505step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18505step0 raw18505step0Labels permutation80 hz
    mixedMoment B raw18505step1 raw18505step1Labels = mixedMoment B raw18505step2 raw18505step2Labels := by
      have ha : raw18505step2 = (fun i j => raw18505step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18505step2 raw18505step1; decide +kernel
      have hl : raw18505step2Labels = raw18505step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18505step1 raw18505step1Labels permutation8 permutation3
    mixedMoment B raw18505step2 raw18505step2Labels = mixedMoment B raw18505step3 raw18505step3Labels := by
      have ha : raw18505step3 = raw18505step2 := by apply Matrix.ext; unfold raw18505step3 raw18505step2; decide +kernel
      have hl : raw18505step2Labels = labelEmbedding6 ∘ raw18505step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18505step2 raw18505step2Labels raw18505step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5451 node5451Labels := by rfl

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

theorem canonical2475 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2475 raw2475Labels = mixedMoment B node5401 node5401Labels := by
  calc
    mixedMoment B raw2475 raw2475Labels = mixedMoment B raw2475step0 raw2475step0Labels := by
      have ha : raw2475step0 = (fun i j => raw2475 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2475step0 raw2475; decide +kernel
      have hl : raw2475step0Labels = raw2475Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2475 raw2475Labels permutation152 permutation4
    mixedMoment B raw2475step0 raw2475step0Labels = mixedMoment B raw2475step1 raw2475step1Labels := by
      have ha : raw2475step1 = raw2475step0 := by apply Matrix.ext; unfold raw2475step1 raw2475step0; decide +kernel
      have hl : raw2475step0Labels = labelEmbedding7 ∘ raw2475step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2475step0 raw2475step0Labels raw2475step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5401 node5401Labels := by rfl

theorem canonical2476 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2476 raw2476Labels = mixedMoment B node3787 node3787Labels := by
  calc
    mixedMoment B raw2476 raw2476Labels = mixedMoment B raw2476step0 raw2476step0Labels := by
      have ha : raw2476step0 = (fun i j => raw2476 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2476step0 raw2476; decide +kernel
      have hl : raw2476step0Labels = raw2476Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2476 raw2476Labels permutation152 permutation4
    _ = mixedMoment B node3787 node3787Labels := by rfl

theorem canonical2477 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2477 raw2477Labels = mixedMoment B node3804 node3804Labels := by
  calc
    mixedMoment B raw2477 raw2477Labels = mixedMoment B raw2477step0 raw2477step0Labels := by
      have ha : raw2477step0 = (fun i j => raw2477 (permutation158 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2477step0 raw2477; decide +kernel
      have hl : raw2477step0Labels = raw2477Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2477 raw2477Labels permutation158 permutation6
    mixedMoment B raw2477step0 raw2477step0Labels = mixedMoment B raw2477step1 raw2477step1Labels := by
      have ha : raw2477step1 = -raw2477step0 := by apply Matrix.ext; change ∀ i j, raw2477step1 i j = -(raw2477step0 i j); unfold raw2477step1 raw2477step0; decide +kernel
      have hl : raw2477step1Labels = raw2477step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2477step1 raw2477step1Labels = mixedMoment B raw2477step2 raw2477step2Labels := by
      have ha : raw2477step2 = raw2477step1 := by apply Matrix.ext; unfold raw2477step2 raw2477step1; decide +kernel
      have hl : raw2477step1Labels = labelEmbedding1 ∘ raw2477step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2477step1 raw2477step1Labels raw2477step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3804 node3804Labels := by rfl

theorem canonical2487 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2487 raw2487Labels = mixedMoment B node5406 node5406Labels := by
  calc
    mixedMoment B raw2487 raw2487Labels = mixedMoment B raw2487step0 raw2487step0Labels := by
      have ha : raw2487step0 = (fun i j => raw2487 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2487step0 raw2487; decide +kernel
      have hl : raw2487step0Labels = raw2487Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2487 raw2487Labels permutation152 permutation4
    mixedMoment B raw2487step0 raw2487step0Labels = mixedMoment B raw2487step1 raw2487step1Labels := by
      have ha : raw2487step1 = raw2487step0 := by apply Matrix.ext; unfold raw2487step1 raw2487step0; decide +kernel
      have hl : raw2487step0Labels = labelEmbedding7 ∘ raw2487step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2487step0 raw2487step0Labels raw2487step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5406 node5406Labels := by rfl

theorem canonical2488 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2488 raw2488Labels = mixedMoment B node3801 node3801Labels := by
  calc
    mixedMoment B raw2488 raw2488Labels = mixedMoment B raw2488step0 raw2488step0Labels := by
      have ha : raw2488step0 = (fun i j => raw2488 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2488step0 raw2488; decide +kernel
      have hl : raw2488step0Labels = raw2488Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2488 raw2488Labels permutation152 permutation4
    _ = mixedMoment B node3801 node3801Labels := by rfl

theorem canonical2489 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2489 raw2489Labels = mixedMoment B node3812 node3812Labels := by
  calc
    mixedMoment B raw2489 raw2489Labels = mixedMoment B raw2489step0 raw2489step0Labels := by
      have ha : raw2489step0 = (fun i j => raw2489 (permutation170 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2489step0 raw2489; decide +kernel
      have hl : raw2489step0Labels = raw2489Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2489 raw2489Labels permutation170 permutation6
    mixedMoment B raw2489step0 raw2489step0Labels = mixedMoment B raw2489step1 raw2489step1Labels := by
      have ha : raw2489step1 = -raw2489step0 := by apply Matrix.ext; change ∀ i j, raw2489step1 i j = -(raw2489step0 i j); unfold raw2489step1 raw2489step0; decide +kernel
      have hl : raw2489step1Labels = raw2489step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2489step1 raw2489step1Labels = mixedMoment B raw2489step2 raw2489step2Labels := by
      have ha : raw2489step2 = raw2489step1 := by apply Matrix.ext; unfold raw2489step2 raw2489step1; decide +kernel
      have hl : raw2489step1Labels = labelEmbedding1 ∘ raw2489step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2489step1 raw2489step1Labels raw2489step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3812 node3812Labels := by rfl

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

theorem canonical2559 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2559 raw2559Labels = mixedMoment B node5451 node5451Labels := by
  calc
    mixedMoment B raw2559 raw2559Labels = mixedMoment B raw2559step0 raw2559step0Labels := by
      have ha : raw2559step0 = (fun i j => raw2559 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2559step0 raw2559; decide +kernel
      have hl : raw2559step0Labels = raw2559Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2559 raw2559Labels permutation8 permutation4
    mixedMoment B raw2559step0 raw2559step0Labels = mixedMoment B raw2559step1 raw2559step1Labels := by
      have ha : raw2559step1 = raw2559step0 := by apply Matrix.ext; unfold raw2559step1 raw2559step0; decide +kernel
      have hl : raw2559step0Labels = labelEmbedding7 ∘ raw2559step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2559step0 raw2559step0Labels raw2559step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5451 node5451Labels := by rfl

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

theorem canonical2560 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2560 raw2560Labels = mixedMoment B node3888 node3888Labels := by
  calc
    mixedMoment B raw2560 raw2560Labels = mixedMoment B raw2560step0 raw2560step0Labels := by
      have ha : raw2560step0 = (fun i j => raw2560 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2560step0 raw2560; decide +kernel
      have hl : raw2560step0Labels = raw2560Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2560 raw2560Labels permutation8 permutation4
    _ = mixedMoment B node3888 node3888Labels := by rfl

theorem canonical2561 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2561 raw2561Labels = mixedMoment B node3913 node3913Labels := by
  calc
    mixedMoment B raw2561 raw2561Labels = mixedMoment B raw2561step0 raw2561step0Labels := by
      have ha : raw2561step0 = (fun i j => raw2561 (permutation10 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2561step0 raw2561; decide +kernel
      have hl : raw2561step0Labels = raw2561Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2561 raw2561Labels permutation10 permutation6
    mixedMoment B raw2561step0 raw2561step0Labels = mixedMoment B raw2561step1 raw2561step1Labels := by
      have ha : raw2561step1 = -raw2561step0 := by apply Matrix.ext; change ∀ i j, raw2561step1 i j = -(raw2561step0 i j); unfold raw2561step1 raw2561step0; decide +kernel
      have hl : raw2561step1Labels = raw2561step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2561step1 raw2561step1Labels = mixedMoment B raw2561step2 raw2561step2Labels := by
      have ha : raw2561step2 = raw2561step1 := by apply Matrix.ext; unfold raw2561step2 raw2561step1; decide +kernel
      have hl : raw2561step1Labels = labelEmbedding1 ∘ raw2561step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2561step1 raw2561step1Labels raw2561step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3913 node3913Labels := by rfl

theorem canonical2565 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2565 raw2565Labels = mixedMoment B node5453 node5453Labels := by
  calc
    _ = mixedMoment B node5453 node5453Labels := by rfl

theorem canonical2566 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2566 raw2566Labels = mixedMoment B node3912 node3912Labels := by
  calc
    _ = mixedMoment B node3912 node3912Labels := by rfl

theorem canonical2567 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2567 raw2567Labels = mixedMoment B node3912 node3912Labels := by
  calc
    mixedMoment B raw2567 raw2567Labels = mixedMoment B raw2567step0 raw2567step0Labels := by
      have ha : raw2567step0 = (fun i j => raw2567 (permutation29 i) (permutation3 j)) := by apply Matrix.ext; unfold raw2567step0 raw2567; decide +kernel
      have hl : raw2567step0Labels = raw2567Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2567 raw2567Labels permutation29 permutation3
    mixedMoment B raw2567step0 raw2567step0Labels = mixedMoment B raw2567step1 raw2567step1Labels := by
      have ha : raw2567step1 = -raw2567step0 := by apply Matrix.ext; change ∀ i j, raw2567step1 i j = -(raw2567step0 i j); unfold raw2567step1 raw2567step0; decide +kernel
      have hl : raw2567step1Labels = raw2567step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2567step1 raw2567step1Labels = mixedMoment B raw2567step2 raw2567step2Labels := by
      have ha : raw2567step2 = raw2567step1 := by apply Matrix.ext; unfold raw2567step2 raw2567step1; decide +kernel
      have hl : raw2567step1Labels = labelEmbedding1 ∘ raw2567step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2567step1 raw2567step1Labels raw2567step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3912 node3912Labels := by rfl

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

theorem canonical550 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw550 raw550Labels = mixedMoment B node3912 node3912Labels := by
  calc
    mixedMoment B raw550 raw550Labels = mixedMoment B raw550step0 raw550step0Labels := by
      have ha : raw550step0 = (fun i j => raw550 (permutation8 i) (permutation5 j)) := by apply Matrix.ext; unfold raw550step0 raw550; decide +kernel
      have hl : raw550step0Labels = raw550Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw550 raw550Labels permutation8 permutation5
    mixedMoment B raw550step0 raw550step0Labels = mixedMoment B raw550step1 raw550step1Labels := by
      have ha : raw550step1 = raw550step0 := by apply Matrix.ext; unfold raw550step1 raw550step0; decide +kernel
      have hl : raw550step0Labels = labelEmbedding1 ∘ raw550step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw550step0 raw550step0Labels raw550step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3912 node3912Labels := by rfl

theorem canonical551 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw551 raw551Labels = mixedMoment B node505 node505Labels := by
  calc
    mixedMoment B raw551 raw551Labels = mixedMoment B raw551step0 raw551step0Labels := by
      have ha : raw551step0 = (fun i j => raw551 (permutation29 i) (permutation4 j)) := by apply Matrix.ext; unfold raw551step0 raw551; decide +kernel
      have hl : raw551step0Labels = raw551Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw551 raw551Labels permutation29 permutation4
    mixedMoment B raw551step0 raw551step0Labels = mixedMoment B raw551step1 raw551step1Labels := by
      have ha : raw551step1 = -raw551step0 := by apply Matrix.ext; change ∀ i j, raw551step1 i j = -(raw551step0 i j); unfold raw551step1 raw551step0; decide +kernel
      have hl : raw551step1Labels = raw551step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node505 node505Labels := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical128
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical4117 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4117 = injectiveMoment H node207 := by
  rfl

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

theorem canonical4141 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4141 = injectiveMoment H node41 := by
  rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical160
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical5141 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5141 = injectiveMoment H node46 := by
  rfl

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

theorem canonical5169 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5169 = injectiveMoment H node4 := by
  clear _hH
  calc
    injectiveMoment H raw5169 = injectiveMoment H raw5169step0 := by
      have hz : ∀ j, raw5169 (permutation21 0) j = 0 := by decide +kernel
      have heq : raw5169step0 = (fun i j => raw5169 (permutation21 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw5169 permutation21 hz
    injectiveMoment H raw5169step0 = injectiveMoment H raw5169step1 := by
      have hz : ∀ j, raw5169step0 (permutation5 0) j = 0 := by decide +kernel
      have heq : raw5169step1 = (fun i j => raw5169step0 (permutation5 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw5169step0 permutation5 hz
    _ = injectiveMoment H node4 := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical162
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

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

theorem canonical5204 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5204 = injectiveMoment H node11 := by
  calc
    injectiveMoment H raw5204 = injectiveMoment H raw5204step0 := by
      have hz : ∀ j, raw5204 (permutation27 0) j = 0 := by decide +kernel
      have heq : raw5204step0 = (fun i j => raw5204 (permutation27 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw5204 permutation27 hz
    _ = injectiveMoment H node11 := by rfl

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

end MUB6.Certificate.PairSemantics

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

theorem singlePair505 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node505 node505Labels = Sparse.eval singlePairValue505 (familyPairVector B) := by
  have hp := single_label_three B hB node505
  have hl : node505Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node505 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node505 (EqualityPatterns.family3.label 0) = PairSemantics.raw7980 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node505 PairSemantics.raw7980; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7980 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node505 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value11 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node505 (EqualityPatterns.family3.label 1) = PairSemantics.raw5204 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node505 PairSemantics.raw5204; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5204 hH).trans (PairSemantics.sound11 hH)
  have hm2 : familyPairMoment B (groupedColumns node505 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value11 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node505 (EqualityPatterns.family3.label 2) = PairSemantics.raw9013 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node505 PairSemantics.raw9013; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical9013 hH).trans (PairSemantics.sound11 hH)
  have hm3 : familyPairMoment B (groupedColumns node505 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value4 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node505 (EqualityPatterns.family3.label 3) = PairSemantics.raw5169 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node505 PairSemantics.raw5169; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5169 hH).trans (PairSemantics.sound4 hH)
  have hm4 : familyPairMoment B (groupedColumns node505 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value207 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node505 (EqualityPatterns.family3.label 4) = PairSemantics.raw4117 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node505 PairSemantics.raw4117; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical4117 hH).trans (PairSemantics.sound207 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue505, PairSemantics.value0, PairSemantics.value4, PairSemantics.value11, PairSemantics.value207, Sparse.eval] at hp ⊢
  linarith only [hp]

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons61
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singleton3912 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node3912 node3912Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node505 node505Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw550 singletonSmall3912
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall3912) = raw550Labels := by decide +kernel
  rw [hl, canonical550 B hB] at h
  have hc0 : mixedMoment B raw550 (Fin.cases (0 : Fin 1) singletonSmall3912) =
      mixedMoment B node505 node505Labels := by
    have ha : raw550 = raw551 := by apply Matrix.ext; unfold raw550 raw551; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall3912 = raw551Labels := by decide +kernel
    rw [ha, hj, canonical551 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
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

theorem singleton5401 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5401 node5401Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3787 node3787Labels + mixedMoment B node3804 node3804Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2475 singletonSmall5401
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5401) = raw2475Labels := by decide +kernel
  rw [hl, canonical2475 B hB] at h
  have hc0 : mixedMoment B raw2475 (Fin.cases (0 : Fin 2) singletonSmall5401) =
      mixedMoment B node3787 node3787Labels := by
    have ha : raw2475 = raw2476 := by apply Matrix.ext; unfold raw2475 raw2476; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5401 = raw2476Labels := by decide +kernel
    rw [ha, hj, canonical2476 B hB]
  have hc1 : mixedMoment B raw2475 (Fin.cases (1 : Fin 2) singletonSmall5401) =
      mixedMoment B node3804 node3804Labels := by
    have ha : raw2475 = raw2477 := by apply Matrix.ext; unfold raw2475 raw2477; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5401 = raw2477Labels := by decide +kernel
    rw [ha, hj, canonical2477 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton5406 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5406 node5406Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3801 node3801Labels + mixedMoment B node3812 node3812Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2487 singletonSmall5406
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5406) = raw2487Labels := by decide +kernel
  rw [hl, canonical2487 B hB] at h
  have hc0 : mixedMoment B raw2487 (Fin.cases (0 : Fin 2) singletonSmall5406) =
      mixedMoment B node3801 node3801Labels := by
    have ha : raw2487 = raw2488 := by apply Matrix.ext; unfold raw2487 raw2488; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5406 = raw2488Labels := by decide +kernel
    rw [ha, hj, canonical2488 B hB]
  have hc1 : mixedMoment B raw2487 (Fin.cases (1 : Fin 2) singletonSmall5406) =
      mixedMoment B node3812 node3812Labels := by
    have ha : raw2487 = raw2489 := by apply Matrix.ext; unfold raw2487 raw2489; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5406 = raw2489Labels := by decide +kernel
    rw [ha, hj, canonical2489 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

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

theorem singleton5451 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5451 node5451Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3888 node3888Labels + mixedMoment B node3913 node3913Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2559 singletonSmall5451
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5451) = raw2559Labels := by decide +kernel
  rw [hl, canonical2559 B hB] at h
  have hc0 : mixedMoment B raw2559 (Fin.cases (0 : Fin 2) singletonSmall5451) =
      mixedMoment B node3888 node3888Labels := by
    have ha : raw2559 = raw2560 := by apply Matrix.ext; unfold raw2559 raw2560; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5451 = raw2560Labels := by decide +kernel
    rw [ha, hj, canonical2560 B hB]
  have hc1 : mixedMoment B raw2559 (Fin.cases (1 : Fin 2) singletonSmall5451) =
      mixedMoment B node3913 node3913Labels := by
    have ha : raw2559 = raw2561 := by apply Matrix.ext; unfold raw2559 raw2561; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5451 = raw2561Labels := by decide +kernel
    rw [ha, hj, canonical2561 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton5453 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5453 node5453Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3912 node3912Labels + mixedMoment B node3912 node3912Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2565 singletonSmall5453
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5453) = raw2565Labels := by decide +kernel
  rw [hl, canonical2565 B hB] at h
  have hc0 : mixedMoment B raw2565 (Fin.cases (0 : Fin 2) singletonSmall5453) =
      mixedMoment B node3912 node3912Labels := by
    have ha : raw2565 = raw2566 := by apply Matrix.ext; unfold raw2565 raw2566; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5453 = raw2566Labels := by decide +kernel
    rw [ha, hj, canonical2566 B hB]
  have hc1 : mixedMoment B raw2565 (Fin.cases (1 : Fin 2) singletonSmall5453) =
      mixedMoment B node3912 node3912Labels := by
    have ha : raw2565 = raw2567 := by apply Matrix.ext; unfold raw2565 raw2567; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5453 = raw2567Labels := by decide +kernel
    rw [ha, hj, canonical2567 B hB]
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

theorem sound505 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node505 node505Labels = Sparse.eval nodeValue505 (mixedVector B) := by
  calc
    _ = Sparse.eval singlePairValue505 (familyPairVector B) := singlePair505 B _hB
    _ = _ := by norm_num [singlePairValue505, nodeValue505, Sparse.eval, mixedVector] <;> ring

theorem sound3912 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3912 node3912Labels = Sparse.eval nodeValue3912 (mixedVector B) := by
  have h := singleton3912 B _hB
  rw [sound505 B _hB _hF] at h
  norm_num [nodeValue3912, nodeValue505, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5453 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5453 node5453Labels = Sparse.eval nodeValue5453 (mixedVector B) := by
  have h := singleton5453 B _hB
  rw [sound3912 B _hB _hF] at h
  norm_num [nodeValue5453, nodeValue3912, Sparse.eval] at h ⊢
  linarith only [h]

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

theorem sound2105 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2105 node2105Labels = Sparse.eval nodeValue2105 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2105) = mixedMoment B node2105 node2105Labels := rfl
  simpa [nodeValue2105, Sparse.eval] using hc.symm

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound7
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

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

theorem sound3787 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3787 node3787Labels = Sparse.eval nodeValue3787 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3787) = mixedMoment B node3787 node3787Labels := rfl
  simpa [nodeValue3787, Sparse.eval] using hc.symm

theorem sound3799 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3799 node3799Labels = Sparse.eval nodeValue3799 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3799) = mixedMoment B node3799 node3799Labels := rfl
  simpa [nodeValue3799, Sparse.eval] using hc.symm

theorem sound3801 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3801 node3801Labels = Sparse.eval nodeValue3801 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3801) = mixedMoment B node3801 node3801Labels := rfl
  simpa [nodeValue3801, Sparse.eval] using hc.symm

theorem sound3804 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3804 node3804Labels = Sparse.eval nodeValue3804 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3804) = mixedMoment B node3804 node3804Labels := rfl
  simpa [nodeValue3804, Sparse.eval] using hc.symm

theorem sound3812 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3812 node3812Labels = Sparse.eval nodeValue3812 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3812) = mixedMoment B node3812 node3812Labels := rfl
  simpa [nodeValue3812, Sparse.eval] using hc.symm

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound61
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound3913 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3913 node3913Labels = Sparse.eval nodeValue3913 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3913) = mixedMoment B node3913 node3913Labels := rfl
  simpa [nodeValue3913, Sparse.eval] using hc.symm

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

theorem sound5400 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5400 node5400Labels = Sparse.eval nodeValue5400 (mixedVector B) := by
  have h := singleton5400 B _hB
  rw [sound3786 B _hB _hF, sound3799 B _hB _hF] at h
  norm_num [nodeValue5400, nodeValue3786, nodeValue3799, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5401 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5401 node5401Labels = Sparse.eval nodeValue5401 (mixedVector B) := by
  have h := singleton5401 B _hB
  rw [sound3787 B _hB _hF, sound3804 B _hB _hF] at h
  norm_num [nodeValue5401, nodeValue3787, nodeValue3804, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5406 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5406 node5406Labels = Sparse.eval nodeValue5406 (mixedVector B) := by
  have h := singleton5406 B _hB
  rw [sound3801 B _hB _hF, sound3812 B _hB _hF] at h
  norm_num [nodeValue5406, nodeValue3801, nodeValue3812, Sparse.eval] at h ⊢
  linarith only [h]

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

theorem sound5451 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5451 node5451Labels = Sparse.eval nodeValue5451 (mixedVector B) := by
  have h := singleton5451 B _hB
  rw [sound3888 B _hB _hF, sound3913 B _hB _hF] at h
  norm_num [nodeValue5451, nodeValue3888, nodeValue3913, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5489 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5489 node5489Labels = Sparse.eval nodeValue5489 (mixedVector B) := by
  simpa only [nodeValue5489, Sparse.eval_nil] using zero5489 B _hB _hF

theorem sound5493 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5493 node5493Labels = Sparse.eval nodeValue5493 (mixedVector B) := by
  simpa only [nodeValue5493, Sparse.eval_nil] using zero5493 B _hB _hF

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources34
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sourceEq1103 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1103 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1103 + difference 0 1) (sourceB1103 + difference 1 0) sourceC1103) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5440) := by
    have ha : (tripleCharges (sourceA1103 + difference 0 1) (sourceB1103 + difference 1 0) sourceC1103) = raw18485 := by
      apply Matrix.ext; unfold tripleCharges sourceA1103 sourceB1103 sourceC1103 difference raw18485; decide +kernel
    rw [ha]
    exact (canonical18485 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1103 + difference 0 2) (sourceB1103 + difference 2 0) sourceC1103) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5489) := by
    have ha : (tripleCharges (sourceA1103 + difference 0 2) (sourceB1103 + difference 2 0) sourceC1103) = raw18486 := by
      apply Matrix.ext; unfold tripleCharges sourceA1103 sourceB1103 sourceC1103 difference raw18486; decide +kernel
    rw [ha]
    exact (canonical18486 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1103 + difference 0 3) (sourceB1103 + difference 3 0) sourceC1103) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5490) := by
    have ha : (tripleCharges (sourceA1103 + difference 0 3) (sourceB1103 + difference 3 0) sourceC1103) = raw18186 := by
      apply Matrix.ext; unfold tripleCharges sourceA1103 sourceB1103 sourceC1103 difference raw18186; decide +kernel
    rw [ha]
    exact (canonical18186 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1103 + difference 0 4) (sourceB1103 + difference 4 0) sourceC1103) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5490) := by
    have ha : (tripleCharges (sourceA1103 + difference 0 4) (sourceB1103 + difference 4 0) sourceC1103) = raw18487 := by
      apply Matrix.ext; unfold tripleCharges sourceA1103 sourceB1103 sourceC1103 difference raw18487; decide +kernel
    rw [ha]
    exact (canonical18487 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1103 + difference 0 5) (sourceB1103 + difference 5 0) sourceC1103) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5493) := by
    have ha : (tripleCharges (sourceA1103 + difference 0 5) (sourceB1103 + difference 5 0) sourceC1103) = raw18488 := by
      apply Matrix.ext; unfold tripleCharges sourceA1103 sourceB1103 sourceC1103 difference raw18488; decide +kernel
    rw [ha]
    exact (canonical18488 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1103 + difference 1 0) (sourceB1103 + difference 0 1) sourceC1103) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4889) := by
    have ha : (tripleCharges (sourceA1103 + difference 1 0) (sourceB1103 + difference 0 1) sourceC1103) = raw18489 := by
      apply Matrix.ext; unfold tripleCharges sourceA1103 sourceB1103 sourceC1103 difference raw18489; decide +kernel
    rw [ha]
    exact (canonical18489 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1103 + difference 1 2) (sourceB1103 + difference 2 1) sourceC1103) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5406) := by
    have ha : (tripleCharges (sourceA1103 + difference 1 2) (sourceB1103 + difference 2 1) sourceC1103) = raw18490 := by
      apply Matrix.ext; unfold tripleCharges sourceA1103 sourceB1103 sourceC1103 difference raw18490; decide +kernel
    rw [ha]
    exact (canonical18490 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1103 + difference 1 3) (sourceB1103 + difference 3 1) sourceC1103) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5435) := by
    have ha : (tripleCharges (sourceA1103 + difference 1 3) (sourceB1103 + difference 3 1) sourceC1103) = raw18191 := by
      apply Matrix.ext; unfold tripleCharges sourceA1103 sourceB1103 sourceC1103 difference raw18191; decide +kernel
    rw [ha]
    exact (canonical18191 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1103 + difference 1 4) (sourceB1103 + difference 4 1) sourceC1103) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5435) := by
    have ha : (tripleCharges (sourceA1103 + difference 1 4) (sourceB1103 + difference 4 1) sourceC1103) = raw18491 := by
      apply Matrix.ext; unfold tripleCharges sourceA1103 sourceB1103 sourceC1103 difference raw18491; decide +kernel
    rw [ha]
    exact (canonical18491 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1103 + difference 1 5) (sourceB1103 + difference 5 1) sourceC1103) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5453) := by
    have ha : (tripleCharges (sourceA1103 + difference 1 5) (sourceB1103 + difference 5 1) sourceC1103) = raw18492 := by
      apply Matrix.ext; unfold tripleCharges sourceA1103 sourceB1103 sourceC1103 difference raw18492; decide +kernel
    rw [ha]
    exact (canonical18492 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1103 + difference 2 0) (sourceB1103 + difference 0 2) sourceC1103) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4864) := by
    have ha : (tripleCharges (sourceA1103 + difference 2 0) (sourceB1103 + difference 0 2) sourceC1103) = raw18493 := by
      apply Matrix.ext; unfold tripleCharges sourceA1103 sourceB1103 sourceC1103 difference raw18493; decide +kernel
    rw [ha]
    exact (canonical18493 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1103 + difference 2 1) (sourceB1103 + difference 1 2) sourceC1103) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5386) := by
    have ha : (tripleCharges (sourceA1103 + difference 2 1) (sourceB1103 + difference 1 2) sourceC1103) = raw18494 := by
      apply Matrix.ext; unfold tripleCharges sourceA1103 sourceB1103 sourceC1103 difference raw18494; decide +kernel
    rw [ha]
    exact (canonical18494 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1103 + difference 2 3) (sourceB1103 + difference 3 2) sourceC1103) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5431) := by
    have ha : (tripleCharges (sourceA1103 + difference 2 3) (sourceB1103 + difference 3 2) sourceC1103) = raw18196 := by
      apply Matrix.ext; unfold tripleCharges sourceA1103 sourceB1103 sourceC1103 difference raw18196; decide +kernel
    rw [ha]
    exact (canonical18196 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1103 + difference 2 4) (sourceB1103 + difference 4 2) sourceC1103) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5431) := by
    have ha : (tripleCharges (sourceA1103 + difference 2 4) (sourceB1103 + difference 4 2) sourceC1103) = raw18495 := by
      apply Matrix.ext; unfold tripleCharges sourceA1103 sourceB1103 sourceC1103 difference raw18495; decide +kernel
    rw [ha]
    exact (canonical18495 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1103 + difference 2 5) (sourceB1103 + difference 5 2) sourceC1103) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5450) := by
    have ha : (tripleCharges (sourceA1103 + difference 2 5) (sourceB1103 + difference 5 2) sourceC1103) = raw18496 := by
      apply Matrix.ext; unfold tripleCharges sourceA1103 sourceB1103 sourceC1103 difference raw18496; decide +kernel
    rw [ha]
    exact (canonical18496 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1103 + difference 3 0) (sourceB1103 + difference 0 3) sourceC1103) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4866) := by
    have ha : (tripleCharges (sourceA1103 + difference 3 0) (sourceB1103 + difference 0 3) sourceC1103) = raw18497 := by
      apply Matrix.ext; unfold tripleCharges sourceA1103 sourceB1103 sourceC1103 difference raw18497; decide +kernel
    rw [ha]
    exact (canonical18497 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1103 + difference 3 1) (sourceB1103 + difference 1 3) sourceC1103) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5388) := by
    have ha : (tripleCharges (sourceA1103 + difference 3 1) (sourceB1103 + difference 1 3) sourceC1103) = raw18498 := by
      apply Matrix.ext; unfold tripleCharges sourceA1103 sourceB1103 sourceC1103 difference raw18498; decide +kernel
    rw [ha]
    exact (canonical18498 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1103 + difference 3 2) (sourceB1103 + difference 2 3) sourceC1103) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5401) := by
    have ha : (tripleCharges (sourceA1103 + difference 3 2) (sourceB1103 + difference 2 3) sourceC1103) = raw18499 := by
      apply Matrix.ext; unfold tripleCharges sourceA1103 sourceB1103 sourceC1103 difference raw18499; decide +kernel
    rw [ha]
    exact (canonical18499 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1103 + difference 3 4) (sourceB1103 + difference 4 3) sourceC1103) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5438) := by
    have ha : (tripleCharges (sourceA1103 + difference 3 4) (sourceB1103 + difference 4 3) sourceC1103) = raw18500 := by
      apply Matrix.ext; unfold tripleCharges sourceA1103 sourceB1103 sourceC1103 difference raw18500; decide +kernel
    rw [ha]
    exact (canonical18500 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1103 + difference 3 5) (sourceB1103 + difference 5 3) sourceC1103) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5451) := by
    have ha : (tripleCharges (sourceA1103 + difference 3 5) (sourceB1103 + difference 5 3) sourceC1103) = raw18501 := by
      apply Matrix.ext; unfold tripleCharges sourceA1103 sourceB1103 sourceC1103 difference raw18501; decide +kernel
    rw [ha]
    exact (canonical18501 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1103 + difference 4 0) (sourceB1103 + difference 0 4) sourceC1103) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4866) := by
    have ha : (tripleCharges (sourceA1103 + difference 4 0) (sourceB1103 + difference 0 4) sourceC1103) = raw18502 := by
      apply Matrix.ext; unfold tripleCharges sourceA1103 sourceB1103 sourceC1103 difference raw18502; decide +kernel
    rw [ha]
    exact (canonical18502 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1103 + difference 4 1) (sourceB1103 + difference 1 4) sourceC1103) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5388) := by
    have ha : (tripleCharges (sourceA1103 + difference 4 1) (sourceB1103 + difference 1 4) sourceC1103) = raw18503 := by
      apply Matrix.ext; unfold tripleCharges sourceA1103 sourceB1103 sourceC1103 difference raw18503; decide +kernel
    rw [ha]
    exact (canonical18503 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1103 + difference 4 2) (sourceB1103 + difference 2 4) sourceC1103) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5401) := by
    have ha : (tripleCharges (sourceA1103 + difference 4 2) (sourceB1103 + difference 2 4) sourceC1103) = raw18504 := by
      apply Matrix.ext; unfold tripleCharges sourceA1103 sourceB1103 sourceC1103 difference raw18504; decide +kernel
    rw [ha]
    exact (canonical18504 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1103 + difference 4 3) (sourceB1103 + difference 3 4) sourceC1103) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5438) := by
    have ha : (tripleCharges (sourceA1103 + difference 4 3) (sourceB1103 + difference 3 4) sourceC1103) = raw18206 := by
      apply Matrix.ext; unfold tripleCharges sourceA1103 sourceB1103 sourceC1103 difference raw18206; decide +kernel
    rw [ha]
    exact (canonical18206 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1103 + difference 4 5) (sourceB1103 + difference 5 4) sourceC1103) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5451) := by
    have ha : (tripleCharges (sourceA1103 + difference 4 5) (sourceB1103 + difference 5 4) sourceC1103) = raw18505 := by
      apply Matrix.ext; unfold tripleCharges sourceA1103 sourceB1103 sourceC1103 difference raw18505; decide +kernel
    rw [ha]
    exact (canonical18505 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1103 + difference 5 0) (sourceB1103 + difference 0 5) sourceC1103) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4865) := by
    have ha : (tripleCharges (sourceA1103 + difference 5 0) (sourceB1103 + difference 0 5) sourceC1103) = raw18197 := by
      apply Matrix.ext; unfold tripleCharges sourceA1103 sourceB1103 sourceC1103 difference raw18197; decide +kernel
    rw [ha]
    exact (canonical18197 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1103 + difference 5 1) (sourceB1103 + difference 1 5) sourceC1103) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5387) := by
    have ha : (tripleCharges (sourceA1103 + difference 5 1) (sourceB1103 + difference 1 5) sourceC1103) = raw18198 := by
      apply Matrix.ext; unfold tripleCharges sourceA1103 sourceB1103 sourceC1103 difference raw18198; decide +kernel
    rw [ha]
    exact (canonical18198 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1103 + difference 5 2) (sourceB1103 + difference 2 5) sourceC1103) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5400) := by
    have ha : (tripleCharges (sourceA1103 + difference 5 2) (sourceB1103 + difference 2 5) sourceC1103) = raw18199 := by
      apply Matrix.ext; unfold tripleCharges sourceA1103 sourceB1103 sourceC1103 difference raw18199; decide +kernel
    rw [ha]
    exact (canonical18199 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1103 + difference 5 3) (sourceB1103 + difference 3 5) sourceC1103) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5432) := by
    have ha : (tripleCharges (sourceA1103 + difference 5 3) (sourceB1103 + difference 3 5) sourceC1103) = raw18506 := by
      apply Matrix.ext; unfold tripleCharges sourceA1103 sourceB1103 sourceC1103 difference raw18506; decide +kernel
    rw [ha]
    exact (canonical18506 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1103 + difference 5 4) (sourceB1103 + difference 4 5) sourceC1103) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5432) := by
    have ha : (tripleCharges (sourceA1103 + difference 5 4) (sourceB1103 + difference 4 5) sourceC1103) = raw18200 := by
      apply Matrix.ext; unfold tripleCharges sourceA1103 sourceB1103 sourceC1103 difference raw18200; decide +kernel
    rw [ha]
    exact (canonical18200 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1103 sourceB1103 sourceC1103
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1103, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic59
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reindexCheck956 : Integer.Sparse.reindex keyMap MixedData.row956 = numericRow956 := by decide +kernel

theorem numericCheck956 (x : Master → ℝ) : Integer.Sparse.eval numericRow956 x =
    (1440 : ℝ) * reducedSource956 x := by
  norm_num [numericRow956, reducedSource956, Integer.Sparse.eval, Sparse.eval, nodeValue4864, nodeValue4865, nodeValue4866, nodeValue4889, nodeValue5386, nodeValue5387, nodeValue5388, nodeValue5400, nodeValue5401, nodeValue5406, nodeValue5431, nodeValue5432, nodeValue5435, nodeValue5438, nodeValue5440, nodeValue5450, nodeValue5451, nodeValue5453, nodeValue5489, nodeValue5490, nodeValue5493] <;> ring

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Rows59
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero956 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource956 (mixedVector B) = 0 := by
  have h4864 : mixedVector B (Sum.inr 4864) = Sparse.eval nodeValue4864 (mixedVector B) := by
    change mixedMoment B node4864 node4864Labels = _
    exact sound4864 B hB hF
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
  have h5387 : mixedVector B (Sum.inr 5387) = Sparse.eval nodeValue5387 (mixedVector B) := by
    change mixedMoment B node5387 node5387Labels = _
    exact sound5387_e B hB hF
  have h5388 : mixedVector B (Sum.inr 5388) = Sparse.eval nodeValue5388 (mixedVector B) := by
    change mixedMoment B node5388 node5388Labels = _
    exact sound5388_e B hB hF
  have h5400 : mixedVector B (Sum.inr 5400) = Sparse.eval nodeValue5400 (mixedVector B) := by
    change mixedMoment B node5400 node5400Labels = _
    exact sound5400 B hB hF
  have h5401 : mixedVector B (Sum.inr 5401) = Sparse.eval nodeValue5401 (mixedVector B) := by
    change mixedMoment B node5401 node5401Labels = _
    exact sound5401 B hB hF
  have h5406 : mixedVector B (Sum.inr 5406) = Sparse.eval nodeValue5406 (mixedVector B) := by
    change mixedMoment B node5406 node5406Labels = _
    exact sound5406 B hB hF
  have h5431 : mixedVector B (Sum.inr 5431) = Sparse.eval nodeValue5431 (mixedVector B) := by
    change mixedMoment B node5431 node5431Labels = _
    exact sound5431 B hB hF
  have h5432 : mixedVector B (Sum.inr 5432) = Sparse.eval nodeValue5432 (mixedVector B) := by
    change mixedMoment B node5432 node5432Labels = _
    exact sound5432 B hB hF
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
  have h5451 : mixedVector B (Sum.inr 5451) = Sparse.eval nodeValue5451 (mixedVector B) := by
    change mixedMoment B node5451 node5451Labels = _
    exact sound5451 B hB hF
  have h5453 : mixedVector B (Sum.inr 5453) = Sparse.eval nodeValue5453 (mixedVector B) := by
    change mixedMoment B node5453 node5453Labels = _
    exact sound5453 B hB hF
  have h5489 : mixedVector B (Sum.inr 5489) = Sparse.eval nodeValue5489 (mixedVector B) := by
    change mixedMoment B node5489 node5489Labels = _
    exact sound5489 B hB hF
  have h5490 : mixedVector B (Sum.inr 5490) = Sparse.eval nodeValue5490 (mixedVector B) := by
    change mixedMoment B node5490 node5490Labels = _
    exact sound5490_e B hB hF
  have h5493 : mixedVector B (Sum.inr 5493) = Sparse.eval nodeValue5493 (mixedVector B) := by
    change mixedMoment B node5493 node5493Labels = _
    exact sound5493 B hB hF
  simpa only [sourceForm1103, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4864, h4865, h4866, h4889, h5386, h5387, h5388, h5400, h5401, h5406, h5431, h5432, h5435, h5438, h5440, h5450, h5451, h5453, h5489, h5490, h5493, reducedSource956] using sourceEq1103 B hB

theorem rowSound956_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row956 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck956, numericCheck956, reducedZero956 B hB hF, mul_zero]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedSourceBridge.rowSound956_e_oai := @OAI.MUB6.Certificate.MixedSourceBridge.rowSound956_e_oai
