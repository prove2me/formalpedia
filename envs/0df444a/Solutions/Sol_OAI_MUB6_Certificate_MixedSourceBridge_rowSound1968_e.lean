-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedSourceBridge.rowSound1968_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-08T22:31:11.920812+00:00
-- url     : https://prove2.me/submissions/c203a005-d130-4917-86c3-eab75aad4188

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
import Definitions.Def_OAIQ106E194
import Definitions.Def_OAIQ106E195
import Definitions.Def_OAIQ106E101
import Definitions.Def_OAIQ106E105
import Definitions.Def_OAIQ106E107
import Definitions.Def_OAIQ106E115
import Definitions.Def_OAIQ106E118
import Definitions.Def_OAIQ106E119
import Definitions.Def_OAIQ106E120
import Definitions.Def_OAIQ106E125
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
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound5388_e
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical12
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

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

theorem canonical1563 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1563 raw1563Labels = mixedMoment B node4681 node4681Labels := by
  calc
    mixedMoment B raw1563 raw1563Labels = mixedMoment B raw1563step0 raw1563step0Labels := by
      have ha : raw1563step0 = (fun i j => raw1563 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1563step0 raw1563; decide +kernel
      have hl : raw1563step0Labels = raw1563Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1563 raw1563Labels permutation32 permutation4
    mixedMoment B raw1563step0 raw1563step0Labels = mixedMoment B raw1563step1 raw1563step1Labels := by
      have ha : raw1563step1 = raw1563step0 := by apply Matrix.ext; unfold raw1563step1 raw1563step0; decide +kernel
      have hl : raw1563step0Labels = labelEmbedding7 ∘ raw1563step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1563step0 raw1563step0Labels raw1563step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4681 node4681Labels := by rfl

theorem canonical1564 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1564 raw1564Labels = mixedMoment B node1807 node1807Labels := by
  calc
    mixedMoment B raw1564 raw1564Labels = mixedMoment B raw1564step0 raw1564step0Labels := by
      have ha : raw1564step0 = (fun i j => raw1564 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1564step0 raw1564; decide +kernel
      have hl : raw1564step0Labels = raw1564Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1564 raw1564Labels permutation32 permutation4
    _ = mixedMoment B node1807 node1807Labels := by rfl

theorem canonical1565 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1565 raw1565Labels = mixedMoment B node2151 node2151Labels := by
  calc
    mixedMoment B raw1565 raw1565Labels = mixedMoment B raw1565step0 raw1565step0Labels := by
      have ha : raw1565step0 = (fun i j => raw1565 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1565step0 raw1565; decide +kernel
      have hl : raw1565step0Labels = raw1565Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1565 raw1565Labels permutation32 permutation6
    mixedMoment B raw1565step0 raw1565step0Labels = mixedMoment B raw1565step1 raw1565step1Labels := by
      have ha : raw1565step1 = -raw1565step0 := by apply Matrix.ext; change ∀ i j, raw1565step1 i j = -(raw1565step0 i j); unfold raw1565step1 raw1565step0; decide +kernel
      have hl : raw1565step1Labels = raw1565step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1565step1 raw1565step1Labels = mixedMoment B raw1565step2 raw1565step2Labels := by
      have ha : raw1565step2 = raw1565step1 := by apply Matrix.ext; unfold raw1565step2 raw1565step1; decide +kernel
      have hl : raw1565step1Labels = labelEmbedding1 ∘ raw1565step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1565step1 raw1565step1Labels raw1565step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2151 node2151Labels := by rfl

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

theorem canonical1578 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1578 raw1578Labels = mixedMoment B node4689 node4689Labels := by
  calc
    mixedMoment B raw1578 raw1578Labels = mixedMoment B raw1578step0 raw1578step0Labels := by
      have ha : raw1578step0 = (fun i j => raw1578 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1578step0 raw1578; decide +kernel
      have hl : raw1578step0Labels = raw1578Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1578 raw1578Labels permutation32 permutation4
    mixedMoment B raw1578step0 raw1578step0Labels = mixedMoment B raw1578step1 raw1578step1Labels := by
      have ha : raw1578step1 = raw1578step0 := by apply Matrix.ext; unfold raw1578step1 raw1578step0; decide +kernel
      have hl : raw1578step0Labels = labelEmbedding7 ∘ raw1578step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1578step0 raw1578step0Labels raw1578step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4689 node4689Labels := by rfl

theorem canonical1579 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1579 raw1579Labels = mixedMoment B node1815 node1815Labels := by
  calc
    mixedMoment B raw1579 raw1579Labels = mixedMoment B raw1579step0 raw1579step0Labels := by
      have ha : raw1579step0 = (fun i j => raw1579 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1579step0 raw1579; decide +kernel
      have hl : raw1579step0Labels = raw1579Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1579 raw1579Labels permutation32 permutation4
    _ = mixedMoment B node1815 node1815Labels := by rfl

theorem canonical1580 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1580 raw1580Labels = mixedMoment B node2166 node2166Labels := by
  calc
    mixedMoment B raw1580 raw1580Labels = mixedMoment B raw1580step0 raw1580step0Labels := by
      have ha : raw1580step0 = (fun i j => raw1580 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1580step0 raw1580; decide +kernel
      have hl : raw1580step0Labels = raw1580Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1580 raw1580Labels permutation32 permutation6
    mixedMoment B raw1580step0 raw1580step0Labels = mixedMoment B raw1580step1 raw1580step1Labels := by
      have ha : raw1580step1 = -raw1580step0 := by apply Matrix.ext; change ∀ i j, raw1580step1 i j = -(raw1580step0 i j); unfold raw1580step1 raw1580step0; decide +kernel
      have hl : raw1580step1Labels = raw1580step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1580step1 raw1580step1Labels = mixedMoment B raw1580step2 raw1580step2Labels := by
      have ha : raw1580step2 = raw1580step1 := by apply Matrix.ext; unfold raw1580step2 raw1580step1; decide +kernel
      have hl : raw1580step1Labels = labelEmbedding1 ∘ raw1580step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1580step1 raw1580step1Labels raw1580step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2166 node2166Labels := by rfl

theorem canonical1620 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1620 raw1620Labels = mixedMoment B node4721 node4721Labels := by
  calc
    mixedMoment B raw1620 raw1620Labels = mixedMoment B raw1620step0 raw1620step0Labels := by
      have ha : raw1620step0 = (fun i j => raw1620 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1620step0 raw1620; decide +kernel
      have hl : raw1620step0Labels = raw1620Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1620 raw1620Labels permutation152 permutation4
    mixedMoment B raw1620step0 raw1620step0Labels = mixedMoment B raw1620step1 raw1620step1Labels := by
      have ha : raw1620step1 = raw1620step0 := by apply Matrix.ext; unfold raw1620step1 raw1620step0; decide +kernel
      have hl : raw1620step0Labels = labelEmbedding7 ∘ raw1620step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1620step0 raw1620step0Labels raw1620step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4721 node4721Labels := by rfl

theorem canonical1621 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1621 raw1621Labels = mixedMoment B node1875 node1875Labels := by
  calc
    mixedMoment B raw1621 raw1621Labels = mixedMoment B raw1621step0 raw1621step0Labels := by
      have ha : raw1621step0 = (fun i j => raw1621 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1621step0 raw1621; decide +kernel
      have hl : raw1621step0Labels = raw1621Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1621 raw1621Labels permutation152 permutation4
    _ = mixedMoment B node1875 node1875Labels := by rfl

theorem canonical1622 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1622 raw1622Labels = mixedMoment B node1905 node1905Labels := by
  calc
    mixedMoment B raw1622 raw1622Labels = mixedMoment B raw1622step0 raw1622step0Labels := by
      have ha : raw1622step0 = (fun i j => raw1622 (permutation158 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1622step0 raw1622; decide +kernel
      have hl : raw1622step0Labels = raw1622Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1622 raw1622Labels permutation158 permutation6
    mixedMoment B raw1622step0 raw1622step0Labels = mixedMoment B raw1622step1 raw1622step1Labels := by
      have ha : raw1622step1 = -raw1622step0 := by apply Matrix.ext; change ∀ i j, raw1622step1 i j = -(raw1622step0 i j); unfold raw1622step1 raw1622step0; decide +kernel
      have hl : raw1622step1Labels = raw1622step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1622step1 raw1622step1Labels = mixedMoment B raw1622step2 raw1622step2Labels := by
      have ha : raw1622step2 = raw1622step1 := by apply Matrix.ext; unfold raw1622step2 raw1622step1; decide +kernel
      have hl : raw1622step1Labels = labelEmbedding1 ∘ raw1622step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1622step1 raw1622step1Labels raw1622step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1905 node1905Labels := by rfl

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

theorem canonical1632 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1632 raw1632Labels = mixedMoment B node4725 node4725Labels := by
  calc
    mixedMoment B raw1632 raw1632Labels = mixedMoment B raw1632step0 raw1632step0Labels := by
      have ha : raw1632step0 = (fun i j => raw1632 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1632step0 raw1632; decide +kernel
      have hl : raw1632step0Labels = raw1632Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1632 raw1632Labels permutation152 permutation4
    mixedMoment B raw1632step0 raw1632step0Labels = mixedMoment B raw1632step1 raw1632step1Labels := by
      have ha : raw1632step1 = raw1632step0 := by apply Matrix.ext; unfold raw1632step1 raw1632step0; decide +kernel
      have hl : raw1632step0Labels = labelEmbedding7 ∘ raw1632step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1632step0 raw1632step0Labels raw1632step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4725 node4725Labels := by rfl

theorem canonical1633 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1633 raw1633Labels = mixedMoment B node1879 node1879Labels := by
  calc
    mixedMoment B raw1633 raw1633Labels = mixedMoment B raw1633step0 raw1633step0Labels := by
      have ha : raw1633step0 = (fun i j => raw1633 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1633step0 raw1633; decide +kernel
      have hl : raw1633step0Labels = raw1633Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1633 raw1633Labels permutation152 permutation4
    _ = mixedMoment B node1879 node1879Labels := by rfl

theorem canonical1634 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1634 raw1634Labels = mixedMoment B node1936 node1936Labels := by
  calc
    mixedMoment B raw1634 raw1634Labels = mixedMoment B raw1634step0 raw1634step0Labels := by
      have ha : raw1634step0 = (fun i j => raw1634 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1634step0 raw1634; decide +kernel
      have hl : raw1634step0Labels = raw1634Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1634 raw1634Labels permutation152 permutation6
    mixedMoment B raw1634step0 raw1634step0Labels = mixedMoment B raw1634step1 raw1634step1Labels := by
      have ha : raw1634step1 = -raw1634step0 := by apply Matrix.ext; change ∀ i j, raw1634step1 i j = -(raw1634step0 i j); unfold raw1634step1 raw1634step0; decide +kernel
      have hl : raw1634step1Labels = raw1634step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1634step1 raw1634step1Labels = mixedMoment B raw1634step2 raw1634step2Labels := by
      have ha : raw1634step2 = raw1634step1 := by apply Matrix.ext; unfold raw1634step2 raw1634step1; decide +kernel
      have hl : raw1634step1Labels = labelEmbedding1 ∘ raw1634step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1634step1 raw1634step1Labels raw1634step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1936 node1936Labels := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical127
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical16284 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16284 raw16284Labels = mixedMoment B node4896 node4896Labels := by
  calc
    mixedMoment B raw16284 raw16284Labels = mixedMoment B raw16284step0 raw16284step0Labels := by
      have hz : ∀ j, raw16284 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw16284step0 = (fun i j => raw16284 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw16284step0 raw16284; decide +kernel
      have hl : raw16284step0Labels = raw16284Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16284 raw16284Labels permutation434 hz
    mixedMoment B raw16284step0 raw16284step0Labels = mixedMoment B raw16284step1 raw16284step1Labels := by
      have hz : ∀ j, raw16284step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw16284step1 = (fun i j => raw16284step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw16284step1 raw16284step0; decide +kernel
      have hl : raw16284step1Labels = raw16284step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16284step0 raw16284step0Labels permutation80 hz
    mixedMoment B raw16284step1 raw16284step1Labels = mixedMoment B raw16284step2 raw16284step2Labels := by
      have ha : raw16284step2 = (fun i j => raw16284step1 (permutation11 i) (permutation5 j)) := by apply Matrix.ext; unfold raw16284step2 raw16284step1; decide +kernel
      have hl : raw16284step2Labels = raw16284step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16284step1 raw16284step1Labels permutation11 permutation5
    mixedMoment B raw16284step2 raw16284step2Labels = mixedMoment B raw16284step3 raw16284step3Labels := by
      have ha : raw16284step3 = -raw16284step2 := by apply Matrix.ext; change ∀ i j, raw16284step3 i j = -(raw16284step2 i j); unfold raw16284step3 raw16284step2; decide +kernel
      have hl : raw16284step3Labels = raw16284step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16284step3 raw16284step3Labels = mixedMoment B raw16284step4 raw16284step4Labels := by
      have ha : raw16284step4 = raw16284step3 := by apply Matrix.ext; unfold raw16284step4 raw16284step3; decide +kernel
      have hl : raw16284step3Labels = labelEmbedding8 ∘ raw16284step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16284step3 raw16284step3Labels raw16284step4Labels labelEmbedding8 hl
    _ = mixedMoment B node4896 node4896Labels := by rfl

theorem canonical16289 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16289 raw16289Labels = mixedMoment B node5388 node5388Labels := by
  calc
    mixedMoment B raw16289 raw16289Labels = mixedMoment B raw16289step0 raw16289step0Labels := by
      have hz : ∀ j, raw16289 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16289step0 = (fun i j => raw16289 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16289step0 raw16289; decide +kernel
      have hl : raw16289step0Labels = raw16289Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16289 raw16289Labels permutation346 hz
    mixedMoment B raw16289step0 raw16289step0Labels = mixedMoment B raw16289step1 raw16289step1Labels := by
      have ha : raw16289step1 = (fun i j => raw16289step0 (permutation56 i) (permutation2 j)) := by apply Matrix.ext; unfold raw16289step1 raw16289step0; decide +kernel
      have hl : raw16289step1Labels = raw16289step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16289step0 raw16289step0Labels permutation56 permutation2
    _ = mixedMoment B node5388 node5388Labels := by rfl

theorem canonical16290 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16290 raw16290Labels = mixedMoment B node5401 node5401Labels := by
  calc
    mixedMoment B raw16290 raw16290Labels = mixedMoment B raw16290step0 raw16290step0Labels := by
      have ha : raw16290step0 = (fun i j => raw16290 (permutation178 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16290step0 raw16290; decide +kernel
      have hl : raw16290step0Labels = raw16290Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16290 raw16290Labels permutation178 permutation3
    mixedMoment B raw16290step0 raw16290step0Labels = mixedMoment B raw16290step1 raw16290step1Labels := by
      have ha : raw16290step1 = raw16290step0 := by apply Matrix.ext; unfold raw16290step1 raw16290step0; decide +kernel
      have hl : raw16290step0Labels = labelEmbedding6 ∘ raw16290step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16290step0 raw16290step0Labels raw16290step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5401 node5401Labels := by rfl

theorem canonical16291 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16291 raw16291Labels = mixedMoment B node5438 node5438Labels := by
  calc
    mixedMoment B raw16291 raw16291Labels = mixedMoment B raw16291step0 raw16291step0Labels := by
      have hz : ∀ j, raw16291 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16291step0 = (fun i j => raw16291 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16291step0 raw16291; decide +kernel
      have hl : raw16291step0Labels = raw16291Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16291 raw16291Labels permutation346 hz
    mixedMoment B raw16291step0 raw16291step0Labels = mixedMoment B raw16291step1 raw16291step1Labels := by
      have ha : raw16291step1 = (fun i j => raw16291step0 (permutation44 i) (permutation5 j)) := by apply Matrix.ext; unfold raw16291step1 raw16291step0; decide +kernel
      have hl : raw16291step1Labels = raw16291step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16291step0 raw16291step0Labels permutation44 permutation5
    mixedMoment B raw16291step1 raw16291step1Labels = mixedMoment B raw16291step2 raw16291step2Labels := by
      have ha : raw16291step2 = -raw16291step1 := by apply Matrix.ext; change ∀ i j, raw16291step2 i j = -(raw16291step1 i j); unfold raw16291step2 raw16291step1; decide +kernel
      have hl : raw16291step2Labels = raw16291step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16291step2 raw16291step2Labels = mixedMoment B raw16291step3 raw16291step3Labels := by
      have ha : raw16291step3 = raw16291step2 := by apply Matrix.ext; unfold raw16291step3 raw16291step2; decide +kernel
      have hl : raw16291step2Labels = labelEmbedding8 ∘ raw16291step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16291step2 raw16291step2Labels raw16291step3Labels labelEmbedding8 hl
    _ = mixedMoment B node5438 node5438Labels := by rfl

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

theorem canonical1755 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1755 raw1755Labels = mixedMoment B node4827 node4827Labels := by
  calc
    mixedMoment B raw1755 raw1755Labels = mixedMoment B raw1755step0 raw1755step0Labels := by
      have ha : raw1755step0 = (fun i j => raw1755 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1755step0 raw1755; decide +kernel
      have hl : raw1755step0Labels = raw1755Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1755 raw1755Labels permutation32 permutation4
    mixedMoment B raw1755step0 raw1755step0Labels = mixedMoment B raw1755step1 raw1755step1Labels := by
      have ha : raw1755step1 = raw1755step0 := by apply Matrix.ext; unfold raw1755step1 raw1755step0; decide +kernel
      have hl : raw1755step0Labels = labelEmbedding7 ∘ raw1755step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1755step0 raw1755step0Labels raw1755step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4827 node4827Labels := by rfl

theorem canonical1756 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1756 raw1756Labels = mixedMoment B node2047 node2047Labels := by
  calc
    mixedMoment B raw1756 raw1756Labels = mixedMoment B raw1756step0 raw1756step0Labels := by
      have ha : raw1756step0 = (fun i j => raw1756 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1756step0 raw1756; decide +kernel
      have hl : raw1756step0Labels = raw1756Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1756 raw1756Labels permutation32 permutation4
    _ = mixedMoment B node2047 node2047Labels := by rfl

theorem canonical1757 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1757 raw1757Labels = mixedMoment B node2079 node2079Labels := by
  calc
    mixedMoment B raw1757 raw1757Labels = mixedMoment B raw1757step0 raw1757step0Labels := by
      have ha : raw1757step0 = (fun i j => raw1757 (permutation38 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1757step0 raw1757; decide +kernel
      have hl : raw1757step0Labels = raw1757Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1757 raw1757Labels permutation38 permutation6
    mixedMoment B raw1757step0 raw1757step0Labels = mixedMoment B raw1757step1 raw1757step1Labels := by
      have ha : raw1757step1 = -raw1757step0 := by apply Matrix.ext; change ∀ i j, raw1757step1 i j = -(raw1757step0 i j); unfold raw1757step1 raw1757step0; decide +kernel
      have hl : raw1757step1Labels = raw1757step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1757step1 raw1757step1Labels = mixedMoment B raw1757step2 raw1757step2Labels := by
      have ha : raw1757step2 = raw1757step1 := by apply Matrix.ext; unfold raw1757step2 raw1757step1; decide +kernel
      have hl : raw1757step1Labels = labelEmbedding1 ∘ raw1757step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1757step1 raw1757step1Labels raw1757step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2079 node2079Labels := by rfl

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

theorem canonical1797 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1797 raw1797Labels = mixedMoment B node4868 node4868Labels := by
  calc
    mixedMoment B raw1797 raw1797Labels = mixedMoment B raw1797step0 raw1797step0Labels := by
      have ha : raw1797step0 = (fun i j => raw1797 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1797step0 raw1797; decide +kernel
      have hl : raw1797step0Labels = raw1797Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1797 raw1797Labels permutation8 permutation4
    mixedMoment B raw1797step0 raw1797step0Labels = mixedMoment B raw1797step1 raw1797step1Labels := by
      have ha : raw1797step1 = raw1797step0 := by apply Matrix.ext; unfold raw1797step1 raw1797step0; decide +kernel
      have hl : raw1797step0Labels = labelEmbedding7 ∘ raw1797step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1797step0 raw1797step0Labels raw1797step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4868 node4868Labels := by rfl

theorem canonical1798 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1798 raw1798Labels = mixedMoment B node2109 node2109Labels := by
  calc
    mixedMoment B raw1798 raw1798Labels = mixedMoment B raw1798step0 raw1798step0Labels := by
      have ha : raw1798step0 = (fun i j => raw1798 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1798step0 raw1798; decide +kernel
      have hl : raw1798step0Labels = raw1798Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1798 raw1798Labels permutation8 permutation4
    _ = mixedMoment B node2109 node2109Labels := by rfl

theorem canonical1799 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1799 raw1799Labels = mixedMoment B node2261 node2261Labels := by
  calc
    mixedMoment B raw1799 raw1799Labels = mixedMoment B raw1799step0 raw1799step0Labels := by
      have ha : raw1799step0 = (fun i j => raw1799 (permutation10 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1799step0 raw1799; decide +kernel
      have hl : raw1799step0Labels = raw1799Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1799 raw1799Labels permutation10 permutation6
    mixedMoment B raw1799step0 raw1799step0Labels = mixedMoment B raw1799step1 raw1799step1Labels := by
      have ha : raw1799step1 = -raw1799step0 := by apply Matrix.ext; change ∀ i j, raw1799step1 i j = -(raw1799step0 i j); unfold raw1799step1 raw1799step0; decide +kernel
      have hl : raw1799step1Labels = raw1799step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1799step1 raw1799step1Labels = mixedMoment B raw1799step2 raw1799step2Labels := by
      have ha : raw1799step2 = raw1799step1 := by apply Matrix.ext; unfold raw1799step2 raw1799step1; decide +kernel
      have hl : raw1799step1Labels = labelEmbedding1 ∘ raw1799step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1799step1 raw1799step1Labels raw1799step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2261 node2261Labels := by rfl

theorem canonical1809 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1809 raw1809Labels = mixedMoment B node4875 node4875Labels := by
  calc
    mixedMoment B raw1809 raw1809Labels = mixedMoment B raw1809step0 raw1809step0Labels := by
      have ha : raw1809step0 = (fun i j => raw1809 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1809step0 raw1809; decide +kernel
      have hl : raw1809step0Labels = raw1809Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1809 raw1809Labels permutation8 permutation4
    mixedMoment B raw1809step0 raw1809step0Labels = mixedMoment B raw1809step1 raw1809step1Labels := by
      have ha : raw1809step1 = raw1809step0 := by apply Matrix.ext; unfold raw1809step1 raw1809step0; decide +kernel
      have hl : raw1809step0Labels = labelEmbedding7 ∘ raw1809step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1809step0 raw1809step0Labels raw1809step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4875 node4875Labels := by rfl

theorem canonical1810 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1810 raw1810Labels = mixedMoment B node2116 node2116Labels := by
  calc
    mixedMoment B raw1810 raw1810Labels = mixedMoment B raw1810step0 raw1810step0Labels := by
      have ha : raw1810step0 = (fun i j => raw1810 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1810step0 raw1810; decide +kernel
      have hl : raw1810step0Labels = raw1810Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1810 raw1810Labels permutation8 permutation4
    _ = mixedMoment B node2116 node2116Labels := by rfl

theorem canonical1811 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1811 raw1811Labels = mixedMoment B node2288 node2288Labels := by
  calc
    mixedMoment B raw1811 raw1811Labels = mixedMoment B raw1811step0 raw1811step0Labels := by
      have ha : raw1811step0 = (fun i j => raw1811 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1811step0 raw1811; decide +kernel
      have hl : raw1811step0Labels = raw1811Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1811 raw1811Labels permutation8 permutation6
    mixedMoment B raw1811step0 raw1811step0Labels = mixedMoment B raw1811step1 raw1811step1Labels := by
      have ha : raw1811step1 = -raw1811step0 := by apply Matrix.ext; change ∀ i j, raw1811step1 i j = -(raw1811step0 i j); unfold raw1811step1 raw1811step0; decide +kernel
      have hl : raw1811step1Labels = raw1811step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1811step1 raw1811step1Labels = mixedMoment B raw1811step2 raw1811step2Labels := by
      have ha : raw1811step2 = raw1811step1 := by apply Matrix.ext; unfold raw1811step2 raw1811step1; decide +kernel
      have hl : raw1811step1Labels = labelEmbedding1 ∘ raw1811step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1811step1 raw1811step1Labels raw1811step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2288 node2288Labels := by rfl

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

theorem canonical1824 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1824 raw1824Labels = mixedMoment B node4896 node4896Labels := by
  calc
    mixedMoment B raw1824 raw1824Labels = mixedMoment B raw1824step0 raw1824step0Labels := by
      have ha : raw1824step0 = (fun i j => raw1824 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1824step0 raw1824; decide +kernel
      have hl : raw1824step0Labels = raw1824Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1824 raw1824Labels permutation8 permutation4
    mixedMoment B raw1824step0 raw1824step0Labels = mixedMoment B raw1824step1 raw1824step1Labels := by
      have ha : raw1824step1 = raw1824step0 := by apply Matrix.ext; unfold raw1824step1 raw1824step0; decide +kernel
      have hl : raw1824step0Labels = labelEmbedding7 ∘ raw1824step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1824step0 raw1824step0Labels raw1824step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4896 node4896Labels := by rfl

theorem canonical1825 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1825 raw1825Labels = mixedMoment B node2266 node2266Labels := by
  calc
    mixedMoment B raw1825 raw1825Labels = mixedMoment B raw1825step0 raw1825step0Labels := by
      have ha : raw1825step0 = (fun i j => raw1825 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1825step0 raw1825; decide +kernel
      have hl : raw1825step0Labels = raw1825Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1825 raw1825Labels permutation8 permutation4
    _ = mixedMoment B node2266 node2266Labels := by rfl

theorem canonical1826 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1826 raw1826Labels = mixedMoment B node2278 node2278Labels := by
  calc
    mixedMoment B raw1826 raw1826Labels = mixedMoment B raw1826step0 raw1826step0Labels := by
      have ha : raw1826step0 = (fun i j => raw1826 (permutation12 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1826step0 raw1826; decide +kernel
      have hl : raw1826step0Labels = raw1826Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1826 raw1826Labels permutation12 permutation6
    mixedMoment B raw1826step0 raw1826step0Labels = mixedMoment B raw1826step1 raw1826step1Labels := by
      have ha : raw1826step1 = -raw1826step0 := by apply Matrix.ext; change ∀ i j, raw1826step1 i j = -(raw1826step0 i j); unfold raw1826step1 raw1826step0; decide +kernel
      have hl : raw1826step1Labels = raw1826step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1826step1 raw1826step1Labels = mixedMoment B raw1826step2 raw1826step2Labels := by
      have ha : raw1826step2 = raw1826step1 := by apply Matrix.ext; unfold raw1826step2 raw1826step1; decide +kernel
      have hl : raw1826step1Labels = labelEmbedding1 ∘ raw1826step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1826step1 raw1826step1Labels raw1826step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2278 node2278Labels := by rfl

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

theorem canonical31204 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31204 raw31204Labels = mixedMoment B node4239 node4239Labels := by
  calc
    mixedMoment B raw31204 raw31204Labels = mixedMoment B raw31204step0 raw31204step0Labels := by
      have hz : ∀ j, raw31204 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw31204step0 = (fun i j => raw31204 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw31204step0 raw31204; decide +kernel
      have hl : raw31204step0Labels = raw31204Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31204 raw31204Labels permutation346 hz
    mixedMoment B raw31204step0 raw31204step0Labels = mixedMoment B raw31204step1 raw31204step1Labels := by
      have ha : raw31204step1 = (fun i j => raw31204step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31204step1 raw31204step0; decide +kernel
      have hl : raw31204step1Labels = raw31204step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31204step0 raw31204step0Labels permutation32 permutation3
    mixedMoment B raw31204step1 raw31204step1Labels = mixedMoment B raw31204step2 raw31204step2Labels := by
      have ha : raw31204step2 = raw31204step1 := by apply Matrix.ext; unfold raw31204step2 raw31204step1; decide +kernel
      have hl : raw31204step1Labels = labelEmbedding6 ∘ raw31204step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31204step1 raw31204step1Labels raw31204step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4239 node4239Labels := by rfl

theorem canonical31205 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31205 raw31205Labels = mixedMoment B node4689 node4689Labels := by
  calc
    mixedMoment B raw31205 raw31205Labels = mixedMoment B raw31205step0 raw31205step0Labels := by
      have hz : ∀ j, raw31205 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw31205step0 = (fun i j => raw31205 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw31205step0 raw31205; decide +kernel
      have hl : raw31205step0Labels = raw31205Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31205 raw31205Labels permutation346 hz
    mixedMoment B raw31205step0 raw31205step0Labels = mixedMoment B raw31205step1 raw31205step1Labels := by
      have ha : raw31205step1 = (fun i j => raw31205step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31205step1 raw31205step0; decide +kernel
      have hl : raw31205step1Labels = raw31205step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31205step0 raw31205step0Labels permutation32 permutation3
    mixedMoment B raw31205step1 raw31205step1Labels = mixedMoment B raw31205step2 raw31205step2Labels := by
      have ha : raw31205step2 = raw31205step1 := by apply Matrix.ext; unfold raw31205step2 raw31205step1; decide +kernel
      have hl : raw31205step1Labels = labelEmbedding6 ∘ raw31205step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31205step1 raw31205step1Labels raw31205step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4689 node4689Labels := by rfl

theorem canonical31206 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31206 raw31206Labels = mixedMoment B node4725 node4725Labels := by
  calc
    mixedMoment B raw31206 raw31206Labels = mixedMoment B raw31206step0 raw31206step0Labels := by
      have ha : raw31206step0 = (fun i j => raw31206 (permutation176 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31206step0 raw31206; decide +kernel
      have hl : raw31206step0Labels = raw31206Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31206 raw31206Labels permutation176 permutation3
    mixedMoment B raw31206step0 raw31206step0Labels = mixedMoment B raw31206step1 raw31206step1Labels := by
      have ha : raw31206step1 = raw31206step0 := by apply Matrix.ext; unfold raw31206step1 raw31206step0; decide +kernel
      have hl : raw31206step0Labels = labelEmbedding6 ∘ raw31206step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31206step0 raw31206step0Labels raw31206step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4725 node4725Labels := by rfl

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

theorem canonical33619 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33619 raw33619Labels = mixedMoment B node4864 node4864Labels := by
  calc
    mixedMoment B raw33619 raw33619Labels = mixedMoment B raw33619step0 raw33619step0Labels := by
      have ha : raw33619step0 = (fun i j => raw33619 (permutation168 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33619step0 raw33619; decide +kernel
      have hl : raw33619step0Labels = raw33619Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33619 raw33619Labels permutation168 permutation3
    mixedMoment B raw33619step0 raw33619step0Labels = mixedMoment B raw33619step1 raw33619step1Labels := by
      have ha : raw33619step1 = raw33619step0 := by apply Matrix.ext; unfold raw33619step1 raw33619step0; decide +kernel
      have hl : raw33619step0Labels = labelEmbedding6 ∘ raw33619step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33619step0 raw33619step0Labels raw33619step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4864 node4864Labels := by rfl

theorem canonical33620 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33620 raw33620Labels = mixedMoment B node4234 node4234Labels := by
  calc
    mixedMoment B raw33620 raw33620Labels = mixedMoment B raw33620step0 raw33620step0Labels := by
      have hz : ∀ j, raw33620 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33620step0 = (fun i j => raw33620 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33620step0 raw33620; decide +kernel
      have hl : raw33620step0Labels = raw33620Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33620 raw33620Labels permutation346 hz
    mixedMoment B raw33620step0 raw33620step0Labels = mixedMoment B raw33620step1 raw33620step1Labels := by
      have ha : raw33620step1 = (fun i j => raw33620step0 (permutation35 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33620step1 raw33620step0; decide +kernel
      have hl : raw33620step1Labels = raw33620step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33620step0 raw33620step0Labels permutation35 permutation3
    mixedMoment B raw33620step1 raw33620step1Labels = mixedMoment B raw33620step2 raw33620step2Labels := by
      have ha : raw33620step2 = raw33620step1 := by apply Matrix.ext; unfold raw33620step2 raw33620step1; decide +kernel
      have hl : raw33620step1Labels = labelEmbedding6 ∘ raw33620step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33620step1 raw33620step1Labels raw33620step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4234 node4234Labels := by rfl

theorem canonical33621 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33621 raw33621Labels = mixedMoment B node4684 node4684Labels := by
  calc
    mixedMoment B raw33621 raw33621Labels = mixedMoment B raw33621step0 raw33621step0Labels := by
      have hz : ∀ j, raw33621 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33621step0 = (fun i j => raw33621 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33621step0 raw33621; decide +kernel
      have hl : raw33621step0Labels = raw33621Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33621 raw33621Labels permutation346 hz
    mixedMoment B raw33621step0 raw33621step0Labels = mixedMoment B raw33621step1 raw33621step1Labels := by
      have ha : raw33621step1 = (fun i j => raw33621step0 (permutation35 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33621step1 raw33621step0; decide +kernel
      have hl : raw33621step1Labels = raw33621step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33621step0 raw33621step0Labels permutation35 permutation3
    mixedMoment B raw33621step1 raw33621step1Labels = mixedMoment B raw33621step2 raw33621step2Labels := by
      have ha : raw33621step2 = raw33621step1 := by apply Matrix.ext; unfold raw33621step2 raw33621step1; decide +kernel
      have hl : raw33621step1Labels = labelEmbedding6 ∘ raw33621step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33621step1 raw33621step1Labels raw33621step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4684 node4684Labels := by rfl

theorem canonical33622 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33622 raw33622Labels = mixedMoment B node4722 node4722Labels := by
  calc
    mixedMoment B raw33622 raw33622Labels = mixedMoment B raw33622step0 raw33622step0Labels := by
      have ha : raw33622step0 = (fun i j => raw33622 (permutation179 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33622step0 raw33622; decide +kernel
      have hl : raw33622step0Labels = raw33622Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33622 raw33622Labels permutation179 permutation3
    mixedMoment B raw33622step0 raw33622step0Labels = mixedMoment B raw33622step1 raw33622step1Labels := by
      have ha : raw33622step1 = raw33622step0 := by apply Matrix.ext; unfold raw33622step1 raw33622step0; decide +kernel
      have hl : raw33622step0Labels = labelEmbedding6 ∘ raw33622step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33622step0 raw33622step0Labels raw33622step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4722 node4722Labels := by rfl

theorem canonical33623 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33623 raw33623Labels = mixedMoment B node4828 node4828Labels := by
  calc
    mixedMoment B raw33623 raw33623Labels = mixedMoment B raw33623step0 raw33623step0Labels := by
      have hz : ∀ j, raw33623 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33623step0 = (fun i j => raw33623 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33623step0 raw33623; decide +kernel
      have hl : raw33623step0Labels = raw33623Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33623 raw33623Labels permutation346 hz
    mixedMoment B raw33623step0 raw33623step0Labels = mixedMoment B raw33623step1 raw33623step1Labels := by
      have ha : raw33623step1 = (fun i j => raw33623step0 (permutation45 i) (permutation5 j)) := by apply Matrix.ext; unfold raw33623step1 raw33623step0; decide +kernel
      have hl : raw33623step1Labels = raw33623step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33623step0 raw33623step0Labels permutation45 permutation5
    mixedMoment B raw33623step1 raw33623step1Labels = mixedMoment B raw33623step2 raw33623step2Labels := by
      have ha : raw33623step2 = -raw33623step1 := by apply Matrix.ext; change ∀ i j, raw33623step2 i j = -(raw33623step1 i j); unfold raw33623step2 raw33623step1; decide +kernel
      have hl : raw33623step2Labels = raw33623step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33623step2 raw33623step2Labels = mixedMoment B raw33623step3 raw33623step3Labels := by
      have ha : raw33623step3 = raw33623step2 := by apply Matrix.ext; unfold raw33623step3 raw33623step2; decide +kernel
      have hl : raw33623step2Labels = labelEmbedding8 ∘ raw33623step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33623step2 raw33623step2Labels raw33623step3Labels labelEmbedding8 hl
    _ = mixedMoment B node4828 node4828Labels := by rfl

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

theorem canonical33625 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33625 raw33625Labels = mixedMoment B node4233 node4233Labels := by
  calc
    mixedMoment B raw33625 raw33625Labels = mixedMoment B raw33625step0 raw33625step0Labels := by
      have hz : ∀ j, raw33625 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33625step0 = (fun i j => raw33625 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33625step0 raw33625; decide +kernel
      have hl : raw33625step0Labels = raw33625Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33625 raw33625Labels permutation346 hz
    mixedMoment B raw33625step0 raw33625step0Labels = mixedMoment B raw33625step1 raw33625step1Labels := by
      have ha : raw33625step1 = (fun i j => raw33625step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33625step1 raw33625step0; decide +kernel
      have hl : raw33625step1Labels = raw33625step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33625step0 raw33625step0Labels permutation34 permutation3
    mixedMoment B raw33625step1 raw33625step1Labels = mixedMoment B raw33625step2 raw33625step2Labels := by
      have ha : raw33625step2 = raw33625step1 := by apply Matrix.ext; unfold raw33625step2 raw33625step1; decide +kernel
      have hl : raw33625step1Labels = labelEmbedding6 ∘ raw33625step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33625step1 raw33625step1Labels raw33625step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4233 node4233Labels := by rfl

theorem canonical33626 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33626 raw33626Labels = mixedMoment B node4681 node4681Labels := by
  calc
    mixedMoment B raw33626 raw33626Labels = mixedMoment B raw33626step0 raw33626step0Labels := by
      have hz : ∀ j, raw33626 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33626step0 = (fun i j => raw33626 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33626step0 raw33626; decide +kernel
      have hl : raw33626step0Labels = raw33626Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33626 raw33626Labels permutation346 hz
    mixedMoment B raw33626step0 raw33626step0Labels = mixedMoment B raw33626step1 raw33626step1Labels := by
      have ha : raw33626step1 = (fun i j => raw33626step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33626step1 raw33626step0; decide +kernel
      have hl : raw33626step1Labels = raw33626step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33626step0 raw33626step0Labels permutation34 permutation3
    mixedMoment B raw33626step1 raw33626step1Labels = mixedMoment B raw33626step2 raw33626step2Labels := by
      have ha : raw33626step2 = raw33626step1 := by apply Matrix.ext; unfold raw33626step2 raw33626step1; decide +kernel
      have hl : raw33626step1Labels = labelEmbedding6 ∘ raw33626step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33626step1 raw33626step1Labels raw33626step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4681 node4681Labels := by rfl

theorem canonical33627 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33627 raw33627Labels = mixedMoment B node4721 node4721Labels := by
  calc
    mixedMoment B raw33627 raw33627Labels = mixedMoment B raw33627step0 raw33627step0Labels := by
      have ha : raw33627step0 = (fun i j => raw33627 (permutation178 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33627step0 raw33627; decide +kernel
      have hl : raw33627step0Labels = raw33627Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33627 raw33627Labels permutation178 permutation3
    mixedMoment B raw33627step0 raw33627step0Labels = mixedMoment B raw33627step1 raw33627step1Labels := by
      have ha : raw33627step1 = raw33627step0 := by apply Matrix.ext; unfold raw33627step1 raw33627step0; decide +kernel
      have hl : raw33627step0Labels = labelEmbedding6 ∘ raw33627step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33627step0 raw33627step0Labels raw33627step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4721 node4721Labels := by rfl

theorem canonical33628 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33628 raw33628Labels = mixedMoment B node4827 node4827Labels := by
  calc
    mixedMoment B raw33628 raw33628Labels = mixedMoment B raw33628step0 raw33628step0Labels := by
      have hz : ∀ j, raw33628 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33628step0 = (fun i j => raw33628 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33628step0 raw33628; decide +kernel
      have hl : raw33628step0Labels = raw33628Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33628 raw33628Labels permutation346 hz
    mixedMoment B raw33628step0 raw33628step0Labels = mixedMoment B raw33628step1 raw33628step1Labels := by
      have ha : raw33628step1 = (fun i j => raw33628step0 (permutation44 i) (permutation5 j)) := by apply Matrix.ext; unfold raw33628step1 raw33628step0; decide +kernel
      have hl : raw33628step1Labels = raw33628step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33628step0 raw33628step0Labels permutation44 permutation5
    mixedMoment B raw33628step1 raw33628step1Labels = mixedMoment B raw33628step2 raw33628step2Labels := by
      have ha : raw33628step2 = -raw33628step1 := by apply Matrix.ext; change ∀ i j, raw33628step2 i j = -(raw33628step1 i j); unfold raw33628step2 raw33628step1; decide +kernel
      have hl : raw33628step2Labels = raw33628step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33628step2 raw33628step2Labels = mixedMoment B raw33628step3 raw33628step3Labels := by
      have ha : raw33628step3 = raw33628step2 := by apply Matrix.ext; unfold raw33628step3 raw33628step2; decide +kernel
      have hl : raw33628step2Labels = labelEmbedding8 ∘ raw33628step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33628step2 raw33628step2Labels raw33628step3Labels labelEmbedding8 hl
    _ = mixedMoment B node4827 node4827Labels := by rfl

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

theorem canonical933 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw933 raw933Labels = mixedMoment B node4233 node4233Labels := by
  calc
    mixedMoment B raw933 raw933Labels = mixedMoment B raw933step0 raw933step0Labels := by
      have ha : raw933step0 = (fun i j => raw933 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw933step0 raw933; decide +kernel
      have hl : raw933step0Labels = raw933Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw933 raw933Labels permutation32 permutation4
    mixedMoment B raw933step0 raw933step0Labels = mixedMoment B raw933step1 raw933step1Labels := by
      have ha : raw933step1 = raw933step0 := by apply Matrix.ext; unfold raw933step1 raw933step0; decide +kernel
      have hl : raw933step0Labels = labelEmbedding7 ∘ raw933step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw933step0 raw933step0Labels raw933step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4233 node4233Labels := by rfl

theorem canonical934 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw934 raw934Labels = mixedMoment B node733 node733Labels := by
  calc
    mixedMoment B raw934 raw934Labels = mixedMoment B raw934step0 raw934step0Labels := by
      have ha : raw934step0 = (fun i j => raw934 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw934step0 raw934; decide +kernel
      have hl : raw934step0Labels = raw934Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw934 raw934Labels permutation32 permutation4
    _ = mixedMoment B node733 node733Labels := by rfl

theorem canonical935 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw935 raw935Labels = mixedMoment B node799 node799Labels := by
  calc
    mixedMoment B raw935 raw935Labels = mixedMoment B raw935step0 raw935step0Labels := by
      have ha : raw935step0 = (fun i j => raw935 (permutation38 i) (permutation6 j)) := by apply Matrix.ext; unfold raw935step0 raw935; decide +kernel
      have hl : raw935step0Labels = raw935Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw935 raw935Labels permutation38 permutation6
    mixedMoment B raw935step0 raw935step0Labels = mixedMoment B raw935step1 raw935step1Labels := by
      have ha : raw935step1 = -raw935step0 := by apply Matrix.ext; change ∀ i j, raw935step1 i j = -(raw935step0 i j); unfold raw935step1 raw935step0; decide +kernel
      have hl : raw935step1Labels = raw935step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw935step1 raw935step1Labels = mixedMoment B raw935step2 raw935step2Labels := by
      have ha : raw935step2 = raw935step1 := by apply Matrix.ext; unfold raw935step2 raw935step1; decide +kernel
      have hl : raw935step1Labels = labelEmbedding1 ∘ raw935step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw935step1 raw935step1Labels raw935step2Labels labelEmbedding1 hl
    _ = mixedMoment B node799 node799Labels := by rfl

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

theorem canonical951 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw951 raw951Labels = mixedMoment B node4239 node4239Labels := by
  calc
    mixedMoment B raw951 raw951Labels = mixedMoment B raw951step0 raw951step0Labels := by
      have ha : raw951step0 = (fun i j => raw951 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw951step0 raw951; decide +kernel
      have hl : raw951step0Labels = raw951Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw951 raw951Labels permutation32 permutation4
    mixedMoment B raw951step0 raw951step0Labels = mixedMoment B raw951step1 raw951step1Labels := by
      have ha : raw951step1 = raw951step0 := by apply Matrix.ext; unfold raw951step1 raw951step0; decide +kernel
      have hl : raw951step0Labels = labelEmbedding7 ∘ raw951step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw951step0 raw951step0Labels raw951step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4239 node4239Labels := by rfl

theorem canonical952 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw952 raw952Labels = mixedMoment B node739 node739Labels := by
  calc
    mixedMoment B raw952 raw952Labels = mixedMoment B raw952step0 raw952step0Labels := by
      have ha : raw952step0 = (fun i j => raw952 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw952step0 raw952; decide +kernel
      have hl : raw952step0Labels = raw952Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw952 raw952Labels permutation32 permutation4
    _ = mixedMoment B node739 node739Labels := by rfl

theorem canonical953 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw953 raw953Labels = mixedMoment B node841 node841Labels := by
  calc
    mixedMoment B raw953 raw953Labels = mixedMoment B raw953step0 raw953step0Labels := by
      have ha : raw953step0 = (fun i j => raw953 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw953step0 raw953; decide +kernel
      have hl : raw953step0Labels = raw953Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw953 raw953Labels permutation32 permutation6
    mixedMoment B raw953step0 raw953step0Labels = mixedMoment B raw953step1 raw953step1Labels := by
      have ha : raw953step1 = -raw953step0 := by apply Matrix.ext; change ∀ i j, raw953step1 i j = -(raw953step0 i j); unfold raw953step1 raw953step0; decide +kernel
      have hl : raw953step1Labels = raw953step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw953step1 raw953step1Labels = mixedMoment B raw953step2 raw953step2Labels := by
      have ha : raw953step2 = raw953step1 := by apply Matrix.ext; unfold raw953step2 raw953step1; decide +kernel
      have hl : raw953step1Labels = labelEmbedding1 ∘ raw953step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw953step1 raw953step1Labels raw953step2Labels labelEmbedding1 hl
    _ = mixedMoment B node841 node841Labels := by rfl

theorem canonical993 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw993 raw993Labels = mixedMoment B node4268 node4268Labels := by
  calc
    mixedMoment B raw993 raw993Labels = mixedMoment B raw993step0 raw993step0Labels := by
      have ha : raw993step0 = (fun i j => raw993 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw993step0 raw993; decide +kernel
      have hl : raw993step0Labels = raw993Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw993 raw993Labels permutation32 permutation4
    mixedMoment B raw993step0 raw993step0Labels = mixedMoment B raw993step1 raw993step1Labels := by
      have ha : raw993step1 = raw993step0 := by apply Matrix.ext; unfold raw993step1 raw993step0; decide +kernel
      have hl : raw993step0Labels = labelEmbedding7 ∘ raw993step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw993step0 raw993step0Labels raw993step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4268 node4268Labels := by rfl

theorem canonical994 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw994 raw994Labels = mixedMoment B node811 node811Labels := by
  calc
    mixedMoment B raw994 raw994Labels = mixedMoment B raw994step0 raw994step0Labels := by
      have ha : raw994step0 = (fun i j => raw994 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw994step0 raw994; decide +kernel
      have hl : raw994step0Labels = raw994Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw994 raw994Labels permutation32 permutation4
    _ = mixedMoment B node811 node811Labels := by rfl

theorem canonical995 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw995 raw995Labels = mixedMoment B node824 node824Labels := by
  calc
    mixedMoment B raw995 raw995Labels = mixedMoment B raw995step0 raw995step0Labels := by
      have ha : raw995step0 = (fun i j => raw995 (permutation50 i) (permutation6 j)) := by apply Matrix.ext; unfold raw995step0 raw995; decide +kernel
      have hl : raw995step0Labels = raw995Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw995 raw995Labels permutation50 permutation6
    mixedMoment B raw995step0 raw995step0Labels = mixedMoment B raw995step1 raw995step1Labels := by
      have ha : raw995step1 = -raw995step0 := by apply Matrix.ext; change ∀ i j, raw995step1 i j = -(raw995step0 i j); unfold raw995step1 raw995step0; decide +kernel
      have hl : raw995step1Labels = raw995step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw995step1 raw995step1Labels = mixedMoment B raw995step2 raw995step2Labels := by
      have ha : raw995step2 = raw995step1 := by apply Matrix.ext; unfold raw995step2 raw995step1; decide +kernel
      have hl : raw995step1Labels = labelEmbedding1 ∘ raw995step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw995step1 raw995step1Labels raw995step2Labels labelEmbedding1 hl
    _ = mixedMoment B node824 node824Labels := by rfl

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

theorem canonical10900 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10900 raw10900Labels = mixedMoment B node5451 node5451Labels := by
  calc
    mixedMoment B raw10900 raw10900Labels = mixedMoment B raw10900step0 raw10900step0Labels := by
      have hz : ∀ j, raw10900 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10900step0 = (fun i j => raw10900 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10900step0 raw10900; decide +kernel
      have hl : raw10900step0Labels = raw10900Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10900 raw10900Labels permutation434 hz
    mixedMoment B raw10900step0 raw10900step0Labels = mixedMoment B raw10900step1 raw10900step1Labels := by
      have hz : ∀ j, raw10900step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw10900step1 = (fun i j => raw10900step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw10900step1 raw10900step0; decide +kernel
      have hl : raw10900step1Labels = raw10900step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10900step0 raw10900step0Labels permutation80 hz
    mixedMoment B raw10900step1 raw10900step1Labels = mixedMoment B raw10900step2 raw10900step2Labels := by
      have ha : raw10900step2 = (fun i j => raw10900step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10900step2 raw10900step1; decide +kernel
      have hl : raw10900step2Labels = raw10900step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10900step1 raw10900step1Labels permutation8 permutation3
    mixedMoment B raw10900step2 raw10900step2Labels = mixedMoment B raw10900step3 raw10900step3Labels := by
      have ha : raw10900step3 = raw10900step2 := by apply Matrix.ext; unfold raw10900step3 raw10900step2; decide +kernel
      have hl : raw10900step2Labels = labelEmbedding6 ∘ raw10900step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10900step2 raw10900step2Labels raw10900step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5451 node5451Labels := by rfl

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

theorem canonical10915 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10915 raw10915Labels = mixedMoment B node4268 node4268Labels := by
  calc
    mixedMoment B raw10915 raw10915Labels = mixedMoment B raw10915step0 raw10915step0Labels := by
      have hz : ∀ j, raw10915 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10915step0 = (fun i j => raw10915 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10915step0 raw10915; decide +kernel
      have hl : raw10915step0Labels = raw10915Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10915 raw10915Labels permutation346 hz
    mixedMoment B raw10915step0 raw10915step0Labels = mixedMoment B raw10915step1 raw10915step1Labels := by
      have ha : raw10915step1 = (fun i j => raw10915step0 (permutation47 i) (permutation5 j)) := by apply Matrix.ext; unfold raw10915step1 raw10915step0; decide +kernel
      have hl : raw10915step1Labels = raw10915step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10915step0 raw10915step0Labels permutation47 permutation5
    mixedMoment B raw10915step1 raw10915step1Labels = mixedMoment B raw10915step2 raw10915step2Labels := by
      have ha : raw10915step2 = -raw10915step1 := by apply Matrix.ext; change ∀ i j, raw10915step2 i j = -(raw10915step1 i j); unfold raw10915step2 raw10915step1; decide +kernel
      have hl : raw10915step2Labels = raw10915step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw10915step2 raw10915step2Labels = mixedMoment B raw10915step3 raw10915step3Labels := by
      have ha : raw10915step3 = raw10915step2 := by apply Matrix.ext; unfold raw10915step3 raw10915step2; decide +kernel
      have hl : raw10915step2Labels = labelEmbedding8 ∘ raw10915step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10915step2 raw10915step2Labels raw10915step3Labels labelEmbedding8 hl
    _ = mixedMoment B node4268 node4268Labels := by rfl

theorem canonical10917 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10917 raw10917Labels = mixedMoment B node4740 node4740Labels := by
  calc
    mixedMoment B raw10917 raw10917Labels = mixedMoment B raw10917step0 raw10917step0Labels := by
      have ha : raw10917step0 = (fun i j => raw10917 (permutation191 i) (permutation5 j)) := by apply Matrix.ext; unfold raw10917step0 raw10917; decide +kernel
      have hl : raw10917step0Labels = raw10917Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10917 raw10917Labels permutation191 permutation5
    mixedMoment B raw10917step0 raw10917step0Labels = mixedMoment B raw10917step1 raw10917step1Labels := by
      have ha : raw10917step1 = -raw10917step0 := by apply Matrix.ext; change ∀ i j, raw10917step1 i j = -(raw10917step0 i j); unfold raw10917step1 raw10917step0; decide +kernel
      have hl : raw10917step1Labels = raw10917step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw10917step1 raw10917step1Labels = mixedMoment B raw10917step2 raw10917step2Labels := by
      have ha : raw10917step2 = raw10917step1 := by apply Matrix.ext; unfold raw10917step2 raw10917step1; decide +kernel
      have hl : raw10917step1Labels = labelEmbedding8 ∘ raw10917step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10917step1 raw10917step1Labels raw10917step2Labels labelEmbedding8 hl
    _ = mixedMoment B node4740 node4740Labels := by rfl

theorem canonical10918 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10918 raw10918Labels = mixedMoment B node4839 node4839Labels := by
  calc
    mixedMoment B raw10918 raw10918Labels = mixedMoment B raw10918step0 raw10918step0Labels := by
      have hz : ∀ j, raw10918 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10918step0 = (fun i j => raw10918 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10918step0 raw10918; decide +kernel
      have hl : raw10918step0Labels = raw10918Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10918 raw10918Labels permutation346 hz
    mixedMoment B raw10918step0 raw10918step0Labels = mixedMoment B raw10918step1 raw10918step1Labels := by
      have ha : raw10918step1 = (fun i j => raw10918step0 (permutation47 i) (permutation5 j)) := by apply Matrix.ext; unfold raw10918step1 raw10918step0; decide +kernel
      have hl : raw10918step1Labels = raw10918step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10918step0 raw10918step0Labels permutation47 permutation5
    mixedMoment B raw10918step1 raw10918step1Labels = mixedMoment B raw10918step2 raw10918step2Labels := by
      have ha : raw10918step2 = -raw10918step1 := by apply Matrix.ext; change ∀ i j, raw10918step2 i j = -(raw10918step1 i j); unfold raw10918step2 raw10918step1; decide +kernel
      have hl : raw10918step2Labels = raw10918step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw10918step2 raw10918step2Labels = mixedMoment B raw10918step3 raw10918step3Labels := by
      have ha : raw10918step3 = raw10918step2 := by apply Matrix.ext; unfold raw10918step3 raw10918step2; decide +kernel
      have hl : raw10918step2Labels = labelEmbedding8 ∘ raw10918step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10918step2 raw10918step2Labels raw10918step3Labels labelEmbedding8 hl
    _ = mixedMoment B node4839 node4839Labels := by rfl

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

theorem canonical10921 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10921 raw10921Labels = mixedMoment B node4875 node4875Labels := by
  calc
    mixedMoment B raw10921 raw10921Labels = mixedMoment B raw10921step0 raw10921step0Labels := by
      have hz : ∀ j, raw10921 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10921step0 = (fun i j => raw10921 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10921step0 raw10921; decide +kernel
      have hl : raw10921step0Labels = raw10921Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10921 raw10921Labels permutation434 hz
    mixedMoment B raw10921step0 raw10921step0Labels = mixedMoment B raw10921step1 raw10921step1Labels := by
      have hz : ∀ j, raw10921step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw10921step1 = (fun i j => raw10921step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw10921step1 raw10921step0; decide +kernel
      have hl : raw10921step1Labels = raw10921step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10921step0 raw10921step0Labels permutation80 hz
    mixedMoment B raw10921step1 raw10921step1Labels = mixedMoment B raw10921step2 raw10921step2Labels := by
      have ha : raw10921step2 = (fun i j => raw10921step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10921step2 raw10921step1; decide +kernel
      have hl : raw10921step2Labels = raw10921step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10921step1 raw10921step1Labels permutation8 permutation3
    mixedMoment B raw10921step2 raw10921step2Labels = mixedMoment B raw10921step3 raw10921step3Labels := by
      have ha : raw10921step3 = raw10921step2 := by apply Matrix.ext; unfold raw10921step3 raw10921step2; decide +kernel
      have hl : raw10921step2Labels = labelEmbedding6 ∘ raw10921step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10921step2 raw10921step2Labels raw10921step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4875 node4875Labels := by rfl

theorem canonical10926 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10926 raw10926Labels = mixedMoment B node4868 node4868Labels := by
  calc
    mixedMoment B raw10926 raw10926Labels = mixedMoment B raw10926step0 raw10926step0Labels := by
      have hz : ∀ j, raw10926 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10926step0 = (fun i j => raw10926 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10926step0 raw10926; decide +kernel
      have hl : raw10926step0Labels = raw10926Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10926 raw10926Labels permutation434 hz
    mixedMoment B raw10926step0 raw10926step0Labels = mixedMoment B raw10926step1 raw10926step1Labels := by
      have hz : ∀ j, raw10926step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw10926step1 = (fun i j => raw10926step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw10926step1 raw10926step0; decide +kernel
      have hl : raw10926step1Labels = raw10926step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10926step0 raw10926step0Labels permutation80 hz
    mixedMoment B raw10926step1 raw10926step1Labels = mixedMoment B raw10926step2 raw10926step2Labels := by
      have ha : raw10926step2 = (fun i j => raw10926step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10926step2 raw10926step1; decide +kernel
      have hl : raw10926step2Labels = raw10926step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10926step1 raw10926step1Labels permutation8 permutation3
    mixedMoment B raw10926step2 raw10926step2Labels = mixedMoment B raw10926step3 raw10926step3Labels := by
      have ha : raw10926step3 = raw10926step2 := by apply Matrix.ext; unfold raw10926step3 raw10926step2; decide +kernel
      have hl : raw10926step2Labels = labelEmbedding6 ∘ raw10926step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10926step2 raw10926step2Labels raw10926step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4868 node4868Labels := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical129
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons66
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

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

theorem singleton4233 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4233 node4233Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node733 node733Labels + mixedMoment B node799 node799Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw933 singletonSmall4233
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4233) = raw933Labels := by decide +kernel
  rw [hl, canonical933 B hB] at h
  have hc0 : mixedMoment B raw933 (Fin.cases (0 : Fin 2) singletonSmall4233) =
      mixedMoment B node733 node733Labels := by
    have ha : raw933 = raw934 := by apply Matrix.ext; unfold raw933 raw934; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4233 = raw934Labels := by decide +kernel
    rw [ha, hj, canonical934 B hB]
  have hc1 : mixedMoment B raw933 (Fin.cases (1 : Fin 2) singletonSmall4233) =
      mixedMoment B node799 node799Labels := by
    have ha : raw933 = raw935 := by apply Matrix.ext; unfold raw933 raw935; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4233 = raw935Labels := by decide +kernel
    rw [ha, hj, canonical935 B hB]
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

theorem singleton4239 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4239 node4239Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node739 node739Labels + mixedMoment B node841 node841Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw951 singletonSmall4239
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4239) = raw951Labels := by decide +kernel
  rw [hl, canonical951 B hB] at h
  have hc0 : mixedMoment B raw951 (Fin.cases (0 : Fin 2) singletonSmall4239) =
      mixedMoment B node739 node739Labels := by
    have ha : raw951 = raw952 := by apply Matrix.ext; unfold raw951 raw952; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4239 = raw952Labels := by decide +kernel
    rw [ha, hj, canonical952 B hB]
  have hc1 : mixedMoment B raw951 (Fin.cases (1 : Fin 2) singletonSmall4239) =
      mixedMoment B node841 node841Labels := by
    have ha : raw951 = raw953 := by apply Matrix.ext; unfold raw951 raw953; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4239 = raw953Labels := by decide +kernel
    rw [ha, hj, canonical953 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4268 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4268 node4268Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node811 node811Labels + mixedMoment B node824 node824Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw993 singletonSmall4268
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4268) = raw993Labels := by decide +kernel
  rw [hl, canonical993 B hB] at h
  have hc0 : mixedMoment B raw993 (Fin.cases (0 : Fin 2) singletonSmall4268) =
      mixedMoment B node811 node811Labels := by
    have ha : raw993 = raw994 := by apply Matrix.ext; unfold raw993 raw994; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4268 = raw994Labels := by decide +kernel
    rw [ha, hj, canonical994 B hB]
  have hc1 : mixedMoment B raw993 (Fin.cases (1 : Fin 2) singletonSmall4268) =
      mixedMoment B node824 node824Labels := by
    have ha : raw993 = raw995 := by apply Matrix.ext; unfold raw993 raw995; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4268 = raw995Labels := by decide +kernel
    rw [ha, hj, canonical995 B hB]
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

theorem singleton4681 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4681 node4681Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1807 node1807Labels + mixedMoment B node2151 node2151Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1563 singletonSmall4681
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4681) = raw1563Labels := by decide +kernel
  rw [hl, canonical1563 B hB] at h
  have hc0 : mixedMoment B raw1563 (Fin.cases (0 : Fin 2) singletonSmall4681) =
      mixedMoment B node1807 node1807Labels := by
    have ha : raw1563 = raw1564 := by apply Matrix.ext; unfold raw1563 raw1564; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4681 = raw1564Labels := by decide +kernel
    rw [ha, hj, canonical1564 B hB]
  have hc1 : mixedMoment B raw1563 (Fin.cases (1 : Fin 2) singletonSmall4681) =
      mixedMoment B node2151 node2151Labels := by
    have ha : raw1563 = raw1565 := by apply Matrix.ext; unfold raw1563 raw1565; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4681 = raw1565Labels := by decide +kernel
    rw [ha, hj, canonical1565 B hB]
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

theorem singleton4689 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4689 node4689Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1815 node1815Labels + mixedMoment B node2166 node2166Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1578 singletonSmall4689
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4689) = raw1578Labels := by decide +kernel
  rw [hl, canonical1578 B hB] at h
  have hc0 : mixedMoment B raw1578 (Fin.cases (0 : Fin 2) singletonSmall4689) =
      mixedMoment B node1815 node1815Labels := by
    have ha : raw1578 = raw1579 := by apply Matrix.ext; unfold raw1578 raw1579; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4689 = raw1579Labels := by decide +kernel
    rw [ha, hj, canonical1579 B hB]
  have hc1 : mixedMoment B raw1578 (Fin.cases (1 : Fin 2) singletonSmall4689) =
      mixedMoment B node2166 node2166Labels := by
    have ha : raw1578 = raw1580 := by apply Matrix.ext; unfold raw1578 raw1580; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4689 = raw1580Labels := by decide +kernel
    rw [ha, hj, canonical1580 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4721 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4721 node4721Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1875 node1875Labels + mixedMoment B node1905 node1905Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1620 singletonSmall4721
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4721) = raw1620Labels := by decide +kernel
  rw [hl, canonical1620 B hB] at h
  have hc0 : mixedMoment B raw1620 (Fin.cases (0 : Fin 2) singletonSmall4721) =
      mixedMoment B node1875 node1875Labels := by
    have ha : raw1620 = raw1621 := by apply Matrix.ext; unfold raw1620 raw1621; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4721 = raw1621Labels := by decide +kernel
    rw [ha, hj, canonical1621 B hB]
  have hc1 : mixedMoment B raw1620 (Fin.cases (1 : Fin 2) singletonSmall4721) =
      mixedMoment B node1905 node1905Labels := by
    have ha : raw1620 = raw1622 := by apply Matrix.ext; unfold raw1620 raw1622; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4721 = raw1622Labels := by decide +kernel
    rw [ha, hj, canonical1622 B hB]
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

theorem singleton4725 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4725 node4725Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1879 node1879Labels + mixedMoment B node1936 node1936Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1632 singletonSmall4725
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4725) = raw1632Labels := by decide +kernel
  rw [hl, canonical1632 B hB] at h
  have hc0 : mixedMoment B raw1632 (Fin.cases (0 : Fin 2) singletonSmall4725) =
      mixedMoment B node1879 node1879Labels := by
    have ha : raw1632 = raw1633 := by apply Matrix.ext; unfold raw1632 raw1633; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4725 = raw1633Labels := by decide +kernel
    rw [ha, hj, canonical1633 B hB]
  have hc1 : mixedMoment B raw1632 (Fin.cases (1 : Fin 2) singletonSmall4725) =
      mixedMoment B node1936 node1936Labels := by
    have ha : raw1632 = raw1634 := by apply Matrix.ext; unfold raw1632 raw1634; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4725 = raw1634Labels := by decide +kernel
    rw [ha, hj, canonical1634 B hB]
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

theorem singleton4827 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4827 node4827Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2047 node2047Labels + mixedMoment B node2079 node2079Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1755 singletonSmall4827
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4827) = raw1755Labels := by decide +kernel
  rw [hl, canonical1755 B hB] at h
  have hc0 : mixedMoment B raw1755 (Fin.cases (0 : Fin 2) singletonSmall4827) =
      mixedMoment B node2047 node2047Labels := by
    have ha : raw1755 = raw1756 := by apply Matrix.ext; unfold raw1755 raw1756; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4827 = raw1756Labels := by decide +kernel
    rw [ha, hj, canonical1756 B hB]
  have hc1 : mixedMoment B raw1755 (Fin.cases (1 : Fin 2) singletonSmall4827) =
      mixedMoment B node2079 node2079Labels := by
    have ha : raw1755 = raw1757 := by apply Matrix.ext; unfold raw1755 raw1757; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4827 = raw1757Labels := by decide +kernel
    rw [ha, hj, canonical1757 B hB]
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

theorem singleton4868 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4868 node4868Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2109 node2109Labels + mixedMoment B node2261 node2261Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1797 singletonSmall4868
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4868) = raw1797Labels := by decide +kernel
  rw [hl, canonical1797 B hB] at h
  have hc0 : mixedMoment B raw1797 (Fin.cases (0 : Fin 2) singletonSmall4868) =
      mixedMoment B node2109 node2109Labels := by
    have ha : raw1797 = raw1798 := by apply Matrix.ext; unfold raw1797 raw1798; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4868 = raw1798Labels := by decide +kernel
    rw [ha, hj, canonical1798 B hB]
  have hc1 : mixedMoment B raw1797 (Fin.cases (1 : Fin 2) singletonSmall4868) =
      mixedMoment B node2261 node2261Labels := by
    have ha : raw1797 = raw1799 := by apply Matrix.ext; unfold raw1797 raw1799; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4868 = raw1799Labels := by decide +kernel
    rw [ha, hj, canonical1799 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4875 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4875 node4875Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2116 node2116Labels + mixedMoment B node2288 node2288Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1809 singletonSmall4875
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4875) = raw1809Labels := by decide +kernel
  rw [hl, canonical1809 B hB] at h
  have hc0 : mixedMoment B raw1809 (Fin.cases (0 : Fin 2) singletonSmall4875) =
      mixedMoment B node2116 node2116Labels := by
    have ha : raw1809 = raw1810 := by apply Matrix.ext; unfold raw1809 raw1810; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4875 = raw1810Labels := by decide +kernel
    rw [ha, hj, canonical1810 B hB]
  have hc1 : mixedMoment B raw1809 (Fin.cases (1 : Fin 2) singletonSmall4875) =
      mixedMoment B node2288 node2288Labels := by
    have ha : raw1809 = raw1811 := by apply Matrix.ext; unfold raw1809 raw1811; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4875 = raw1811Labels := by decide +kernel
    rw [ha, hj, canonical1811 B hB]
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

theorem singleton4896 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4896 node4896Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2266 node2266Labels + mixedMoment B node2278 node2278Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1824 singletonSmall4896
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4896) = raw1824Labels := by decide +kernel
  rw [hl, canonical1824 B hB] at h
  have hc0 : mixedMoment B raw1824 (Fin.cases (0 : Fin 2) singletonSmall4896) =
      mixedMoment B node2266 node2266Labels := by
    have ha : raw1824 = raw1825 := by apply Matrix.ext; unfold raw1824 raw1825; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4896 = raw1825Labels := by decide +kernel
    rw [ha, hj, canonical1825 B hB]
  have hc1 : mixedMoment B raw1824 (Fin.cases (1 : Fin 2) singletonSmall4896) =
      mixedMoment B node2278 node2278Labels := by
    have ha : raw1824 = raw1826 := by apply Matrix.ext; unfold raw1824 raw1826; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4896 = raw1826Labels := by decide +kernel
    rw [ha, hj, canonical1826 B hB]
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

theorem sound732 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node732 node732Labels = Sparse.eval nodeValue732 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 732) = mixedMoment B node732 node732Labels := rfl
  simpa [nodeValue732, Sparse.eval] using hc.symm

theorem sound733 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node733 node733Labels = Sparse.eval nodeValue733 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 733) = mixedMoment B node733 node733Labels := rfl
  simpa [nodeValue733, Sparse.eval] using hc.symm

theorem sound734 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node734 node734Labels = Sparse.eval nodeValue734 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 734) = mixedMoment B node734 node734Labels := rfl
  simpa [nodeValue734, Sparse.eval] using hc.symm

theorem sound739 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node739 node739Labels = Sparse.eval nodeValue739 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 739) = mixedMoment B node739 node739Labels := rfl
  simpa [nodeValue739, Sparse.eval] using hc.symm

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

theorem sound798 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node798 node798Labels = Sparse.eval nodeValue798 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 798) = mixedMoment B node798 node798Labels := rfl
  simpa [nodeValue798, Sparse.eval] using hc.symm

theorem sound799 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node799 node799Labels = Sparse.eval nodeValue799 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 799) = mixedMoment B node799 node799Labels := rfl
  simpa [nodeValue799, Sparse.eval] using hc.symm

theorem sound800 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node800 node800Labels = Sparse.eval nodeValue800 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 800) = mixedMoment B node800 node800Labels := rfl
  simpa [nodeValue800, Sparse.eval] using hc.symm

theorem sound811 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node811 node811Labels = Sparse.eval nodeValue811 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 811) = mixedMoment B node811 node811Labels := rfl
  simpa [nodeValue811, Sparse.eval] using hc.symm

theorem sound824 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node824 node824Labels = Sparse.eval nodeValue824 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 824) = mixedMoment B node824 node824Labels := rfl
  simpa [nodeValue824, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound13
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound841 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node841 node841Labels = Sparse.eval nodeValue841 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 841) = mixedMoment B node841 node841Labels := rfl
  simpa [nodeValue841, Sparse.eval] using hc.symm

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

theorem sound1805 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1805 node1805Labels = Sparse.eval nodeValue1805 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1805) = mixedMoment B node1805 node1805Labels := rfl
  simpa [nodeValue1805, Sparse.eval] using hc.symm

theorem sound1807 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1807 node1807Labels = Sparse.eval nodeValue1807 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1807) = mixedMoment B node1807 node1807Labels := rfl
  simpa [nodeValue1807, Sparse.eval] using hc.symm

theorem sound1810 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1810 node1810Labels = Sparse.eval nodeValue1810 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1810) = mixedMoment B node1810 node1810Labels := rfl
  simpa [nodeValue1810, Sparse.eval] using hc.symm

theorem sound1815 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1815 node1815Labels = Sparse.eval nodeValue1815 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1815) = mixedMoment B node1815 node1815Labels := rfl
  simpa [nodeValue1815, Sparse.eval] using hc.symm

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

theorem sound1875 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1875 node1875Labels = Sparse.eval nodeValue1875 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1875) = mixedMoment B node1875 node1875Labels := rfl
  simpa [nodeValue1875, Sparse.eval] using hc.symm

theorem sound1876 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1876 node1876Labels = Sparse.eval nodeValue1876 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1876) = mixedMoment B node1876 node1876Labels := rfl
  simpa [nodeValue1876, Sparse.eval] using hc.symm

theorem sound1879 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1879 node1879Labels = Sparse.eval nodeValue1879 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1879) = mixedMoment B node1879 node1879Labels := rfl
  simpa [nodeValue1879, Sparse.eval] using hc.symm

theorem sound1905 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1905 node1905Labels = Sparse.eval nodeValue1905 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1905) = mixedMoment B node1905 node1905Labels := rfl
  simpa [nodeValue1905, Sparse.eval] using hc.symm

theorem sound1906 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1906 node1906Labels = Sparse.eval nodeValue1906 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1906) = mixedMoment B node1906 node1906Labels := rfl
  simpa [nodeValue1906, Sparse.eval] using hc.symm

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

theorem sound1936 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1936 node1936Labels = Sparse.eval nodeValue1936 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1936) = mixedMoment B node1936 node1936Labels := rfl
  simpa [nodeValue1936, Sparse.eval] using hc.symm

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

theorem sound2046 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2046 node2046Labels = Sparse.eval nodeValue2046 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2046) = mixedMoment B node2046 node2046Labels := rfl
  simpa [nodeValue2046, Sparse.eval] using hc.symm

theorem sound2047 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2047 node2047Labels = Sparse.eval nodeValue2047 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2047) = mixedMoment B node2047 node2047Labels := rfl
  simpa [nodeValue2047, Sparse.eval] using hc.symm

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

theorem sound2058 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2058 node2058Labels = Sparse.eval nodeValue2058 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2058) = mixedMoment B node2058 node2058Labels := rfl
  simpa [nodeValue2058, Sparse.eval] using hc.symm

theorem sound2077 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2077 node2077Labels = Sparse.eval nodeValue2077 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2077) = mixedMoment B node2077 node2077Labels := rfl
  simpa [nodeValue2077, Sparse.eval] using hc.symm

theorem sound2079 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2079 node2079Labels = Sparse.eval nodeValue2079 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2079) = mixedMoment B node2079 node2079Labels := rfl
  simpa [nodeValue2079, Sparse.eval] using hc.symm

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

theorem sound2109 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2109 node2109Labels = Sparse.eval nodeValue2109 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2109) = mixedMoment B node2109 node2109Labels := rfl
  simpa [nodeValue2109, Sparse.eval] using hc.symm

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

theorem sound2116 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2116 node2116Labels = Sparse.eval nodeValue2116 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2116) = mixedMoment B node2116 node2116Labels := rfl
  simpa [nodeValue2116, Sparse.eval] using hc.symm

theorem sound2150 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2150 node2150Labels = Sparse.eval nodeValue2150 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2150) = mixedMoment B node2150 node2150Labels := rfl
  simpa [nodeValue2150, Sparse.eval] using hc.symm

theorem sound2151 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2151 node2151Labels = Sparse.eval nodeValue2151 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2151) = mixedMoment B node2151 node2151Labels := rfl
  simpa [nodeValue2151, Sparse.eval] using hc.symm

theorem sound2152 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2152 node2152Labels = Sparse.eval nodeValue2152 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2152) = mixedMoment B node2152 node2152Labels := rfl
  simpa [nodeValue2152, Sparse.eval] using hc.symm

theorem sound2166 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2166 node2166Labels = Sparse.eval nodeValue2166 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2166) = mixedMoment B node2166 node2166Labels := rfl
  simpa [nodeValue2166, Sparse.eval] using hc.symm

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

theorem sound2261 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2261 node2261Labels = Sparse.eval nodeValue2261 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2261) = mixedMoment B node2261 node2261Labels := rfl
  simpa [nodeValue2261, Sparse.eval] using hc.symm

theorem sound2266 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2266 node2266Labels = Sparse.eval nodeValue2266 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2266) = mixedMoment B node2266 node2266Labels := rfl
  simpa [nodeValue2266, Sparse.eval] using hc.symm

theorem sound2277 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2277 node2277Labels = Sparse.eval nodeValue2277 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2277) = mixedMoment B node2277 node2277Labels := rfl
  simpa [nodeValue2277, Sparse.eval] using hc.symm

theorem sound2278 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2278 node2278Labels = Sparse.eval nodeValue2278 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2278) = mixedMoment B node2278 node2278Labels := rfl
  simpa [nodeValue2278, Sparse.eval] using hc.symm

theorem sound2288 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2288 node2288Labels = Sparse.eval nodeValue2288 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2288) = mixedMoment B node2288 node2288Labels := rfl
  simpa [nodeValue2288, Sparse.eval] using hc.symm

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

theorem sound3787 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3787 node3787Labels = Sparse.eval nodeValue3787 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3787) = mixedMoment B node3787 node3787Labels := rfl
  simpa [nodeValue3787, Sparse.eval] using hc.symm

theorem sound3804 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3804 node3804Labels = Sparse.eval nodeValue3804 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3804) = mixedMoment B node3804 node3804Labels := rfl
  simpa [nodeValue3804, Sparse.eval] using hc.symm

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

theorem sound3857 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3857 node3857Labels = Sparse.eval nodeValue3857 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3857) = mixedMoment B node3857 node3857Labels := rfl
  simpa [nodeValue3857, Sparse.eval] using hc.symm

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound66
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound4232 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4232 node4232Labels = Sparse.eval nodeValue4232 (mixedVector B) := by
  have h := singleton4232 B _hB
  rw [sound732 B _hB _hF, sound798 B _hB _hF] at h
  norm_num [nodeValue4232, nodeValue732, nodeValue798, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4233 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4233 node4233Labels = Sparse.eval nodeValue4233 (mixedVector B) := by
  have h := singleton4233 B _hB
  rw [sound733 B _hB _hF, sound799 B _hB _hF] at h
  norm_num [nodeValue4233, nodeValue733, nodeValue799, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4234 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4234 node4234Labels = Sparse.eval nodeValue4234 (mixedVector B) := by
  have h := singleton4234 B _hB
  rw [sound734 B _hB _hF, sound800 B _hB _hF] at h
  norm_num [nodeValue4234, nodeValue734, nodeValue800, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4239 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4239 node4239Labels = Sparse.eval nodeValue4239 (mixedVector B) := by
  have h := singleton4239 B _hB
  rw [sound739 B _hB _hF, sound841 B _hB _hF] at h
  norm_num [nodeValue4239, nodeValue739, nodeValue841, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4268 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4268 node4268Labels = Sparse.eval nodeValue4268 (mixedVector B) := by
  have h := singleton4268 B _hB
  rw [sound811 B _hB _hF, sound824 B _hB _hF] at h
  norm_num [nodeValue4268, nodeValue811, nodeValue824, Sparse.eval] at h ⊢
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

theorem sound4679 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4679 node4679Labels = Sparse.eval nodeValue4679 (mixedVector B) := by
  have h := singleton4679 B _hB
  rw [sound1805 B _hB _hF, sound2150 B _hB _hF] at h
  norm_num [nodeValue4679, nodeValue1805, nodeValue2150, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4681 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4681 node4681Labels = Sparse.eval nodeValue4681 (mixedVector B) := by
  have h := singleton4681 B _hB
  rw [sound1807 B _hB _hF, sound2151 B _hB _hF] at h
  norm_num [nodeValue4681, nodeValue1807, nodeValue2151, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4684 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4684 node4684Labels = Sparse.eval nodeValue4684 (mixedVector B) := by
  have h := singleton4684 B _hB
  rw [sound1810 B _hB _hF, sound2152 B _hB _hF] at h
  norm_num [nodeValue4684, nodeValue1810, nodeValue2152, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4689 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4689 node4689Labels = Sparse.eval nodeValue4689 (mixedVector B) := by
  have h := singleton4689 B _hB
  rw [sound1815 B _hB _hF, sound2166 B _hB _hF] at h
  norm_num [nodeValue4689, nodeValue1815, nodeValue2166, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4721 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4721 node4721Labels = Sparse.eval nodeValue4721 (mixedVector B) := by
  have h := singleton4721 B _hB
  rw [sound1875 B _hB _hF, sound1905 B _hB _hF] at h
  norm_num [nodeValue4721, nodeValue1875, nodeValue1905, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4722 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4722 node4722Labels = Sparse.eval nodeValue4722 (mixedVector B) := by
  have h := singleton4722 B _hB
  rw [sound1876 B _hB _hF, sound1906 B _hB _hF] at h
  norm_num [nodeValue4722, nodeValue1876, nodeValue1906, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4725 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4725 node4725Labels = Sparse.eval nodeValue4725 (mixedVector B) := by
  have h := singleton4725 B _hB
  rw [sound1879 B _hB _hF, sound1936 B _hB _hF] at h
  norm_num [nodeValue4725, nodeValue1879, nodeValue1936, Sparse.eval] at h ⊢
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

theorem sound4740 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4740 node4740Labels = Sparse.eval nodeValue4740 (mixedVector B) := by
  have h := singleton4740 B _hB
  rw [sound1913 B _hB _hF, sound1922 B _hB _hF] at h
  norm_num [nodeValue4740, nodeValue1913, nodeValue1922, Sparse.eval] at h ⊢
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

theorem sound4826 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4826 node4826Labels = Sparse.eval nodeValue4826 (mixedVector B) := by
  have h := singleton4826 B _hB
  rw [sound2046 B _hB _hF, sound2077 B _hB _hF] at h
  norm_num [nodeValue4826, nodeValue2046, nodeValue2077, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4827 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4827 node4827Labels = Sparse.eval nodeValue4827 (mixedVector B) := by
  have h := singleton4827 B _hB
  rw [sound2047 B _hB _hF, sound2079 B _hB _hF] at h
  norm_num [nodeValue4827, nodeValue2047, nodeValue2079, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4828 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4828 node4828Labels = Sparse.eval nodeValue4828 (mixedVector B) := by
  have h := singleton4828 B _hB
  rw [sound2048 B _hB _hF, sound2082 B _hB _hF] at h
  norm_num [nodeValue4828, nodeValue2048, nodeValue2082, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4839 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4839 node4839Labels = Sparse.eval nodeValue4839 (mixedVector B) := by
  have h := singleton4839 B _hB
  rw [sound2058 B _hB _hF, sound2216 B _hB _hF] at h
  norm_num [nodeValue4839, nodeValue2058, nodeValue2216, Sparse.eval] at h ⊢
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

theorem sound4868 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4868 node4868Labels = Sparse.eval nodeValue4868 (mixedVector B) := by
  have h := singleton4868 B _hB
  rw [sound2109 B _hB _hF, sound2261 B _hB _hF] at h
  norm_num [nodeValue4868, nodeValue2109, nodeValue2261, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4875 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4875 node4875Labels = Sparse.eval nodeValue4875 (mixedVector B) := by
  have h := singleton4875 B _hB
  rw [sound2116 B _hB _hF, sound2288 B _hB _hF] at h
  norm_num [nodeValue4875, nodeValue2116, nodeValue2288, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4889 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4889 node4889Labels = Sparse.eval nodeValue4889 (mixedVector B) := by
  have h := singleton4889 B _hB
  rw [sound2245 B _hB _hF, sound2277 B _hB _hF] at h
  norm_num [nodeValue4889, nodeValue2245, nodeValue2277, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4896 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4896 node4896Labels = Sparse.eval nodeValue4896 (mixedVector B) := by
  have h := singleton4896 B _hB
  rw [sound2266 B _hB _hF, sound2278 B _hB _hF] at h
  norm_num [nodeValue4896, nodeValue2266, nodeValue2278, Sparse.eval] at h ⊢
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

theorem sound5401 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5401 node5401Labels = Sparse.eval nodeValue5401 (mixedVector B) := by
  have h := singleton5401 B _hB
  rw [sound3787 B _hB _hF, sound3804 B _hB _hF] at h
  norm_num [nodeValue5401, nodeValue3787, nodeValue3804, Sparse.eval] at h ⊢
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

theorem sound5451 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5451 node5451Labels = Sparse.eval nodeValue5451 (mixedVector B) := by
  have h := singleton5451 B _hB
  rw [sound3888 B _hB _hF, sound3913 B _hB _hF] at h
  norm_num [nodeValue5451, nodeValue3888, nodeValue3913, Sparse.eval] at h ⊢
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

theorem sourceEq2448 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2448 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2448 + difference 0 1) (sourceB2448 + difference 1 0) sourceC2448) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5388) := by
    have ha : (tripleCharges (sourceA2448 + difference 0 1) (sourceB2448 + difference 1 0) sourceC2448) = raw16289 := by
      apply Matrix.ext; unfold tripleCharges sourceA2448 sourceB2448 sourceC2448 difference raw16289; decide +kernel
    rw [ha]
    exact (canonical16289 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2448 + difference 0 2) (sourceB2448 + difference 2 0) sourceC2448) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5401) := by
    have ha : (tripleCharges (sourceA2448 + difference 0 2) (sourceB2448 + difference 2 0) sourceC2448) = raw16290 := by
      apply Matrix.ext; unfold tripleCharges sourceA2448 sourceB2448 sourceC2448 difference raw16290; decide +kernel
    rw [ha]
    exact (canonical16290 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2448 + difference 0 3) (sourceB2448 + difference 3 0) sourceC2448) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5451) := by
    have ha : (tripleCharges (sourceA2448 + difference 0 3) (sourceB2448 + difference 3 0) sourceC2448) = raw10900 := by
      apply Matrix.ext; unfold tripleCharges sourceA2448 sourceB2448 sourceC2448 difference raw10900; decide +kernel
    rw [ha]
    exact (canonical10900 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2448 + difference 0 4) (sourceB2448 + difference 4 0) sourceC2448) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5438) := by
    have ha : (tripleCharges (sourceA2448 + difference 0 4) (sourceB2448 + difference 4 0) sourceC2448) = raw16291 := by
      apply Matrix.ext; unfold tripleCharges sourceA2448 sourceB2448 sourceC2448 difference raw16291; decide +kernel
    rw [ha]
    exact (canonical16291 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2448 + difference 0 5) (sourceB2448 + difference 5 0) sourceC2448) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5450) := by
    have ha : (tripleCharges (sourceA2448 + difference 0 5) (sourceB2448 + difference 5 0) sourceC2448) = raw16292 := by
      apply Matrix.ext; unfold tripleCharges sourceA2448 sourceB2448 sourceC2448 difference raw16292; decide +kernel
    rw [ha]
    exact (canonical16292 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2448 + difference 1 0) (sourceB2448 + difference 0 1) sourceC2448) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4268) := by
    have ha : (tripleCharges (sourceA2448 + difference 1 0) (sourceB2448 + difference 0 1) sourceC2448) = raw10915 := by
      apply Matrix.ext; unfold tripleCharges sourceA2448 sourceB2448 sourceC2448 difference raw10915; decide +kernel
    rw [ha]
    exact (canonical10915 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2448 + difference 1 2) (sourceB2448 + difference 2 1) sourceC2448) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4740) := by
    have ha : (tripleCharges (sourceA2448 + difference 1 2) (sourceB2448 + difference 2 1) sourceC2448) = raw10917 := by
      apply Matrix.ext; unfold tripleCharges sourceA2448 sourceB2448 sourceC2448 difference raw10917; decide +kernel
    rw [ha]
    exact (canonical10917 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2448 + difference 1 3) (sourceB2448 + difference 3 1) sourceC2448) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4896) := by
    have ha : (tripleCharges (sourceA2448 + difference 1 3) (sourceB2448 + difference 3 1) sourceC2448) = raw16284 := by
      apply Matrix.ext; unfold tripleCharges sourceA2448 sourceB2448 sourceC2448 difference raw16284; decide +kernel
    rw [ha]
    exact (canonical16284 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2448 + difference 1 4) (sourceB2448 + difference 4 1) sourceC2448) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4839) := by
    have ha : (tripleCharges (sourceA2448 + difference 1 4) (sourceB2448 + difference 4 1) sourceC2448) = raw10918 := by
      apply Matrix.ext; unfold tripleCharges sourceA2448 sourceB2448 sourceC2448 difference raw10918; decide +kernel
    rw [ha]
    exact (canonical10918 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2448 + difference 1 5) (sourceB2448 + difference 5 1) sourceC2448) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4889) := by
    have ha : (tripleCharges (sourceA2448 + difference 1 5) (sourceB2448 + difference 5 1) sourceC2448) = raw10919 := by
      apply Matrix.ext; unfold tripleCharges sourceA2448 sourceB2448 sourceC2448 difference raw10919; decide +kernel
    rw [ha]
    exact (canonical10919 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2448 + difference 2 0) (sourceB2448 + difference 0 2) sourceC2448) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4232) := by
    have ha : (tripleCharges (sourceA2448 + difference 2 0) (sourceB2448 + difference 0 2) sourceC2448) = raw33616 := by
      apply Matrix.ext; unfold tripleCharges sourceA2448 sourceB2448 sourceC2448 difference raw33616; decide +kernel
    rw [ha]
    exact (canonical33616 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2448 + difference 2 1) (sourceB2448 + difference 1 2) sourceC2448) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4679) := by
    have ha : (tripleCharges (sourceA2448 + difference 2 1) (sourceB2448 + difference 1 2) sourceC2448) = raw33617 := by
      apply Matrix.ext; unfold tripleCharges sourceA2448 sourceB2448 sourceC2448 difference raw33617; decide +kernel
    rw [ha]
    exact (canonical33617 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2448 + difference 2 3) (sourceB2448 + difference 3 2) sourceC2448) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4866) := by
    have ha : (tripleCharges (sourceA2448 + difference 2 3) (sourceB2448 + difference 3 2) sourceC2448) = raw10911 := by
      apply Matrix.ext; unfold tripleCharges sourceA2448 sourceB2448 sourceC2448 difference raw10911; decide +kernel
    rw [ha]
    exact (canonical10911 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2448 + difference 2 4) (sourceB2448 + difference 4 2) sourceC2448) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4826) := by
    have ha : (tripleCharges (sourceA2448 + difference 2 4) (sourceB2448 + difference 4 2) sourceC2448) = raw33618 := by
      apply Matrix.ext; unfold tripleCharges sourceA2448 sourceB2448 sourceC2448 difference raw33618; decide +kernel
    rw [ha]
    exact (canonical33618 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2448 + difference 2 5) (sourceB2448 + difference 5 2) sourceC2448) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4864) := by
    have ha : (tripleCharges (sourceA2448 + difference 2 5) (sourceB2448 + difference 5 2) sourceC2448) = raw33619 := by
      apply Matrix.ext; unfold tripleCharges sourceA2448 sourceB2448 sourceC2448 difference raw33619; decide +kernel
    rw [ha]
    exact (canonical33619 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2448 + difference 3 0) (sourceB2448 + difference 0 3) sourceC2448) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4234) := by
    have ha : (tripleCharges (sourceA2448 + difference 3 0) (sourceB2448 + difference 0 3) sourceC2448) = raw33620 := by
      apply Matrix.ext; unfold tripleCharges sourceA2448 sourceB2448 sourceC2448 difference raw33620; decide +kernel
    rw [ha]
    exact (canonical33620 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2448 + difference 3 1) (sourceB2448 + difference 1 3) sourceC2448) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4684) := by
    have ha : (tripleCharges (sourceA2448 + difference 3 1) (sourceB2448 + difference 1 3) sourceC2448) = raw33621 := by
      apply Matrix.ext; unfold tripleCharges sourceA2448 sourceB2448 sourceC2448 difference raw33621; decide +kernel
    rw [ha]
    exact (canonical33621 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2448 + difference 3 2) (sourceB2448 + difference 2 3) sourceC2448) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4722) := by
    have ha : (tripleCharges (sourceA2448 + difference 3 2) (sourceB2448 + difference 2 3) sourceC2448) = raw33622 := by
      apply Matrix.ext; unfold tripleCharges sourceA2448 sourceB2448 sourceC2448 difference raw33622; decide +kernel
    rw [ha]
    exact (canonical33622 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2448 + difference 3 4) (sourceB2448 + difference 4 3) sourceC2448) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4828) := by
    have ha : (tripleCharges (sourceA2448 + difference 3 4) (sourceB2448 + difference 4 3) sourceC2448) = raw33623 := by
      apply Matrix.ext; unfold tripleCharges sourceA2448 sourceB2448 sourceC2448 difference raw33623; decide +kernel
    rw [ha]
    exact (canonical33623 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2448 + difference 3 5) (sourceB2448 + difference 5 3) sourceC2448) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4865) := by
    have ha : (tripleCharges (sourceA2448 + difference 3 5) (sourceB2448 + difference 5 3) sourceC2448) = raw33624 := by
      apply Matrix.ext; unfold tripleCharges sourceA2448 sourceB2448 sourceC2448 difference raw33624; decide +kernel
    rw [ha]
    exact (canonical33624 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2448 + difference 4 0) (sourceB2448 + difference 0 4) sourceC2448) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4239) := by
    have ha : (tripleCharges (sourceA2448 + difference 4 0) (sourceB2448 + difference 0 4) sourceC2448) = raw31204 := by
      apply Matrix.ext; unfold tripleCharges sourceA2448 sourceB2448 sourceC2448 difference raw31204; decide +kernel
    rw [ha]
    exact (canonical31204 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2448 + difference 4 1) (sourceB2448 + difference 1 4) sourceC2448) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4689) := by
    have ha : (tripleCharges (sourceA2448 + difference 4 1) (sourceB2448 + difference 1 4) sourceC2448) = raw31205 := by
      apply Matrix.ext; unfold tripleCharges sourceA2448 sourceB2448 sourceC2448 difference raw31205; decide +kernel
    rw [ha]
    exact (canonical31205 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2448 + difference 4 2) (sourceB2448 + difference 2 4) sourceC2448) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4725) := by
    have ha : (tripleCharges (sourceA2448 + difference 4 2) (sourceB2448 + difference 2 4) sourceC2448) = raw31206 := by
      apply Matrix.ext; unfold tripleCharges sourceA2448 sourceB2448 sourceC2448 difference raw31206; decide +kernel
    rw [ha]
    exact (canonical31206 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2448 + difference 4 3) (sourceB2448 + difference 3 4) sourceC2448) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4875) := by
    have ha : (tripleCharges (sourceA2448 + difference 4 3) (sourceB2448 + difference 3 4) sourceC2448) = raw10921 := by
      apply Matrix.ext; unfold tripleCharges sourceA2448 sourceB2448 sourceC2448 difference raw10921; decide +kernel
    rw [ha]
    exact (canonical10921 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2448 + difference 4 5) (sourceB2448 + difference 5 4) sourceC2448) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4866) := by
    have ha : (tripleCharges (sourceA2448 + difference 4 5) (sourceB2448 + difference 5 4) sourceC2448) = raw31207 := by
      apply Matrix.ext; unfold tripleCharges sourceA2448 sourceB2448 sourceC2448 difference raw31207; decide +kernel
    rw [ha]
    exact (canonical31207 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2448 + difference 5 0) (sourceB2448 + difference 0 5) sourceC2448) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4233) := by
    have ha : (tripleCharges (sourceA2448 + difference 5 0) (sourceB2448 + difference 0 5) sourceC2448) = raw33625 := by
      apply Matrix.ext; unfold tripleCharges sourceA2448 sourceB2448 sourceC2448 difference raw33625; decide +kernel
    rw [ha]
    exact (canonical33625 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2448 + difference 5 1) (sourceB2448 + difference 1 5) sourceC2448) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4681) := by
    have ha : (tripleCharges (sourceA2448 + difference 5 1) (sourceB2448 + difference 1 5) sourceC2448) = raw33626 := by
      apply Matrix.ext; unfold tripleCharges sourceA2448 sourceB2448 sourceC2448 difference raw33626; decide +kernel
    rw [ha]
    exact (canonical33626 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2448 + difference 5 2) (sourceB2448 + difference 2 5) sourceC2448) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4721) := by
    have ha : (tripleCharges (sourceA2448 + difference 5 2) (sourceB2448 + difference 2 5) sourceC2448) = raw33627 := by
      apply Matrix.ext; unfold tripleCharges sourceA2448 sourceB2448 sourceC2448 difference raw33627; decide +kernel
    rw [ha]
    exact (canonical33627 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2448 + difference 5 3) (sourceB2448 + difference 3 5) sourceC2448) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4868) := by
    have ha : (tripleCharges (sourceA2448 + difference 5 3) (sourceB2448 + difference 3 5) sourceC2448) = raw10926 := by
      apply Matrix.ext; unfold tripleCharges sourceA2448 sourceB2448 sourceC2448 difference raw10926; decide +kernel
    rw [ha]
    exact (canonical10926 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2448 + difference 5 4) (sourceB2448 + difference 4 5) sourceC2448) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4827) := by
    have ha : (tripleCharges (sourceA2448 + difference 5 4) (sourceB2448 + difference 4 5) sourceC2448) = raw33628 := by
      apply Matrix.ext; unfold tripleCharges sourceA2448 sourceB2448 sourceC2448 difference raw33628; decide +kernel
    rw [ha]
    exact (canonical33628 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2448 sourceB2448 sourceC2448
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2448, Integer.Sparse.eval]
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

theorem reindexCheck1968 : Integer.Sparse.reindex keyMap MixedData.row1968 = numericRow1968 := by decide +kernel

theorem numericCheck1968 (x : Master → ℝ) : Integer.Sparse.eval numericRow1968 x =
    (51840 : ℝ) * reducedSource1968 x := by
  norm_num [numericRow1968, reducedSource1968, Integer.Sparse.eval, Sparse.eval, nodeValue4232, nodeValue4233, nodeValue4234, nodeValue4239, nodeValue4268, nodeValue4679, nodeValue4681, nodeValue4684, nodeValue4689, nodeValue4721, nodeValue4722, nodeValue4725, nodeValue4740, nodeValue4826, nodeValue4827, nodeValue4828, nodeValue4839, nodeValue4864, nodeValue4865, nodeValue4866, nodeValue4868, nodeValue4875, nodeValue4889, nodeValue4896, nodeValue5388, nodeValue5401, nodeValue5438, nodeValue5450, nodeValue5451]
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

theorem reducedZero1968 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1968 (mixedVector B) = 0 := by
  have h4232 : mixedVector B (Sum.inr 4232) = Sparse.eval nodeValue4232 (mixedVector B) := by
    change mixedMoment B node4232 node4232Labels = _
    exact sound4232 B hB hF
  have h4233 : mixedVector B (Sum.inr 4233) = Sparse.eval nodeValue4233 (mixedVector B) := by
    change mixedMoment B node4233 node4233Labels = _
    exact sound4233 B hB hF
  have h4234 : mixedVector B (Sum.inr 4234) = Sparse.eval nodeValue4234 (mixedVector B) := by
    change mixedMoment B node4234 node4234Labels = _
    exact sound4234 B hB hF
  have h4239 : mixedVector B (Sum.inr 4239) = Sparse.eval nodeValue4239 (mixedVector B) := by
    change mixedMoment B node4239 node4239Labels = _
    exact sound4239 B hB hF
  have h4268 : mixedVector B (Sum.inr 4268) = Sparse.eval nodeValue4268 (mixedVector B) := by
    change mixedMoment B node4268 node4268Labels = _
    exact sound4268 B hB hF
  have h4679 : mixedVector B (Sum.inr 4679) = Sparse.eval nodeValue4679 (mixedVector B) := by
    change mixedMoment B node4679 node4679Labels = _
    exact sound4679 B hB hF
  have h4681 : mixedVector B (Sum.inr 4681) = Sparse.eval nodeValue4681 (mixedVector B) := by
    change mixedMoment B node4681 node4681Labels = _
    exact sound4681 B hB hF
  have h4684 : mixedVector B (Sum.inr 4684) = Sparse.eval nodeValue4684 (mixedVector B) := by
    change mixedMoment B node4684 node4684Labels = _
    exact sound4684 B hB hF
  have h4689 : mixedVector B (Sum.inr 4689) = Sparse.eval nodeValue4689 (mixedVector B) := by
    change mixedMoment B node4689 node4689Labels = _
    exact sound4689 B hB hF
  have h4721 : mixedVector B (Sum.inr 4721) = Sparse.eval nodeValue4721 (mixedVector B) := by
    change mixedMoment B node4721 node4721Labels = _
    exact sound4721 B hB hF
  have h4722 : mixedVector B (Sum.inr 4722) = Sparse.eval nodeValue4722 (mixedVector B) := by
    change mixedMoment B node4722 node4722Labels = _
    exact sound4722 B hB hF
  have h4725 : mixedVector B (Sum.inr 4725) = Sparse.eval nodeValue4725 (mixedVector B) := by
    change mixedMoment B node4725 node4725Labels = _
    exact sound4725 B hB hF
  have h4740 : mixedVector B (Sum.inr 4740) = Sparse.eval nodeValue4740 (mixedVector B) := by
    change mixedMoment B node4740 node4740Labels = _
    exact sound4740 B hB hF
  have h4826 : mixedVector B (Sum.inr 4826) = Sparse.eval nodeValue4826 (mixedVector B) := by
    change mixedMoment B node4826 node4826Labels = _
    exact sound4826 B hB hF
  have h4827 : mixedVector B (Sum.inr 4827) = Sparse.eval nodeValue4827 (mixedVector B) := by
    change mixedMoment B node4827 node4827Labels = _
    exact sound4827 B hB hF
  have h4828 : mixedVector B (Sum.inr 4828) = Sparse.eval nodeValue4828 (mixedVector B) := by
    change mixedMoment B node4828 node4828Labels = _
    exact sound4828 B hB hF
  have h4839 : mixedVector B (Sum.inr 4839) = Sparse.eval nodeValue4839 (mixedVector B) := by
    change mixedMoment B node4839 node4839Labels = _
    exact sound4839 B hB hF
  have h4864 : mixedVector B (Sum.inr 4864) = Sparse.eval nodeValue4864 (mixedVector B) := by
    change mixedMoment B node4864 node4864Labels = _
    exact sound4864 B hB hF
  have h4865 : mixedVector B (Sum.inr 4865) = Sparse.eval nodeValue4865 (mixedVector B) := by
    change mixedMoment B node4865 node4865Labels = _
    exact sound4865 B hB hF
  have h4866 : mixedVector B (Sum.inr 4866) = Sparse.eval nodeValue4866 (mixedVector B) := by
    change mixedMoment B node4866 node4866Labels = _
    exact sound4866 B hB hF
  have h4868 : mixedVector B (Sum.inr 4868) = Sparse.eval nodeValue4868 (mixedVector B) := by
    change mixedMoment B node4868 node4868Labels = _
    exact sound4868 B hB hF
  have h4875 : mixedVector B (Sum.inr 4875) = Sparse.eval nodeValue4875 (mixedVector B) := by
    change mixedMoment B node4875 node4875Labels = _
    exact sound4875 B hB hF
  have h4889 : mixedVector B (Sum.inr 4889) = Sparse.eval nodeValue4889 (mixedVector B) := by
    change mixedMoment B node4889 node4889Labels = _
    exact sound4889 B hB hF
  have h4896 : mixedVector B (Sum.inr 4896) = Sparse.eval nodeValue4896 (mixedVector B) := by
    change mixedMoment B node4896 node4896Labels = _
    exact sound4896 B hB hF
  have h5388 : mixedVector B (Sum.inr 5388) = Sparse.eval nodeValue5388 (mixedVector B) := by
    change mixedMoment B node5388 node5388Labels = _
    exact sound5388_e B hB hF
  have h5401 : mixedVector B (Sum.inr 5401) = Sparse.eval nodeValue5401 (mixedVector B) := by
    change mixedMoment B node5401 node5401Labels = _
    exact sound5401 B hB hF
  have h5438 : mixedVector B (Sum.inr 5438) = Sparse.eval nodeValue5438 (mixedVector B) := by
    change mixedMoment B node5438 node5438Labels = _
    exact sound5438 B hB hF
  have h5450 : mixedVector B (Sum.inr 5450) = Sparse.eval nodeValue5450 (mixedVector B) := by
    change mixedMoment B node5450 node5450Labels = _
    exact sound5450_e B hB hF
  have h5451 : mixedVector B (Sum.inr 5451) = Sparse.eval nodeValue5451 (mixedVector B) := by
    change mixedMoment B node5451 node5451Labels = _
    exact sound5451 B hB hF
  simpa only [sourceForm2448, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4232, h4233, h4234, h4239, h4268, h4679, h4681, h4684, h4689, h4721, h4722, h4725, h4740, h4826, h4827, h4828, h4839, h4864, h4865, h4866, h4868, h4875, h4889, h4896, h5388, h5401, h5438, h5450, h5451, reducedSource1968] using sourceEq2448 B hB

theorem rowSound1968_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1968 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1968, numericCheck1968, reducedZero1968 B hB hF, mul_zero]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedSourceBridge.rowSound1968_e_oai := @OAI.MUB6.Certificate.MixedSourceBridge.rowSound1968_e_oai
