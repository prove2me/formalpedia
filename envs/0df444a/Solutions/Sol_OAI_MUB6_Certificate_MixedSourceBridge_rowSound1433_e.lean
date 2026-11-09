-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedSourceBridge.rowSound1433_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-08T20:58:28.762305+00:00
-- url     : https://prove2.me/submissions/dc30d9f3-dfe9-4184-88b4-abf106a32547

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E184
import Definitions.Def_OAIQ106E086
import Definitions.Def_OAIQ106E089
import Definitions.Def_OAIQ106E090
import Definitions.Def_OAIQ106E094
import Definitions.Def_OAIQ106E098
import Definitions.Def_OAIQ106E191
import Definitions.Def_OAIQ106E100
import Definitions.Def_OAIQ106E102
import Definitions.Def_OAIQ106E117
import Definitions.Def_OAIQ106E119
import Definitions.Def_OAIQ106E120
import Definitions.Def_OAIQ106E124
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
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound1299_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound5292_e

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical78 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw78 raw78Labels = mixedMoment B node1301 node1301Labels := by
  calc
    mixedMoment B raw78 raw78Labels = mixedMoment B raw78step0 raw78step0Labels := by
      have ha : raw78step0 = (fun i j => raw78 (permutation8 i) (permutation5 j)) := by apply Matrix.ext; unfold raw78step0 raw78; decide +kernel
      have hl : raw78step0Labels = raw78Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw78 raw78Labels permutation8 permutation5
    mixedMoment B raw78step0 raw78step0Labels = mixedMoment B raw78step1 raw78step1Labels := by
      have ha : raw78step1 = raw78step0 := by apply Matrix.ext; unfold raw78step1 raw78step0; decide +kernel
      have hl : raw78step0Labels = labelEmbedding1 ∘ raw78step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw78step0 raw78step0Labels raw78step1Labels labelEmbedding1 hl
    _ = mixedMoment B node1301 node1301Labels := by rfl

theorem canonical79 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw79 raw79Labels = mixedMoment B node157 node157Labels := by
  calc
    mixedMoment B raw79 raw79Labels = mixedMoment B raw79step0 raw79step0Labels := by
      have ha : raw79step0 = (fun i j => raw79 (permutation10 i) (permutation4 j)) := by apply Matrix.ext; unfold raw79step0 raw79; decide +kernel
      have hl : raw79step0Labels = raw79Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw79 raw79Labels permutation10 permutation4
    _ = mixedMoment B node157 node157Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical10
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical1320 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1320 raw1320Labels = mixedMoment B node4516 node4516Labels := by
  calc
    mixedMoment B raw1320 raw1320Labels = mixedMoment B raw1320step0 raw1320step0Labels := by
      have ha : raw1320step0 = (fun i j => raw1320 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1320step0 raw1320; decide +kernel
      have hl : raw1320step0Labels = raw1320Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1320 raw1320Labels permutation152 permutation4
    mixedMoment B raw1320step0 raw1320step0Labels = mixedMoment B raw1320step1 raw1320step1Labels := by
      have ha : raw1320step1 = raw1320step0 := by apply Matrix.ext; unfold raw1320step1 raw1320step0; decide +kernel
      have hl : raw1320step0Labels = labelEmbedding7 ∘ raw1320step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1320step0 raw1320step0Labels raw1320step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4516 node4516Labels := by rfl

theorem canonical1321 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1321 raw1321Labels = mixedMoment B node1100 node1100Labels := by
  calc
    mixedMoment B raw1321 raw1321Labels = mixedMoment B raw1321step0 raw1321step0Labels := by
      have ha : raw1321step0 = (fun i j => raw1321 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1321step0 raw1321; decide +kernel
      have hl : raw1321step0Labels = raw1321Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1321 raw1321Labels permutation152 permutation4
    _ = mixedMoment B node1100 node1100Labels := by rfl

theorem canonical1322 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1322 raw1322Labels = mixedMoment B node3234 node3234Labels := by
  calc
    mixedMoment B raw1322 raw1322Labels = mixedMoment B raw1322step0 raw1322step0Labels := by
      have ha : raw1322step0 = (fun i j => raw1322 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1322step0 raw1322; decide +kernel
      have hl : raw1322step0Labels = raw1322Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1322 raw1322Labels permutation152 permutation6
    mixedMoment B raw1322step0 raw1322step0Labels = mixedMoment B raw1322step1 raw1322step1Labels := by
      have ha : raw1322step1 = -raw1322step0 := by apply Matrix.ext; change ∀ i j, raw1322step1 i j = -(raw1322step0 i j); unfold raw1322step1 raw1322step0; decide +kernel
      have hl : raw1322step1Labels = raw1322step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1322step1 raw1322step1Labels = mixedMoment B raw1322step2 raw1322step2Labels := by
      have ha : raw1322step2 = raw1322step1 := by apply Matrix.ext; unfold raw1322step2 raw1322step1; decide +kernel
      have hl : raw1322step1Labels = labelEmbedding1 ∘ raw1322step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1322step1 raw1322step1Labels raw1322step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3234 node3234Labels := by rfl

theorem canonical1323 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1323 raw1323Labels = mixedMoment B node4517 node4517Labels := by
  calc
    mixedMoment B raw1323 raw1323Labels = mixedMoment B raw1323step0 raw1323step0Labels := by
      have ha : raw1323step0 = (fun i j => raw1323 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1323step0 raw1323; decide +kernel
      have hl : raw1323step0Labels = raw1323Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1323 raw1323Labels permutation32 permutation4
    mixedMoment B raw1323step0 raw1323step0Labels = mixedMoment B raw1323step1 raw1323step1Labels := by
      have ha : raw1323step1 = raw1323step0 := by apply Matrix.ext; unfold raw1323step1 raw1323step0; decide +kernel
      have hl : raw1323step0Labels = labelEmbedding7 ∘ raw1323step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1323step0 raw1323step0Labels raw1323step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4517 node4517Labels := by rfl

theorem canonical1324 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1324 raw1324Labels = mixedMoment B node1101 node1101Labels := by
  calc
    mixedMoment B raw1324 raw1324Labels = mixedMoment B raw1324step0 raw1324step0Labels := by
      have ha : raw1324step0 = (fun i j => raw1324 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1324step0 raw1324; decide +kernel
      have hl : raw1324step0Labels = raw1324Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1324 raw1324Labels permutation32 permutation4
    _ = mixedMoment B node1101 node1101Labels := by rfl

theorem canonical1325 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1325 raw1325Labels = mixedMoment B node3235 node3235Labels := by
  calc
    mixedMoment B raw1325 raw1325Labels = mixedMoment B raw1325step0 raw1325step0Labels := by
      have ha : raw1325step0 = (fun i j => raw1325 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1325step0 raw1325; decide +kernel
      have hl : raw1325step0Labels = raw1325Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1325 raw1325Labels permutation32 permutation6
    mixedMoment B raw1325step0 raw1325step0Labels = mixedMoment B raw1325step1 raw1325step1Labels := by
      have ha : raw1325step1 = -raw1325step0 := by apply Matrix.ext; change ∀ i j, raw1325step1 i j = -(raw1325step0 i j); unfold raw1325step1 raw1325step0; decide +kernel
      have hl : raw1325step1Labels = raw1325step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1325step1 raw1325step1Labels = mixedMoment B raw1325step2 raw1325step2Labels := by
      have ha : raw1325step2 = raw1325step1 := by apply Matrix.ext; unfold raw1325step2 raw1325step1; decide +kernel
      have hl : raw1325step1Labels = labelEmbedding1 ∘ raw1325step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1325step1 raw1325step1Labels raw1325step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3235 node3235Labels := by rfl

theorem canonical1326 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1326 raw1326Labels = mixedMoment B node4518 node4518Labels := by
  calc
    mixedMoment B raw1326 raw1326Labels = mixedMoment B raw1326step0 raw1326step0Labels := by
      have ha : raw1326step0 = (fun i j => raw1326 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1326step0 raw1326; decide +kernel
      have hl : raw1326step0Labels = raw1326Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1326 raw1326Labels permutation32 permutation4
    mixedMoment B raw1326step0 raw1326step0Labels = mixedMoment B raw1326step1 raw1326step1Labels := by
      have ha : raw1326step1 = raw1326step0 := by apply Matrix.ext; unfold raw1326step1 raw1326step0; decide +kernel
      have hl : raw1326step0Labels = labelEmbedding7 ∘ raw1326step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1326step0 raw1326step0Labels raw1326step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4518 node4518Labels := by rfl

theorem canonical1327 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1327 raw1327Labels = mixedMoment B node1102 node1102Labels := by
  calc
    mixedMoment B raw1327 raw1327Labels = mixedMoment B raw1327step0 raw1327step0Labels := by
      have ha : raw1327step0 = (fun i j => raw1327 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1327step0 raw1327; decide +kernel
      have hl : raw1327step0Labels = raw1327Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1327 raw1327Labels permutation32 permutation4
    _ = mixedMoment B node1102 node1102Labels := by rfl

theorem canonical1328 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1328 raw1328Labels = mixedMoment B node3236 node3236Labels := by
  calc
    mixedMoment B raw1328 raw1328Labels = mixedMoment B raw1328step0 raw1328step0Labels := by
      have ha : raw1328step0 = (fun i j => raw1328 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1328step0 raw1328; decide +kernel
      have hl : raw1328step0Labels = raw1328Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1328 raw1328Labels permutation32 permutation6
    mixedMoment B raw1328step0 raw1328step0Labels = mixedMoment B raw1328step1 raw1328step1Labels := by
      have ha : raw1328step1 = -raw1328step0 := by apply Matrix.ext; change ∀ i j, raw1328step1 i j = -(raw1328step0 i j); unfold raw1328step1 raw1328step0; decide +kernel
      have hl : raw1328step1Labels = raw1328step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1328step1 raw1328step1Labels = mixedMoment B raw1328step2 raw1328step2Labels := by
      have ha : raw1328step2 = raw1328step1 := by apply Matrix.ext; unfold raw1328step2 raw1328step1; decide +kernel
      have hl : raw1328step1Labels = labelEmbedding1 ∘ raw1328step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1328step1 raw1328step1Labels raw1328step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3236 node3236Labels := by rfl

theorem canonical1341 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1341 raw1341Labels = mixedMoment B node4523 node4523Labels := by
  calc
    mixedMoment B raw1341 raw1341Labels = mixedMoment B raw1341step0 raw1341step0Labels := by
      have ha : raw1341step0 = (fun i j => raw1341 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1341step0 raw1341; decide +kernel
      have hl : raw1341step0Labels = raw1341Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1341 raw1341Labels permutation152 permutation4
    mixedMoment B raw1341step0 raw1341step0Labels = mixedMoment B raw1341step1 raw1341step1Labels := by
      have ha : raw1341step1 = raw1341step0 := by apply Matrix.ext; unfold raw1341step1 raw1341step0; decide +kernel
      have hl : raw1341step0Labels = labelEmbedding7 ∘ raw1341step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1341step0 raw1341step0Labels raw1341step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4523 node4523Labels := by rfl

theorem canonical1342 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1342 raw1342Labels = mixedMoment B node1107 node1107Labels := by
  calc
    mixedMoment B raw1342 raw1342Labels = mixedMoment B raw1342step0 raw1342step0Labels := by
      have ha : raw1342step0 = (fun i j => raw1342 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1342step0 raw1342; decide +kernel
      have hl : raw1342step0Labels = raw1342Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1342 raw1342Labels permutation152 permutation4
    _ = mixedMoment B node1107 node1107Labels := by rfl

theorem canonical1343 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1343 raw1343Labels = mixedMoment B node3250 node3250Labels := by
  calc
    mixedMoment B raw1343 raw1343Labels = mixedMoment B raw1343step0 raw1343step0Labels := by
      have ha : raw1343step0 = (fun i j => raw1343 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1343step0 raw1343; decide +kernel
      have hl : raw1343step0Labels = raw1343Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1343 raw1343Labels permutation152 permutation6
    mixedMoment B raw1343step0 raw1343step0Labels = mixedMoment B raw1343step1 raw1343step1Labels := by
      have ha : raw1343step1 = -raw1343step0 := by apply Matrix.ext; change ∀ i j, raw1343step1 i j = -(raw1343step0 i j); unfold raw1343step1 raw1343step0; decide +kernel
      have hl : raw1343step1Labels = raw1343step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1343step1 raw1343step1Labels = mixedMoment B raw1343step2 raw1343step2Labels := by
      have ha : raw1343step2 = raw1343step1 := by apply Matrix.ext; unfold raw1343step2 raw1343step1; decide +kernel
      have hl : raw1343step1Labels = labelEmbedding1 ∘ raw1343step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1343step1 raw1343step1Labels raw1343step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3250 node3250Labels := by rfl

theorem canonical1344 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1344 raw1344Labels = mixedMoment B node4524 node4524Labels := by
  calc
    mixedMoment B raw1344 raw1344Labels = mixedMoment B raw1344step0 raw1344step0Labels := by
      have ha : raw1344step0 = (fun i j => raw1344 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1344step0 raw1344; decide +kernel
      have hl : raw1344step0Labels = raw1344Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1344 raw1344Labels permutation152 permutation4
    mixedMoment B raw1344step0 raw1344step0Labels = mixedMoment B raw1344step1 raw1344step1Labels := by
      have ha : raw1344step1 = raw1344step0 := by apply Matrix.ext; unfold raw1344step1 raw1344step0; decide +kernel
      have hl : raw1344step0Labels = labelEmbedding7 ∘ raw1344step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1344step0 raw1344step0Labels raw1344step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4524 node4524Labels := by rfl

theorem canonical1345 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1345 raw1345Labels = mixedMoment B node1108 node1108Labels := by
  calc
    mixedMoment B raw1345 raw1345Labels = mixedMoment B raw1345step0 raw1345step0Labels := by
      have ha : raw1345step0 = (fun i j => raw1345 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1345step0 raw1345; decide +kernel
      have hl : raw1345step0Labels = raw1345Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1345 raw1345Labels permutation152 permutation4
    _ = mixedMoment B node1108 node1108Labels := by rfl

theorem canonical1346 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1346 raw1346Labels = mixedMoment B node3251 node3251Labels := by
  calc
    mixedMoment B raw1346 raw1346Labels = mixedMoment B raw1346step0 raw1346step0Labels := by
      have ha : raw1346step0 = (fun i j => raw1346 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1346step0 raw1346; decide +kernel
      have hl : raw1346step0Labels = raw1346Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1346 raw1346Labels permutation152 permutation6
    mixedMoment B raw1346step0 raw1346step0Labels = mixedMoment B raw1346step1 raw1346step1Labels := by
      have ha : raw1346step1 = -raw1346step0 := by apply Matrix.ext; change ∀ i j, raw1346step1 i j = -(raw1346step0 i j); unfold raw1346step1 raw1346step0; decide +kernel
      have hl : raw1346step1Labels = raw1346step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1346step1 raw1346step1Labels = mixedMoment B raw1346step2 raw1346step2Labels := by
      have ha : raw1346step2 = raw1346step1 := by apply Matrix.ext; unfold raw1346step2 raw1346step1; decide +kernel
      have hl : raw1346step1Labels = labelEmbedding1 ∘ raw1346step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1346step1 raw1346step1Labels raw1346step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3251 node3251Labels := by rfl

theorem canonical1368 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1368 raw1368Labels = mixedMoment B node4544 node4544Labels := by
  calc
    mixedMoment B raw1368 raw1368Labels = mixedMoment B raw1368step0 raw1368step0Labels := by
      have ha : raw1368step0 = (fun i j => raw1368 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1368step0 raw1368; decide +kernel
      have hl : raw1368step0Labels = raw1368Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1368 raw1368Labels permutation152 permutation4
    mixedMoment B raw1368step0 raw1368step0Labels = mixedMoment B raw1368step1 raw1368step1Labels := by
      have ha : raw1368step1 = raw1368step0 := by apply Matrix.ext; unfold raw1368step1 raw1368step0; decide +kernel
      have hl : raw1368step0Labels = labelEmbedding7 ∘ raw1368step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1368step0 raw1368step0Labels raw1368step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4544 node4544Labels := by rfl

theorem canonical1369 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1369 raw1369Labels = mixedMoment B node1129 node1129Labels := by
  calc
    mixedMoment B raw1369 raw1369Labels = mixedMoment B raw1369step0 raw1369step0Labels := by
      have ha : raw1369step0 = (fun i j => raw1369 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1369step0 raw1369; decide +kernel
      have hl : raw1369step0Labels = raw1369Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1369 raw1369Labels permutation152 permutation4
    _ = mixedMoment B node1129 node1129Labels := by rfl

theorem canonical1370 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1370 raw1370Labels = mixedMoment B node3263 node3263Labels := by
  calc
    mixedMoment B raw1370 raw1370Labels = mixedMoment B raw1370step0 raw1370step0Labels := by
      have ha : raw1370step0 = (fun i j => raw1370 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1370step0 raw1370; decide +kernel
      have hl : raw1370step0Labels = raw1370Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1370 raw1370Labels permutation152 permutation6
    mixedMoment B raw1370step0 raw1370step0Labels = mixedMoment B raw1370step1 raw1370step1Labels := by
      have ha : raw1370step1 = -raw1370step0 := by apply Matrix.ext; change ∀ i j, raw1370step1 i j = -(raw1370step0 i j); unfold raw1370step1 raw1370step0; decide +kernel
      have hl : raw1370step1Labels = raw1370step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1370step1 raw1370step1Labels = mixedMoment B raw1370step2 raw1370step2Labels := by
      have ha : raw1370step2 = raw1370step1 := by apply Matrix.ext; unfold raw1370step2 raw1370step1; decide +kernel
      have hl : raw1370step1Labels = labelEmbedding1 ∘ raw1370step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1370step1 raw1370step1Labels raw1370step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3263 node3263Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical11
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical1422 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1422 raw1422Labels = mixedMoment B node4601 node4601Labels := by
  calc
    mixedMoment B raw1422 raw1422Labels = mixedMoment B raw1422step0 raw1422step0Labels := by
      have ha : raw1422step0 = (fun i j => raw1422 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1422step0 raw1422; decide +kernel
      have hl : raw1422step0Labels = raw1422Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1422 raw1422Labels permutation152 permutation4
    mixedMoment B raw1422step0 raw1422step0Labels = mixedMoment B raw1422step1 raw1422step1Labels := by
      have ha : raw1422step1 = raw1422step0 := by apply Matrix.ext; unfold raw1422step1 raw1422step0; decide +kernel
      have hl : raw1422step0Labels = labelEmbedding7 ∘ raw1422step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1422step0 raw1422step0Labels raw1422step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4601 node4601Labels := by rfl

theorem canonical1423 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1423 raw1423Labels = mixedMoment B node1235 node1235Labels := by
  calc
    mixedMoment B raw1423 raw1423Labels = mixedMoment B raw1423step0 raw1423step0Labels := by
      have ha : raw1423step0 = (fun i j => raw1423 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1423step0 raw1423; decide +kernel
      have hl : raw1423step0Labels = raw1423Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1423 raw1423Labels permutation152 permutation4
    _ = mixedMoment B node1235 node1235Labels := by rfl

theorem canonical1424 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1424 raw1424Labels = mixedMoment B node3292 node3292Labels := by
  calc
    mixedMoment B raw1424 raw1424Labels = mixedMoment B raw1424step0 raw1424step0Labels := by
      have ha : raw1424step0 = (fun i j => raw1424 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1424step0 raw1424; decide +kernel
      have hl : raw1424step0Labels = raw1424Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1424 raw1424Labels permutation152 permutation6
    mixedMoment B raw1424step0 raw1424step0Labels = mixedMoment B raw1424step1 raw1424step1Labels := by
      have ha : raw1424step1 = -raw1424step0 := by apply Matrix.ext; change ∀ i j, raw1424step1 i j = -(raw1424step0 i j); unfold raw1424step1 raw1424step0; decide +kernel
      have hl : raw1424step1Labels = raw1424step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1424step1 raw1424step1Labels = mixedMoment B raw1424step2 raw1424step2Labels := by
      have ha : raw1424step2 = raw1424step1 := by apply Matrix.ext; unfold raw1424step2 raw1424step1; decide +kernel
      have hl : raw1424step1Labels = labelEmbedding1 ∘ raw1424step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1424step1 raw1424step1Labels raw1424step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3292 node3292Labels := by rfl

theorem canonical1425 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1425 raw1425Labels = mixedMoment B node4602 node4602Labels := by
  calc
    mixedMoment B raw1425 raw1425Labels = mixedMoment B raw1425step0 raw1425step0Labels := by
      have ha : raw1425step0 = (fun i j => raw1425 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1425step0 raw1425; decide +kernel
      have hl : raw1425step0Labels = raw1425Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1425 raw1425Labels permutation32 permutation4
    mixedMoment B raw1425step0 raw1425step0Labels = mixedMoment B raw1425step1 raw1425step1Labels := by
      have ha : raw1425step1 = raw1425step0 := by apply Matrix.ext; unfold raw1425step1 raw1425step0; decide +kernel
      have hl : raw1425step0Labels = labelEmbedding7 ∘ raw1425step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1425step0 raw1425step0Labels raw1425step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4602 node4602Labels := by rfl

theorem canonical1426 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1426 raw1426Labels = mixedMoment B node1236 node1236Labels := by
  calc
    mixedMoment B raw1426 raw1426Labels = mixedMoment B raw1426step0 raw1426step0Labels := by
      have ha : raw1426step0 = (fun i j => raw1426 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1426step0 raw1426; decide +kernel
      have hl : raw1426step0Labels = raw1426Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1426 raw1426Labels permutation32 permutation4
    _ = mixedMoment B node1236 node1236Labels := by rfl

theorem canonical1427 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1427 raw1427Labels = mixedMoment B node3293 node3293Labels := by
  calc
    mixedMoment B raw1427 raw1427Labels = mixedMoment B raw1427step0 raw1427step0Labels := by
      have ha : raw1427step0 = (fun i j => raw1427 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1427step0 raw1427; decide +kernel
      have hl : raw1427step0Labels = raw1427Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1427 raw1427Labels permutation32 permutation6
    mixedMoment B raw1427step0 raw1427step0Labels = mixedMoment B raw1427step1 raw1427step1Labels := by
      have ha : raw1427step1 = -raw1427step0 := by apply Matrix.ext; change ∀ i j, raw1427step1 i j = -(raw1427step0 i j); unfold raw1427step1 raw1427step0; decide +kernel
      have hl : raw1427step1Labels = raw1427step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1427step1 raw1427step1Labels = mixedMoment B raw1427step2 raw1427step2Labels := by
      have ha : raw1427step2 = raw1427step1 := by apply Matrix.ext; unfold raw1427step2 raw1427step1; decide +kernel
      have hl : raw1427step1Labels = labelEmbedding1 ∘ raw1427step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1427step1 raw1427step1Labels raw1427step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3293 node3293Labels := by rfl

theorem canonical1431 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1431 raw1431Labels = mixedMoment B node4606 node4606Labels := by
  calc
    mixedMoment B raw1431 raw1431Labels = mixedMoment B raw1431step0 raw1431step0Labels := by
      have ha : raw1431step0 = (fun i j => raw1431 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1431step0 raw1431; decide +kernel
      have hl : raw1431step0Labels = raw1431Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1431 raw1431Labels permutation32 permutation4
    mixedMoment B raw1431step0 raw1431step0Labels = mixedMoment B raw1431step1 raw1431step1Labels := by
      have ha : raw1431step1 = raw1431step0 := by apply Matrix.ext; unfold raw1431step1 raw1431step0; decide +kernel
      have hl : raw1431step0Labels = labelEmbedding7 ∘ raw1431step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1431step0 raw1431step0Labels raw1431step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4606 node4606Labels := by rfl

theorem canonical1432 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1432 raw1432Labels = mixedMoment B node1240 node1240Labels := by
  calc
    mixedMoment B raw1432 raw1432Labels = mixedMoment B raw1432step0 raw1432step0Labels := by
      have ha : raw1432step0 = (fun i j => raw1432 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1432step0 raw1432; decide +kernel
      have hl : raw1432step0Labels = raw1432Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1432 raw1432Labels permutation32 permutation4
    _ = mixedMoment B node1240 node1240Labels := by rfl

theorem canonical1433 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1433 raw1433Labels = mixedMoment B node3299 node3299Labels := by
  calc
    mixedMoment B raw1433 raw1433Labels = mixedMoment B raw1433step0 raw1433step0Labels := by
      have ha : raw1433step0 = (fun i j => raw1433 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1433step0 raw1433; decide +kernel
      have hl : raw1433step0Labels = raw1433Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1433 raw1433Labels permutation32 permutation6
    mixedMoment B raw1433step0 raw1433step0Labels = mixedMoment B raw1433step1 raw1433step1Labels := by
      have ha : raw1433step1 = -raw1433step0 := by apply Matrix.ext; change ∀ i j, raw1433step1 i j = -(raw1433step0 i j); unfold raw1433step1 raw1433step0; decide +kernel
      have hl : raw1433step1Labels = raw1433step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1433step1 raw1433step1Labels = mixedMoment B raw1433step2 raw1433step2Labels := by
      have ha : raw1433step2 = raw1433step1 := by apply Matrix.ext; unfold raw1433step2 raw1433step1; decide +kernel
      have hl : raw1433step1Labels = labelEmbedding1 ∘ raw1433step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1433step1 raw1433step1Labels raw1433step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3299 node3299Labels := by rfl

theorem canonical1434 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1434 raw1434Labels = mixedMoment B node4608 node4608Labels := by
  calc
    mixedMoment B raw1434 raw1434Labels = mixedMoment B raw1434step0 raw1434step0Labels := by
      have ha : raw1434step0 = (fun i j => raw1434 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1434step0 raw1434; decide +kernel
      have hl : raw1434step0Labels = raw1434Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1434 raw1434Labels permutation8 permutation4
    mixedMoment B raw1434step0 raw1434step0Labels = mixedMoment B raw1434step1 raw1434step1Labels := by
      have ha : raw1434step1 = raw1434step0 := by apply Matrix.ext; unfold raw1434step1 raw1434step0; decide +kernel
      have hl : raw1434step0Labels = labelEmbedding7 ∘ raw1434step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1434step0 raw1434step0Labels raw1434step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4608 node4608Labels := by rfl

theorem canonical1435 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1435 raw1435Labels = mixedMoment B node1242 node1242Labels := by
  calc
    mixedMoment B raw1435 raw1435Labels = mixedMoment B raw1435step0 raw1435step0Labels := by
      have ha : raw1435step0 = (fun i j => raw1435 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1435step0 raw1435; decide +kernel
      have hl : raw1435step0Labels = raw1435Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1435 raw1435Labels permutation8 permutation4
    _ = mixedMoment B node1242 node1242Labels := by rfl

theorem canonical1436 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1436 raw1436Labels = mixedMoment B node3300 node3300Labels := by
  calc
    mixedMoment B raw1436 raw1436Labels = mixedMoment B raw1436step0 raw1436step0Labels := by
      have ha : raw1436step0 = (fun i j => raw1436 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1436step0 raw1436; decide +kernel
      have hl : raw1436step0Labels = raw1436Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1436 raw1436Labels permutation8 permutation6
    mixedMoment B raw1436step0 raw1436step0Labels = mixedMoment B raw1436step1 raw1436step1Labels := by
      have ha : raw1436step1 = -raw1436step0 := by apply Matrix.ext; change ∀ i j, raw1436step1 i j = -(raw1436step0 i j); unfold raw1436step1 raw1436step0; decide +kernel
      have hl : raw1436step1Labels = raw1436step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1436step1 raw1436step1Labels = mixedMoment B raw1436step2 raw1436step2Labels := by
      have ha : raw1436step2 = raw1436step1 := by apply Matrix.ext; unfold raw1436step2 raw1436step1; decide +kernel
      have hl : raw1436step1Labels = labelEmbedding1 ∘ raw1436step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1436step1 raw1436step1Labels raw1436step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3300 node3300Labels := by rfl

theorem canonical1437 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1437 raw1437Labels = mixedMoment B node4612 node4612Labels := by
  calc
    mixedMoment B raw1437 raw1437Labels = mixedMoment B raw1437step0 raw1437step0Labels := by
      have ha : raw1437step0 = (fun i j => raw1437 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1437step0 raw1437; decide +kernel
      have hl : raw1437step0Labels = raw1437Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1437 raw1437Labels permutation8 permutation4
    mixedMoment B raw1437step0 raw1437step0Labels = mixedMoment B raw1437step1 raw1437step1Labels := by
      have ha : raw1437step1 = raw1437step0 := by apply Matrix.ext; unfold raw1437step1 raw1437step0; decide +kernel
      have hl : raw1437step0Labels = labelEmbedding7 ∘ raw1437step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1437step0 raw1437step0Labels raw1437step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4612 node4612Labels := by rfl

theorem canonical1438 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1438 raw1438Labels = mixedMoment B node1246 node1246Labels := by
  calc
    mixedMoment B raw1438 raw1438Labels = mixedMoment B raw1438step0 raw1438step0Labels := by
      have ha : raw1438step0 = (fun i j => raw1438 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1438step0 raw1438; decide +kernel
      have hl : raw1438step0Labels = raw1438Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1438 raw1438Labels permutation8 permutation4
    _ = mixedMoment B node1246 node1246Labels := by rfl

theorem canonical1439 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1439 raw1439Labels = mixedMoment B node3301 node3301Labels := by
  calc
    mixedMoment B raw1439 raw1439Labels = mixedMoment B raw1439step0 raw1439step0Labels := by
      have ha : raw1439step0 = (fun i j => raw1439 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1439step0 raw1439; decide +kernel
      have hl : raw1439step0Labels = raw1439Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1439 raw1439Labels permutation8 permutation6
    mixedMoment B raw1439step0 raw1439step0Labels = mixedMoment B raw1439step1 raw1439step1Labels := by
      have ha : raw1439step1 = -raw1439step0 := by apply Matrix.ext; change ∀ i j, raw1439step1 i j = -(raw1439step0 i j); unfold raw1439step1 raw1439step0; decide +kernel
      have hl : raw1439step1Labels = raw1439step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1439step1 raw1439step1Labels = mixedMoment B raw1439step2 raw1439step2Labels := by
      have ha : raw1439step2 = raw1439step1 := by apply Matrix.ext; unfold raw1439step2 raw1439step1; decide +kernel
      have hl : raw1439step1Labels = labelEmbedding1 ∘ raw1439step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1439step1 raw1439step1Labels raw1439step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3301 node3301Labels := by rfl

theorem canonical1449 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1449 raw1449Labels = mixedMoment B node4622 node4622Labels := by
  calc
    mixedMoment B raw1449 raw1449Labels = mixedMoment B raw1449step0 raw1449step0Labels := by
      have ha : raw1449step0 = (fun i j => raw1449 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1449step0 raw1449; decide +kernel
      have hl : raw1449step0Labels = raw1449Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1449 raw1449Labels permutation32 permutation4
    mixedMoment B raw1449step0 raw1449step0Labels = mixedMoment B raw1449step1 raw1449step1Labels := by
      have ha : raw1449step1 = raw1449step0 := by apply Matrix.ext; unfold raw1449step1 raw1449step0; decide +kernel
      have hl : raw1449step0Labels = labelEmbedding7 ∘ raw1449step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1449step0 raw1449step0Labels raw1449step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4622 node4622Labels := by rfl

theorem canonical1450 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1450 raw1450Labels = mixedMoment B node1299 node1299Labels := by
  calc
    mixedMoment B raw1450 raw1450Labels = mixedMoment B raw1450step0 raw1450step0Labels := by
      have ha : raw1450step0 = (fun i j => raw1450 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1450step0 raw1450; decide +kernel
      have hl : raw1450step0Labels = raw1450Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1450 raw1450Labels permutation32 permutation4
    _ = mixedMoment B node1299 node1299Labels := by rfl

theorem canonical1451 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1451 raw1451Labels = mixedMoment B node3307 node3307Labels := by
  calc
    mixedMoment B raw1451 raw1451Labels = mixedMoment B raw1451step0 raw1451step0Labels := by
      have ha : raw1451step0 = (fun i j => raw1451 (permutation48 i) (permutation3 j)) := by apply Matrix.ext; unfold raw1451step0 raw1451; decide +kernel
      have hl : raw1451step0Labels = raw1451Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1451 raw1451Labels permutation48 permutation3
    mixedMoment B raw1451step0 raw1451step0Labels = mixedMoment B raw1451step1 raw1451step1Labels := by
      have ha : raw1451step1 = -raw1451step0 := by apply Matrix.ext; change ∀ i j, raw1451step1 i j = -(raw1451step0 i j); unfold raw1451step1 raw1451step0; decide +kernel
      have hl : raw1451step1Labels = raw1451step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1451step1 raw1451step1Labels = mixedMoment B raw1451step2 raw1451step2Labels := by
      have ha : raw1451step2 = raw1451step1 := by apply Matrix.ext; unfold raw1451step2 raw1451step1; decide +kernel
      have hl : raw1451step1Labels = labelEmbedding1 ∘ raw1451step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1451step1 raw1451step1Labels raw1451step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3307 node3307Labels := by rfl

theorem canonical1455 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1455 raw1455Labels = mixedMoment B node4624 node4624Labels := by
  calc
    mixedMoment B raw1455 raw1455Labels = mixedMoment B raw1455step0 raw1455step0Labels := by
      have ha : raw1455step0 = (fun i j => raw1455 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1455step0 raw1455; decide +kernel
      have hl : raw1455step0Labels = raw1455Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1455 raw1455Labels permutation8 permutation4
    mixedMoment B raw1455step0 raw1455step0Labels = mixedMoment B raw1455step1 raw1455step1Labels := by
      have ha : raw1455step1 = raw1455step0 := by apply Matrix.ext; unfold raw1455step1 raw1455step0; decide +kernel
      have hl : raw1455step0Labels = labelEmbedding7 ∘ raw1455step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1455step0 raw1455step0Labels raw1455step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4624 node4624Labels := by rfl

theorem canonical1456 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1456 raw1456Labels = mixedMoment B node1301 node1301Labels := by
  calc
    mixedMoment B raw1456 raw1456Labels = mixedMoment B raw1456step0 raw1456step0Labels := by
      have ha : raw1456step0 = (fun i j => raw1456 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1456step0 raw1456; decide +kernel
      have hl : raw1456step0Labels = raw1456Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1456 raw1456Labels permutation8 permutation4
    _ = mixedMoment B node1301 node1301Labels := by rfl

theorem canonical1457 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1457 raw1457Labels = mixedMoment B node3309 node3309Labels := by
  calc
    mixedMoment B raw1457 raw1457Labels = mixedMoment B raw1457step0 raw1457step0Labels := by
      have ha : raw1457step0 = (fun i j => raw1457 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw1457step0 raw1457; decide +kernel
      have hl : raw1457step0Labels = raw1457Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1457 raw1457Labels permutation10 permutation3
    mixedMoment B raw1457step0 raw1457step0Labels = mixedMoment B raw1457step1 raw1457step1Labels := by
      have ha : raw1457step1 = -raw1457step0 := by apply Matrix.ext; change ∀ i j, raw1457step1 i j = -(raw1457step0 i j); unfold raw1457step1 raw1457step0; decide +kernel
      have hl : raw1457step1Labels = raw1457step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1457step1 raw1457step1Labels = mixedMoment B raw1457step2 raw1457step2Labels := by
      have ha : raw1457step2 = raw1457step1 := by apply Matrix.ext; unfold raw1457step2 raw1457step1; decide +kernel
      have hl : raw1457step1Labels = labelEmbedding1 ∘ raw1457step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1457step1 raw1457step1Labels raw1457step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3309 node3309Labels := by rfl

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

theorem canonical18364 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18364 raw18364Labels = mixedMoment B node5292 node5292Labels := by
  calc
    mixedMoment B raw18364 raw18364Labels = mixedMoment B raw18364step0 raw18364step0Labels := by
      have hz : ∀ j, raw18364 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw18364step0 = (fun i j => raw18364 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw18364step0 raw18364; decide +kernel
      have hl : raw18364step0Labels = raw18364Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18364 raw18364Labels permutation265 hz
    _ = mixedMoment B node5292 node5292Labels := by rfl

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

theorem canonical2229 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2229 raw2229Labels = mixedMoment B node5203 node5203Labels := by
  calc
    mixedMoment B raw2229 raw2229Labels = mixedMoment B raw2229step0 raw2229step0Labels := by
      have ha : raw2229step0 = (fun i j => raw2229 (permutation32 i) (permutation5 j)) := by apply Matrix.ext; unfold raw2229step0 raw2229; decide +kernel
      have hl : raw2229step0Labels = raw2229Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2229 raw2229Labels permutation32 permutation5
    mixedMoment B raw2229step0 raw2229step0Labels = mixedMoment B raw2229step1 raw2229step1Labels := by
      have ha : raw2229step1 = raw2229step0 := by apply Matrix.ext; unfold raw2229step1 raw2229step0; decide +kernel
      have hl : raw2229step0Labels = labelEmbedding8 ∘ raw2229step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2229step0 raw2229step0Labels raw2229step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5203 node5203Labels := by rfl

theorem canonical2230 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2230 raw2230Labels = mixedMoment B node2884 node2884Labels := by
  calc
    mixedMoment B raw2230 raw2230Labels = mixedMoment B raw2230step0 raw2230step0Labels := by
      have ha : raw2230step0 = (fun i j => raw2230 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2230step0 raw2230; decide +kernel
      have hl : raw2230step0Labels = raw2230Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2230 raw2230Labels permutation32 permutation4
    _ = mixedMoment B node2884 node2884Labels := by rfl

theorem canonical2231 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2231 raw2231Labels = mixedMoment B node3621 node3621Labels := by
  calc
    mixedMoment B raw2231 raw2231Labels = mixedMoment B raw2231step0 raw2231step0Labels := by
      have ha : raw2231step0 = (fun i j => raw2231 (permutation40 i) (permutation3 j)) := by apply Matrix.ext; unfold raw2231step0 raw2231; decide +kernel
      have hl : raw2231step0Labels = raw2231Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2231 raw2231Labels permutation40 permutation3
    mixedMoment B raw2231step0 raw2231step0Labels = mixedMoment B raw2231step1 raw2231step1Labels := by
      have ha : raw2231step1 = -raw2231step0 := by apply Matrix.ext; change ∀ i j, raw2231step1 i j = -(raw2231step0 i j); unfold raw2231step1 raw2231step0; decide +kernel
      have hl : raw2231step1Labels = raw2231step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2231step1 raw2231step1Labels = mixedMoment B raw2231step2 raw2231step2Labels := by
      have ha : raw2231step2 = raw2231step1 := by apply Matrix.ext; unfold raw2231step2 raw2231step1; decide +kernel
      have hl : raw2231step1Labels = labelEmbedding1 ∘ raw2231step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2231step1 raw2231step1Labels raw2231step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3621 node3621Labels := by rfl

theorem canonical2301 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2301 raw2301Labels = mixedMoment B node5293 node5293Labels := by
  calc
    mixedMoment B raw2301 raw2301Labels = mixedMoment B raw2301step0 raw2301step0Labels := by
      have ha : raw2301step0 = (fun i j => raw2301 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2301step0 raw2301; decide +kernel
      have hl : raw2301step0Labels = raw2301Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2301 raw2301Labels permutation8 permutation4
    mixedMoment B raw2301step0 raw2301step0Labels = mixedMoment B raw2301step1 raw2301step1Labels := by
      have ha : raw2301step1 = raw2301step0 := by apply Matrix.ext; unfold raw2301step1 raw2301step0; decide +kernel
      have hl : raw2301step0Labels = labelEmbedding7 ∘ raw2301step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2301step0 raw2301step0Labels raw2301step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5293 node5293Labels := by rfl

theorem canonical2302 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2302 raw2302Labels = mixedMoment B node2767 node2767Labels := by
  calc
    mixedMoment B raw2302 raw2302Labels = mixedMoment B raw2302step0 raw2302step0Labels := by
      have ha : raw2302step0 = (fun i j => raw2302 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2302step0 raw2302; decide +kernel
      have hl : raw2302step0Labels = raw2302Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2302 raw2302Labels permutation8 permutation4
    _ = mixedMoment B node2767 node2767Labels := by rfl

theorem canonical2303 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2303 raw2303Labels = mixedMoment B node3627 node3627Labels := by
  calc
    mixedMoment B raw2303 raw2303Labels = mixedMoment B raw2303step0 raw2303step0Labels := by
      have ha : raw2303step0 = (fun i j => raw2303 (permutation10 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2303step0 raw2303; decide +kernel
      have hl : raw2303step0Labels = raw2303Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2303 raw2303Labels permutation10 permutation6
    mixedMoment B raw2303step0 raw2303step0Labels = mixedMoment B raw2303step1 raw2303step1Labels := by
      have ha : raw2303step1 = -raw2303step0 := by apply Matrix.ext; change ∀ i j, raw2303step1 i j = -(raw2303step0 i j); unfold raw2303step1 raw2303step0; decide +kernel
      have hl : raw2303step1Labels = raw2303step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2303step1 raw2303step1Labels = mixedMoment B raw2303step2 raw2303step2Labels := by
      have ha : raw2303step2 = raw2303step1 := by apply Matrix.ext; unfold raw2303step2 raw2303step1; decide +kernel
      have hl : raw2303step1Labels = labelEmbedding1 ∘ raw2303step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2303step1 raw2303step1Labels raw2303step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3627 node3627Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical191
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical24558 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24558 raw24558Labels = mixedMoment B node4143 node4143Labels := by
  calc
    mixedMoment B raw24558 raw24558Labels = mixedMoment B raw24558step0 raw24558step0Labels := by
      have ha : raw24558step0 = (fun i j => raw24558 (permutation176 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24558step0 raw24558; decide +kernel
      have hl : raw24558step0Labels = raw24558Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24558 raw24558Labels permutation176 permutation3
    mixedMoment B raw24558step0 raw24558step0Labels = mixedMoment B raw24558step1 raw24558step1Labels := by
      have ha : raw24558step1 = raw24558step0 := by apply Matrix.ext; unfold raw24558step1 raw24558step0; decide +kernel
      have hl : raw24558step0Labels = labelEmbedding6 ∘ raw24558step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24558step0 raw24558step0Labels raw24558step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4143 node4143Labels := by rfl

theorem canonical24559 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24559 raw24559Labels = mixedMoment B node4516 node4516Labels := by
  calc
    mixedMoment B raw24559 raw24559Labels = mixedMoment B raw24559step0 raw24559step0Labels := by
      have ha : raw24559step0 = (fun i j => raw24559 (permutation176 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24559step0 raw24559; decide +kernel
      have hl : raw24559step0Labels = raw24559Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24559 raw24559Labels permutation176 permutation3
    mixedMoment B raw24559step0 raw24559step0Labels = mixedMoment B raw24559step1 raw24559step1Labels := by
      have ha : raw24559step1 = raw24559step0 := by apply Matrix.ext; unfold raw24559step1 raw24559step0; decide +kernel
      have hl : raw24559step0Labels = labelEmbedding6 ∘ raw24559step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24559step0 raw24559step0Labels raw24559step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4516 node4516Labels := by rfl

theorem canonical24560 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24560 raw24560Labels = mixedMoment B node4606 node4606Labels := by
  calc
    mixedMoment B raw24560 raw24560Labels = mixedMoment B raw24560step0 raw24560step0Labels := by
      have hz : ∀ j, raw24560 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw24560step0 = (fun i j => raw24560 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw24560step0 raw24560; decide +kernel
      have hl : raw24560step0Labels = raw24560Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24560 raw24560Labels permutation434 hz
    mixedMoment B raw24560step0 raw24560step0Labels = mixedMoment B raw24560step1 raw24560step1Labels := by
      have ha : raw24560step1 = (fun i j => raw24560step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24560step1 raw24560step0; decide +kernel
      have hl : raw24560step1Labels = raw24560step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24560step0 raw24560step0Labels permutation38 permutation3
    mixedMoment B raw24560step1 raw24560step1Labels = mixedMoment B raw24560step2 raw24560step2Labels := by
      have ha : raw24560step2 = raw24560step1 := by apply Matrix.ext; unfold raw24560step2 raw24560step1; decide +kernel
      have hl : raw24560step1Labels = labelEmbedding6 ∘ raw24560step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24560step1 raw24560step1Labels raw24560step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4606 node4606Labels := by rfl

theorem canonical24561 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24561 raw24561Labels = mixedMoment B node4606 node4606Labels := by
  calc
    mixedMoment B raw24561 raw24561Labels = mixedMoment B raw24561step0 raw24561step0Labels := by
      have hz : ∀ j, raw24561 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw24561step0 = (fun i j => raw24561 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw24561step0 raw24561; decide +kernel
      have hl : raw24561step0Labels = raw24561Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24561 raw24561Labels permutation520 hz
    mixedMoment B raw24561step0 raw24561step0Labels = mixedMoment B raw24561step1 raw24561step1Labels := by
      have ha : raw24561step1 = (fun i j => raw24561step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24561step1 raw24561step0; decide +kernel
      have hl : raw24561step1Labels = raw24561step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24561step0 raw24561step0Labels permutation38 permutation3
    mixedMoment B raw24561step1 raw24561step1Labels = mixedMoment B raw24561step2 raw24561step2Labels := by
      have ha : raw24561step2 = raw24561step1 := by apply Matrix.ext; unfold raw24561step2 raw24561step1; decide +kernel
      have hl : raw24561step1Labels = labelEmbedding6 ∘ raw24561step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24561step1 raw24561step1Labels raw24561step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4606 node4606Labels := by rfl

theorem canonical24562 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24562 raw24562Labels = mixedMoment B node4175 node4175Labels := by
  calc
    mixedMoment B raw24562 raw24562Labels = mixedMoment B raw24562step0 raw24562step0Labels := by
      have hz : ∀ j, raw24562 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24562step0 = (fun i j => raw24562 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24562step0 raw24562; decide +kernel
      have hl : raw24562step0Labels = raw24562Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24562 raw24562Labels permutation265 hz
    mixedMoment B raw24562step0 raw24562step0Labels = mixedMoment B raw24562step1 raw24562step1Labels := by
      have ha : raw24562step1 = (fun i j => raw24562step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24562step1 raw24562step0; decide +kernel
      have hl : raw24562step1Labels = raw24562step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24562step0 raw24562step0Labels permutation32 permutation3
    mixedMoment B raw24562step1 raw24562step1Labels = mixedMoment B raw24562step2 raw24562step2Labels := by
      have ha : raw24562step2 = raw24562step1 := by apply Matrix.ext; unfold raw24562step2 raw24562step1; decide +kernel
      have hl : raw24562step1Labels = labelEmbedding6 ∘ raw24562step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24562step1 raw24562step1Labels raw24562step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4175 node4175Labels := by rfl

theorem canonical24563 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24563 raw24563Labels = mixedMoment B node4544 node4544Labels := by
  calc
    mixedMoment B raw24563 raw24563Labels = mixedMoment B raw24563step0 raw24563step0Labels := by
      have ha : raw24563step0 = (fun i j => raw24563 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24563step0 raw24563; decide +kernel
      have hl : raw24563step0Labels = raw24563Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24563 raw24563Labels permutation152 permutation3
    mixedMoment B raw24563step0 raw24563step0Labels = mixedMoment B raw24563step1 raw24563step1Labels := by
      have ha : raw24563step1 = raw24563step0 := by apply Matrix.ext; unfold raw24563step1 raw24563step0; decide +kernel
      have hl : raw24563step0Labels = labelEmbedding6 ∘ raw24563step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24563step0 raw24563step0Labels raw24563step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4544 node4544Labels := by rfl

theorem canonical24564 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24564 raw24564Labels = mixedMoment B node4624 node4624Labels := by
  calc
    mixedMoment B raw24564 raw24564Labels = mixedMoment B raw24564step0 raw24564step0Labels := by
      have hz : ∀ j, raw24564 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw24564step0 = (fun i j => raw24564 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw24564step0 raw24564; decide +kernel
      have hl : raw24564step0Labels = raw24564Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24564 raw24564Labels permutation434 hz
    mixedMoment B raw24564step0 raw24564step0Labels = mixedMoment B raw24564step1 raw24564step1Labels := by
      have hz : ∀ j, raw24564step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw24564step1 = (fun i j => raw24564step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw24564step1 raw24564step0; decide +kernel
      have hl : raw24564step1Labels = raw24564step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24564step0 raw24564step0Labels permutation56 hz
    mixedMoment B raw24564step1 raw24564step1Labels = mixedMoment B raw24564step2 raw24564step2Labels := by
      have ha : raw24564step2 = (fun i j => raw24564step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24564step2 raw24564step1; decide +kernel
      have hl : raw24564step2Labels = raw24564step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24564step1 raw24564step1Labels permutation10 permutation2
    _ = mixedMoment B node4624 node4624Labels := by rfl

theorem canonical24565 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24565 raw24565Labels = mixedMoment B node4624 node4624Labels := by
  calc
    mixedMoment B raw24565 raw24565Labels = mixedMoment B raw24565step0 raw24565step0Labels := by
      have hz : ∀ j, raw24565 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw24565step0 = (fun i j => raw24565 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw24565step0 raw24565; decide +kernel
      have hl : raw24565step0Labels = raw24565Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24565 raw24565Labels permutation520 hz
    mixedMoment B raw24565step0 raw24565step0Labels = mixedMoment B raw24565step1 raw24565step1Labels := by
      have hz : ∀ j, raw24565step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw24565step1 = (fun i j => raw24565step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw24565step1 raw24565step0; decide +kernel
      have hl : raw24565step1Labels = raw24565step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24565step0 raw24565step0Labels permutation56 hz
    mixedMoment B raw24565step1 raw24565step1Labels = mixedMoment B raw24565step2 raw24565step2Labels := by
      have ha : raw24565step2 = (fun i j => raw24565step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24565step2 raw24565step1; decide +kernel
      have hl : raw24565step2Labels = raw24565step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24565step1 raw24565step1Labels permutation10 permutation2
    _ = mixedMoment B node4624 node4624Labels := by rfl

theorem canonical24566 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24566 raw24566Labels = mixedMoment B node4145 node4145Labels := by
  calc
    mixedMoment B raw24566 raw24566Labels = mixedMoment B raw24566step0 raw24566step0Labels := by
      have hz : ∀ j, raw24566 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24566step0 = (fun i j => raw24566 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24566step0 raw24566; decide +kernel
      have hl : raw24566step0Labels = raw24566Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24566 raw24566Labels permutation265 hz
    mixedMoment B raw24566step0 raw24566step0Labels = mixedMoment B raw24566step1 raw24566step1Labels := by
      have ha : raw24566step1 = (fun i j => raw24566step0 (permutation35 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24566step1 raw24566step0; decide +kernel
      have hl : raw24566step1Labels = raw24566step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24566step0 raw24566step0Labels permutation35 permutation3
    mixedMoment B raw24566step1 raw24566step1Labels = mixedMoment B raw24566step2 raw24566step2Labels := by
      have ha : raw24566step2 = raw24566step1 := by apply Matrix.ext; unfold raw24566step2 raw24566step1; decide +kernel
      have hl : raw24566step1Labels = labelEmbedding6 ∘ raw24566step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24566step1 raw24566step1Labels raw24566step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4145 node4145Labels := by rfl

theorem canonical24567 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24567 raw24567Labels = mixedMoment B node4524 node4524Labels := by
  calc
    mixedMoment B raw24567 raw24567Labels = mixedMoment B raw24567step0 raw24567step0Labels := by
      have ha : raw24567step0 = (fun i j => raw24567 (permutation155 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24567step0 raw24567; decide +kernel
      have hl : raw24567step0Labels = raw24567Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24567 raw24567Labels permutation155 permutation3
    mixedMoment B raw24567step0 raw24567step0Labels = mixedMoment B raw24567step1 raw24567step1Labels := by
      have ha : raw24567step1 = raw24567step0 := by apply Matrix.ext; unfold raw24567step1 raw24567step0; decide +kernel
      have hl : raw24567step0Labels = labelEmbedding6 ∘ raw24567step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24567step0 raw24567step0Labels raw24567step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4524 node4524Labels := by rfl

theorem canonical24568 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24568 raw24568Labels = mixedMoment B node4518 node4518Labels := by
  calc
    mixedMoment B raw24568 raw24568Labels = mixedMoment B raw24568step0 raw24568step0Labels := by
      have hz : ∀ j, raw24568 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24568step0 = (fun i j => raw24568 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24568step0 raw24568; decide +kernel
      have hl : raw24568step0Labels = raw24568Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24568 raw24568Labels permutation265 hz
    mixedMoment B raw24568step0 raw24568step0Labels = mixedMoment B raw24568step1 raw24568step1Labels := by
      have ha : raw24568step1 = (fun i j => raw24568step0 (permutation35 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24568step1 raw24568step0; decide +kernel
      have hl : raw24568step1Labels = raw24568step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24568step0 raw24568step0Labels permutation35 permutation3
    mixedMoment B raw24568step1 raw24568step1Labels = mixedMoment B raw24568step2 raw24568step2Labels := by
      have ha : raw24568step2 = raw24568step1 := by apply Matrix.ext; unfold raw24568step2 raw24568step1; decide +kernel
      have hl : raw24568step1Labels = labelEmbedding6 ∘ raw24568step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24568step1 raw24568step1Labels raw24568step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4518 node4518Labels := by rfl

theorem canonical24569 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24569 raw24569Labels = mixedMoment B node4612 node4612Labels := by
  calc
    mixedMoment B raw24569 raw24569Labels = mixedMoment B raw24569step0 raw24569step0Labels := by
      have hz : ∀ j, raw24569 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw24569step0 = (fun i j => raw24569 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw24569step0 raw24569; decide +kernel
      have hl : raw24569step0Labels = raw24569Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24569 raw24569Labels permutation520 hz
    mixedMoment B raw24569step0 raw24569step0Labels = mixedMoment B raw24569step1 raw24569step1Labels := by
      have hz : ∀ j, raw24569step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw24569step1 = (fun i j => raw24569step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw24569step1 raw24569step0; decide +kernel
      have hl : raw24569step1Labels = raw24569step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24569step0 raw24569step0Labels permutation56 hz
    mixedMoment B raw24569step1 raw24569step1Labels = mixedMoment B raw24569step2 raw24569step2Labels := by
      have ha : raw24569step2 = (fun i j => raw24569step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24569step2 raw24569step1; decide +kernel
      have hl : raw24569step2Labels = raw24569step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24569step1 raw24569step1Labels permutation9 permutation3
    mixedMoment B raw24569step2 raw24569step2Labels = mixedMoment B raw24569step3 raw24569step3Labels := by
      have ha : raw24569step3 = raw24569step2 := by apply Matrix.ext; unfold raw24569step3 raw24569step2; decide +kernel
      have hl : raw24569step2Labels = labelEmbedding6 ∘ raw24569step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24569step2 raw24569step2Labels raw24569step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4612 node4612Labels := by rfl

theorem canonical24570 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24570 raw24570Labels = mixedMoment B node4145 node4145Labels := by
  calc
    mixedMoment B raw24570 raw24570Labels = mixedMoment B raw24570step0 raw24570step0Labels := by
      have hz : ∀ j, raw24570 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24570step0 = (fun i j => raw24570 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24570step0 raw24570; decide +kernel
      have hl : raw24570step0Labels = raw24570Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24570 raw24570Labels permutation265 hz
    mixedMoment B raw24570step0 raw24570step0Labels = mixedMoment B raw24570step1 raw24570step1Labels := by
      have ha : raw24570step1 = (fun i j => raw24570step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24570step1 raw24570step0; decide +kernel
      have hl : raw24570step1Labels = raw24570step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24570step0 raw24570step0Labels permutation33 permutation3
    mixedMoment B raw24570step1 raw24570step1Labels = mixedMoment B raw24570step2 raw24570step2Labels := by
      have ha : raw24570step2 = raw24570step1 := by apply Matrix.ext; unfold raw24570step2 raw24570step1; decide +kernel
      have hl : raw24570step1Labels = labelEmbedding6 ∘ raw24570step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24570step1 raw24570step1Labels raw24570step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4145 node4145Labels := by rfl

theorem canonical24571 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24571 raw24571Labels = mixedMoment B node4524 node4524Labels := by
  calc
    mixedMoment B raw24571 raw24571Labels = mixedMoment B raw24571step0 raw24571step0Labels := by
      have ha : raw24571step0 = (fun i j => raw24571 (permutation153 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24571step0 raw24571; decide +kernel
      have hl : raw24571step0Labels = raw24571Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24571 raw24571Labels permutation153 permutation3
    mixedMoment B raw24571step0 raw24571step0Labels = mixedMoment B raw24571step1 raw24571step1Labels := by
      have ha : raw24571step1 = raw24571step0 := by apply Matrix.ext; unfold raw24571step1 raw24571step0; decide +kernel
      have hl : raw24571step0Labels = labelEmbedding6 ∘ raw24571step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24571step0 raw24571step0Labels raw24571step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4524 node4524Labels := by rfl

theorem canonical24572 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24572 raw24572Labels = mixedMoment B node4518 node4518Labels := by
  calc
    mixedMoment B raw24572 raw24572Labels = mixedMoment B raw24572step0 raw24572step0Labels := by
      have hz : ∀ j, raw24572 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24572step0 = (fun i j => raw24572 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24572step0 raw24572; decide +kernel
      have hl : raw24572step0Labels = raw24572Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24572 raw24572Labels permutation265 hz
    mixedMoment B raw24572step0 raw24572step0Labels = mixedMoment B raw24572step1 raw24572step1Labels := by
      have ha : raw24572step1 = (fun i j => raw24572step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24572step1 raw24572step0; decide +kernel
      have hl : raw24572step1Labels = raw24572step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24572step0 raw24572step0Labels permutation33 permutation3
    mixedMoment B raw24572step1 raw24572step1Labels = mixedMoment B raw24572step2 raw24572step2Labels := by
      have ha : raw24572step2 = raw24572step1 := by apply Matrix.ext; unfold raw24572step2 raw24572step1; decide +kernel
      have hl : raw24572step1Labels = labelEmbedding6 ∘ raw24572step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24572step1 raw24572step1Labels raw24572step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4518 node4518Labels := by rfl

theorem canonical24573 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24573 raw24573Labels = mixedMoment B node4612 node4612Labels := by
  calc
    mixedMoment B raw24573 raw24573Labels = mixedMoment B raw24573step0 raw24573step0Labels := by
      have hz : ∀ j, raw24573 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw24573step0 = (fun i j => raw24573 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw24573step0 raw24573; decide +kernel
      have hl : raw24573step0Labels = raw24573Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24573 raw24573Labels permutation434 hz
    mixedMoment B raw24573step0 raw24573step0Labels = mixedMoment B raw24573step1 raw24573step1Labels := by
      have hz : ∀ j, raw24573step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw24573step1 = (fun i j => raw24573step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw24573step1 raw24573step0; decide +kernel
      have hl : raw24573step1Labels = raw24573step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24573step0 raw24573step0Labels permutation56 hz
    mixedMoment B raw24573step1 raw24573step1Labels = mixedMoment B raw24573step2 raw24573step2Labels := by
      have ha : raw24573step2 = (fun i j => raw24573step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24573step2 raw24573step1; decide +kernel
      have hl : raw24573step2Labels = raw24573step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24573step1 raw24573step1Labels permutation9 permutation3
    mixedMoment B raw24573step2 raw24573step2Labels = mixedMoment B raw24573step3 raw24573step3Labels := by
      have ha : raw24573step3 = raw24573step2 := by apply Matrix.ext; unfold raw24573step3 raw24573step2; decide +kernel
      have hl : raw24573step2Labels = labelEmbedding6 ∘ raw24573step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24573step2 raw24573step2Labels raw24573step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4612 node4612Labels := by rfl

theorem canonical24574 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24574 raw24574Labels = mixedMoment B node4144 node4144Labels := by
  calc
    mixedMoment B raw24574 raw24574Labels = mixedMoment B raw24574step0 raw24574step0Labels := by
      have hz : ∀ j, raw24574 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24574step0 = (fun i j => raw24574 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24574step0 raw24574; decide +kernel
      have hl : raw24574step0Labels = raw24574Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24574 raw24574Labels permutation265 hz
    mixedMoment B raw24574step0 raw24574step0Labels = mixedMoment B raw24574step1 raw24574step1Labels := by
      have ha : raw24574step1 = (fun i j => raw24574step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24574step1 raw24574step0; decide +kernel
      have hl : raw24574step1Labels = raw24574step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24574step0 raw24574step0Labels permutation32 permutation3
    mixedMoment B raw24574step1 raw24574step1Labels = mixedMoment B raw24574step2 raw24574step2Labels := by
      have ha : raw24574step2 = raw24574step1 := by apply Matrix.ext; unfold raw24574step2 raw24574step1; decide +kernel
      have hl : raw24574step1Labels = labelEmbedding6 ∘ raw24574step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24574step1 raw24574step1Labels raw24574step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4144 node4144Labels := by rfl

theorem canonical24575 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24575 raw24575Labels = mixedMoment B node4523 node4523Labels := by
  calc
    mixedMoment B raw24575 raw24575Labels = mixedMoment B raw24575step0 raw24575step0Labels := by
      have ha : raw24575step0 = (fun i j => raw24575 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24575step0 raw24575; decide +kernel
      have hl : raw24575step0Labels = raw24575Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24575 raw24575Labels permutation152 permutation3
    mixedMoment B raw24575step0 raw24575step0Labels = mixedMoment B raw24575step1 raw24575step1Labels := by
      have ha : raw24575step1 = raw24575step0 := by apply Matrix.ext; unfold raw24575step1 raw24575step0; decide +kernel
      have hl : raw24575step0Labels = labelEmbedding6 ∘ raw24575step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24575step0 raw24575step0Labels raw24575step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4523 node4523Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical192
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical24576 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24576 raw24576Labels = mixedMoment B node4517 node4517Labels := by
  calc
    mixedMoment B raw24576 raw24576Labels = mixedMoment B raw24576step0 raw24576step0Labels := by
      have hz : ∀ j, raw24576 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24576step0 = (fun i j => raw24576 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24576step0 raw24576; decide +kernel
      have hl : raw24576step0Labels = raw24576Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24576 raw24576Labels permutation265 hz
    mixedMoment B raw24576step0 raw24576step0Labels = mixedMoment B raw24576step1 raw24576step1Labels := by
      have ha : raw24576step1 = (fun i j => raw24576step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24576step1 raw24576step0; decide +kernel
      have hl : raw24576step1Labels = raw24576step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24576step0 raw24576step0Labels permutation32 permutation3
    mixedMoment B raw24576step1 raw24576step1Labels = mixedMoment B raw24576step2 raw24576step2Labels := by
      have ha : raw24576step2 = raw24576step1 := by apply Matrix.ext; unfold raw24576step2 raw24576step1; decide +kernel
      have hl : raw24576step1Labels = labelEmbedding6 ∘ raw24576step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24576step1 raw24576step1Labels raw24576step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4517 node4517Labels := by rfl

theorem canonical24577 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24577 raw24577Labels = mixedMoment B node4608 node4608Labels := by
  calc
    mixedMoment B raw24577 raw24577Labels = mixedMoment B raw24577step0 raw24577step0Labels := by
      have hz : ∀ j, raw24577 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw24577step0 = (fun i j => raw24577 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw24577step0 raw24577; decide +kernel
      have hl : raw24577step0Labels = raw24577Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24577 raw24577Labels permutation434 hz
    mixedMoment B raw24577step0 raw24577step0Labels = mixedMoment B raw24577step1 raw24577step1Labels := by
      have hz : ∀ j, raw24577step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw24577step1 = (fun i j => raw24577step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw24577step1 raw24577step0; decide +kernel
      have hl : raw24577step1Labels = raw24577step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24577step0 raw24577step0Labels permutation56 hz
    mixedMoment B raw24577step1 raw24577step1Labels = mixedMoment B raw24577step2 raw24577step2Labels := by
      have ha : raw24577step2 = (fun i j => raw24577step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24577step2 raw24577step1; decide +kernel
      have hl : raw24577step2Labels = raw24577step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24577step1 raw24577step1Labels permutation8 permutation3
    mixedMoment B raw24577step2 raw24577step2Labels = mixedMoment B raw24577step3 raw24577step3Labels := by
      have ha : raw24577step3 = raw24577step2 := by apply Matrix.ext; unfold raw24577step3 raw24577step2; decide +kernel
      have hl : raw24577step2Labels = labelEmbedding6 ∘ raw24577step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24577step2 raw24577step2Labels raw24577step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4608 node4608Labels := by rfl

theorem canonical24578 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24578 raw24578Labels = mixedMoment B node4608 node4608Labels := by
  calc
    mixedMoment B raw24578 raw24578Labels = mixedMoment B raw24578step0 raw24578step0Labels := by
      have hz : ∀ j, raw24578 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw24578step0 = (fun i j => raw24578 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw24578step0 raw24578; decide +kernel
      have hl : raw24578step0Labels = raw24578Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24578 raw24578Labels permutation520 hz
    mixedMoment B raw24578step0 raw24578step0Labels = mixedMoment B raw24578step1 raw24578step1Labels := by
      have hz : ∀ j, raw24578step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw24578step1 = (fun i j => raw24578step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw24578step1 raw24578step0; decide +kernel
      have hl : raw24578step1Labels = raw24578step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24578step0 raw24578step0Labels permutation56 hz
    mixedMoment B raw24578step1 raw24578step1Labels = mixedMoment B raw24578step2 raw24578step2Labels := by
      have ha : raw24578step2 = (fun i j => raw24578step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24578step2 raw24578step1; decide +kernel
      have hl : raw24578step2Labels = raw24578step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24578step1 raw24578step1Labels permutation8 permutation3
    mixedMoment B raw24578step2 raw24578step2Labels = mixedMoment B raw24578step3 raw24578step3Labels := by
      have ha : raw24578step3 = raw24578step2 := by apply Matrix.ext; unfold raw24578step3 raw24578step2; decide +kernel
      have hl : raw24578step2Labels = labelEmbedding6 ∘ raw24578step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24578step2 raw24578step2Labels raw24578step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4608 node4608Labels := by rfl

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

theorem canonical270 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw270 raw270Labels = mixedMoment B node2767 node2767Labels := by
  calc
    mixedMoment B raw270 raw270Labels = mixedMoment B raw270step0 raw270step0Labels := by
      have ha : raw270step0 = (fun i j => raw270 (permutation8 i) (permutation5 j)) := by apply Matrix.ext; unfold raw270step0 raw270; decide +kernel
      have hl : raw270step0Labels = raw270Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw270 raw270Labels permutation8 permutation5
    mixedMoment B raw270step0 raw270step0Labels = mixedMoment B raw270step1 raw270step1Labels := by
      have ha : raw270step1 = raw270step0 := by apply Matrix.ext; unfold raw270step1 raw270step0; decide +kernel
      have hl : raw270step0Labels = labelEmbedding1 ∘ raw270step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw270step0 raw270step0Labels raw270step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2767 node2767Labels := by rfl

theorem canonical271 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw271 raw271Labels = mixedMoment B node404 node404Labels := by
  calc
    mixedMoment B raw271 raw271Labels = mixedMoment B raw271step0 raw271step0Labels := by
      have ha : raw271step0 = (fun i j => raw271 (permutation8 i) (permutation5 j)) := by apply Matrix.ext; unfold raw271step0 raw271; decide +kernel
      have hl : raw271step0Labels = raw271Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw271 raw271Labels permutation8 permutation5
    _ = mixedMoment B node404 node404Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical6
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical768 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw768 raw768Labels = mixedMoment B node4143 node4143Labels := by
  calc
    mixedMoment B raw768 raw768Labels = mixedMoment B raw768step0 raw768step0Labels := by
      have ha : raw768step0 = (fun i j => raw768 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw768step0 raw768; decide +kernel
      have hl : raw768step0Labels = raw768Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw768 raw768Labels permutation152 permutation4
    mixedMoment B raw768step0 raw768step0Labels = mixedMoment B raw768step1 raw768step1Labels := by
      have ha : raw768step1 = raw768step0 := by apply Matrix.ext; unfold raw768step1 raw768step0; decide +kernel
      have hl : raw768step0Labels = labelEmbedding7 ∘ raw768step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw768step0 raw768step0Labels raw768step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4143 node4143Labels := by rfl

theorem canonical769 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw769 raw769Labels = mixedMoment B node571 node571Labels := by
  calc
    mixedMoment B raw769 raw769Labels = mixedMoment B raw769step0 raw769step0Labels := by
      have ha : raw769step0 = (fun i j => raw769 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw769step0 raw769; decide +kernel
      have hl : raw769step0Labels = raw769Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw769 raw769Labels permutation152 permutation4
    _ = mixedMoment B node571 node571Labels := by rfl

theorem canonical770 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw770 raw770Labels = mixedMoment B node1491 node1491Labels := by
  calc
    mixedMoment B raw770 raw770Labels = mixedMoment B raw770step0 raw770step0Labels := by
      have ha : raw770step0 = (fun i j => raw770 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw770step0 raw770; decide +kernel
      have hl : raw770step0Labels = raw770Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw770 raw770Labels permutation152 permutation6
    mixedMoment B raw770step0 raw770step0Labels = mixedMoment B raw770step1 raw770step1Labels := by
      have ha : raw770step1 = -raw770step0 := by apply Matrix.ext; change ∀ i j, raw770step1 i j = -(raw770step0 i j); unfold raw770step1 raw770step0; decide +kernel
      have hl : raw770step1Labels = raw770step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw770step1 raw770step1Labels = mixedMoment B raw770step2 raw770step2Labels := by
      have ha : raw770step2 = raw770step1 := by apply Matrix.ext; unfold raw770step2 raw770step1; decide +kernel
      have hl : raw770step1Labels = labelEmbedding1 ∘ raw770step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw770step1 raw770step1Labels raw770step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1491 node1491Labels := by rfl

theorem canonical771 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw771 raw771Labels = mixedMoment B node4144 node4144Labels := by
  calc
    mixedMoment B raw771 raw771Labels = mixedMoment B raw771step0 raw771step0Labels := by
      have ha : raw771step0 = (fun i j => raw771 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw771step0 raw771; decide +kernel
      have hl : raw771step0Labels = raw771Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw771 raw771Labels permutation32 permutation4
    mixedMoment B raw771step0 raw771step0Labels = mixedMoment B raw771step1 raw771step1Labels := by
      have ha : raw771step1 = raw771step0 := by apply Matrix.ext; unfold raw771step1 raw771step0; decide +kernel
      have hl : raw771step0Labels = labelEmbedding7 ∘ raw771step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw771step0 raw771step0Labels raw771step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4144 node4144Labels := by rfl

theorem canonical772 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw772 raw772Labels = mixedMoment B node572 node572Labels := by
  calc
    mixedMoment B raw772 raw772Labels = mixedMoment B raw772step0 raw772step0Labels := by
      have ha : raw772step0 = (fun i j => raw772 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw772step0 raw772; decide +kernel
      have hl : raw772step0Labels = raw772Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw772 raw772Labels permutation32 permutation4
    _ = mixedMoment B node572 node572Labels := by rfl

theorem canonical773 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw773 raw773Labels = mixedMoment B node1492 node1492Labels := by
  calc
    mixedMoment B raw773 raw773Labels = mixedMoment B raw773step0 raw773step0Labels := by
      have ha : raw773step0 = (fun i j => raw773 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw773step0 raw773; decide +kernel
      have hl : raw773step0Labels = raw773Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw773 raw773Labels permutation32 permutation6
    mixedMoment B raw773step0 raw773step0Labels = mixedMoment B raw773step1 raw773step1Labels := by
      have ha : raw773step1 = -raw773step0 := by apply Matrix.ext; change ∀ i j, raw773step1 i j = -(raw773step0 i j); unfold raw773step1 raw773step0; decide +kernel
      have hl : raw773step1Labels = raw773step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw773step1 raw773step1Labels = mixedMoment B raw773step2 raw773step2Labels := by
      have ha : raw773step2 = raw773step1 := by apply Matrix.ext; unfold raw773step2 raw773step1; decide +kernel
      have hl : raw773step1Labels = labelEmbedding1 ∘ raw773step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw773step1 raw773step1Labels raw773step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1492 node1492Labels := by rfl

theorem canonical774 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw774 raw774Labels = mixedMoment B node4145 node4145Labels := by
  calc
    mixedMoment B raw774 raw774Labels = mixedMoment B raw774step0 raw774step0Labels := by
      have ha : raw774step0 = (fun i j => raw774 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw774step0 raw774; decide +kernel
      have hl : raw774step0Labels = raw774Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw774 raw774Labels permutation32 permutation4
    mixedMoment B raw774step0 raw774step0Labels = mixedMoment B raw774step1 raw774step1Labels := by
      have ha : raw774step1 = raw774step0 := by apply Matrix.ext; unfold raw774step1 raw774step0; decide +kernel
      have hl : raw774step0Labels = labelEmbedding7 ∘ raw774step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw774step0 raw774step0Labels raw774step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4145 node4145Labels := by rfl

theorem canonical775 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw775 raw775Labels = mixedMoment B node573 node573Labels := by
  calc
    mixedMoment B raw775 raw775Labels = mixedMoment B raw775step0 raw775step0Labels := by
      have ha : raw775step0 = (fun i j => raw775 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw775step0 raw775; decide +kernel
      have hl : raw775step0Labels = raw775Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw775 raw775Labels permutation32 permutation4
    _ = mixedMoment B node573 node573Labels := by rfl

theorem canonical776 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw776 raw776Labels = mixedMoment B node1493 node1493Labels := by
  calc
    mixedMoment B raw776 raw776Labels = mixedMoment B raw776step0 raw776step0Labels := by
      have ha : raw776step0 = (fun i j => raw776 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw776step0 raw776; decide +kernel
      have hl : raw776step0Labels = raw776Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw776 raw776Labels permutation32 permutation6
    mixedMoment B raw776step0 raw776step0Labels = mixedMoment B raw776step1 raw776step1Labels := by
      have ha : raw776step1 = -raw776step0 := by apply Matrix.ext; change ∀ i j, raw776step1 i j = -(raw776step0 i j); unfold raw776step1 raw776step0; decide +kernel
      have hl : raw776step1Labels = raw776step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw776step1 raw776step1Labels = mixedMoment B raw776step2 raw776step2Labels := by
      have ha : raw776step2 = raw776step1 := by apply Matrix.ext; unfold raw776step2 raw776step1; decide +kernel
      have hl : raw776step1Labels = labelEmbedding1 ∘ raw776step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw776step1 raw776step1Labels raw776step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1493 node1493Labels := by rfl

theorem canonical810 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw810 raw810Labels = mixedMoment B node4175 node4175Labels := by
  calc
    mixedMoment B raw810 raw810Labels = mixedMoment B raw810step0 raw810step0Labels := by
      have ha : raw810step0 = (fun i j => raw810 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw810step0 raw810; decide +kernel
      have hl : raw810step0Labels = raw810Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw810 raw810Labels permutation32 permutation4
    mixedMoment B raw810step0 raw810step0Labels = mixedMoment B raw810step1 raw810step1Labels := by
      have ha : raw810step1 = raw810step0 := by apply Matrix.ext; unfold raw810step1 raw810step0; decide +kernel
      have hl : raw810step0Labels = labelEmbedding7 ∘ raw810step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw810step0 raw810step0Labels raw810step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4175 node4175Labels := by rfl

theorem canonical811 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw811 raw811Labels = mixedMoment B node603 node603Labels := by
  calc
    mixedMoment B raw811 raw811Labels = mixedMoment B raw811step0 raw811step0Labels := by
      have ha : raw811step0 = (fun i j => raw811 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw811step0 raw811; decide +kernel
      have hl : raw811step0Labels = raw811Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw811 raw811Labels permutation32 permutation4
    _ = mixedMoment B node603 node603Labels := by rfl

theorem canonical812 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw812 raw812Labels = mixedMoment B node1517 node1517Labels := by
  calc
    mixedMoment B raw812 raw812Labels = mixedMoment B raw812step0 raw812step0Labels := by
      have ha : raw812step0 = (fun i j => raw812 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw812step0 raw812; decide +kernel
      have hl : raw812step0Labels = raw812Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw812 raw812Labels permutation32 permutation6
    mixedMoment B raw812step0 raw812step0Labels = mixedMoment B raw812step1 raw812step1Labels := by
      have ha : raw812step1 = -raw812step0 := by apply Matrix.ext; change ∀ i j, raw812step1 i j = -(raw812step0 i j); unfold raw812step1 raw812step0; decide +kernel
      have hl : raw812step1Labels = raw812step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw812step1 raw812step1Labels = mixedMoment B raw812step2 raw812step2Labels := by
      have ha : raw812step2 = raw812step1 := by apply Matrix.ext; unfold raw812step2 raw812step1; decide +kernel
      have hl : raw812step1Labels = labelEmbedding1 ∘ raw812step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw812step1 raw812step1Labels raw812step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1517 node1517Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical97
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical12536 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12536 raw12536Labels = mixedMoment B node4601 node4601Labels := by
  calc
    mixedMoment B raw12536 raw12536Labels = mixedMoment B raw12536step0 raw12536step0Labels := by
      have ha : raw12536step0 = (fun i j => raw12536 (permutation194 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12536step0 raw12536; decide +kernel
      have hl : raw12536step0Labels = raw12536Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12536 raw12536Labels permutation194 permutation3
    mixedMoment B raw12536step0 raw12536step0Labels = mixedMoment B raw12536step1 raw12536step1Labels := by
      have ha : raw12536step1 = raw12536step0 := by apply Matrix.ext; unfold raw12536step1 raw12536step0; decide +kernel
      have hl : raw12536step0Labels = labelEmbedding6 ∘ raw12536step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12536step0 raw12536step0Labels raw12536step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4601 node4601Labels := by rfl

theorem canonical12541 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12541 raw12541Labels = mixedMoment B node4622 node4622Labels := by
  calc
    mixedMoment B raw12541 raw12541Labels = mixedMoment B raw12541step0 raw12541step0Labels := by
      have hz : ∀ j, raw12541 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12541step0 = (fun i j => raw12541 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12541step0 raw12541; decide +kernel
      have hl : raw12541step0Labels = raw12541Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12541 raw12541Labels permutation265 hz
    mixedMoment B raw12541step0 raw12541step0Labels = mixedMoment B raw12541step1 raw12541step1Labels := by
      have ha : raw12541step1 = (fun i j => raw12541step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw12541step1 raw12541step0; decide +kernel
      have hl : raw12541step1Labels = raw12541step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12541step0 raw12541step0Labels permutation40 permutation2
    _ = mixedMoment B node4622 node4622Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical98
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical12546 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12546 raw12546Labels = mixedMoment B node4602 node4602Labels := by
  calc
    mixedMoment B raw12546 raw12546Labels = mixedMoment B raw12546step0 raw12546step0Labels := by
      have hz : ∀ j, raw12546 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12546step0 = (fun i j => raw12546 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12546step0 raw12546; decide +kernel
      have hl : raw12546step0Labels = raw12546Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12546 raw12546Labels permutation265 hz
    mixedMoment B raw12546step0 raw12546step0Labels = mixedMoment B raw12546step1 raw12546step1Labels := by
      have ha : raw12546step1 = (fun i j => raw12546step0 (permutation37 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12546step1 raw12546step0; decide +kernel
      have hl : raw12546step1Labels = raw12546step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12546step0 raw12546step0Labels permutation37 permutation3
    mixedMoment B raw12546step1 raw12546step1Labels = mixedMoment B raw12546step2 raw12546step2Labels := by
      have ha : raw12546step2 = raw12546step1 := by apply Matrix.ext; unfold raw12546step2 raw12546step1; decide +kernel
      have hl : raw12546step1Labels = labelEmbedding6 ∘ raw12546step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12546step1 raw12546step1Labels raw12546step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4602 node4602Labels := by rfl

theorem canonical12551 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12551 raw12551Labels = mixedMoment B node4602 node4602Labels := by
  calc
    mixedMoment B raw12551 raw12551Labels = mixedMoment B raw12551step0 raw12551step0Labels := by
      have hz : ∀ j, raw12551 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12551step0 = (fun i j => raw12551 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12551step0 raw12551; decide +kernel
      have hl : raw12551step0Labels = raw12551Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12551 raw12551Labels permutation265 hz
    mixedMoment B raw12551step0 raw12551step0Labels = mixedMoment B raw12551step1 raw12551step1Labels := by
      have ha : raw12551step1 = (fun i j => raw12551step0 (permutation36 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12551step1 raw12551step0; decide +kernel
      have hl : raw12551step1Labels = raw12551step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12551step0 raw12551step0Labels permutation36 permutation3
    mixedMoment B raw12551step1 raw12551step1Labels = mixedMoment B raw12551step2 raw12551step2Labels := by
      have ha : raw12551step2 = raw12551step1 := by apply Matrix.ext; unfold raw12551step2 raw12551step1; decide +kernel
      have hl : raw12551step1Labels = labelEmbedding6 ∘ raw12551step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12551step1 raw12551step1Labels raw12551step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4602 node4602Labels := by rfl

theorem canonical12557 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12557 raw12557Labels = mixedMoment B node5148 node5148Labels := by
  calc
    _ = mixedMoment B node5148 node5148Labels := by rfl

theorem canonical12558 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12558 raw12558Labels = mixedMoment B node5203 node5203Labels := by
  calc
    mixedMoment B raw12558 raw12558Labels = mixedMoment B raw12558step0 raw12558step0Labels := by
      have hz : ∀ j, raw12558 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12558step0 = (fun i j => raw12558 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12558step0 raw12558; decide +kernel
      have hl : raw12558step0Labels = raw12558Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12558 raw12558Labels permutation265 hz
    _ = mixedMoment B node5203 node5203Labels := by rfl

theorem canonical12559 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12559 raw12559Labels = mixedMoment B node5293 node5293Labels := by
  calc
    mixedMoment B raw12559 raw12559Labels = mixedMoment B raw12559step0 raw12559step0Labels := by
      have hz : ∀ j, raw12559 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw12559step0 = (fun i j => raw12559 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw12559step0 raw12559; decide +kernel
      have hl : raw12559step0Labels = raw12559Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12559 raw12559Labels permutation434 hz
    mixedMoment B raw12559step0 raw12559step0Labels = mixedMoment B raw12559step1 raw12559step1Labels := by
      have hz : ∀ j, raw12559step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw12559step1 = (fun i j => raw12559step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw12559step1 raw12559step0; decide +kernel
      have hl : raw12559step1Labels = raw12559step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12559step0 raw12559step0Labels permutation56 hz
    _ = mixedMoment B node5293 node5293Labels := by rfl

theorem canonical12560 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12560 raw12560Labels = mixedMoment B node5293 node5293Labels := by
  calc
    mixedMoment B raw12560 raw12560Labels = mixedMoment B raw12560step0 raw12560step0Labels := by
      have hz : ∀ j, raw12560 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw12560step0 = (fun i j => raw12560 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw12560step0 raw12560; decide +kernel
      have hl : raw12560step0Labels = raw12560Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12560 raw12560Labels permutation520 hz
    mixedMoment B raw12560step0 raw12560step0Labels = mixedMoment B raw12560step1 raw12560step1Labels := by
      have hz : ∀ j, raw12560step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw12560step1 = (fun i j => raw12560step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw12560step1 raw12560step0; decide +kernel
      have hl : raw12560step1Labels = raw12560step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12560step0 raw12560step0Labels permutation56 hz
    _ = mixedMoment B node5293 node5293Labels := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical239
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical7678 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7678 = injectiveMoment H node65 := by
  rfl

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

theorem canonical781 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw781 = injectiveMoment H node181 := by
  calc
    injectiveMoment H raw781 = injectiveMoment H raw781step0 := by
      have heq : raw781step0 = -raw781 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw781).symm
    injectiveMoment H raw781step0 = injectiveMoment H raw781step1 := by
      have heq : raw781step1 = (fun i j => raw781step0 (permutation11 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw781step0 permutation11 permutation8
    _ = injectiveMoment H node181 := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical161
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical5177 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5177 = injectiveMoment H node11 := by
  clear _hH
  calc
    injectiveMoment H raw5177 = injectiveMoment H raw5177step0 := by
      have hz : ∀ j, raw5177 (permutation15 0) j = 0 := by decide +kernel
      have heq : raw5177step0 = (fun i j => raw5177 (permutation15 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw5177 permutation15 hz
    _ = injectiveMoment H node11 := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical26
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical841 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw841 = injectiveMoment H node10 := by
  calc
    injectiveMoment H raw841 = injectiveMoment H raw841step0 := by
      have heq : raw841step0 = raw841.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw841).symm
    injectiveMoment H raw841step0 = injectiveMoment H raw841step1 := by
      have heq : raw841step1 = (fun i j => raw841step0 (permutation4 i) (permutation1 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw841step0 permutation4 permutation1
    _ = injectiveMoment H node10 := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical5
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical175 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw175 = injectiveMoment H node150 := by
  calc
    injectiveMoment H raw175 = injectiveMoment H raw175step0 := by
      have heq : raw175step0 = -raw175 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw175).symm
    injectiveMoment H raw175step0 = injectiveMoment H raw175step1 := by
      have heq : raw175step1 = (fun i j => raw175step0 (permutation11 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw175step0 permutation11 permutation6
    _ = injectiveMoment H node150 := by rfl

theorem canonical180 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw180 = injectiveMoment H node9 := by
  calc
    injectiveMoment H raw180 = injectiveMoment H raw180step0 := by
      have heq : raw180step0 = raw180.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw180).symm
    _ = injectiveMoment H node9 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical6
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical208 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw208 = injectiveMoment H node16 := by
  rfl

theorem canonical211 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw211 = injectiveMoment H node8 := by
  rfl

theorem canonical214 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw214 = injectiveMoment H node9 := by
  rfl

theorem canonical215 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw215 = injectiveMoment H node2 := by
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

theorem sound2 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node2 = Sparse.eval value2 (momentVector H) := by
  have hc : momentVector H 6 = injectiveMoment H node2 := rfl
  simp [value2, Sparse.eval, hc]

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

theorem sound8 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node8 = Sparse.eval value8 (momentVector H) := by
  have heq : pivotMatrix8 = (fun u v => node8 (pivotPermutation8 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node8 = injectiveMoment H pivotMatrix8 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix8 0 = Pi.single (0 : Fin 2) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 2 < 6) hH pivotMatrix8 0 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix8 (0 : Fin 2)) =
      Sparse.eval value3 (momentVector H) := by
    have heq : mergeFirst pivotMatrix8 (0 : Fin 2) = raw926 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical926 hH).trans (sound3 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix8 (1 : Fin 2)) =
      Sparse.eval value2 (momentVector H) := by
    have heq : mergeFirst pivotMatrix8 (1 : Fin 2) = raw215 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical215 hH).trans (sound2 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (4 : ℝ) * injectiveMoment H node8 + (injectiveMoment H (mergeFirst pivotMatrix8 (0 : Fin 2)) + (injectiveMoment H (mergeFirst pivotMatrix8 (1 : Fin 2)))) = 0 at hc
  rw [hm0, hm1] at hc
  norm_num [value8, value2, value3, Sparse.eval] at hc ⊢
  linarith

theorem sound9 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node9 = Sparse.eval value9 (momentVector H) := by
  have hc : momentVector H 5 = injectiveMoment H node9 := rfl
  simp [value9, Sparse.eval, hc]

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

theorem sound16 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node16 = Sparse.eval value16 (momentVector H) := by
  have heq : pivotMatrix16 = (fun u v => node16 (pivotPermutation16 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node16 = injectiveMoment H pivotMatrix16 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix16 0 = Pi.single (0 : Fin 2) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix16 0 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix16 (0 : Fin 3)) =
      Sparse.eval value10 (momentVector H) := by
    have heq : mergeFirst pivotMatrix16 (0 : Fin 3) = raw917 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical917 hH).trans (sound10 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix16 (1 : Fin 3)) =
      Sparse.eval value9 (momentVector H) := by
    have heq : mergeFirst pivotMatrix16 (1 : Fin 3) = raw214 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical214 hH).trans (sound9 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix16 (2 : Fin 3)) =
      Sparse.eval value8 (momentVector H) := by
    have heq : mergeFirst pivotMatrix16 (2 : Fin 3) = raw211 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical211 hH).trans (sound8 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node16 + (injectiveMoment H (mergeFirst pivotMatrix16 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix16 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix16 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value16, value10, value8, value9, Sparse.eval] at hc ⊢
  linarith

theorem sound35 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node35 = Sparse.eval value35 (momentVector H) := by
  have hc : momentVector H 8 = injectiveMoment H node35 := rfl
  simp [value35, Sparse.eval, hc]

theorem sound52 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node52 = Sparse.eval value52 (momentVector H) := by
  have heq : pivotMatrix52 = (fun u v => node52.transpose (pivotPermutation52 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node52 = injectiveMoment H pivotMatrix52 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix52 0 = Pi.single (2 : Fin 3) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 2 < 6) hH pivotMatrix52 2 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix52 (0 : Fin 2)) =
      Sparse.eval value9 (momentVector H) := by
    have heq : mergeFirst pivotMatrix52 (0 : Fin 2) = raw180 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical180 hH).trans (sound9 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix52 (1 : Fin 2)) =
      Sparse.eval value10 (momentVector H) := by
    have heq : mergeFirst pivotMatrix52 (1 : Fin 2) = raw841 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical841 hH).trans (sound10 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (4 : ℝ) * injectiveMoment H node52 + (injectiveMoment H (mergeFirst pivotMatrix52 (0 : Fin 2)) + (injectiveMoment H (mergeFirst pivotMatrix52 (1 : Fin 2)))) = 0 at hc
  rw [hm0, hm1] at hc
  norm_num [value52, value10, value9, Sparse.eval] at hc ⊢
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical45
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical1447 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1447 = injectiveMoment H node52 := by
  calc
    injectiveMoment H raw1447 = injectiveMoment H raw1447step0 := by
      have heq : raw1447step0 = raw1447.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1447).symm
    injectiveMoment H raw1447step0 = injectiveMoment H raw1447step1 := by
      have heq : raw1447step1 = (fun i j => raw1447step0 (permutation8 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1447step0 permutation8 permutation6
    _ = injectiveMoment H node52 := by rfl

theorem canonical1449 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1449 = injectiveMoment H node35 := by
  rfl

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

theorem canonical2861 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2861 = injectiveMoment H node63 := by
  calc
    injectiveMoment H raw2861 = injectiveMoment H raw2861step0 := by
      have heq : raw2861step0 = raw2861.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2861).symm
    injectiveMoment H raw2861step0 = injectiveMoment H raw2861step1 := by
      have heq : raw2861step1 = (fun i j => raw2861step0 (permutation6 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2861step0 permutation6 permutation5
    _ = injectiveMoment H node63 := by rfl

theorem canonical2862 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2862 = injectiveMoment H node56 := by
  calc
    injectiveMoment H raw2862 = injectiveMoment H raw2862step0 := by
      have heq : raw2862step0 = (fun i j => raw2862 (permutation3 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2862 permutation3 permutation5
    _ = injectiveMoment H node56 := by rfl

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

theorem sound150 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node150 = Sparse.eval value150 (momentVector H) := by
  have heq : pivotMatrix150 = (fun u v => node150 (pivotPermutation150 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node150 = injectiveMoment H pivotMatrix150 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix150 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix150 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix150 (0 : Fin 3)) =
      Sparse.eval value56 (momentVector H) := by
    have heq : mergeFirst pivotMatrix150 (0 : Fin 3) = raw2862 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical2862 hH).trans (sound56 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix150 (1 : Fin 3)) =
      Sparse.eval value35 (momentVector H) := by
    have heq : mergeFirst pivotMatrix150 (1 : Fin 3) = raw1449 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical1449 hH).trans (sound35 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix150 (2 : Fin 3)) =
      Sparse.eval value52 (momentVector H) := by
    have heq : mergeFirst pivotMatrix150 (2 : Fin 3) = raw1447 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical1447 hH).trans (sound52 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node150 + (injectiveMoment H (mergeFirst pivotMatrix150 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix150 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix150 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value150, value35, value52, value56, Sparse.eval] at hc ⊢
  linarith

theorem sound181 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node181 = Sparse.eval value181 (momentVector H) := by
  have heq : pivotMatrix181 = (fun u v => node181 (pivotPermutation181 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node181 = injectiveMoment H pivotMatrix181 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix181 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix181 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix181 (0 : Fin 3)) =
      Sparse.eval value62 (momentVector H) := by
    have heq : mergeFirst pivotMatrix181 (0 : Fin 3) = raw4160 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical4160 hH).trans (sound62 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix181 (1 : Fin 3)) =
      Sparse.eval value56 (momentVector H) := by
    have heq : mergeFirst pivotMatrix181 (1 : Fin 3) = raw2862 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical2862 hH).trans (sound56 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix181 (2 : Fin 3)) =
      Sparse.eval value63 (momentVector H) := by
    have heq : mergeFirst pivotMatrix181 (2 : Fin 3) = raw2861 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical2861 hH).trans (sound63 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node181 + (injectiveMoment H (mergeFirst pivotMatrix181 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix181 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix181 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value181, value56, value62, value63, Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_SingleGroup24
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singlePair404 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node404 node404Labels = Sparse.eval singlePairValue404 (familyPairVector B) := by
  have hp := single_label_three B hB node404
  have hl : node404Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node404 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node404 (EqualityPatterns.family3.label 0) = PairSemantics.raw7980 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node404 PairSemantics.raw7980; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7980 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node404 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value11 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node404 (EqualityPatterns.family3.label 1) = PairSemantics.raw5197 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node404 PairSemantics.raw5197; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5197 hH).trans (PairSemantics.sound11 hH)
  have hm2 : familyPairMoment B (groupedColumns node404 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value65 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node404 (EqualityPatterns.family3.label 2) = PairSemantics.raw7678 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node404 PairSemantics.raw7678; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7678 hH).trans (PairSemantics.sound65 hH)
  have hm3 : familyPairMoment B (groupedColumns node404 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value10 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node404 (EqualityPatterns.family3.label 3) = PairSemantics.raw895 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node404 PairSemantics.raw895; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical895 hH).trans (PairSemantics.sound10 hH)
  have hm4 : familyPairMoment B (groupedColumns node404 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value181 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node404 (EqualityPatterns.family3.label 4) = PairSemantics.raw781 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node404 PairSemantics.raw781; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical781 hH).trans (PairSemantics.sound181 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue404, PairSemantics.value0, PairSemantics.value10, PairSemantics.value11, PairSemantics.value65, PairSemantics.value181, Sparse.eval] at hp ⊢
  linarith only [hp]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_SingleGroup9
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singlePair157 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node157 node157Labels = Sparse.eval singlePairValue157 (familyPairVector B) := by
  have hp := single_label_three B hB node157
  have hl : node157Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node157 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node157 (EqualityPatterns.family3.label 0) = PairSemantics.raw7980 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext
      unfold node157 PairSemantics.raw7980
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7980 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node157 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value11 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node157 (EqualityPatterns.family3.label 1) = PairSemantics.raw5177 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext
      unfold node157 PairSemantics.raw5177
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5177 hH).trans (PairSemantics.sound11 hH)
  have hm2 : familyPairMoment B (groupedColumns node157 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value11 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node157 (EqualityPatterns.family3.label 2) = PairSemantics.raw5197 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext
      unfold node157 PairSemantics.raw5197
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5197 hH).trans (PairSemantics.sound11 hH)
  have hm3 : familyPairMoment B (groupedColumns node157 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value16 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node157 (EqualityPatterns.family3.label 3) = PairSemantics.raw208 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext
      unfold node157 PairSemantics.raw208
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical208 hH).trans (PairSemantics.sound16 hH)
  have hm4 : familyPairMoment B (groupedColumns node157 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value150 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node157 (EqualityPatterns.family3.label 4) = PairSemantics.raw175 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext
      unfold node157 PairSemantics.raw175
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical175 hH).trans (PairSemantics.sound150 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue157, PairSemantics.value0, PairSemantics.value11, PairSemantics.value16, PairSemantics.value150, Sparse.eval] at hp ⊢
  linarith only [hp]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons20
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singleton1301 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node1301 node1301Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node157 node157Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw78 singletonSmall1301
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall1301) = raw78Labels := by decide +kernel
  rw [hl, canonical78 B hB] at h
  have hc0 : mixedMoment B raw78 (Fin.cases (0 : Fin 1) singletonSmall1301) =
      mixedMoment B node157 node157Labels := by
    have ha : raw78 = raw79 := by apply Matrix.ext; unfold raw78 raw79; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall1301 = raw79Labels := by decide +kernel
    rw [ha, hj, canonical79 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

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

theorem singleton2767 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node2767 node2767Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node404 node404Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw270 singletonSmall2767
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall2767) = raw270Labels := by decide +kernel
  rw [hl, canonical270 B hB] at h
  have hc0 : mixedMoment B raw270 (Fin.cases (0 : Fin 1) singletonSmall2767) =
      mixedMoment B node404 node404Labels := by
    have ha : raw270 = raw271 := by apply Matrix.ext; unfold raw270 raw271; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall2767 = raw271Labels := by decide +kernel
    rw [ha, hj, canonical271 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons64
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singleton4143 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4143 node4143Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node571 node571Labels + mixedMoment B node1491 node1491Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw768 singletonSmall4143
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4143) = raw768Labels := by decide +kernel
  rw [hl, canonical768 B hB] at h
  have hc0 : mixedMoment B raw768 (Fin.cases (0 : Fin 2) singletonSmall4143) =
      mixedMoment B node571 node571Labels := by
    have ha : raw768 = raw769 := by apply Matrix.ext; unfold raw768 raw769; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4143 = raw769Labels := by decide +kernel
    rw [ha, hj, canonical769 B hB]
  have hc1 : mixedMoment B raw768 (Fin.cases (1 : Fin 2) singletonSmall4143) =
      mixedMoment B node1491 node1491Labels := by
    have ha : raw768 = raw770 := by apply Matrix.ext; unfold raw768 raw770; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4143 = raw770Labels := by decide +kernel
    rw [ha, hj, canonical770 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4144 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4144 node4144Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node572 node572Labels + mixedMoment B node1492 node1492Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw771 singletonSmall4144
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4144) = raw771Labels := by decide +kernel
  rw [hl, canonical771 B hB] at h
  have hc0 : mixedMoment B raw771 (Fin.cases (0 : Fin 2) singletonSmall4144) =
      mixedMoment B node572 node572Labels := by
    have ha : raw771 = raw772 := by apply Matrix.ext; unfold raw771 raw772; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4144 = raw772Labels := by decide +kernel
    rw [ha, hj, canonical772 B hB]
  have hc1 : mixedMoment B raw771 (Fin.cases (1 : Fin 2) singletonSmall4144) =
      mixedMoment B node1492 node1492Labels := by
    have ha : raw771 = raw773 := by apply Matrix.ext; unfold raw771 raw773; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4144 = raw773Labels := by decide +kernel
    rw [ha, hj, canonical773 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4145 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4145 node4145Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node573 node573Labels + mixedMoment B node1493 node1493Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw774 singletonSmall4145
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4145) = raw774Labels := by decide +kernel
  rw [hl, canonical774 B hB] at h
  have hc0 : mixedMoment B raw774 (Fin.cases (0 : Fin 2) singletonSmall4145) =
      mixedMoment B node573 node573Labels := by
    have ha : raw774 = raw775 := by apply Matrix.ext; unfold raw774 raw775; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4145 = raw775Labels := by decide +kernel
    rw [ha, hj, canonical775 B hB]
  have hc1 : mixedMoment B raw774 (Fin.cases (1 : Fin 2) singletonSmall4145) =
      mixedMoment B node1493 node1493Labels := by
    have ha : raw774 = raw776 := by apply Matrix.ext; unfold raw774 raw776; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4145 = raw776Labels := by decide +kernel
    rw [ha, hj, canonical776 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons65
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singleton4175 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4175 node4175Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node603 node603Labels + mixedMoment B node1517 node1517Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw810 singletonSmall4175
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4175) = raw810Labels := by decide +kernel
  rw [hl, canonical810 B hB] at h
  have hc0 : mixedMoment B raw810 (Fin.cases (0 : Fin 2) singletonSmall4175) =
      mixedMoment B node603 node603Labels := by
    have ha : raw810 = raw811 := by apply Matrix.ext; unfold raw810 raw811; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4175 = raw811Labels := by decide +kernel
    rw [ha, hj, canonical811 B hB]
  have hc1 : mixedMoment B raw810 (Fin.cases (1 : Fin 2) singletonSmall4175) =
      mixedMoment B node1517 node1517Labels := by
    have ha : raw810 = raw812 := by apply Matrix.ext; unfold raw810 raw812; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4175 = raw812Labels := by decide +kernel
    rw [ha, hj, canonical812 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons70
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singleton4516 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4516 node4516Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1100 node1100Labels + mixedMoment B node3234 node3234Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1320 singletonSmall4516
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4516) = raw1320Labels := by decide +kernel
  rw [hl, canonical1320 B hB] at h
  have hc0 : mixedMoment B raw1320 (Fin.cases (0 : Fin 2) singletonSmall4516) =
      mixedMoment B node1100 node1100Labels := by
    have ha : raw1320 = raw1321 := by apply Matrix.ext; unfold raw1320 raw1321; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4516 = raw1321Labels := by decide +kernel
    rw [ha, hj, canonical1321 B hB]
  have hc1 : mixedMoment B raw1320 (Fin.cases (1 : Fin 2) singletonSmall4516) =
      mixedMoment B node3234 node3234Labels := by
    have ha : raw1320 = raw1322 := by apply Matrix.ext; unfold raw1320 raw1322; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4516 = raw1322Labels := by decide +kernel
    rw [ha, hj, canonical1322 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4517 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4517 node4517Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1101 node1101Labels + mixedMoment B node3235 node3235Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1323 singletonSmall4517
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4517) = raw1323Labels := by decide +kernel
  rw [hl, canonical1323 B hB] at h
  have hc0 : mixedMoment B raw1323 (Fin.cases (0 : Fin 2) singletonSmall4517) =
      mixedMoment B node1101 node1101Labels := by
    have ha : raw1323 = raw1324 := by apply Matrix.ext; unfold raw1323 raw1324; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4517 = raw1324Labels := by decide +kernel
    rw [ha, hj, canonical1324 B hB]
  have hc1 : mixedMoment B raw1323 (Fin.cases (1 : Fin 2) singletonSmall4517) =
      mixedMoment B node3235 node3235Labels := by
    have ha : raw1323 = raw1325 := by apply Matrix.ext; unfold raw1323 raw1325; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4517 = raw1325Labels := by decide +kernel
    rw [ha, hj, canonical1325 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4518 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4518 node4518Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1102 node1102Labels + mixedMoment B node3236 node3236Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1326 singletonSmall4518
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4518) = raw1326Labels := by decide +kernel
  rw [hl, canonical1326 B hB] at h
  have hc0 : mixedMoment B raw1326 (Fin.cases (0 : Fin 2) singletonSmall4518) =
      mixedMoment B node1102 node1102Labels := by
    have ha : raw1326 = raw1327 := by apply Matrix.ext; unfold raw1326 raw1327; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4518 = raw1327Labels := by decide +kernel
    rw [ha, hj, canonical1327 B hB]
  have hc1 : mixedMoment B raw1326 (Fin.cases (1 : Fin 2) singletonSmall4518) =
      mixedMoment B node3236 node3236Labels := by
    have ha : raw1326 = raw1328 := by apply Matrix.ext; unfold raw1326 raw1328; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4518 = raw1328Labels := by decide +kernel
    rw [ha, hj, canonical1328 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4523 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4523 node4523Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1107 node1107Labels + mixedMoment B node3250 node3250Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1341 singletonSmall4523
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4523) = raw1341Labels := by decide +kernel
  rw [hl, canonical1341 B hB] at h
  have hc0 : mixedMoment B raw1341 (Fin.cases (0 : Fin 2) singletonSmall4523) =
      mixedMoment B node1107 node1107Labels := by
    have ha : raw1341 = raw1342 := by apply Matrix.ext; unfold raw1341 raw1342; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4523 = raw1342Labels := by decide +kernel
    rw [ha, hj, canonical1342 B hB]
  have hc1 : mixedMoment B raw1341 (Fin.cases (1 : Fin 2) singletonSmall4523) =
      mixedMoment B node3250 node3250Labels := by
    have ha : raw1341 = raw1343 := by apply Matrix.ext; unfold raw1341 raw1343; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4523 = raw1343Labels := by decide +kernel
    rw [ha, hj, canonical1343 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4524 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4524 node4524Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1108 node1108Labels + mixedMoment B node3251 node3251Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1344 singletonSmall4524
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4524) = raw1344Labels := by decide +kernel
  rw [hl, canonical1344 B hB] at h
  have hc0 : mixedMoment B raw1344 (Fin.cases (0 : Fin 2) singletonSmall4524) =
      mixedMoment B node1108 node1108Labels := by
    have ha : raw1344 = raw1345 := by apply Matrix.ext; unfold raw1344 raw1345; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4524 = raw1345Labels := by decide +kernel
    rw [ha, hj, canonical1345 B hB]
  have hc1 : mixedMoment B raw1344 (Fin.cases (1 : Fin 2) singletonSmall4524) =
      mixedMoment B node3251 node3251Labels := by
    have ha : raw1344 = raw1346 := by apply Matrix.ext; unfold raw1344 raw1346; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4524 = raw1346Labels := by decide +kernel
    rw [ha, hj, canonical1346 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons71
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singleton4544 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4544 node4544Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1129 node1129Labels + mixedMoment B node3263 node3263Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1368 singletonSmall4544
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4544) = raw1368Labels := by decide +kernel
  rw [hl, canonical1368 B hB] at h
  have hc0 : mixedMoment B raw1368 (Fin.cases (0 : Fin 2) singletonSmall4544) =
      mixedMoment B node1129 node1129Labels := by
    have ha : raw1368 = raw1369 := by apply Matrix.ext; unfold raw1368 raw1369; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4544 = raw1369Labels := by decide +kernel
    rw [ha, hj, canonical1369 B hB]
  have hc1 : mixedMoment B raw1368 (Fin.cases (1 : Fin 2) singletonSmall4544) =
      mixedMoment B node3263 node3263Labels := by
    have ha : raw1368 = raw1370 := by apply Matrix.ext; unfold raw1368 raw1370; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4544 = raw1370Labels := by decide +kernel
    rw [ha, hj, canonical1370 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4601 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4601 node4601Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1235 node1235Labels + mixedMoment B node3292 node3292Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1422 singletonSmall4601
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4601) = raw1422Labels := by decide +kernel
  rw [hl, canonical1422 B hB] at h
  have hc0 : mixedMoment B raw1422 (Fin.cases (0 : Fin 2) singletonSmall4601) =
      mixedMoment B node1235 node1235Labels := by
    have ha : raw1422 = raw1423 := by apply Matrix.ext; unfold raw1422 raw1423; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4601 = raw1423Labels := by decide +kernel
    rw [ha, hj, canonical1423 B hB]
  have hc1 : mixedMoment B raw1422 (Fin.cases (1 : Fin 2) singletonSmall4601) =
      mixedMoment B node3292 node3292Labels := by
    have ha : raw1422 = raw1424 := by apply Matrix.ext; unfold raw1422 raw1424; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4601 = raw1424Labels := by decide +kernel
    rw [ha, hj, canonical1424 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4602 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4602 node4602Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1236 node1236Labels + mixedMoment B node3293 node3293Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1425 singletonSmall4602
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4602) = raw1425Labels := by decide +kernel
  rw [hl, canonical1425 B hB] at h
  have hc0 : mixedMoment B raw1425 (Fin.cases (0 : Fin 2) singletonSmall4602) =
      mixedMoment B node1236 node1236Labels := by
    have ha : raw1425 = raw1426 := by apply Matrix.ext; unfold raw1425 raw1426; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4602 = raw1426Labels := by decide +kernel
    rw [ha, hj, canonical1426 B hB]
  have hc1 : mixedMoment B raw1425 (Fin.cases (1 : Fin 2) singletonSmall4602) =
      mixedMoment B node3293 node3293Labels := by
    have ha : raw1425 = raw1427 := by apply Matrix.ext; unfold raw1425 raw1427; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4602 = raw1427Labels := by decide +kernel
    rw [ha, hj, canonical1427 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4606 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4606 node4606Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1240 node1240Labels + mixedMoment B node3299 node3299Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1431 singletonSmall4606
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4606) = raw1431Labels := by decide +kernel
  rw [hl, canonical1431 B hB] at h
  have hc0 : mixedMoment B raw1431 (Fin.cases (0 : Fin 2) singletonSmall4606) =
      mixedMoment B node1240 node1240Labels := by
    have ha : raw1431 = raw1432 := by apply Matrix.ext; unfold raw1431 raw1432; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4606 = raw1432Labels := by decide +kernel
    rw [ha, hj, canonical1432 B hB]
  have hc1 : mixedMoment B raw1431 (Fin.cases (1 : Fin 2) singletonSmall4606) =
      mixedMoment B node3299 node3299Labels := by
    have ha : raw1431 = raw1433 := by apply Matrix.ext; unfold raw1431 raw1433; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4606 = raw1433Labels := by decide +kernel
    rw [ha, hj, canonical1433 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons72
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singleton4608 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4608 node4608Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1242 node1242Labels + mixedMoment B node3300 node3300Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1434 singletonSmall4608
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4608) = raw1434Labels := by decide +kernel
  rw [hl, canonical1434 B hB] at h
  have hc0 : mixedMoment B raw1434 (Fin.cases (0 : Fin 2) singletonSmall4608) =
      mixedMoment B node1242 node1242Labels := by
    have ha : raw1434 = raw1435 := by apply Matrix.ext; unfold raw1434 raw1435; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4608 = raw1435Labels := by decide +kernel
    rw [ha, hj, canonical1435 B hB]
  have hc1 : mixedMoment B raw1434 (Fin.cases (1 : Fin 2) singletonSmall4608) =
      mixedMoment B node3300 node3300Labels := by
    have ha : raw1434 = raw1436 := by apply Matrix.ext; unfold raw1434 raw1436; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4608 = raw1436Labels := by decide +kernel
    rw [ha, hj, canonical1436 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4612 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4612 node4612Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1246 node1246Labels + mixedMoment B node3301 node3301Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1437 singletonSmall4612
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4612) = raw1437Labels := by decide +kernel
  rw [hl, canonical1437 B hB] at h
  have hc0 : mixedMoment B raw1437 (Fin.cases (0 : Fin 2) singletonSmall4612) =
      mixedMoment B node1246 node1246Labels := by
    have ha : raw1437 = raw1438 := by apply Matrix.ext; unfold raw1437 raw1438; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4612 = raw1438Labels := by decide +kernel
    rw [ha, hj, canonical1438 B hB]
  have hc1 : mixedMoment B raw1437 (Fin.cases (1 : Fin 2) singletonSmall4612) =
      mixedMoment B node3301 node3301Labels := by
    have ha : raw1437 = raw1439 := by apply Matrix.ext; unfold raw1437 raw1439; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4612 = raw1439Labels := by decide +kernel
    rw [ha, hj, canonical1439 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4622 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4622 node4622Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1299 node1299Labels + mixedMoment B node3307 node3307Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1449 singletonSmall4622
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4622) = raw1449Labels := by decide +kernel
  rw [hl, canonical1449 B hB] at h
  have hc0 : mixedMoment B raw1449 (Fin.cases (0 : Fin 2) singletonSmall4622) =
      mixedMoment B node1299 node1299Labels := by
    have ha : raw1449 = raw1450 := by apply Matrix.ext; unfold raw1449 raw1450; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4622 = raw1450Labels := by decide +kernel
    rw [ha, hj, canonical1450 B hB]
  have hc1 : mixedMoment B raw1449 (Fin.cases (1 : Fin 2) singletonSmall4622) =
      mixedMoment B node3307 node3307Labels := by
    have ha : raw1449 = raw1451 := by apply Matrix.ext; unfold raw1449 raw1451; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4622 = raw1451Labels := by decide +kernel
    rw [ha, hj, canonical1451 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4624 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4624 node4624Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1301 node1301Labels + mixedMoment B node3309 node3309Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1455 singletonSmall4624
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4624) = raw1455Labels := by decide +kernel
  rw [hl, canonical1455 B hB] at h
  have hc0 : mixedMoment B raw1455 (Fin.cases (0 : Fin 2) singletonSmall4624) =
      mixedMoment B node1301 node1301Labels := by
    have ha : raw1455 = raw1456 := by apply Matrix.ext; unfold raw1455 raw1456; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4624 = raw1456Labels := by decide +kernel
    rw [ha, hj, canonical1456 B hB]
  have hc1 : mixedMoment B raw1455 (Fin.cases (1 : Fin 2) singletonSmall4624) =
      mixedMoment B node3309 node3309Labels := by
    have ha : raw1455 = raw1457 := by apply Matrix.ext; unfold raw1455 raw1457; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4624 = raw1457Labels := by decide +kernel
    rw [ha, hj, canonical1457 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons81
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singleton5203 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5203 node5203Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2884 node2884Labels + mixedMoment B node3621 node3621Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2229 singletonSmall5203
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5203) = raw2229Labels := by decide +kernel
  rw [hl, canonical2229 B hB] at h
  have hc0 : mixedMoment B raw2229 (Fin.cases (0 : Fin 2) singletonSmall5203) =
      mixedMoment B node2884 node2884Labels := by
    have ha : raw2229 = raw2230 := by apply Matrix.ext; unfold raw2229 raw2230; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5203 = raw2230Labels := by decide +kernel
    rw [ha, hj, canonical2230 B hB]
  have hc1 : mixedMoment B raw2229 (Fin.cases (1 : Fin 2) singletonSmall5203) =
      mixedMoment B node3621 node3621Labels := by
    have ha : raw2229 = raw2231 := by apply Matrix.ext; unfold raw2229 raw2231; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5203 = raw2231Labels := by decide +kernel
    rw [ha, hj, canonical2231 B hB]
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

theorem singleton5293 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5293 node5293Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2767 node2767Labels + mixedMoment B node3627 node3627Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2301 singletonSmall5293
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5293) = raw2301Labels := by decide +kernel
  rw [hl, canonical2301 B hB] at h
  have hc0 : mixedMoment B raw2301 (Fin.cases (0 : Fin 2) singletonSmall5293) =
      mixedMoment B node2767 node2767Labels := by
    have ha : raw2301 = raw2302 := by apply Matrix.ext; unfold raw2301 raw2302; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5293 = raw2302Labels := by decide +kernel
    rw [ha, hj, canonical2302 B hB]
  have hc1 : mixedMoment B raw2301 (Fin.cases (1 : Fin 2) singletonSmall5293) =
      mixedMoment B node3627 node3627Labels := by
    have ha : raw2301 = raw2303 := by apply Matrix.ext; unfold raw2301 raw2303; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5293 = raw2303Labels := by decide +kernel
    rw [ha, hj, canonical2303 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound17
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound1100 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1100 node1100Labels = Sparse.eval nodeValue1100 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1100) = mixedMoment B node1100 node1100Labels := rfl
  simpa [nodeValue1100, Sparse.eval] using hc.symm

theorem sound1101 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1101 node1101Labels = Sparse.eval nodeValue1101 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1101) = mixedMoment B node1101 node1101Labels := rfl
  simpa [nodeValue1101, Sparse.eval] using hc.symm

theorem sound1102 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1102 node1102Labels = Sparse.eval nodeValue1102 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1102) = mixedMoment B node1102 node1102Labels := rfl
  simpa [nodeValue1102, Sparse.eval] using hc.symm

theorem sound1107 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1107 node1107Labels = Sparse.eval nodeValue1107 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1107) = mixedMoment B node1107 node1107Labels := rfl
  simpa [nodeValue1107, Sparse.eval] using hc.symm

theorem sound1108 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1108 node1108Labels = Sparse.eval nodeValue1108 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1108) = mixedMoment B node1108 node1108Labels := rfl
  simpa [nodeValue1108, Sparse.eval] using hc.symm

theorem sound1129 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1129 node1129Labels = Sparse.eval nodeValue1129 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1129) = mixedMoment B node1129 node1129Labels := rfl
  simpa [nodeValue1129, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound157 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node157 node157Labels = Sparse.eval nodeValue157 (mixedVector B) := by
  calc
    _ = Sparse.eval singlePairValue157 (familyPairVector B) := singlePair157 B _hB
    _ = _ := by
      norm_num [singlePairValue157, nodeValue157, Sparse.eval, mixedVector]
      ring

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound19
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound1235 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1235 node1235Labels = Sparse.eval nodeValue1235 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1235) = mixedMoment B node1235 node1235Labels := rfl
  simpa [nodeValue1235, Sparse.eval] using hc.symm

theorem sound1236 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1236 node1236Labels = Sparse.eval nodeValue1236 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1236) = mixedMoment B node1236 node1236Labels := rfl
  simpa [nodeValue1236, Sparse.eval] using hc.symm

theorem sound1240 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1240 node1240Labels = Sparse.eval nodeValue1240 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1240) = mixedMoment B node1240 node1240Labels := rfl
  simpa [nodeValue1240, Sparse.eval] using hc.symm

theorem sound1242 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1242 node1242Labels = Sparse.eval nodeValue1242 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1242) = mixedMoment B node1242 node1242Labels := rfl
  simpa [nodeValue1242, Sparse.eval] using hc.symm

theorem sound1246 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1246 node1246Labels = Sparse.eval nodeValue1246 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1246) = mixedMoment B node1246 node1246Labels := rfl
  simpa [nodeValue1246, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound20
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound1301 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1301 node1301Labels = Sparse.eval nodeValue1301 (mixedVector B) := by
  have h := singleton1301 B _hB
  rw [sound157 B _hB _hF] at h
  norm_num [nodeValue1301, nodeValue157, Sparse.eval] at h ⊢
  linarith only [h]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound23
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound1491 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1491 node1491Labels = Sparse.eval nodeValue1491 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1491) = mixedMoment B node1491 node1491Labels := rfl
  simpa [nodeValue1491, Sparse.eval] using hc.symm

theorem sound1492 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1492 node1492Labels = Sparse.eval nodeValue1492 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1492) = mixedMoment B node1492 node1492Labels := rfl
  simpa [nodeValue1492, Sparse.eval] using hc.symm

theorem sound1493 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1493 node1493Labels = Sparse.eval nodeValue1493 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1493) = mixedMoment B node1493 node1493Labels := rfl
  simpa [nodeValue1493, Sparse.eval] using hc.symm

theorem sound1517 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1517 node1517Labels = Sparse.eval nodeValue1517 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1517) = mixedMoment B node1517 node1517Labels := rfl
  simpa [nodeValue1517, Sparse.eval] using hc.symm

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

theorem sound404 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node404 node404Labels = Sparse.eval nodeValue404 (mixedVector B) := by
  calc
    _ = Sparse.eval singlePairValue404 (familyPairVector B) := singlePair404 B _hB
    _ = _ := by
      norm_num [singlePairValue404, nodeValue404, Sparse.eval, mixedVector]
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

theorem sound2767 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2767 node2767Labels = Sparse.eval nodeValue2767 (mixedVector B) := by
  have h := singleton2767 B _hB
  rw [sound404 B _hB _hF] at h
  norm_num [nodeValue2767, nodeValue404, Sparse.eval] at h ⊢
  linarith only [h]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound45
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound2884 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2884 node2884Labels = Sparse.eval nodeValue2884 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2884) = mixedMoment B node2884 node2884Labels := rfl
  simpa [nodeValue2884, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound50
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound3234 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3234 node3234Labels = Sparse.eval nodeValue3234 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3234) = mixedMoment B node3234 node3234Labels := rfl
  simpa [nodeValue3234, Sparse.eval] using hc.symm

theorem sound3235 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3235 node3235Labels = Sparse.eval nodeValue3235 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3235) = mixedMoment B node3235 node3235Labels := rfl
  simpa [nodeValue3235, Sparse.eval] using hc.symm

theorem sound3236 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3236 node3236Labels = Sparse.eval nodeValue3236 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3236) = mixedMoment B node3236 node3236Labels := rfl
  simpa [nodeValue3236, Sparse.eval] using hc.symm

theorem sound3250 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3250 node3250Labels = Sparse.eval nodeValue3250 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3250) = mixedMoment B node3250 node3250Labels := rfl
  simpa [nodeValue3250, Sparse.eval] using hc.symm

theorem sound3251 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3251 node3251Labels = Sparse.eval nodeValue3251 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3251) = mixedMoment B node3251 node3251Labels := rfl
  simpa [nodeValue3251, Sparse.eval] using hc.symm

theorem sound3263 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3263 node3263Labels = Sparse.eval nodeValue3263 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3263) = mixedMoment B node3263 node3263Labels := rfl
  simpa [nodeValue3263, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound51
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound3292 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3292 node3292Labels = Sparse.eval nodeValue3292 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3292) = mixedMoment B node3292 node3292Labels := rfl
  simpa [nodeValue3292, Sparse.eval] using hc.symm

theorem sound3293 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3293 node3293Labels = Sparse.eval nodeValue3293 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3293) = mixedMoment B node3293 node3293Labels := rfl
  simpa [nodeValue3293, Sparse.eval] using hc.symm

theorem sound3299 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3299 node3299Labels = Sparse.eval nodeValue3299 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3299) = mixedMoment B node3299 node3299Labels := rfl
  simpa [nodeValue3299, Sparse.eval] using hc.symm

theorem sound3300 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3300 node3300Labels = Sparse.eval nodeValue3300 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3300) = mixedMoment B node3300 node3300Labels := rfl
  simpa [nodeValue3300, Sparse.eval] using hc.symm

theorem sound3301 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3301 node3301Labels = Sparse.eval nodeValue3301 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3301) = mixedMoment B node3301 node3301Labels := rfl
  simpa [nodeValue3301, Sparse.eval] using hc.symm

theorem sound3307 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3307 node3307Labels = Sparse.eval nodeValue3307 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3307) = mixedMoment B node3307 node3307Labels := rfl
  simpa [nodeValue3307, Sparse.eval] using hc.symm

theorem sound3309 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3309 node3309Labels = Sparse.eval nodeValue3309 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3309) = mixedMoment B node3309 node3309Labels := rfl
  simpa [nodeValue3309, Sparse.eval] using hc.symm

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

theorem sound3621 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3621 node3621Labels = Sparse.eval nodeValue3621 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3621) = mixedMoment B node3621 node3621Labels := rfl
  simpa [nodeValue3621, Sparse.eval] using hc.symm

theorem sound3627 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3627 node3627Labels = Sparse.eval nodeValue3627 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3627) = mixedMoment B node3627 node3627Labels := rfl
  simpa [nodeValue3627, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound8
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound571 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node571 node571Labels = Sparse.eval nodeValue571 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 571) = mixedMoment B node571 node571Labels := rfl
  simpa [nodeValue571, Sparse.eval] using hc.symm

theorem sound572 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node572 node572Labels = Sparse.eval nodeValue572 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 572) = mixedMoment B node572 node572Labels := rfl
  simpa [nodeValue572, Sparse.eval] using hc.symm

theorem sound573 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node573 node573Labels = Sparse.eval nodeValue573 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 573) = mixedMoment B node573 node573Labels := rfl
  simpa [nodeValue573, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound9
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound603 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node603 node603Labels = Sparse.eval nodeValue603 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 603) = mixedMoment B node603 node603Labels := rfl
  simpa [nodeValue603, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound64
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound4143 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4143 node4143Labels = Sparse.eval nodeValue4143 (mixedVector B) := by
  have h := singleton4143 B _hB
  rw [sound571 B _hB _hF, sound1491 B _hB _hF] at h
  norm_num [nodeValue4143, nodeValue571, nodeValue1491, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4144 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4144 node4144Labels = Sparse.eval nodeValue4144 (mixedVector B) := by
  have h := singleton4144 B _hB
  rw [sound572 B _hB _hF, sound1492 B _hB _hF] at h
  norm_num [nodeValue4144, nodeValue572, nodeValue1492, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4145 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4145 node4145Labels = Sparse.eval nodeValue4145 (mixedVector B) := by
  have h := singleton4145 B _hB
  rw [sound573 B _hB _hF, sound1493 B _hB _hF] at h
  norm_num [nodeValue4145, nodeValue573, nodeValue1493, Sparse.eval] at h ⊢
  linarith only [h]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound65
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound4175 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4175 node4175Labels = Sparse.eval nodeValue4175 (mixedVector B) := by
  have h := singleton4175 B _hB
  rw [sound603 B _hB _hF, sound1517 B _hB _hF] at h
  norm_num [nodeValue4175, nodeValue603, nodeValue1517, Sparse.eval] at h ⊢
  linarith only [h]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound70
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound4516 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4516 node4516Labels = Sparse.eval nodeValue4516 (mixedVector B) := by
  have h := singleton4516 B _hB
  rw [sound1100 B _hB _hF, sound3234 B _hB _hF] at h
  norm_num [nodeValue4516, nodeValue1100, nodeValue3234, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4517 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4517 node4517Labels = Sparse.eval nodeValue4517 (mixedVector B) := by
  have h := singleton4517 B _hB
  rw [sound1101 B _hB _hF, sound3235 B _hB _hF] at h
  norm_num [nodeValue4517, nodeValue1101, nodeValue3235, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4518 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4518 node4518Labels = Sparse.eval nodeValue4518 (mixedVector B) := by
  have h := singleton4518 B _hB
  rw [sound1102 B _hB _hF, sound3236 B _hB _hF] at h
  norm_num [nodeValue4518, nodeValue1102, nodeValue3236, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4523 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4523 node4523Labels = Sparse.eval nodeValue4523 (mixedVector B) := by
  have h := singleton4523 B _hB
  rw [sound1107 B _hB _hF, sound3250 B _hB _hF] at h
  norm_num [nodeValue4523, nodeValue1107, nodeValue3250, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4524 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4524 node4524Labels = Sparse.eval nodeValue4524 (mixedVector B) := by
  have h := singleton4524 B _hB
  rw [sound1108 B _hB _hF, sound3251 B _hB _hF] at h
  norm_num [nodeValue4524, nodeValue1108, nodeValue3251, Sparse.eval] at h ⊢
  linarith only [h]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound71
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound4544 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4544 node4544Labels = Sparse.eval nodeValue4544 (mixedVector B) := by
  have h := singleton4544 B _hB
  rw [sound1129 B _hB _hF, sound3263 B _hB _hF] at h
  norm_num [nodeValue4544, nodeValue1129, nodeValue3263, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4601 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4601 node4601Labels = Sparse.eval nodeValue4601 (mixedVector B) := by
  have h := singleton4601 B _hB
  rw [sound1235 B _hB _hF, sound3292 B _hB _hF] at h
  norm_num [nodeValue4601, nodeValue1235, nodeValue3292, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4602 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4602 node4602Labels = Sparse.eval nodeValue4602 (mixedVector B) := by
  have h := singleton4602 B _hB
  rw [sound1236 B _hB _hF, sound3293 B _hB _hF] at h
  norm_num [nodeValue4602, nodeValue1236, nodeValue3293, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4606 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4606 node4606Labels = Sparse.eval nodeValue4606 (mixedVector B) := by
  have h := singleton4606 B _hB
  rw [sound1240 B _hB _hF, sound3299 B _hB _hF] at h
  norm_num [nodeValue4606, nodeValue1240, nodeValue3299, Sparse.eval] at h ⊢
  linarith only [h]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound72
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound4608 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4608 node4608Labels = Sparse.eval nodeValue4608 (mixedVector B) := by
  have h := singleton4608 B _hB
  rw [sound1242 B _hB _hF, sound3300 B _hB _hF] at h
  norm_num [nodeValue4608, nodeValue1242, nodeValue3300, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4612 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4612 node4612Labels = Sparse.eval nodeValue4612 (mixedVector B) := by
  have h := singleton4612 B _hB
  rw [sound1246 B _hB _hF, sound3301 B _hB _hF] at h
  norm_num [nodeValue4612, nodeValue1246, nodeValue3301, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4622 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4622 node4622Labels = Sparse.eval nodeValue4622 (mixedVector B) := by
  have h := singleton4622 B _hB
  rw [sound1299_e B _hB _hF, sound3307 B _hB _hF] at h
  norm_num [nodeValue4622, nodeValue1299, nodeValue3307, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4624 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4624 node4624Labels = Sparse.eval nodeValue4624 (mixedVector B) := by
  have h := singleton4624 B _hB
  rw [sound1301 B _hB _hF, sound3309 B _hB _hF] at h
  norm_num [nodeValue4624, nodeValue1301, nodeValue3309, Sparse.eval] at h ⊢
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

theorem zero5148 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node5148 node5148Labels = 0 := by
  exact mixedMoment_alpha B hF node5148 node5148Labels 1 permutation152
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

theorem sound5148 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5148 node5148Labels = Sparse.eval nodeValue5148 (mixedVector B) := by
  simpa only [nodeValue5148, Sparse.eval_nil] using zero5148 B _hB _hF

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound81
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound5203 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5203 node5203Labels = Sparse.eval nodeValue5203 (mixedVector B) := by
  have h := singleton5203 B _hB
  rw [sound2884 B _hB _hF, sound3621 B _hB _hF] at h
  norm_num [nodeValue5203, nodeValue2884, nodeValue3621, Sparse.eval] at h ⊢
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

theorem sound5293 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5293 node5293Labels = Sparse.eval nodeValue5293 (mixedVector B) := by
  have h := singleton5293 B _hB
  rw [sound2767 B _hB _hF, sound3627 B _hB _hF] at h
  norm_num [nodeValue5293, nodeValue2767, nodeValue3627, Sparse.eval] at h ⊢
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources52
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sourceEq1674 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1674 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1674 + difference 0 1) (sourceB1674 + difference 1 0) sourceC1674) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5148) := by
    have ha : (tripleCharges (sourceA1674 + difference 0 1) (sourceB1674 + difference 1 0) sourceC1674) = raw12557 := by
      apply Matrix.ext; unfold tripleCharges sourceA1674 sourceB1674 sourceC1674 difference raw12557; decide +kernel
    rw [ha]
    exact (canonical12557 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1674 + difference 0 2) (sourceB1674 + difference 2 0) sourceC1674) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5203) := by
    have ha : (tripleCharges (sourceA1674 + difference 0 2) (sourceB1674 + difference 2 0) sourceC1674) = raw12558 := by
      apply Matrix.ext; unfold tripleCharges sourceA1674 sourceB1674 sourceC1674 difference raw12558; decide +kernel
    rw [ha]
    exact (canonical12558 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1674 + difference 0 3) (sourceB1674 + difference 3 0) sourceC1674) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5293) := by
    have ha : (tripleCharges (sourceA1674 + difference 0 3) (sourceB1674 + difference 3 0) sourceC1674) = raw12559 := by
      apply Matrix.ext; unfold tripleCharges sourceA1674 sourceB1674 sourceC1674 difference raw12559; decide +kernel
    rw [ha]
    exact (canonical12559 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1674 + difference 0 4) (sourceB1674 + difference 4 0) sourceC1674) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5293) := by
    have ha : (tripleCharges (sourceA1674 + difference 0 4) (sourceB1674 + difference 4 0) sourceC1674) = raw12560 := by
      apply Matrix.ext; unfold tripleCharges sourceA1674 sourceB1674 sourceC1674 difference raw12560; decide +kernel
    rw [ha]
    exact (canonical12560 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1674 + difference 0 5) (sourceB1674 + difference 5 0) sourceC1674) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5292) := by
    have ha : (tripleCharges (sourceA1674 + difference 0 5) (sourceB1674 + difference 5 0) sourceC1674) = raw18364 := by
      apply Matrix.ext; unfold tripleCharges sourceA1674 sourceB1674 sourceC1674 difference raw18364; decide +kernel
    rw [ha]
    exact (canonical18364 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1674 + difference 1 0) (sourceB1674 + difference 0 1) sourceC1674) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4143) := by
    have ha : (tripleCharges (sourceA1674 + difference 1 0) (sourceB1674 + difference 0 1) sourceC1674) = raw24558 := by
      apply Matrix.ext; unfold tripleCharges sourceA1674 sourceB1674 sourceC1674 difference raw24558; decide +kernel
    rw [ha]
    exact (canonical24558 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1674 + difference 1 2) (sourceB1674 + difference 2 1) sourceC1674) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4516) := by
    have ha : (tripleCharges (sourceA1674 + difference 1 2) (sourceB1674 + difference 2 1) sourceC1674) = raw24559 := by
      apply Matrix.ext; unfold tripleCharges sourceA1674 sourceB1674 sourceC1674 difference raw24559; decide +kernel
    rw [ha]
    exact (canonical24559 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1674 + difference 1 3) (sourceB1674 + difference 3 1) sourceC1674) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4606) := by
    have ha : (tripleCharges (sourceA1674 + difference 1 3) (sourceB1674 + difference 3 1) sourceC1674) = raw24560 := by
      apply Matrix.ext; unfold tripleCharges sourceA1674 sourceB1674 sourceC1674 difference raw24560; decide +kernel
    rw [ha]
    exact (canonical24560 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1674 + difference 1 4) (sourceB1674 + difference 4 1) sourceC1674) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4606) := by
    have ha : (tripleCharges (sourceA1674 + difference 1 4) (sourceB1674 + difference 4 1) sourceC1674) = raw24561 := by
      apply Matrix.ext; unfold tripleCharges sourceA1674 sourceB1674 sourceC1674 difference raw24561; decide +kernel
    rw [ha]
    exact (canonical24561 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1674 + difference 1 5) (sourceB1674 + difference 5 1) sourceC1674) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4601) := by
    have ha : (tripleCharges (sourceA1674 + difference 1 5) (sourceB1674 + difference 5 1) sourceC1674) = raw12536 := by
      apply Matrix.ext; unfold tripleCharges sourceA1674 sourceB1674 sourceC1674 difference raw12536; decide +kernel
    rw [ha]
    exact (canonical12536 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1674 + difference 2 0) (sourceB1674 + difference 0 2) sourceC1674) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4175) := by
    have ha : (tripleCharges (sourceA1674 + difference 2 0) (sourceB1674 + difference 0 2) sourceC1674) = raw24562 := by
      apply Matrix.ext; unfold tripleCharges sourceA1674 sourceB1674 sourceC1674 difference raw24562; decide +kernel
    rw [ha]
    exact (canonical24562 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1674 + difference 2 1) (sourceB1674 + difference 1 2) sourceC1674) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4544) := by
    have ha : (tripleCharges (sourceA1674 + difference 2 1) (sourceB1674 + difference 1 2) sourceC1674) = raw24563 := by
      apply Matrix.ext; unfold tripleCharges sourceA1674 sourceB1674 sourceC1674 difference raw24563; decide +kernel
    rw [ha]
    exact (canonical24563 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1674 + difference 2 3) (sourceB1674 + difference 3 2) sourceC1674) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4624) := by
    have ha : (tripleCharges (sourceA1674 + difference 2 3) (sourceB1674 + difference 3 2) sourceC1674) = raw24564 := by
      apply Matrix.ext; unfold tripleCharges sourceA1674 sourceB1674 sourceC1674 difference raw24564; decide +kernel
    rw [ha]
    exact (canonical24564 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1674 + difference 2 4) (sourceB1674 + difference 4 2) sourceC1674) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4624) := by
    have ha : (tripleCharges (sourceA1674 + difference 2 4) (sourceB1674 + difference 4 2) sourceC1674) = raw24565 := by
      apply Matrix.ext; unfold tripleCharges sourceA1674 sourceB1674 sourceC1674 difference raw24565; decide +kernel
    rw [ha]
    exact (canonical24565 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1674 + difference 2 5) (sourceB1674 + difference 5 2) sourceC1674) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4622) := by
    have ha : (tripleCharges (sourceA1674 + difference 2 5) (sourceB1674 + difference 5 2) sourceC1674) = raw12541 := by
      apply Matrix.ext; unfold tripleCharges sourceA1674 sourceB1674 sourceC1674 difference raw12541; decide +kernel
    rw [ha]
    exact (canonical12541 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1674 + difference 3 0) (sourceB1674 + difference 0 3) sourceC1674) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4145) := by
    have ha : (tripleCharges (sourceA1674 + difference 3 0) (sourceB1674 + difference 0 3) sourceC1674) = raw24566 := by
      apply Matrix.ext; unfold tripleCharges sourceA1674 sourceB1674 sourceC1674 difference raw24566; decide +kernel
    rw [ha]
    exact (canonical24566 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1674 + difference 3 1) (sourceB1674 + difference 1 3) sourceC1674) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4524) := by
    have ha : (tripleCharges (sourceA1674 + difference 3 1) (sourceB1674 + difference 1 3) sourceC1674) = raw24567 := by
      apply Matrix.ext; unfold tripleCharges sourceA1674 sourceB1674 sourceC1674 difference raw24567; decide +kernel
    rw [ha]
    exact (canonical24567 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1674 + difference 3 2) (sourceB1674 + difference 2 3) sourceC1674) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4518) := by
    have ha : (tripleCharges (sourceA1674 + difference 3 2) (sourceB1674 + difference 2 3) sourceC1674) = raw24568 := by
      apply Matrix.ext; unfold tripleCharges sourceA1674 sourceB1674 sourceC1674 difference raw24568; decide +kernel
    rw [ha]
    exact (canonical24568 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1674 + difference 3 4) (sourceB1674 + difference 4 3) sourceC1674) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4612) := by
    have ha : (tripleCharges (sourceA1674 + difference 3 4) (sourceB1674 + difference 4 3) sourceC1674) = raw24569 := by
      apply Matrix.ext; unfold tripleCharges sourceA1674 sourceB1674 sourceC1674 difference raw24569; decide +kernel
    rw [ha]
    exact (canonical24569 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1674 + difference 3 5) (sourceB1674 + difference 5 3) sourceC1674) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4602) := by
    have ha : (tripleCharges (sourceA1674 + difference 3 5) (sourceB1674 + difference 5 3) sourceC1674) = raw12546 := by
      apply Matrix.ext; unfold tripleCharges sourceA1674 sourceB1674 sourceC1674 difference raw12546; decide +kernel
    rw [ha]
    exact (canonical12546 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1674 + difference 4 0) (sourceB1674 + difference 0 4) sourceC1674) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4145) := by
    have ha : (tripleCharges (sourceA1674 + difference 4 0) (sourceB1674 + difference 0 4) sourceC1674) = raw24570 := by
      apply Matrix.ext; unfold tripleCharges sourceA1674 sourceB1674 sourceC1674 difference raw24570; decide +kernel
    rw [ha]
    exact (canonical24570 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1674 + difference 4 1) (sourceB1674 + difference 1 4) sourceC1674) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4524) := by
    have ha : (tripleCharges (sourceA1674 + difference 4 1) (sourceB1674 + difference 1 4) sourceC1674) = raw24571 := by
      apply Matrix.ext; unfold tripleCharges sourceA1674 sourceB1674 sourceC1674 difference raw24571; decide +kernel
    rw [ha]
    exact (canonical24571 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1674 + difference 4 2) (sourceB1674 + difference 2 4) sourceC1674) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4518) := by
    have ha : (tripleCharges (sourceA1674 + difference 4 2) (sourceB1674 + difference 2 4) sourceC1674) = raw24572 := by
      apply Matrix.ext; unfold tripleCharges sourceA1674 sourceB1674 sourceC1674 difference raw24572; decide +kernel
    rw [ha]
    exact (canonical24572 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1674 + difference 4 3) (sourceB1674 + difference 3 4) sourceC1674) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4612) := by
    have ha : (tripleCharges (sourceA1674 + difference 4 3) (sourceB1674 + difference 3 4) sourceC1674) = raw24573 := by
      apply Matrix.ext; unfold tripleCharges sourceA1674 sourceB1674 sourceC1674 difference raw24573; decide +kernel
    rw [ha]
    exact (canonical24573 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1674 + difference 4 5) (sourceB1674 + difference 5 4) sourceC1674) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4602) := by
    have ha : (tripleCharges (sourceA1674 + difference 4 5) (sourceB1674 + difference 5 4) sourceC1674) = raw12551 := by
      apply Matrix.ext; unfold tripleCharges sourceA1674 sourceB1674 sourceC1674 difference raw12551; decide +kernel
    rw [ha]
    exact (canonical12551 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1674 + difference 5 0) (sourceB1674 + difference 0 5) sourceC1674) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4144) := by
    have ha : (tripleCharges (sourceA1674 + difference 5 0) (sourceB1674 + difference 0 5) sourceC1674) = raw24574 := by
      apply Matrix.ext; unfold tripleCharges sourceA1674 sourceB1674 sourceC1674 difference raw24574; decide +kernel
    rw [ha]
    exact (canonical24574 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1674 + difference 5 1) (sourceB1674 + difference 1 5) sourceC1674) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4523) := by
    have ha : (tripleCharges (sourceA1674 + difference 5 1) (sourceB1674 + difference 1 5) sourceC1674) = raw24575 := by
      apply Matrix.ext; unfold tripleCharges sourceA1674 sourceB1674 sourceC1674 difference raw24575; decide +kernel
    rw [ha]
    exact (canonical24575 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1674 + difference 5 2) (sourceB1674 + difference 2 5) sourceC1674) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4517) := by
    have ha : (tripleCharges (sourceA1674 + difference 5 2) (sourceB1674 + difference 2 5) sourceC1674) = raw24576 := by
      apply Matrix.ext; unfold tripleCharges sourceA1674 sourceB1674 sourceC1674 difference raw24576; decide +kernel
    rw [ha]
    exact (canonical24576 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1674 + difference 5 3) (sourceB1674 + difference 3 5) sourceC1674) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4608) := by
    have ha : (tripleCharges (sourceA1674 + difference 5 3) (sourceB1674 + difference 3 5) sourceC1674) = raw24577 := by
      apply Matrix.ext; unfold tripleCharges sourceA1674 sourceB1674 sourceC1674 difference raw24577; decide +kernel
    rw [ha]
    exact (canonical24577 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1674 + difference 5 4) (sourceB1674 + difference 4 5) sourceC1674) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4608) := by
    have ha : (tripleCharges (sourceA1674 + difference 5 4) (sourceB1674 + difference 4 5) sourceC1674) = raw24578 := by
      apply Matrix.ext; unfold tripleCharges sourceA1674 sourceB1674 sourceC1674 difference raw24578; decide +kernel
    rw [ha]
    exact (canonical24578 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1674 sourceB1674 sourceC1674
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1674, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic89
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reindexCheck1433 : Integer.Sparse.reindex keyMap MixedData.row1433 = numericRow1433 := by decide +kernel

theorem numericCheck1433 (x : Master → ℝ) : Integer.Sparse.eval numericRow1433 x =
    (17280 : ℝ) * reducedSource1433 x := by
  norm_num [numericRow1433, reducedSource1433, Integer.Sparse.eval, Sparse.eval, nodeValue4143, nodeValue4144, nodeValue4145, nodeValue4175, nodeValue4516, nodeValue4517, nodeValue4518, nodeValue4523, nodeValue4524, nodeValue4544, nodeValue4601, nodeValue4602, nodeValue4606, nodeValue4608, nodeValue4612, nodeValue4622, nodeValue4624, nodeValue5148, nodeValue5203, nodeValue5292, nodeValue5293]
  ring

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Rows89
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero1433 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1433 (mixedVector B) = 0 := by
  have h4143 : mixedVector B (Sum.inr 4143) = Sparse.eval nodeValue4143 (mixedVector B) := by
    change mixedMoment B node4143 node4143Labels = _
    exact sound4143 B hB hF
  have h4144 : mixedVector B (Sum.inr 4144) = Sparse.eval nodeValue4144 (mixedVector B) := by
    change mixedMoment B node4144 node4144Labels = _
    exact sound4144 B hB hF
  have h4145 : mixedVector B (Sum.inr 4145) = Sparse.eval nodeValue4145 (mixedVector B) := by
    change mixedMoment B node4145 node4145Labels = _
    exact sound4145 B hB hF
  have h4175 : mixedVector B (Sum.inr 4175) = Sparse.eval nodeValue4175 (mixedVector B) := by
    change mixedMoment B node4175 node4175Labels = _
    exact sound4175 B hB hF
  have h4516 : mixedVector B (Sum.inr 4516) = Sparse.eval nodeValue4516 (mixedVector B) := by
    change mixedMoment B node4516 node4516Labels = _
    exact sound4516 B hB hF
  have h4517 : mixedVector B (Sum.inr 4517) = Sparse.eval nodeValue4517 (mixedVector B) := by
    change mixedMoment B node4517 node4517Labels = _
    exact sound4517 B hB hF
  have h4518 : mixedVector B (Sum.inr 4518) = Sparse.eval nodeValue4518 (mixedVector B) := by
    change mixedMoment B node4518 node4518Labels = _
    exact sound4518 B hB hF
  have h4523 : mixedVector B (Sum.inr 4523) = Sparse.eval nodeValue4523 (mixedVector B) := by
    change mixedMoment B node4523 node4523Labels = _
    exact sound4523 B hB hF
  have h4524 : mixedVector B (Sum.inr 4524) = Sparse.eval nodeValue4524 (mixedVector B) := by
    change mixedMoment B node4524 node4524Labels = _
    exact sound4524 B hB hF
  have h4544 : mixedVector B (Sum.inr 4544) = Sparse.eval nodeValue4544 (mixedVector B) := by
    change mixedMoment B node4544 node4544Labels = _
    exact sound4544 B hB hF
  have h4601 : mixedVector B (Sum.inr 4601) = Sparse.eval nodeValue4601 (mixedVector B) := by
    change mixedMoment B node4601 node4601Labels = _
    exact sound4601 B hB hF
  have h4602 : mixedVector B (Sum.inr 4602) = Sparse.eval nodeValue4602 (mixedVector B) := by
    change mixedMoment B node4602 node4602Labels = _
    exact sound4602 B hB hF
  have h4606 : mixedVector B (Sum.inr 4606) = Sparse.eval nodeValue4606 (mixedVector B) := by
    change mixedMoment B node4606 node4606Labels = _
    exact sound4606 B hB hF
  have h4608 : mixedVector B (Sum.inr 4608) = Sparse.eval nodeValue4608 (mixedVector B) := by
    change mixedMoment B node4608 node4608Labels = _
    exact sound4608 B hB hF
  have h4612 : mixedVector B (Sum.inr 4612) = Sparse.eval nodeValue4612 (mixedVector B) := by
    change mixedMoment B node4612 node4612Labels = _
    exact sound4612 B hB hF
  have h4622 : mixedVector B (Sum.inr 4622) = Sparse.eval nodeValue4622 (mixedVector B) := by
    change mixedMoment B node4622 node4622Labels = _
    exact sound4622 B hB hF
  have h4624 : mixedVector B (Sum.inr 4624) = Sparse.eval nodeValue4624 (mixedVector B) := by
    change mixedMoment B node4624 node4624Labels = _
    exact sound4624 B hB hF
  have h5148 : mixedVector B (Sum.inr 5148) = Sparse.eval nodeValue5148 (mixedVector B) := by
    change mixedMoment B node5148 node5148Labels = _
    exact sound5148 B hB hF
  have h5203 : mixedVector B (Sum.inr 5203) = Sparse.eval nodeValue5203 (mixedVector B) := by
    change mixedMoment B node5203 node5203Labels = _
    exact sound5203 B hB hF
  have h5292 : mixedVector B (Sum.inr 5292) = Sparse.eval nodeValue5292 (mixedVector B) := by
    change mixedMoment B node5292 node5292Labels = _
    exact sound5292_e B hB hF
  have h5293 : mixedVector B (Sum.inr 5293) = Sparse.eval nodeValue5293 (mixedVector B) := by
    change mixedMoment B node5293 node5293Labels = _
    exact sound5293 B hB hF
  simpa only [sourceForm1674, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4143, h4144, h4145, h4175, h4516, h4517, h4518, h4523, h4524, h4544, h4601, h4602, h4606, h4608, h4612, h4622, h4624, h5148, h5203, h5292, h5293, reducedSource1433] using sourceEq1674 B hB

theorem rowSound1433_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1433 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1433, numericCheck1433, reducedZero1433 B hB hF, mul_zero]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedSourceBridge.rowSound1433_e_oai := @OAI.MUB6.Certificate.MixedSourceBridge.rowSound1433_e_oai
